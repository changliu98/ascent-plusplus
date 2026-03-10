//! Concurrent (par) index types for binary transitive relations.
//!
//! This is the `ascent_par!` counterpart of `trrel_binary_ind.rs`.
//! Follows the same pattern as `ceqrel_ind.rs` does for `eqrel_ind.rs`.

use std::hash::{Hash, BuildHasherDefault};
use std::iter::Map;
use std::marker::PhantomData;
use std::sync::Mutex;
use std::time::{Duration, Instant};

use ascent::internal::{
    CRelFullIndexWrite, CRelIndexRead, CRelIndexReadAll, CRelIndexWrite, Freezable,
    RelFullIndexRead, RelFullIndexWrite, RelIndexMerge, RelIndexRead, RelIndexReadAll,
    RelIndexWrite,
};
use ascent::internal::ToRelIndex0;
use ascent::rayon;
use ascent::rayon::prelude::*;
use hashbrown::HashMap;
use rustc_hash::FxHasher;

use crate::binary_rel::BinaryRel;
use crate::iterator_from_dyn::IteratorFromDyn;
use crate::rel_boilerplate::NoopRelIndexWrite;
use crate::trrel_binary::{MyHashSet, MyHashSetIter};
use crate::utils::{move_hash_map_of_hash_set_contents_disjoint, move_hash_map_of_vec_contents};

// ─── Main concurrent wrapper ────────────────────────────────────────────────

/// Concurrent wrapper for `TrRelIndCommon`.
///
/// - **WriteTarget**: used for the `new` copy during parallel rule evaluation.
///   Concurrent writes go through a `Mutex<BinaryRel<T>>`.
/// - **ReadSource**: used for `delta` and `total` copies. Lock-free reads.
pub enum CTrRelIndCommon<T: Clone + Hash + Eq> {
    WriteTarget {
        rel: Mutex<BinaryRel<T>>,
        anti_reflexive: bool,
    },
    ReadSource {
        rel: BinaryRel<T>,
        anti_reflexive: bool,
    },
}

impl<T: Clone + Hash + Eq> CTrRelIndCommon<T> {
    pub fn anti_reflexive(&self) -> bool {
        match self {
            CTrRelIndCommon::WriteTarget { anti_reflexive, .. } => *anti_reflexive,
            CTrRelIndCommon::ReadSource { anti_reflexive, .. } => *anti_reflexive,
        }
    }

    pub fn rel(&self) -> &BinaryRel<T> {
        match self {
            CTrRelIndCommon::ReadSource { rel, .. } => rel,
            CTrRelIndCommon::WriteTarget { .. } => panic!("CTrRelIndCommon::rel() called on WriteTarget"),
        }
    }

    fn unwrap_read_source(&self) -> &BinaryRel<T> {
        match self {
            CTrRelIndCommon::ReadSource { rel, .. } => rel,
            _ => panic!("unwrap_read_source called on WriteTarget"),
        }
    }

    fn unwrap_mut_read_source(&mut self) -> &mut BinaryRel<T> {
        match self {
            CTrRelIndCommon::ReadSource { rel, .. } => rel,
            _ => panic!("unwrap_mut_read_source called on WriteTarget"),
        }
    }

    fn unwrap_write_mutex(&self) -> &Mutex<BinaryRel<T>> {
        match self {
            CTrRelIndCommon::WriteTarget { rel, .. } => rel,
            _ => panic!("unwrap_write_mutex called on ReadSource"),
        }
    }

    fn take_write_target(&mut self) -> BinaryRel<T> {
        match self {
            CTrRelIndCommon::WriteTarget { rel, .. } => {
                std::mem::take(rel.get_mut().unwrap())
            }
            _ => panic!("take_write_target called on ReadSource"),
        }
    }

    #[inline]
    pub fn insert(&self, x: T, y: T) -> bool {
        self.unwrap_write_mutex().lock().unwrap().insert(x, y)
    }

    #[inline]
    pub fn insert_by_ref(&self, x: &T, y: &T) -> bool {
        self.unwrap_write_mutex().lock().unwrap().insert_by_ref(x, y)
    }

    pub fn is_empty(&self) -> bool {
        match self {
            CTrRelIndCommon::WriteTarget { rel, .. } => rel.lock().unwrap().map.is_empty(),
            CTrRelIndCommon::ReadSource { rel, .. } => rel.map.is_empty(),
        }
    }
}

impl<T: Clone + Hash + Eq> Clone for CTrRelIndCommon<T> {
    fn clone(&self) -> Self {
        match self {
            CTrRelIndCommon::WriteTarget { rel, anti_reflexive } => {
                CTrRelIndCommon::WriteTarget {
                    rel: Mutex::new(rel.lock().unwrap().clone()),
                    anti_reflexive: *anti_reflexive,
                }
            }
            CTrRelIndCommon::ReadSource { rel, anti_reflexive } => {
                CTrRelIndCommon::ReadSource {
                    rel: rel.clone(),
                    anti_reflexive: *anti_reflexive,
                }
            }
        }
    }
}

impl<T: Clone + Hash + Eq> Default for CTrRelIndCommon<T> {
    fn default() -> Self {
        Self::ReadSource {
            rel: Default::default(),
            anti_reflexive: true,
        }
    }
}

impl<T: Clone + Hash + Eq> Freezable for CTrRelIndCommon<T> {}

pub static mut MERGE_TIME: Duration = Duration::ZERO;
pub static mut MERGE_COUNT: usize = 0;

// ─── Trait: access from adaptor structs ─────────────────────────────────────

pub trait ToCTrRelIndCommon<T: Clone + Hash + Eq> {
    fn to_ctr_rel_ind(&self) -> &CTrRelIndCommon<T>;
    fn to_ctr_rel_ind_mut(&mut self) -> &mut CTrRelIndCommon<T>;
}

impl<T: Clone + Hash + Eq> ToCTrRelIndCommon<T> for CTrRelIndCommon<T> {
    fn to_ctr_rel_ind(&self) -> &CTrRelIndCommon<T> {
        self
    }
    fn to_ctr_rel_ind_mut(&mut self) -> &mut CTrRelIndCommon<T> {
        self
    }
}

// ─── RelIndexMerge ──────────────────────────────────────────────────────────
// This is the core transitive closure merge, reused from the serial version.
// It runs sequentially between iterations.

impl<T: Clone + Hash + Eq> RelIndexMerge for CTrRelIndCommon<T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) {
        panic!("merge_delta_to_total_new_to_delta must be called instead.")
    }

    fn init(new: &mut Self, delta: &mut Self, total: &mut Self) {
        assert!(matches!(delta, Self::ReadSource { .. }));
        assert!(matches!(total, Self::ReadSource { .. }));
        let ar = delta.anti_reflexive();
        *new = Self::WriteTarget {
            rel: Mutex::new(Default::default()),
            anti_reflexive: ar,
        };
    }

    fn merge_delta_to_total_new_to_delta(new: &mut Self, delta: &mut Self, total: &mut Self) {
        let before = Instant::now();
        let anti_reflexive = total.anti_reflexive();

        let mut total_rel = std::mem::take(total.unwrap_mut_read_source());
        let mut delta_rel = std::mem::take(delta.unwrap_mut_read_source());

        move_hash_map_of_hash_set_contents_disjoint(&mut delta_rel.map, &mut total_rel.map);
        move_hash_map_of_vec_contents(&mut delta_rel.reverse_map, &mut total_rel.reverse_map);

        let mut new_delta = BinaryRel::<T>::default();

        type RelMap<T> = HashMap<
            T,
            MyHashSet<T, BuildHasherDefault<FxHasher>>,
            BuildHasherDefault<FxHasher>,
        >;
        type RelRevMap<T> = HashMap<T, Vec<T>, BuildHasherDefault<FxHasher>>;

        let new_rel = new.take_write_target();
        let new_map = new_rel.map;
        let mut delta_delta_map = new_map.clone();
        let mut delta_delta_rev_map = new_rel.reverse_map;

        let mut delta_total_map = RelMap::<T>::default();
        let mut delta_total_rev_map = RelRevMap::<T>::default();

        let mut delta_new_map = RelMap::<T>::default();
        let mut delta_new_rev_map = RelRevMap::<T>::default();

        fn join<T: Clone + Hash + Eq>(
            target: &mut RelMap<T>,
            target_rev: &mut RelRevMap<T>,
            rel1: &RelMap<T>,
            rel2_rev: &RelRevMap<T>,
            mut can_add: impl FnMut(&T, &T) -> bool,
            _name: &str,
        ) -> bool {
            let mut changed = false;
            if rel1.len() < rel2_rev.len() {
                for (x, x_set) in rel1.iter() {
                    if let Some(x_rev_set) = rel2_rev.get(x) {
                        for w in x_rev_set {
                            let entry = target.entry(w.clone()).or_default();
                            for y in x_set.iter() {
                                if !can_add(w, y) {
                                    continue;
                                }
                                if entry.insert(y.clone()) {
                                    target_rev.entry(y.clone()).or_default().push(w.clone());
                                    changed = true;
                                }
                            }
                            if entry.is_empty() {
                                target.remove(w);
                            }
                        }
                    }
                }
            } else {
                for (x, x_rev_set) in rel2_rev.iter() {
                    if let Some(x_set) = rel1.get(x) {
                        for w in x_rev_set {
                            let entry = target.entry(w.clone()).or_default();
                            for y in x_set.iter() {
                                if !can_add(w, y) {
                                    continue;
                                }
                                if entry.insert(y.clone()) {
                                    target_rev.entry(y.clone()).or_default().push(w.clone());
                                    changed = true;
                                }
                            }
                            if entry.is_empty() {
                                target.remove(w);
                            }
                        }
                    }
                }
            }
            changed
        }

        loop {
            let mut cached_delta_delta_map_entry_for_can_add = None;
            let mut cached_delta_delta_map_x_for_can_add = None;
            let mut cached_delta_total_map_entry_for_can_add = None;
            let mut cached_delta_total_map_x_for_can_add = None;
            let mut cached_total_map_entry_for_can_add = None;
            let mut cached_total_map_x_for_can_add = None;
            let mut can_add = |x: &T, y: &T| {
                if anti_reflexive && x == y {
                    return false;
                }
                {
                    if cached_delta_delta_map_x_for_can_add.as_ref() != Some(x) {
                        cached_delta_delta_map_entry_for_can_add = delta_delta_map.get(x);
                        cached_delta_delta_map_x_for_can_add = Some(x.clone());
                    };
                }
                !cached_delta_delta_map_entry_for_can_add.map_or(false, |s| s.contains(y))
                    && {
                        if cached_delta_total_map_x_for_can_add.as_ref() != Some(x) {
                            cached_delta_total_map_entry_for_can_add = delta_total_map.get(x);
                            cached_delta_total_map_x_for_can_add = Some(x.clone());
                        };
                        !cached_delta_total_map_entry_for_can_add.map_or(false, |s| s.contains(y))
                    }
                    && {
                        if cached_total_map_x_for_can_add.as_ref() != Some(x) {
                            cached_total_map_entry_for_can_add = total_rel.map.get(x);
                            cached_total_map_x_for_can_add = Some(x.clone());
                        }
                        !cached_total_map_entry_for_can_add.map_or(false, |s| s.contains(y))
                    }
            };

            let join1 = join(
                &mut delta_new_map,
                &mut delta_new_rev_map,
                &delta_delta_map,
                &total_rel.reverse_map,
                &mut can_add,
                "join1",
            );
            let join2 = join(
                &mut delta_new_map,
                &mut delta_new_rev_map,
                &total_rel.map,
                &delta_delta_rev_map,
                &mut can_add,
                "join2",
            );
            let join3 = join(
                &mut delta_new_map,
                &mut delta_new_rev_map,
                &new_map,
                &delta_delta_rev_map,
                &mut can_add,
                "join3",
            );

            let changed = join1 | join2 | join3;

            move_hash_map_of_hash_set_contents_disjoint(
                &mut delta_delta_map,
                &mut delta_total_map,
            );
            move_hash_map_of_vec_contents(&mut delta_delta_rev_map, &mut delta_total_rev_map);

            assert!(delta_delta_map.is_empty());
            assert!(delta_delta_rev_map.is_empty());

            std::mem::swap(&mut delta_delta_map, &mut delta_new_map);
            std::mem::swap(&mut delta_delta_rev_map, &mut delta_new_rev_map);

            if !changed {
                break;
            }
        }
        new_delta.map = delta_total_map;
        new_delta.reverse_map = delta_total_rev_map;

        *total = CTrRelIndCommon::ReadSource {
            rel: total_rel,
            anti_reflexive,
        };
        *delta = CTrRelIndCommon::ReadSource {
            rel: new_delta,
            anti_reflexive,
        };
        *new = CTrRelIndCommon::WriteTarget {
            rel: Mutex::new(Default::default()),
            anti_reflexive,
        };

        unsafe {
            MERGE_TIME += before.elapsed();
            MERGE_COUNT += 1;
        }
    }
}

// ─── Write traits on CTrRelIndCommon directly ───────────────────────────────

impl<T: Clone + Hash + Eq> RelIndexWrite for CTrRelIndCommon<T> {
    type Key = (T, T);
    type Value = ();

    fn index_insert(&mut self, key: Self::Key, _value: Self::Value) {
        match self {
            CTrRelIndCommon::WriteTarget { rel, .. } => {
                rel.get_mut().unwrap().insert(key.0, key.1);
            }
            _ => panic!("index_insert on ReadSource"),
        }
    }
}

impl<T: Clone + Hash + Eq> CRelIndexWrite for CTrRelIndCommon<T> {
    type Key = (T, T);
    type Value = ();

    fn index_insert(&self, key: Self::Key, _value: Self::Value) {
        self.insert(key.0, key.1);
    }
}

impl<T: Clone + Hash + Eq> RelFullIndexWrite for CTrRelIndCommon<T> {
    type Key = (T, T);
    type Value = ();

    fn insert_if_not_present(&mut self, key: &Self::Key, _v: Self::Value) -> bool {
        match self {
            CTrRelIndCommon::WriteTarget { rel, .. } => {
                rel.get_mut().unwrap().insert_by_ref(&key.0, &key.1)
            }
            _ => panic!("insert_if_not_present on ReadSource"),
        }
    }
}

impl<T: Clone + Hash + Eq> CRelFullIndexWrite for CTrRelIndCommon<T> {
    type Key = (T, T);
    type Value = ();

    fn insert_if_not_present(&self, key: &Self::Key, _v: Self::Value) -> bool {
        self.insert_by_ref(&key.0, &key.1)
    }
}

// ─── Read traits on CTrRelIndCommon (full-index / [0,1]) ────────────────────

impl<'a, T: Clone + Hash + Eq + 'a> RelFullIndexRead<'a> for CTrRelIndCommon<T> {
    type Key = (T, T);

    fn contains_key(&'a self, key: &Self::Key) -> bool {
        self.unwrap_read_source()
            .map
            .get(&key.0)
            .map_or(false, |s| s.contains(&key.1))
    }
}

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexRead<'a> for CTrRelIndCommon<T> {
    type Key = &'a (T, T);
    type Value = ();
    type IteratorType = std::iter::Once<()>;

    fn index_get(&'a self, (x, y): &Self::Key) -> Option<Self::IteratorType> {
        if self
            .unwrap_read_source()
            .map
            .get(x)
            .map_or(false, |s| s.contains(y))
        {
            Some(std::iter::once(()))
        } else {
            None
        }
    }

    fn len(&self) -> usize {
        let rel = self.unwrap_read_source();
        let sample_size = 3;
        let sum: usize = rel.map.values().take(sample_size).map(|x| x.len()).sum();
        let map_len = rel.map.len();
        sum * map_len / sample_size.min(map_len).max(1)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + 'a> CRelIndexRead<'a> for CTrRelIndCommon<T> {
    type Key = &'a (T, T);
    type Value = ();
    type IteratorType = rayon::iter::Once<()>;

    fn c_index_get(&'a self, (x, y): &Self::Key) -> Option<Self::IteratorType> {
        if self
            .unwrap_read_source()
            .map
            .get(x)
            .map_or(false, |s| s.contains(y))
        {
            Some(rayon::iter::once(()))
        } else {
            None
        }
    }
}

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexReadAll<'a> for CTrRelIndCommon<T> {
    type Key = (&'a T, &'a T);
    type Value = ();
    type ValueIteratorType = std::iter::Once<()>;
    type AllIteratorType = Box<dyn Iterator<Item = (Self::Key, Self::ValueIteratorType)> + 'a>;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        let rel = self.unwrap_read_source();
        Box::new(
            rel.map
                .iter()
                .flat_map(|(x, x_set)| x_set.iter().map(move |y| ((x, y), std::iter::once(())))),
        )
    }
}

// Parallel iterator for iterating all (x, y) pairs in a BinaryRel.
#[derive(Clone)]
pub struct AllPairsParIter<'a, T: Clone + Hash + Eq + Sync + Send>(pub &'a BinaryRel<T>);

impl<'a, T: Clone + Hash + Eq + Sync + Send> ParallelIterator for AllPairsParIter<'a, T> {
    type Item = ((&'a T, &'a T), rayon::iter::Once<()>);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: rayon::iter::plumbing::UnindexedConsumer<Self::Item>,
    {
        self.0
            .map
            .par_iter()
            .flat_map(|(x, x_set)| {
                x_set
                    .par_iter()
                    .map(move |y| ((x, y), rayon::iter::once(())))
            })
            .drive_unindexed(consumer)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send + 'a> CRelIndexReadAll<'a> for CTrRelIndCommon<T> {
    type Key = (&'a T, &'a T);
    type Value = ();
    type ValueIteratorType = rayon::iter::Once<()>;
    type AllIteratorType = AllPairsParIter<'a, T>;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        AllPairsParIter(self.unwrap_read_source())
    }
}

// Clone-able parallel iterator wrapper for hashbrown HashSet.
// `CRelIndexRead::IteratorType` requires Clone, but `hashbrown::hash_set::rayon::ParIter`
// does not implement Clone. This wrapper holds a reference (Copy) and creates the
// parallel iterator inside `drive_unindexed`.
#[derive(Clone)]
pub struct HashSetParIter<'a, T: Eq + Hash + Sync>(
    pub &'a MyHashSet<T, BuildHasherDefault<FxHasher>>,
);

impl<'a, T: Eq + Hash + Sync + Send> ParallelIterator for HashSetParIter<'a, T> {
    type Item = &'a T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: rayon::iter::plumbing::UnindexedConsumer<Self::Item>,
    {
        self.0.par_iter().drive_unindexed(consumer)
    }
}

// ─── Index by column 0 (forward map) ───────────────────────────────────────

pub struct CTrRelInd0<'a, T: Clone + Hash + Eq>(pub(crate) &'a CTrRelIndCommon<T>);

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexRead<'a> for CTrRelInd0<'a, T> {
    type Key = (T,);
    type Value = (&'a T,);
    type IteratorType = Map<MyHashSetIter<'a, T>, fn(&T) -> (&T,)>;

    fn index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        let set = self.0.unwrap_read_source().map.get(&key.0)?;
        Some(set.iter().map(|x| (x,)))
    }

    fn len(&self) -> usize {
        self.0.unwrap_read_source().map.len()
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send + 'a> CRelIndexRead<'a> for CTrRelInd0<'a, T> {
    type Key = (T,);
    type Value = (&'a T,);
    type IteratorType = rayon::iter::Map<HashSetParIter<'a, T>, fn(&T) -> (&T,)>;

    fn c_index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        let set = self.0.unwrap_read_source().map.get(&key.0)?;
        Some(HashSetParIter(set).map(|x| (x,)))
    }
}

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexReadAll<'a> for CTrRelInd0<'a, T> {
    type Key = (&'a T,);
    type Value = (&'a T,);
    type ValueIteratorType = Map<MyHashSetIter<'a, T>, fn(&T) -> (&T,)>;
    type AllIteratorType = Map<
        hashbrown::hash_map::Iter<
            'a,
            T,
            MyHashSet<T, BuildHasherDefault<FxHasher>>,
        >,
        for<'aa> fn(
            (
                &'aa T,
                &'aa MyHashSet<T, BuildHasherDefault<FxHasher>>,
            ),
        ) -> (
            (&'aa T,),
            Map<MyHashSetIter<'aa, T>, for<'bb> fn(&'bb T) -> (&'bb T,)>,
        ),
    >;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        self.0
            .unwrap_read_source()
            .map
            .iter()
            .map(|(k, v)| ((k,), v.iter().map(|x| (x,))))
    }
}

// Parallel iterator for index-0 ReadAll
#[derive(Clone)]
pub struct CTrRelInd0ParIterAll<'a, T: Clone + Hash + Eq + Sync + Send>(pub &'a BinaryRel<T>);

impl<'a, T: Clone + Hash + Eq + Sync + Send> ParallelIterator for CTrRelInd0ParIterAll<'a, T> {
    type Item = (
        (&'a T,),
        rayon::iter::Map<
            hashbrown::hash_set::rayon::ParIter<'a, T>,
            fn(&T) -> (&T,),
        >,
    );

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: rayon::iter::plumbing::UnindexedConsumer<Self::Item>,
    {
        self.0
            .map
            .par_iter()
            .map(|(k, v)| {
                let vals: rayon::iter::Map<
                    hashbrown::hash_set::rayon::ParIter<'a, T>,
                    fn(&T) -> (&T,),
                > = v.par_iter().map(|x| (x,));
                ((k,), vals)
            })
            .drive_unindexed(consumer)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send + 'a> CRelIndexReadAll<'a> for CTrRelInd0<'a, T> {
    type Key = (&'a T,);
    type Value = (&'a T,);
    type ValueIteratorType = rayon::iter::Map<
        hashbrown::hash_set::rayon::ParIter<'a, T>,
        fn(&T) -> (&T,),
    >;
    type AllIteratorType = CTrRelInd0ParIterAll<'a, T>;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        CTrRelInd0ParIterAll(self.0.unwrap_read_source())
    }
}

impl<'a, T: Clone + Hash + Eq> RelIndexWrite for CTrRelInd0<'a, T> {
    type Key = (T,);
    type Value = (T,);
    fn index_insert(&mut self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<'a, T: Clone + Hash + Eq> CRelIndexWrite for CTrRelInd0<'a, T> {
    type Key = (T,);
    type Value = (T,);
    fn index_insert(&self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<'a, T: Clone + Hash + Eq> RelIndexMerge for CTrRelInd0<'a, T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) { /* noop */ }
}

// ─── Index by column 1 (reverse map) ───────────────────────────────────────

pub struct CTrRelInd1<'a, T: Clone + Hash + Eq>(pub(crate) &'a CTrRelIndCommon<T>);

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexRead<'a> for CTrRelInd1<'a, T> {
    type Key = (T,);
    type Value = (&'a T,);
    type IteratorType = Map<std::slice::Iter<'a, T>, fn(&T) -> (&T,)>;

    fn index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        let set = self.0.rel().reverse_map.get(&key.0)?;
        Some(set.iter().map(|x| (x,)))
    }

    fn len(&self) -> usize {
        self.0.rel().reverse_map.len()
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send + 'a> CRelIndexRead<'a> for CTrRelInd1<'a, T> {
    type Key = (T,);
    type Value = (&'a T,);
    type IteratorType = rayon::iter::Map<rayon::slice::Iter<'a, T>, fn(&T) -> (&T,)>;

    fn c_index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        let vec = self.0.rel().reverse_map.get(&key.0)?;
        Some(vec.par_iter().map(|x| (x,)))
    }
}

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexReadAll<'a> for CTrRelInd1<'a, T> {
    type Key = (&'a T,);
    type Value = (&'a T,);
    type ValueIteratorType = Map<std::slice::Iter<'a, T>, fn(&T) -> (&T,)>;
    type AllIteratorType = Map<
        hashbrown::hash_map::Iter<'a, T, Vec<T>>,
        for<'aa> fn(
            (&'aa T, &'aa Vec<T>),
        ) -> (
            (&'aa T,),
            Map<std::slice::Iter<'aa, T>, for<'bb> fn(&'bb T) -> (&'bb T,)>,
        ),
    >;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        self.0
            .rel()
            .reverse_map
            .iter()
            .map(|(k, v)| ((k,), v.iter().map(|x| (x,))))
    }
}

// Parallel iterator for index-1 ReadAll
#[derive(Clone)]
pub struct CTrRelInd1ParIterAll<'a, T: Clone + Hash + Eq + Sync + Send>(pub &'a BinaryRel<T>);

impl<'a, T: Clone + Hash + Eq + Sync + Send> ParallelIterator for CTrRelInd1ParIterAll<'a, T> {
    type Item = (
        (&'a T,),
        rayon::iter::Map<rayon::slice::Iter<'a, T>, fn(&T) -> (&T,)>,
    );

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: rayon::iter::plumbing::UnindexedConsumer<Self::Item>,
    {
        self.0
            .reverse_map
            .par_iter()
            .map(|(k, v)| {
                let vals: rayon::iter::Map<rayon::slice::Iter<'a, T>, fn(&T) -> (&T,)> =
                    v.par_iter().map(|x| (x,));
                ((k,), vals)
            })
            .drive_unindexed(consumer)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send + 'a> CRelIndexReadAll<'a> for CTrRelInd1<'a, T> {
    type Key = (&'a T,);
    type Value = (&'a T,);
    type ValueIteratorType = rayon::iter::Map<rayon::slice::Iter<'a, T>, fn(&T) -> (&T,)>;
    type AllIteratorType = CTrRelInd1ParIterAll<'a, T>;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        CTrRelInd1ParIterAll(self.0.rel())
    }
}

impl<'a, T: Clone + Hash + Eq> RelIndexWrite for CTrRelInd1<'a, T> {
    type Key = (T,);
    type Value = (T,);
    fn index_insert(&mut self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<'a, T: Clone + Hash + Eq> CRelIndexWrite for CTrRelInd1<'a, T> {
    type Key = (T,);
    type Value = (T,);
    fn index_insert(&self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<'a, T: Clone + Hash + Eq> RelIndexMerge for CTrRelInd1<'a, T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) { /* noop */ }
}

// ─── No index (iterate all pairs) ──────────────────────────────────────────

pub struct CTrRelIndNone<'a, T: Clone + Hash + Eq>(&'a CTrRelIndCommon<T>);

impl<'a, T: Clone + Hash + Eq> RelIndexRead<'a> for CTrRelIndNone<'a, T> {
    type Key = ();
    type Value = (&'a T, &'a T);
    type IteratorType = IteratorFromDyn<'a, Self::Value>;

    fn index_get(&'a self, (): &Self::Key) -> Option<Self::IteratorType> {
        let rel = self.0.unwrap_read_source();
        let res = || {
            rel.map
                .iter()
                .flat_map(|(x, x_set)| x_set.iter().map(move |y| (x, y)))
        };
        Some(IteratorFromDyn::new(res))
    }

    fn len(&self) -> usize {
        1
    }
}

// Parallel iterator over all (x, y) pairs
#[derive(Clone)]
pub struct CTrRelIndNoneParIter<'a, T: Clone + Hash + Eq + Sync + Send>(pub &'a BinaryRel<T>);

impl<'a, T: Clone + Hash + Eq + Sync + Send> ParallelIterator for CTrRelIndNoneParIter<'a, T> {
    type Item = (&'a T, &'a T);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: rayon::iter::plumbing::UnindexedConsumer<Self::Item>,
    {
        self.0
            .map
            .par_iter()
            .flat_map(|(x, x_set)| x_set.par_iter().map(move |y| (x, y)))
            .drive_unindexed(consumer)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> CRelIndexRead<'a> for CTrRelIndNone<'a, T> {
    type Key = ();
    type Value = (&'a T, &'a T);
    type IteratorType = CTrRelIndNoneParIter<'a, T>;

    fn c_index_get(&'a self, _key: &Self::Key) -> Option<Self::IteratorType> {
        Some(CTrRelIndNoneParIter(self.0.unwrap_read_source()))
    }
}

impl<'a, T: Clone + Hash + Eq> RelIndexReadAll<'a> for CTrRelIndNone<'a, T> {
    type Key = ();
    type Value = (&'a T, &'a T);
    type ValueIteratorType = <Self as RelIndexRead<'a>>::IteratorType;
    type AllIteratorType = std::iter::Once<((), Self::ValueIteratorType)>;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        std::iter::once(((), self.index_get(&()).unwrap()))
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> CRelIndexReadAll<'a> for CTrRelIndNone<'a, T> {
    type Key = ();
    type Value = (&'a T, &'a T);
    type ValueIteratorType = CTrRelIndNoneParIter<'a, T>;
    type AllIteratorType = rayon::iter::Once<((), Self::ValueIteratorType)>;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        rayon::iter::once(((), CTrRelIndNoneParIter(self.0.unwrap_read_source())))
    }
}

impl<'a, T: Clone + Hash + Eq> RelIndexWrite for CTrRelIndNone<'a, T> {
    type Key = ();
    type Value = (T, T);
    fn index_insert(&mut self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<'a, T: Clone + Hash + Eq> CRelIndexWrite for CTrRelIndNone<'a, T> {
    type Key = ();
    type Value = (T, T);
    fn index_insert(&self, _key: Self::Key, _value: Self::Value) { /* noop */ }
}

impl<'a, T: Clone + Hash + Eq> RelIndexMerge for CTrRelIndNone<'a, T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) { /* noop */ }
}

// ─── Full index (read-only view) ───────────────────────────────────────────

pub struct CTrRelIndFull<'a, T: Clone + Hash + Eq>(pub(crate) &'a CTrRelIndCommon<T>);

impl<'a, T: Clone + Hash + Eq> RelFullIndexRead<'a> for CTrRelIndFull<'a, T> {
    type Key = (T, T);

    fn contains_key(&'a self, key: &Self::Key) -> bool {
        self.0
            .rel()
            .map
            .get(&key.0)
            .map_or(false, |s| s.contains(&key.1))
    }
}

impl<'a, T: Clone + Hash + Eq> RelIndexRead<'a> for CTrRelIndFull<'a, T> {
    type Key = (T, T);
    type Value = ();
    type IteratorType = std::iter::Once<()>;

    fn index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        if self.0.rel().map.get(&key.0)?.contains(&key.1) {
            Some(std::iter::once(()))
        } else {
            None
        }
    }

    fn len(&self) -> usize {
        let rel = self.0.rel();
        let sample_size = 3;
        let sum: usize = rel.map.values().take(sample_size).map(|x| x.len()).sum();
        let map_len = rel.map.len();
        sum * map_len / sample_size.min(map_len).max(1)
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send> CRelIndexRead<'a> for CTrRelIndFull<'a, T> {
    type Key = (T, T);
    type Value = ();
    type IteratorType = rayon::iter::Once<()>;

    fn c_index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
        if self.0.rel().map.get(&key.0)?.contains(&key.1) {
            Some(rayon::iter::once(()))
        } else {
            None
        }
    }
}

impl<'a, T: Clone + Hash + Eq + 'a> RelIndexReadAll<'a> for CTrRelIndFull<'a, T> {
    type Key = (&'a T, &'a T);
    type Value = ();
    type ValueIteratorType = std::iter::Once<Self::Value>;
    type AllIteratorType = Box<dyn Iterator<Item = (Self::Key, Self::ValueIteratorType)> + 'a>;

    fn iter_all(&'a self) -> Self::AllIteratorType {
        let rel = self.0.rel();
        Box::new(
            rel.map
                .iter()
                .flat_map(|(x, x_set)| x_set.iter().map(move |y| ((x, y), std::iter::once(())))),
        )
    }
}

impl<'a, T: Clone + Hash + Eq + Sync + Send + 'a> CRelIndexReadAll<'a> for CTrRelIndFull<'a, T> {
    type Key = (&'a T, &'a T);
    type Value = ();
    type ValueIteratorType = rayon::iter::Once<()>;
    type AllIteratorType = AllPairsParIter<'a, T>;

    fn c_iter_all(&'a self) -> Self::AllIteratorType {
        AllPairsParIter(self.0.rel())
    }
}

// ─── Full index write (concurrent) ─────────────────────────────────────────

pub struct CTrRelIndFullWrite<'a, T: Clone + Hash + Eq>(&'a CTrRelIndCommon<T>);

impl<'a, T: Clone + Hash + Eq> RelIndexMerge for CTrRelIndFullWrite<'a, T> {
    fn move_index_contents(_from: &mut Self, _to: &mut Self) { /* noop */ }
}

impl<'a, T: Clone + Hash + Eq> RelIndexWrite for CTrRelIndFullWrite<'a, T> {
    type Key = (T, T);
    type Value = ();

    fn index_insert(&mut self, key: Self::Key, _value: Self::Value) {
        self.0.insert(key.0, key.1);
    }
}

impl<'a, T: Clone + Hash + Eq> CRelIndexWrite for CTrRelIndFullWrite<'a, T> {
    type Key = (T, T);
    type Value = ();

    fn index_insert(&self, key: Self::Key, _value: Self::Value) {
        self.0.insert(key.0, key.1);
    }
}

impl<'a, T: Clone + Hash + Eq> RelFullIndexWrite for CTrRelIndFullWrite<'a, T> {
    type Key = (T, T);
    type Value = ();

    fn insert_if_not_present(&mut self, key: &Self::Key, _v: Self::Value) -> bool {
        self.0.insert_by_ref(&key.0, &key.1)
    }
}

impl<'a, T: Clone + Hash + Eq> CRelFullIndexWrite for CTrRelIndFullWrite<'a, T> {
    type Key = (T, T);
    type Value = ();

    fn insert_if_not_present(&self, key: &Self::Key, _v: Self::Value) -> bool {
        self.0.insert_by_ref(&key.0, &key.1)
    }
}

// ─── ToRelIndex0 adaptor structs ────────────────────────────────────────────
// These are the types referenced from the macros in trrel.rs.
// They must implement ToRelIndex0 (which has CRelIndexWrite) for par support.

macro_rules! to_ctr_rel_ind {
    ($adaptor_name:ident, $index_name:ident, $key:ty, $val:ty) => {
        pub struct $adaptor_name<T: Clone + Hash + Eq>(PhantomData<T>);

        impl<T: Clone + Hash + Eq> Freezable for $adaptor_name<T> {}

        impl<T: Clone + Hash + Eq> Default for $adaptor_name<T> {
            fn default() -> Self {
                Self(PhantomData)
            }
        }

        impl<T: Clone + Hash + Eq> ToRelIndex0<CTrRelIndCommon<T>> for $adaptor_name<T>
        {
            type RelIndex<'a> = $index_name<'a, T> where Self: 'a, T: 'a;
            fn to_rel_index<'a>(&'a self, rel: &'a CTrRelIndCommon<T>) -> Self::RelIndex<'a> {
                $index_name(rel)
            }

            type RelIndexWrite<'a> = NoopRelIndexWrite<$key, $val> where Self: 'a, T: 'a;
            fn to_rel_index_write<'a>(
                &'a mut self,
                _rel: &'a mut CTrRelIndCommon<T>,
            ) -> Self::RelIndexWrite<'a> {
                NoopRelIndexWrite::default()
            }

            type CRelIndexWrite<'a> = NoopRelIndexWrite<$key, $val> where Self: 'a, T: 'a;
            fn to_c_rel_index_write<'a>(
                &'a self,
                _rel: &'a CTrRelIndCommon<T>,
            ) -> Self::CRelIndexWrite<'a> {
                NoopRelIndexWrite::default()
            }
        }
    };
}

to_ctr_rel_ind!(ToCTrRelIndNone, CTrRelIndNone, (), (T, T));
to_ctr_rel_ind!(ToCTrRelInd0, CTrRelInd0, (T,), (T,));
to_ctr_rel_ind!(ToCTrRelInd1, CTrRelInd1, (T,), (T,));

// Full index adaptor — special because it has actual writes
pub struct ToCTrRelIndFull<T: Clone + Hash + Eq>(PhantomData<T>);

impl<T: Clone + Hash + Eq> Freezable for ToCTrRelIndFull<T> {}

impl<T: Clone + Hash + Eq> Default for ToCTrRelIndFull<T> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<T: Clone + Hash + Eq> ToRelIndex0<CTrRelIndCommon<T>> for ToCTrRelIndFull<T>
{
    type RelIndex<'a> = CTrRelIndFull<'a, T> where Self: 'a, T: 'a;
    fn to_rel_index<'a>(&'a self, rel: &'a CTrRelIndCommon<T>) -> Self::RelIndex<'a> {
        CTrRelIndFull(rel)
    }

    type RelIndexWrite<'a> = CTrRelIndFullWrite<'a, T> where Self: 'a, T: 'a;
    fn to_rel_index_write<'a>(&'a mut self, rel: &'a mut CTrRelIndCommon<T>) -> Self::RelIndexWrite<'a> {
        // Safe: CTrRelIndCommon::insert() goes through a Mutex for concurrent writes.
        let ptr: *const CTrRelIndCommon<T> = rel;
        CTrRelIndFullWrite(unsafe { &*ptr })
    }

    type CRelIndexWrite<'a> = CTrRelIndFullWrite<'a, T> where Self: 'a, T: 'a;
    fn to_c_rel_index_write<'a>(&'a self, rel: &'a CTrRelIndCommon<T>) -> Self::CRelIndexWrite<'a> {
        CTrRelIndFullWrite(rel)
    }
}
