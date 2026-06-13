//! Milestone 2: `#[semiring(K)]` **automatic threading**. The rules below are
//! ordinary Datalog — no hand-written `⊗`. The macro lowers each annotated
//! relation to a `lattice` relation with a hidden trailing `K` column, binds the
//! annotation of every semiring body atom, multiplies them (`⊗`) onto the head,
//! and lets the lattice join do `⊕` on duplicate keys. Results must match the
//! hand-threaded versions in `semiring_manual.rs`.

#![allow(warnings)]

use ascent::semiring::{Trop, Why};
use ascent::*;

// ── Tropical shortest path, fully automatic. ─────────────────────────────────
// Both relations are `#[semiring(Trop<u32>)]`; `edge` is populated with its
// weight as the annotation. The rules never mention costs.
ascent! {
   struct ShortestPathAuto;

   #[semiring(Trop<u32>)]
   relation edge(i32, i32);
   #[semiring(Trop<u32>)]
   relation path(i32, i32);

   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}

#[test]
fn tropical_auto_matches_manual() {
   let mut prog = ShortestPathAuto::default();
   // (from, to, weight-as-annotation); same graph as the manual test.
   prog.edge = vec![(1, 2, Trop::Fin(1)), (2, 3, Trop::Fin(1)), (3, 1, Trop::Fin(1)), (1, 3, Trop::Fin(5))];
   prog.run();

   let cost =
      |x: i32, y: i32| prog.path.iter().find(|(a, b, _)| *a == x && *b == y).map(|(_, _, c)| c.clone());

   assert_eq!(cost(1, 3), Some(Trop::Fin(2))); // 1→2→3 beats the direct 5
   assert_eq!(cost(1, 1), Some(Trop::Fin(3))); // around the cycle
   assert_eq!(cost(2, 1), Some(Trop::Fin(2)));
}

// ── Why-provenance, fully automatic. ─────────────────────────────────────────
// Each base edge is populated with its token; the rules thread the conjunction
// (`⊗`) / disjunction (`⊕`) of those tokens automatically.
ascent! {
   struct WhyAuto;

   #[semiring(Why<(i32, i32)>)]
   relation edge(i32, i32);
   #[semiring(Why<(i32, i32)>)]
   relation path(i32, i32);

   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}

#[test]
fn why_auto_matches_manual() {
   let mut prog = WhyAuto::default();
   prog.edge = vec![(1, 2, Why::token((1, 2))), (2, 3, Why::token((2, 3))), (1, 3, Why::token((1, 3)))];
   prog.run();

   let prov = prog.path.iter().find(|(a, b, _)| *a == 1 && *b == 3).map(|(_, _, p)| p.clone()).unwrap();

   assert_eq!(prov.clauses().len(), 2);
   let direct: std::collections::BTreeSet<(i32, i32)> = [(1, 3)].into_iter().collect();
   let via2: std::collections::BTreeSet<(i32, i32)> = [(1, 2), (2, 3)].into_iter().collect();
   assert!(prov.clauses().contains(&direct));
   assert!(prov.clauses().contains(&via2));
}

// ── Boolean reachability (set semantics), automatic. ─────────────────────────
// Smoke test that the `bool` semiring threads: every reachable pair is present
// with annotation `true`.
ascent! {
   struct ReachAuto;

   #[semiring(bool)]
   relation edge(i32, i32);
   #[semiring(bool)]
   relation reach(i32, i32);

   reach(x, y) <-- edge(x, y);
   reach(x, z) <-- edge(x, y), reach(y, z);
}

#[test]
fn boolean_auto_reachability() {
   let mut prog = ReachAuto::default();
   prog.edge = vec![(1, 2, true), (2, 3, true), (3, 1, true)];
   prog.run();

   // The cycle makes every node reach every node (9 ordered pairs).
   assert_eq!(prog.reach.len(), 9);
   assert!(prog.reach.iter().all(|(_, _, b)| *b));
   assert!(prog.reach.iter().any(|(a, b, _)| *a == 1 && *b == 3));
}

// ── Negation of a semiring relation. ─────────────────────────────────────────
// Under `!` the annotation column is matched with a wildcard (it doesn't change
// "is this key absent?"), so negating a semiring relation just works.
ascent! {
   struct NegSemiring;

   #[semiring(bool)]
   relation edge(i32, i32);
   relation asym(i32, i32);

   asym(x, y) <-- edge(x, y), !edge(y, x);
}

#[test]
fn negation_over_semiring_relation() {
   let mut prog = NegSemiring::default();
   prog.edge = vec![(1, 2, true), (2, 1, true), (1, 3, true)];
   prog.run();

   // (1,3) is asymmetric (no 3→1); (1,2)/(2,1) are symmetric.
   assert!(prog.asym.contains(&(1, 3)));
   assert!(!prog.asym.contains(&(1, 2)));
   assert!(!prog.asym.contains(&(2, 1)));
}

// ── Semiring atoms inside a disjunction. ─────────────────────────────────────
// Threading runs after disjunction-splitting, so an annotated atom inside
// `( .. || .. )` is threaded in each branch.
ascent! {
   struct DisjSemiring;

   #[semiring(bool)]
   relation a(i32);
   #[semiring(bool)]
   relation b(i32);
   #[semiring(bool)]
   relation c(i32);

   c(x) <-- (a(x) || b(x));
}

#[test]
fn disjunction_over_semiring_relations() {
   let mut prog = DisjSemiring::default();
   prog.a = vec![(1, true), (2, true)];
   prog.b = vec![(2, true), (3, true)];
   prog.run();

   let mut cs: Vec<i32> = prog.c.iter().map(|(x, _)| *x).collect();
   cs.sort();
   assert_eq!(cs, vec![1, 2, 3]);
}

// ── Parallel engine: automatic threading over `ascent_par!`. ──────────────────
ascent_par! {
   struct ShortestPathPar;

   #[semiring(Trop<u32>)]
   relation edge(i32, i32);
   #[semiring(Trop<u32>)]
   relation path(i32, i32);

   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}

#[test]
fn tropical_auto_parallel() {
   use std::sync::RwLock;
   let mut prog = ShortestPathPar::default();
   // Parallel lattice rows (input included) are stored behind an `RwLock`.
   prog.edge = ascent::boxcar::vec![
      RwLock::new((1, 2, Trop::Fin(1))),
      RwLock::new((2, 3, Trop::Fin(1))),
      RwLock::new((3, 1, Trop::Fin(1))),
      RwLock::new((1, 3, Trop::Fin(5)))
   ];
   prog.run();
   // Parallel lattice rows are stored behind an `RwLock`.
   let cost = |x: i32, y: i32| {
      prog.path.iter().find_map(|cell| {
         let r = cell.read().unwrap();
         (r.0 == x && r.1 == y).then(|| r.2.clone())
      })
   };
   assert_eq!(cost(1, 3), Some(Trop::Fin(2)));
   assert_eq!(cost(1, 1), Some(Trop::Fin(3)));
}
