//! Intensive end-to-end correctness tests for `#[semiring(K)]` automatic
//! threading: random graphs cross-checked against **independent reference
//! algorithms** (Floyd–Warshall for bool/tropical/Viterbi), the definitive
//! provenance check that `Why`-provenance is *exactly* the reachability Boolean
//! function over **every** edge subset, a dense-cyclic stress test, and a
//! serial-vs-parallel differential.

#![allow(warnings)]

use std::collections::{HashMap, HashSet};

use ascent::semiring::{Trop, Viterbi, Why};
use ascent::*;

// ── Programs under test (transitive closure, paths of length ≥ 1). ───────────
ascent! { struct ReachG;
   #[semiring(bool)] relation edge(u32, u32);
   #[semiring(bool)] relation path(u32, u32);
   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}
ascent! { struct TropG;
   #[semiring(Trop<u32>)] relation edge(u32, u32);
   #[semiring(Trop<u32>)] relation path(u32, u32);
   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}
ascent! { struct VitG;
   #[semiring(Viterbi)] relation edge(u32, u32);
   #[semiring(Viterbi)] relation path(u32, u32);
   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}
ascent! { struct WhyG;
   #[semiring(Why<(u32, u32)>)] relation edge(u32, u32);
   #[semiring(Why<(u32, u32)>)] relation path(u32, u32);
   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}
ascent_par! { struct TropParG;
   #[semiring(Trop<u32>)] relation edge(u32, u32);
   #[semiring(Trop<u32>)] relation path(u32, u32);
   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}

// Two different semirings in one program, plus a rule whose body mixes both
// annotation types: `reach_tag(y) <-- edge(x,y), reach_tag(x)` has a `Trop` atom
// (`edge`) and a `Why` atom (`reach_tag`) but a `Why` head, so only the `Why`
// annotation may thread (the `Trop` one is grouped out — and mixing the two in
// one `⊗` would not even type-check).
ascent! { struct MultiSr;
   #[semiring(Trop<u32>)] relation edge(u32, u32);
   #[semiring(Trop<u32>)] relation dist(u32, u32);
   #[semiring(Why<u32>)] relation tagged(u32);
   #[semiring(Why<u32>)] relation reach_tag(u32);

   dist(x, y) <-- edge(x, y);
   dist(x, z) <-- edge(x, y), dist(y, z);

   reach_tag(n) <-- tagged(n);
   reach_tag(y) <-- edge(x, y), reach_tag(x);
}

#[test]
fn multiple_semirings_coexist_and_group_by_type() {
   let mut prog = MultiSr::default();
   prog.edge = vec![(0, 1, Trop::Fin(1)), (1, 2, Trop::Fin(1)), (0, 2, Trop::Fin(5))];
   prog.tagged = vec![(0, Why::token(0))];
   prog.run();

   // Tropical side: shortest 0→2 is 2 (via 1), beating the direct edge of 5.
   let dist02 = prog.dist.iter().find(|(a, b, _)| *a == 0 && *b == 2).map(|(_, _, c)| c.clone());
   assert_eq!(dist02, Some(Trop::Fin(2)));

   // Why side: tag 0 flows along edges; the only justification is {tag 0}.
   let only_tag0: std::collections::BTreeSet<u32> = [0].into_iter().collect();
   for n in [0u32, 1, 2] {
      let p = prog.reach_tag.iter().find(|(x, _)| *x == n).map(|(_, w)| w.clone()).expect("reach_tag missing");
      assert_eq!(p.clauses().len(), 1, "node {n}");
      assert!(p.clauses().contains(&only_tag0), "node {n}");
   }
}

// ── Deterministic PRNG + random graph generation. ────────────────────────────
struct Rng(u64);
impl Rng {
   fn new(seed: u64) -> Self {
      Rng(seed | 1)
   }
   fn next(&mut self) -> u64 {
      let mut x = self.0;
      x ^= x << 13;
      x ^= x >> 7;
      x ^= x << 17;
      self.0 = x;
      x
   }
   fn below(&mut self, n: u64) -> u64 {
      self.next() % n
   }
}

/// Distinct directed pairs over `0..n` (self-loops allowed), ~40% density,
/// capped at `max` edges.
fn gen_pairs(rng: &mut Rng, n: u32, max: usize) -> Vec<(u32, u32)> {
   let mut v = vec![];
   for i in 0..n {
      for j in 0..n {
         if v.len() >= max {
            return v;
         }
         if rng.below(10) < 4 {
            v.push((i, j));
         }
      }
   }
   v
}

// ── Reference algorithms (Floyd–Warshall, paths of length ≥ 1). ──────────────
fn tc_bool(n: u32, edges: &[(u32, u32)]) -> Vec<Vec<bool>> {
   let n = n as usize;
   let mut r = vec![vec![false; n]; n];
   for &(a, b) in edges {
      r[a as usize][b as usize] = true;
   }
   for k in 0..n {
      for i in 0..n {
         for j in 0..n {
            if r[i][k] && r[k][j] {
               r[i][j] = true;
            }
         }
      }
   }
   r
}

fn sp_trop(n: u32, edges: &[(u32, u32, u32)]) -> Vec<Vec<Option<u32>>> {
   let n = n as usize;
   let mut d = vec![vec![None::<u32>; n]; n];
   for &(a, b, w) in edges {
      let cell = &mut d[a as usize][b as usize];
      *cell = Some(cell.map_or(w, |o| o.min(w)));
   }
   for k in 0..n {
      for i in 0..n {
         for j in 0..n {
            if let (Some(ik), Some(kj)) = (d[i][k], d[k][j]) {
               let c = ik + kj;
               d[i][j] = Some(d[i][j].map_or(c, |o| o.min(c)));
            }
         }
      }
   }
   d
}

fn vit_best(n: u32, edges: &[(u32, u32, f64)]) -> Vec<Vec<f64>> {
   let n = n as usize;
   let mut p = vec![vec![0.0f64; n]; n];
   for &(a, b, pr) in edges {
      let cell = &mut p[a as usize][b as usize];
      *cell = cell.max(pr);
   }
   for k in 0..n {
      for i in 0..n {
         for j in 0..n {
            let c = p[i][k] * p[k][j];
            if c > p[i][j] {
               p[i][j] = c;
            }
         }
      }
   }
   p
}

#[test]
fn boolean_matches_transitive_closure() {
   let mut rng = Rng::new(0xB001);
   for _ in 0..60 {
      let n = 6;
      let pairs = gen_pairs(&mut rng, n, 16);
      let mut prog = ReachG::default();
      prog.edge = pairs.iter().map(|&(a, b)| (a, b, true)).collect();
      prog.run();

      assert!(prog.path.iter().all(|(_, _, v)| *v), "all bool annotations must be true");
      let got: HashSet<(u32, u32)> = prog.path.iter().map(|(a, b, _)| (*a, *b)).collect();
      let tc = tc_bool(n, &pairs);
      for i in 0..n {
         for j in 0..n {
            assert_eq!(got.contains(&(i, j)), tc[i as usize][j as usize], "reach ({i},{j})");
         }
      }
   }
}

#[test]
fn tropical_matches_floyd_warshall() {
   let mut rng = Rng::new(0x5151);
   for _ in 0..60 {
      let n = 6;
      let edges: Vec<(u32, u32, u32)> =
         gen_pairs(&mut rng, n, 16).into_iter().map(|(a, b)| (a, b, 1 + rng.below(9) as u32)).collect();
      let mut prog = TropG::default();
      prog.edge = edges.iter().map(|&(a, b, w)| (a, b, Trop::Fin(w))).collect();
      prog.run();

      let mut got: HashMap<(u32, u32), u32> = HashMap::new();
      for (a, b, c) in &prog.path {
         match c {
            Trop::Fin(w) => {
               got.insert((*a, *b), *w);
            }
            Trop::Inf => panic!("a derived tuple must not carry the 0 annotation (Inf)"),
         }
      }
      let d = sp_trop(n, &edges);
      for i in 0..n {
         for j in 0..n {
            assert_eq!(got.get(&(i, j)).copied(), d[i as usize][j as usize], "shortest path ({i},{j})");
         }
      }
   }
}

#[test]
fn viterbi_matches_max_product() {
   let mut rng = Rng::new(0x71B1);
   for _ in 0..60 {
      let n = 6;
      // dyadic probabilities keep all products exact in f64.
      let edges: Vec<(u32, u32, f64)> =
         gen_pairs(&mut rng, n, 16).into_iter().map(|(a, b)| (a, b, (1 + rng.below(8)) as f64 / 8.0)).collect();
      let mut prog = VitG::default();
      prog.edge = edges.iter().map(|&(a, b, p)| (a, b, Viterbi(p))).collect();
      prog.run();

      let got: HashMap<(u32, u32), f64> = prog.path.iter().map(|(a, b, v)| ((*a, *b), v.0)).collect();
      let vb = vit_best(n, &edges);
      for i in 0..n {
         for j in 0..n {
            let r = vb[i as usize][j as usize];
            match got.get(&(i, j)) {
               Some(&e) => assert!((e - r).abs() < 1e-9 && r > 0.0, "viterbi ({i},{j}) e={e} r={r}"),
               None => assert!(r == 0.0, "viterbi ({i},{j}) missing but reference={r}"),
            }
         }
      }
   }
}

/// The definitive provenance test: the `Why`-provenance of `path(a,b)`, as a
/// monotone Boolean function over the edge tokens, must equal "is `b` reachable
/// from `a` using only this edge subset?" — checked for **every** subset of
/// edges and every node pair.
#[test]
fn why_provenance_is_exactly_reachability_over_all_edge_subsets() {
   let mut rng = Rng::new(0x3333);
   let mut trials = 0;
   for _ in 0..40 {
      let n = 5;
      let edges = gen_pairs(&mut rng, n, 10);
      if edges.is_empty() {
         continue;
      }
      trials += 1;

      let mut prog = WhyG::default();
      prog.edge = edges.iter().map(|&(a, b)| (a, b, Why::token((a, b)))).collect();
      prog.run();
      let prov: HashMap<(u32, u32), Why<(u32, u32)>> =
         prog.path.iter().map(|(a, b, w)| ((*a, *b), w.clone())).collect();

      let m = edges.len();
      for mask in 0u32..(1u32 << m) {
         let subset: Vec<(u32, u32)> =
            (0..m).filter(|i| mask & (1 << i) != 0).map(|i| edges[i]).collect();
         let reach = tc_bool(n, &subset);
         for a in 0..n {
            for b in 0..n {
               // does the provenance Boolean function accept this subset?
               let accepts = prov.get(&(a, b)).map_or(false, |w| {
                  w.clauses().iter().any(|clause| clause.iter().all(|e| subset.contains(e)))
               });
               assert_eq!(accepts, reach[a as usize][b as usize], "Why ({a},{b}) subset {mask:b}");
            }
         }
      }
   }
   assert!(trials >= 30, "expected enough non-empty trials, got {trials}");
}

/// Heavy recursion: a dense graph full of cycles must still terminate (thanks to
/// absorption) and agree with Floyd–Warshall.
#[test]
fn tropical_dense_cyclic_stress() {
   let mut rng = Rng::new(0xDEAD);
   let n = 12u32;
   let mut edges = vec![];
   for i in 0..n {
      for j in 0..n {
         if i != j {
            edges.push((i, j, 1 + rng.below(9) as u32));
         }
      }
   }
   let mut prog = TropG::default();
   prog.edge = edges.iter().map(|&(a, b, w)| (a, b, Trop::Fin(w))).collect();
   prog.run();

   let d = sp_trop(n, &edges);
   let got: HashMap<(u32, u32), u32> =
      prog.path.iter().filter_map(|(a, b, c)| c.clone().finite().map(|w| ((*a, *b), w))).collect();
   for i in 0..n {
      for j in 0..n {
         assert_eq!(got.get(&(i, j)).copied(), d[i as usize][j as usize], "dense ({i},{j})");
      }
   }
}

/// Serial and parallel engines must compute identical annotations.
#[test]
fn tropical_serial_equals_parallel() {
   use std::sync::RwLock;
   let mut rng = Rng::new(0x9A9A);
   for _ in 0..30 {
      let n = 6;
      let edges: Vec<(u32, u32, u32)> =
         gen_pairs(&mut rng, n, 16).into_iter().map(|(a, b)| (a, b, 1 + rng.below(9) as u32)).collect();

      let mut s = TropG::default();
      s.edge = edges.iter().map(|&(a, b, w)| (a, b, Trop::Fin(w))).collect();
      s.run();

      let mut p = TropParG::default();
      for &(a, b, w) in &edges {
         p.edge.push(RwLock::new((a, b, Trop::Fin(w))));
      }
      p.run();

      let smap: HashMap<(u32, u32), Trop<u32>> = s.path.iter().map(|(a, b, c)| ((*a, *b), c.clone())).collect();
      let pmap: HashMap<(u32, u32), Trop<u32>> = p
         .path
         .iter()
         .map(|cell| {
            let r = cell.read().unwrap();
            ((r.0, r.1), r.2.clone())
         })
         .collect();
      assert_eq!(smap, pmap, "serial and parallel disagree");
   }
}

// ─────────────────────────────────────────────────────────────────────────────
// More tests: (1) rules whose body joins 3+ semiring atoms (a `⊗` of three
// annotations), and (2) a relation that is simultaneously an EDB input and a
// recursively-derived relation, whose annotations must merge via `⊕`.
// ─────────────────────────────────────────────────────────────────────────────

// A 3-edge path: tri(a,d)'s annotation is edge(a,b) ⊗ edge(b,c) ⊗ edge(c,d),
// summed (⊕) over all intermediate b,c.
ascent! { struct Tri3;
   #[semiring(Trop<u32>)] relation edge(u32, u32);
   #[semiring(Trop<u32>)] relation tri(u32, u32);
   tri(a, d) <-- edge(a, b), edge(b, c), edge(c, d);
}
ascent! { struct Tri3Why;
   #[semiring(Why<(u32, u32)>)] relation edge(u32, u32);
   #[semiring(Why<(u32, u32)>)] relation tri(u32, u32);
   tri(a, d) <-- edge(a, b), edge(b, c), edge(c, d);
}

#[test]
fn tropical_three_way_join_matches_brute_force() {
   let mut rng = Rng::new(0xA3A3);
   for _ in 0..50 {
      let n = 5;
      let edges: Vec<(u32, u32, u32)> =
         gen_pairs(&mut rng, n, 12).into_iter().map(|(a, b)| (a, b, 1 + rng.below(9) as u32)).collect();
      let mut prog = Tri3::default();
      prog.edge = edges.iter().map(|&(a, b, w)| (a, b, Trop::Fin(w))).collect();
      prog.run();

      // brute force: min over b,c of w(a,b)+w(b,c)+w(c,d)
      let w: HashMap<(u32, u32), u32> = edges.iter().map(|&(a, b, wt)| ((a, b), wt)).collect();
      let mut reference: HashMap<(u32, u32), u32> = HashMap::new();
      for a in 0..n {
         for b in 0..n {
            for c in 0..n {
               for d in 0..n {
                  if let (Some(&w1), Some(&w2), Some(&w3)) = (w.get(&(a, b)), w.get(&(b, c)), w.get(&(c, d))) {
                     let cost = w1 + w2 + w3;
                     let e = reference.entry((a, d)).or_insert(u32::MAX);
                     *e = (*e).min(cost);
                  }
               }
            }
         }
      }
      let engine: HashMap<(u32, u32), u32> =
         prog.tri.iter().filter_map(|(a, b, c)| c.clone().finite().map(|x| ((*a, *b), x))).collect();
      assert_eq!(engine, reference, "3-way tropical join mismatch");
   }
}

#[test]
fn why_three_way_join_matches_subset_reachability() {
   let mut rng = Rng::new(0xB4B4);
   let mut trials = 0;
   for _ in 0..30 {
      let n = 4;
      let edges = gen_pairs(&mut rng, n, 8);
      if edges.is_empty() {
         continue;
      }
      trials += 1;
      let mut prog = Tri3Why::default();
      prog.edge = edges.iter().map(|&(a, b)| (a, b, Why::token((a, b)))).collect();
      prog.run();
      let prov: HashMap<(u32, u32), Why<(u32, u32)>> =
         prog.tri.iter().map(|(a, b, w)| ((*a, *b), w.clone())).collect();

      let m = edges.len();
      for mask in 0u32..(1u32 << m) {
         let subset: Vec<(u32, u32)> = (0..m).filter(|i| mask & (1 << i) != 0).map(|i| edges[i]).collect();
         let has = |a: u32, b: u32| subset.contains(&(a, b));
         for a in 0..n {
            for d in 0..n {
               let mut reachable = false;
               for b in 0..n {
                  for c in 0..n {
                     if has(a, b) && has(b, c) && has(c, d) {
                        reachable = true;
                     }
                  }
               }
               let accepts = prov.get(&(a, d)).map_or(false, |w| {
                  w.clauses().iter().any(|cl| cl.iter().all(|e| subset.contains(e)))
               });
               assert_eq!(accepts, reachable, "Why 3-join ({a},{d}) subset {mask:b}");
            }
         }
      }
   }
   assert!(trials >= 20, "expected enough non-empty trials, got {trials}");
}

/// Naive least-fixpoint oracle for `TropG` with input seed facts in `path`:
///   path(x,y) ⊑ edge(x,y);  path(a,b) ⊑ seed(a,b);  path(x,z) ⊑ w_xy + path(y,z)
fn dist_lfp(edges: &[(u32, u32, u32)], seeds: &[(u32, u32, u32)]) -> HashMap<(u32, u32), u32> {
   fn relax(dist: &mut HashMap<(u32, u32), u32>, k: (u32, u32), v: u32) -> bool {
      match dist.get(&k) {
         Some(&old) if old <= v => false,
         _ => {
            dist.insert(k, v);
            true
         }
      }
   }
   let mut dist = HashMap::new();
   for &(a, b, w) in edges {
      relax(&mut dist, (a, b), w);
   }
   for &(a, b, s) in seeds {
      relax(&mut dist, (a, b), s);
   }
   loop {
      let mut changed = false;
      let cur: Vec<((u32, u32), u32)> = dist.iter().map(|(k, v)| (*k, *v)).collect();
      for &(x, y, w) in edges {
         for &((yy, z), d) in &cur {
            if yy == y {
               changed |= relax(&mut dist, (x, z), w + d);
            }
         }
      }
      if !changed {
         break;
      }
   }
   dist
}

#[test]
fn input_and_derived_merge_tropical_random() {
   let mut rng = Rng::new(0x1234_5678);
   for _ in 0..50 {
      let n = 6;
      let edges: Vec<(u32, u32, u32)> =
         gen_pairs(&mut rng, n, 14).into_iter().map(|(a, b)| (a, b, 1 + rng.below(9) as u32)).collect();
      // input seed facts in `path` itself, deliberately overlapping derived keys.
      let seeds: Vec<(u32, u32, u32)> =
         gen_pairs(&mut rng, n, 5).into_iter().map(|(a, b)| (a, b, 1 + rng.below(15) as u32)).collect();

      let mut prog = TropG::default();
      prog.edge = edges.iter().map(|&(a, b, w)| (a, b, Trop::Fin(w))).collect();
      prog.path = seeds.iter().map(|&(a, b, s)| (a, b, Trop::Fin(s))).collect();
      prog.run();

      let engine: HashMap<(u32, u32), u32> =
         prog.path.iter().filter_map(|(a, b, c)| c.clone().finite().map(|w| ((*a, *b), w))).collect();
      let reference = dist_lfp(&edges, &seeds);
      assert_eq!(engine, reference, "input+derived tropical least-fixpoint mismatch");
   }
}

#[test]
fn input_and_derived_merge_tropical_concrete() {
   let mut prog = TropG::default();
   prog.edge = vec![(0, 1, Trop::Fin(5)), (1, 2, Trop::Fin(5)), (9, 0, Trop::Fin(1))];
   // an input fact for `path` that competes with the derived 0→2 = 10
   prog.path = vec![(0, 2, Trop::Fin(3))];
   prog.run();

   let cost = |x: u32, y: u32| prog.path.iter().find(|(a, b, _)| *a == x && *b == y).map(|(_, _, c)| c.clone());
   assert_eq!(cost(0, 2), Some(Trop::Fin(3))); // input 3 beats derived 10 (⊕ = min)
   assert_eq!(cost(9, 2), Some(Trop::Fin(4))); // seed propagates: 9→0 (1) + seed(0→2) (3)
   assert_eq!(cost(0, 1), Some(Trop::Fin(5)));
}

#[test]
fn input_and_derived_merge_why() {
   let mut prog = WhyG::default();
   prog.edge = vec![(0, 1, Why::token((0, 1))), (1, 2, Why::token((1, 2)))];
   // seed path(0,2) with an external justification token
   prog.path = vec![(0, 2, Why::token((99, 99)))];
   prog.run();

   let prov = prog.path.iter().find(|(a, b, _)| *a == 0 && *b == 2).map(|(_, _, w)| w.clone()).unwrap();
   // both the seed token AND the derived edge-set justify path(0,2) — ⊕ = union
   assert_eq!(prov.clauses().len(), 2);
   let seed: std::collections::BTreeSet<(u32, u32)> = [(99, 99)].into_iter().collect();
   let derived: std::collections::BTreeSet<(u32, u32)> = [(0, 1), (1, 2)].into_iter().collect();
   assert!(prov.clauses().contains(&seed));
   assert!(prov.clauses().contains(&derived));
}
