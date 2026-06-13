//! Milestone 1 integration check: the new `ascent_base::semiring` types used
//! *manually* as `lattice` value columns, exercising the existing
//! lattice-join-on-duplicate-key fixpoint. No macro changes are required for
//! these — automatic threading (Milestone 2) removes the hand-written `⊗`.

#![allow(warnings)]

use ascent::semiring::{Semiring, Trop, Why};
use ascent::*;

// ── Tropical (min-plus) semiring as a lattice column: shortest paths. ────────
// `⊕` (join) = min picks the cheapest derivation; `⊗` = `Trop::mul` (here `+`)
// is written by hand in the rule body. Absorptive + non-negative costs ⇒ the
// recursive fixpoint terminates even with a cycle in the graph.
ascent! {
   struct ShortestPath;

   relation edge(i32, i32, u32);
   lattice path(i32, i32, Trop<u32>);

   path(x, y, Trop::Fin(*w)) <-- edge(x, y, w);
   path(x, z, Trop::Fin(*w).mul(p.clone())) <-- edge(x, y, w), path(y, z, ?p);
}

#[test]
fn tropical_shortest_path_terminates_with_cycle() {
   let mut prog = ShortestPath::default();
   // 1→2→3→1 is a cycle; there is also a direct 1→3 of cost 5.
   prog.edge = vec![(1, 2, 1), (2, 3, 1), (3, 1, 1), (1, 3, 5)];
   prog.run();

   let cost = |x: i32, y: i32| {
      prog.path.iter().find(|(a, b, _)| *a == x && *b == y).map(|(_, _, c)| c.clone())
   };

   // 1→3 directly is 5, but 1→2→3 is 2 — the join keeps the minimum.
   assert_eq!(cost(1, 3), Some(Trop::Fin(2)));
   // around the cycle back to 1: 1→2→3→1 = 3.
   assert_eq!(cost(1, 1), Some(Trop::Fin(3)));
   assert_eq!(cost(2, 1), Some(Trop::Fin(2))); // 2→3→1
}

// ── Why-provenance semiring as a lattice column. ─────────────────────────────
// Each base edge is tagged with a token (its endpoints). `⊗` = `Why::mul`
// (conjunction of the inputs used by one derivation), `⊕` (join) = `Why::add`
// (disjunction of alternative derivations), pruned to ⊆-minimal clauses — so it
// terminates and reports *which sets of edges* justify each path.
ascent! {
   struct WhyProv;

   relation edge(i32, i32);
   lattice path(i32, i32, Why<(i32, i32)>);

   path(x, y, Why::token((*x, *y))) <-- edge(x, y);
   path(x, z, p.clone().mul(Why::token((*y, *z)))) <-- path(x, y, ?p), edge(y, z);
}

#[test]
fn why_provenance_collects_minimal_derivations() {
   let mut prog = WhyProv::default();
   // Two ways from 1 to 3: directly, or via 2.
   prog.edge = vec![(1, 2), (2, 3), (1, 3)];
   prog.run();

   let prov = prog.path.iter().find(|(a, b, _)| *a == 1 && *b == 3).map(|(_, _, p)| p.clone()).unwrap();

   // Expect exactly two minimal justifications:
   //   {edge(1,3)}  and  {edge(1,2), edge(2,3)}
   assert_eq!(prov.clauses().len(), 2);
   let direct: std::collections::BTreeSet<(i32, i32)> = [(1, 3)].into_iter().collect();
   let via2: std::collections::BTreeSet<(i32, i32)> = [(1, 2), (2, 3)].into_iter().collect();
   assert!(prov.clauses().contains(&direct));
   assert!(prov.clauses().contains(&via2));
}
