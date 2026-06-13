//! Automatic **semiring-provenance** threading via `#[semiring(K)]`.
//!
//! Tag a relation with `#[semiring(K)]` and the macro threads the provenance
//! algebra through your ordinary rules: the body atoms of one rule firing are
//! combined with the semiring product `⊗`, and the alternative derivations of a
//! tuple are combined with the sum `⊕` (the lattice join on duplicate keys).
//!
//! Run with: `cargo run --example ascent_semiring`

use ascent::ascent;
use ascent::semiring::{Trop, Why};

pub type Node = &'static str;

// ── 1. Shortest paths via the tropical (min-plus) semiring. ──────────────────
// `⊕ = min` keeps the cheapest derivation, `⊗ = +` adds edge costs. The cost is
// the annotation; the rules never mention it.
ascent! {
   struct ShortestPaths;

   #[semiring(Trop<u32>)]
   relation edge(Node, Node);
   #[semiring(Trop<u32>)]
   relation path(Node, Node);

   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}

// ── 2. Why-provenance: which sets of input edges justify each path. ──────────
// `⊕ = ∨` collects alternative derivations, `⊗ = ∧` conjoins the inputs of one
// derivation, pruned to ⊆-minimal clauses (so it terminates even with cycles).
ascent! {
   struct Provenance;

   #[semiring(Why<(Node, Node)>)]
   relation edge(Node, Node);
   #[semiring(Why<(Node, Node)>)]
   relation path(Node, Node);

   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}

fn main() {
   // 1. Shortest paths -------------------------------------------------------
   let mut sp = ShortestPaths::default();
   sp.edge = vec![
      ("A", "B", Trop::Fin(1)),
      ("B", "C", Trop::Fin(2)),
      ("C", "D", Trop::Fin(1)),
      ("A", "C", Trop::Fin(5)), // a longer direct route, beaten by A→B→C
   ];
   sp.run();
   println!("shortest paths (tropical semiring):");
   let mut paths = sp.path.clone();
   paths.sort();
   for (x, y, cost) in &paths {
      if let Trop::Fin(c) = cost {
         println!("  {x} → {y}: {c}");
      }
   }

   // 2. Why-provenance -------------------------------------------------------
   let mut pv = Provenance::default();
   pv.edge = vec![
      ("A", "B", Why::token(("A", "B"))),
      ("B", "C", Why::token(("B", "C"))),
      ("A", "C", Why::token(("A", "C"))),
   ];
   pv.run();
   println!("\nwhy-provenance (which edge sets justify A → C):");
   if let Some((_, _, prov)) = pv.path.iter().find(|(x, y, _)| *x == "A" && *y == "C") {
      for clause in prov.clauses() {
         let edges: Vec<String> = clause.iter().map(|(a, b)| format!("{a}→{b}")).collect();
         println!("  {{ {} }}", edges.join(", "));
      }
   }
}
