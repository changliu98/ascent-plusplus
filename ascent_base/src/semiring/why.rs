//! The why-provenance / positive-Boolean-provenance semiring [`Why`].

use std::cmp::Ordering;
use std::collections::BTreeSet;

use crate::semiring::{AbsorptiveSemiring, Semiring};
use crate::Lattice;

/// The why-provenance semiring `PosBool(X)` over source-tuple tokens of type `X`.
///
/// A value is a set of **clauses**; each clause is a set of tokens that together
/// suffice to derive the tuple (a conjunction of inputs), and the value is the
/// disjunction of its clauses (alternative derivations). In other words a value
/// is a monotone DNF over the source tokens, e.g. `{a,b} ∨ {c}` means "derivable
/// from `a` and `b` together, or from `c` alone".
///
/// Only **⊆-minimal** clauses are kept: if `A ⊆ B` then `A ∨ (A ∧ extra) = A`, so
/// the superset clause `B` is redundant and dropped. This pruning is what makes
/// the semiring **absorptive** and, since `X` is finite, **ω-continuous** (the
/// number of minimal clauses cannot grow without bound — antichains over a finite
/// powerset are finite). Therefore `Why<X>` gives terminating why-provenance even
/// for **recursive** programs, answering *"which sets of inputs are responsible
/// for this fact?"*.
///
/// * `⊕ = ∨` — union of clause sets, pruned to minimal clauses
/// * `⊗ = ∧` — pairwise union of clauses (distributing ∧ over ∨), pruned
/// * `0 = false = {}` — not derivable
/// * `1 = true = {∅}` — derivable with no inputs
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Why<X: Ord>(BTreeSet<BTreeSet<X>>);

impl<X: Ord> Default for Why<X> {
   /// The additive identity `0` (`false`, not derivable).
   fn default() -> Self {
      Why(BTreeSet::new())
   }
}

impl<X: Ord + Clone> Why<X> {
   /// `0` / `false`: not derivable.
   pub fn never() -> Self {
      Why(BTreeSet::new())
   }

   /// `1` / `true`: derivable with no inputs (a single empty clause).
   pub fn always() -> Self {
      let mut clauses = BTreeSet::new();
      clauses.insert(BTreeSet::new());
      Why(clauses)
   }

   /// The provenance of a single source tuple tagged with token `x`.
   pub fn token(x: X) -> Self {
      let mut clause = BTreeSet::new();
      clause.insert(x);
      let mut clauses = BTreeSet::new();
      clauses.insert(clause);
      Why(clauses)
   }

   /// The minimal clauses (each an antichain element). Reading view.
   pub fn clauses(&self) -> &BTreeSet<BTreeSet<X>> {
      &self.0
   }

   /// Insert `clause` into `set`, preserving the "⊆-minimal clauses only"
   /// invariant. Returns whether `set` changed.
   fn insert_minimal(set: &mut BTreeSet<BTreeSet<X>>, clause: BTreeSet<X>) -> bool {
      // If some existing clause is a subset of `clause`, then `clause` is
      // dominated/absorbed — drop it.
      if set.iter().any(|c| c.is_subset(&clause)) {
         return false;
      }
      // Otherwise `clause` dominates any existing supersets — remove them, then
      // insert `clause`.
      set.retain(|c| !clause.is_subset(c));
      set.insert(clause);
      true
   }

   /// `self ⊕ other = other`? i.e. is `self` below `other` in the natural order
   /// (every clause of `self` is dominated by — a superset of — some clause of
   /// `other`)?
   fn is_below(&self, other: &Self) -> bool {
      self.0.iter().all(|c| other.0.iter().any(|c2| c2.is_subset(c)))
   }
}

impl<X: Ord + Clone> Semiring for Why<X> {
   #[inline]
   fn zero() -> Self {
      Self::never()
   }
   #[inline]
   fn one() -> Self {
      Self::always()
   }

   /// `⊕ = ∨`: the union of the two DNFs, pruned to minimal clauses.
   fn add(mut self, other: Self) -> Self {
      for clause in other.0 {
         Self::insert_minimal(&mut self.0, clause);
      }
      self
   }

   /// `⊗ = ∧`: distribute conjunction over the disjuncts — every clause of
   /// `self` unioned with every clause of `other` — then prune.
   fn mul(self, other: Self) -> Self {
      let mut result = BTreeSet::new();
      for a in &self.0 {
         for b in &other.0 {
            let mut clause = a.clone();
            clause.extend(b.iter().cloned());
            Self::insert_minimal(&mut result, clause);
         }
      }
      Why(result)
   }
}

impl<X: Ord + Clone> AbsorptiveSemiring for Why<X> {}

impl<X: Ord + Clone> PartialOrd for Why<X> {
   fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
      match (self.is_below(other), other.is_below(self)) {
         (true, true) => Some(Ordering::Equal),
         (true, false) => Some(Ordering::Less),
         (false, true) => Some(Ordering::Greater),
         (false, false) => None,
      }
   }
}

impl<X: Ord + Clone> Lattice for Why<X> {
   /// `join = ⊕ = ∨`. Returns whether `self` changed.
   fn join_mut(&mut self, other: Self) -> bool {
      let mut changed = false;
      for clause in other.0 {
         changed |= Self::insert_minimal(&mut self.0, clause);
      }
      changed
   }

   /// `meet = ∧ = ⊗` (`PosBool` is a distributive lattice where meet coincides
   /// with semiring multiplication).
   fn meet_mut(&mut self, other: Self) -> bool {
      let old = std::mem::replace(&mut self.0, BTreeSet::new());
      let met = Why(old).mul(other);
      let changed = met.0 != self.0;
      self.0 = met.0;
      changed
   }
}

#[cfg(test)]
mod tests {
   use super::*;
   use crate::semiring::{check_absorption, check_semiring_laws};

   fn w(clauses: &[&[u32]]) -> Why<u32> {
      let mut set = BTreeSet::new();
      for clause in clauses {
         let c: BTreeSet<u32> = clause.iter().copied().collect();
         Why::insert_minimal(&mut set, c);
      }
      Why(set)
   }

   fn samples() -> Vec<Why<u32>> {
      vec![
         Why::never(),
         Why::always(),
         Why::token(1),
         Why::token(2),
         w(&[&[1, 2]]),
         w(&[&[1], &[2]]),
         w(&[&[1, 2], &[3]]),
      ]
   }

   #[test]
   fn laws() {
      check_semiring_laws(&samples());
      check_absorption(&samples());
   }

   #[test]
   fn identities() {
      assert_eq!(Why::<u32>::zero(), Why::never());
      assert_eq!(Why::<u32>::one(), Why::always());
      let x = Why::token(1);
      assert_eq!(x.clone().add(Why::never()), x); // a ⊕ 0 = a
      assert_eq!(x.clone().mul(Why::always()), x); // a ⊗ 1 = a
      assert_eq!(x.clone().mul(Why::never()), Why::never()); // a ⊗ 0 = 0
      assert_eq!(x.clone().add(Why::always()), Why::always()); // a ⊕ 1 = 1 (absorption)
   }

   #[test]
   fn conjunction_and_disjunction() {
      // {1} ∧ {2} = {1,2}
      assert_eq!(Why::token(1).mul(Why::token(2)), w(&[&[1, 2]]));
      // {1} ∨ {2} = {1} ∨ {2}
      assert_eq!(Why::token(1).add(Why::token(2)), w(&[&[1], &[2]]));
      // ({1} ∨ {2}) ∧ {3} = {1,3} ∨ {2,3}
      assert_eq!(w(&[&[1], &[2]]).mul(Why::token(3)), w(&[&[1, 3], &[2, 3]]));
   }

   #[test]
   fn minimal_clauses_kept() {
      // {1} ∨ {1,2} prunes to {1}
      assert_eq!(w(&[&[1], &[1, 2]]), Why::token(1));
      // adding a superset clause to {1} is a no-op
      let mut a = Why::token(1);
      assert!(!a.join_mut(w(&[&[1, 2, 3]])));
      assert_eq!(a, Why::token(1));
      // adding a fresh alternative changes it
      assert!(a.join_mut(Why::token(9)));
      assert_eq!(a, w(&[&[1], &[9]]));
   }

   #[test]
   fn join_equals_add() {
      for a in samples() {
         for b in samples() {
            let mut j = a.clone();
            j.join_mut(b.clone());
            assert_eq!(j, a.clone().add(b.clone()), "join must equal ⊕");
         }
      }
   }

   #[test]
   fn natural_order_matches_addition() {
      for a in samples() {
         for b in samples() {
            let le = a <= b;
            let add_eq = a.clone().add(b.clone()) == b;
            assert_eq!(le, add_eq, "order vs addition mismatch: {a:?} ≤ {b:?}");
         }
      }
   }
}
