//! The counting / bag semiring [`Counting`].

use crate::semiring::Semiring;

/// The counting (bag) semiring `(ℕ, +, ×, 0, 1)`: an annotation counts the
/// *number of derivations* of a tuple, recovering bag/multiset semantics.
///
/// # Not absorptive — no recursion
///
/// `Counting` is **not** absorptive and **not** ω-continuous: under recursion a
/// tuple can have infinitely many derivations (e.g. the transitive closure of a
/// graph with a cycle), so the count diverges and a naive fixpoint never
/// terminates. Accordingly this type intentionally does **not** implement
/// [`Lattice`](crate::Lattice), which means automatic provenance threading
/// (`#[semiring(Counting)]`) is a *compile error* on any relation that
/// participates in recursion. It is sound and useful for non-recursive /
/// stratified programs.
///
/// Arithmetic saturates at [`u64::MAX`] rather than overflowing, so a count that
/// blows up degrades gracefully instead of panicking.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default, PartialOrd, Ord)]
pub struct Counting(pub u64);

impl Counting {
   /// The number of derivations recorded.
   #[inline]
   pub fn count(self) -> u64 {
      self.0
   }
}

impl Semiring for Counting {
   #[inline]
   fn zero() -> Self {
      Counting(0)
   }
   #[inline]
   fn one() -> Self {
      Counting(1)
   }
   /// `⊕ = +` (saturating).
   #[inline]
   fn add(self, other: Self) -> Self {
      Counting(self.0.saturating_add(other.0))
   }
   /// `⊗ = ×` (saturating).
   #[inline]
   fn mul(self, other: Self) -> Self {
      Counting(self.0.saturating_mul(other.0))
   }
}

// NOTE: deliberately no `Lattice` and no `AbsorptiveSemiring` impl — see the
// type-level docs. Adding either would (incorrectly) allow non-terminating
// recursive use.

#[cfg(test)]
mod tests {
   use super::*;
   use crate::semiring::check_semiring_laws;

   #[test]
   fn laws() {
      let samples = [Counting(0), Counting(1), Counting(2), Counting(5)];
      check_semiring_laws(&samples);
   }

   #[test]
   fn counts_derivations() {
      assert_eq!(Counting::zero(), Counting(0));
      assert_eq!(Counting::one(), Counting(1));
      assert_eq!(Counting(2).add(Counting(3)), Counting(5)); // alternative derivations
      assert_eq!(Counting(2).mul(Counting(3)), Counting(6)); // combined body atoms
   }

   #[test]
   fn not_absorptive() {
      // a ⊕ (a ⊗ b) = a would require 1 + 1·1 = 1, but here it is 2: this is
      // exactly why `Counting` must not be used under recursion.
      let a = Counting(1);
      let b = Counting(1);
      assert_ne!(a.add(a.mul(b)), a);
   }

   #[test]
   fn saturates() {
      assert_eq!(Counting(u64::MAX).add(Counting(1)), Counting(u64::MAX));
      assert_eq!(Counting(u64::MAX).mul(Counting(2)), Counting(u64::MAX));
   }
}
