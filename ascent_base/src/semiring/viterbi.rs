//! The Viterbi (max-times) confidence semiring [`Viterbi`].

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

use crate::semiring::{AbsorptiveSemiring, Semiring};
use crate::Lattice;

/// The Viterbi (max-times) semiring on probabilities in `[0, 1]`:
/// `⊕ = max`, `⊗ = ×`, `0 = 0.0`, `1 = 1.0`.
///
/// Annotating a relation with `Viterbi` computes **best-derivation confidence**:
/// each derivation multiplies the confidences of its body atoms, and a tuple's
/// annotation is the maximum confidence over all of its derivations (the Viterbi
/// / most-probable-explanation score).
///
/// `Viterbi` is **absorptive** — `max(a, a·b) = a` whenever `b ≤ 1`, which holds
/// for all probabilities — so it terminates under recursion. Values are clamped
/// to `[0, 1]` on construction; reading the inner `f64` directly bypasses the
/// clamp, so prefer [`Viterbi::new`].
///
/// `Eq`/`Hash`/`Ord` use [`f64::total_cmp`], giving a total order (`NaN` is
/// ordered, not panicking), so `Viterbi` is usable as a lattice value.
#[derive(Clone, Copy, Debug)]
pub struct Viterbi(pub f64);

impl Viterbi {
   /// Construct a confidence, clamping into `[0, 1]`.
   #[inline]
   pub fn new(p: f64) -> Self {
      Viterbi(p.clamp(0.0, 1.0))
   }

   /// The inner probability.
   #[inline]
   pub fn prob(self) -> f64 {
      self.0
   }
}

impl PartialEq for Viterbi {
   fn eq(&self, other: &Self) -> bool {
      self.0.total_cmp(&other.0) == Ordering::Equal
   }
}
impl Eq for Viterbi {}

impl Hash for Viterbi {
   fn hash<H: Hasher>(&self, state: &mut H) {
      // Normalize -0.0 and +0.0 to the same bit pattern so they hash equal.
      let bits = if self.0 == 0.0 { 0u64 } else { self.0.to_bits() };
      bits.hash(state);
   }
}

impl PartialOrd for Viterbi {
   fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
      Some(self.cmp(other))
   }
}
impl Ord for Viterbi {
   fn cmp(&self, other: &Self) -> Ordering {
      self.0.total_cmp(&other.0)
   }
}

impl Semiring for Viterbi {
   #[inline]
   fn zero() -> Self {
      Viterbi(0.0)
   }
   #[inline]
   fn one() -> Self {
      Viterbi(1.0)
   }
   /// `⊕ = max`.
   #[inline]
   fn add(self, other: Self) -> Self {
      Viterbi(self.0.max(other.0))
   }
   /// `⊗ = ×`.
   #[inline]
   fn mul(self, other: Self) -> Self {
      Viterbi(self.0 * other.0)
   }
}

impl AbsorptiveSemiring for Viterbi {}

// Natural order: `a ≤ b ⇔ max(a,b) = b ⇔ a ≤ b` numerically. `join = ⊕ = max`,
// bottom = `0.0` = the additive identity.
impl Lattice for Viterbi {
   #[inline]
   fn join_mut(&mut self, other: Self) -> bool {
      if other.0 > self.0 {
         self.0 = other.0;
         true
      } else {
         false
      }
   }
   #[inline]
   fn meet_mut(&mut self, other: Self) -> bool {
      if other.0 < self.0 {
         self.0 = other.0;
         true
      } else {
         false
      }
   }
}

#[cfg(test)]
mod tests {
   use super::*;
   use crate::semiring::{check_absorption, check_semiring_laws};

   fn samples() -> Vec<Viterbi> {
      vec![Viterbi(0.0), Viterbi(0.25), Viterbi(0.5), Viterbi(0.9), Viterbi(1.0)]
   }

   #[test]
   fn laws() {
      check_semiring_laws(&samples());
      check_absorption(&samples());
   }

   #[test]
   fn max_times() {
      assert_eq!(Viterbi(0.2).add(Viterbi(0.7)), Viterbi(0.7)); // ⊕ = max
      assert_eq!(Viterbi(0.5).mul(Viterbi(0.5)), Viterbi(0.25)); // ⊗ = ×
      assert_eq!(Viterbi::zero(), Viterbi(0.0));
      assert_eq!(Viterbi::one(), Viterbi(1.0));
   }

   #[test]
   fn lattice_join_keeps_best_confidence() {
      let mut a = Viterbi(0.3);
      assert!(a.join_mut(Viterbi(0.8)));
      assert_eq!(a, Viterbi(0.8));
      assert!(!a.join_mut(Viterbi(0.5)));
      assert_eq!(a, Viterbi(0.8));
   }

   #[test]
   fn clamps() {
      assert_eq!(Viterbi::new(1.5), Viterbi(1.0));
      assert_eq!(Viterbi::new(-2.0), Viterbi(0.0));
   }
}
