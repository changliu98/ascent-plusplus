//! The tropical (min-plus) semiring [`Trop`].

use std::cmp::Ordering;
use std::ops::Add;

use crate::semiring::{AbsorptiveSemiring, Semiring};
use crate::Lattice;

/// The tropical (min-plus) semiring: `⊕ = min`, `⊗ = +`, `0 = +∞`, `1 = 0`.
///
/// Annotating a relation with `Trop<T>` computes **least-cost / shortest-path**
/// provenance: a derived tuple's annotation is the minimum, over all of its
/// derivations, of the sum of the costs along that derivation. This is exactly
/// the algebra behind the canonical `lattice shortest_path(_, _, Dual<u32>)`
/// example, packaged as a semiring so it can be threaded automatically.
///
/// The cost type `T` must be `Ord` (for `min`) and `Add` (for `+`). Its
/// [`Default`] value is taken to be the additive zero of `T` (e.g. `0` for the
/// integer types), used as the multiplicative identity `1 = Fin(0)`.
///
/// `Trop` is **absorptive**: `min(a, a + b) = a` whenever `b ≥ 0` (true for the
/// usual non-negative cost domains), so threading it through a recursive
/// fixpoint terminates. Costs are expected to be non-negative; negative cycles
/// have no least-cost fixpoint, as in any shortest-path algorithm.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub enum Trop<T> {
   /// `+∞`: the additive identity `0`. A tuple annotated `Inf` is not derivable
   /// (unreachable / no finite-cost derivation).
   #[default]
   Inf,
   /// A finite cost.
   Fin(T),
}

impl<T> Trop<T> {
   /// `Some(cost)` if finite, `None` if `+∞`.
   pub fn finite(self) -> Option<T> {
      match self {
         Trop::Fin(t) => Some(t),
         Trop::Inf => None,
      }
   }

   /// `true` iff this is `+∞` (the additive identity `0`).
   pub fn is_inf(&self) -> bool {
      matches!(self, Trop::Inf)
   }
}

impl<T: Clone + Ord + Add<Output = T> + Default> Semiring for Trop<T> {
   #[inline]
   fn zero() -> Self {
      Trop::Inf
   }
   #[inline]
   fn one() -> Self {
      Trop::Fin(T::default())
   }
   /// `⊕ = min`.
   fn add(self, other: Self) -> Self {
      match (self, other) {
         (Trop::Inf, x) | (x, Trop::Inf) => x,
         (Trop::Fin(a), Trop::Fin(b)) => Trop::Fin(a.min(b)),
      }
   }
   /// `⊗ = +` (with `+∞` absorbing).
   fn mul(self, other: Self) -> Self {
      match (self, other) {
         (Trop::Inf, _) | (_, Trop::Inf) => Trop::Inf,
         (Trop::Fin(a), Trop::Fin(b)) => Trop::Fin(a + b),
      }
   }
}

impl<T: Clone + Ord + Add<Output = T> + Default> AbsorptiveSemiring for Trop<T> {}

// The natural order of the min-plus semiring: `a ≤ b ⇔ a ⊕ b = b ⇔ min(a,b) = b`
// `⇔ b ≤ a` numerically. So the lattice order is the *reverse* of the numeric
// order, with `Inf` (`+∞`) as the bottom element. `join = ⊕ = min`.
impl<T: Ord> PartialOrd for Trop<T> {
   fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
      Some(self.cmp(other))
   }
}

impl<T: Ord> Ord for Trop<T> {
   fn cmp(&self, other: &Self) -> Ordering {
      match (self, other) {
         (Trop::Inf, Trop::Inf) => Ordering::Equal,
         (Trop::Inf, Trop::Fin(_)) => Ordering::Less, // +∞ is the bottom
         (Trop::Fin(_), Trop::Inf) => Ordering::Greater,
         (Trop::Fin(a), Trop::Fin(b)) => b.cmp(a), // reverse of numeric order
      }
   }
}

impl<T: Clone + Ord> Lattice for Trop<T> {
   /// `join = ⊕ = min` (numerically). `self` becomes the numerically-smaller
   /// value; returns whether it changed.
   fn join_mut(&mut self, other: Self) -> bool {
      let take_other = match (&*self, &other) {
         (Trop::Inf, Trop::Inf) => false,
         (Trop::Inf, Trop::Fin(_)) => true, // any finite cost < +∞
         (Trop::Fin(_), Trop::Inf) => false,
         (Trop::Fin(a), Trop::Fin(b)) => b < a,
      };
      if take_other {
         *self = other;
         true
      } else {
         false
      }
   }

   /// `meet = max` (numerically), with `Inf` as the bottom.
   fn meet_mut(&mut self, other: Self) -> bool {
      let take_other = match (&*self, &other) {
         (Trop::Inf, _) => false, // already the bottom
         (Trop::Fin(_), Trop::Inf) => true,
         (Trop::Fin(a), Trop::Fin(b)) => b > a,
      };
      if take_other {
         *self = other;
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

   fn samples() -> Vec<Trop<u32>> {
      vec![Trop::Inf, Trop::Fin(0), Trop::Fin(1), Trop::Fin(3), Trop::Fin(7)]
   }

   #[test]
   fn laws() {
      check_semiring_laws(&samples());
      check_absorption(&samples());
   }

   #[test]
   fn identities() {
      assert_eq!(Trop::<u32>::zero(), Trop::Inf);
      assert_eq!(Trop::<u32>::one(), Trop::Fin(0));
   }

   #[test]
   fn min_plus() {
      // ⊕ = min
      assert_eq!(Trop::Fin(3u32).add(Trop::Fin(5)), Trop::Fin(3));
      assert_eq!(Trop::Fin(3u32).add(Trop::Inf), Trop::Fin(3));
      // ⊗ = +
      assert_eq!(Trop::Fin(3u32).mul(Trop::Fin(5)), Trop::Fin(8));
      assert_eq!(Trop::Fin(3u32).mul(Trop::Inf), Trop::Inf);
   }

   #[test]
   fn lattice_join_is_min_and_reports_change() {
      let mut a = Trop::Fin(5u32);
      assert!(a.join_mut(Trop::Fin(3))); // improved to a cheaper cost
      assert_eq!(a, Trop::Fin(3));
      assert!(!a.join_mut(Trop::Fin(8))); // no improvement
      assert_eq!(a, Trop::Fin(3));
      // join is the lattice lub and equals ⊕
      assert_eq!(Trop::Fin(5u32).join(Trop::Fin(3)), Trop::Fin(5u32).add(Trop::Fin(3)));
   }

   #[test]
   fn natural_order_matches_addition() {
      // a ≤ b  ⇔  a ⊕ b = b
      for a in samples() {
         for b in samples() {
            let le = a <= b;
            let add_eq = a.clone().add(b.clone()) == b;
            assert_eq!(le, add_eq, "order vs addition mismatch for {a:?}, {b:?}");
         }
      }
      // +∞ is the bottom
      assert!(Trop::Inf <= Trop::Fin(0u32));
   }
}
