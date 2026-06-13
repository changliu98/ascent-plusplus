//! The [`Semiring`] trait and a library of commutative semirings for
//! provenance-annotated Datalog, in the style of Green, Karvounarakis & Tannen,
//! *"Provenance Semirings"* (PODS 2007).
//!
//! A relation annotated over a commutative semiring `K = (K, ⊕, ⊗, 0, 1)` maps
//! each tuple to a value in `K`. During evaluation:
//!
//! * the body atoms of a *single* rule firing are combined with multiplication
//!   `⊗` ([`Semiring::mul`]) — "this derivation used all of these facts";
//! * the *alternative* derivations of the same head tuple are combined with
//!   addition `⊕` ([`Semiring::add`]) — "the tuple holds because of this
//!   derivation *or* that one".
//!
//! `0` annotates a tuple that is not derivable (and annihilates `⊗`); `1`
//! annotates a trivially-true / empty derivation (the unit of `⊗`).
//!
//! # Absorption, termination, and the lattice bridge
//!
//! Threading a semiring through a *recursive* fixpoint only terminates for
//! semirings where re-deriving an already-derived tuple eventually stops adding
//! information. The precise sufficient condition is **absorption**
//! (`a ⊕ (a ⊗ b) = a`, equivalently `1 ⊕ b = 1`); see [`AbsorptiveSemiring`].
//! Absorption implies `⊕`-idempotence, and an idempotent commutative semiring is
//! a join-semilattice under its *natural order* (`a ≤ b ⇔ a ⊕ b = b`) with
//! `join = ⊕`. Such semirings therefore *also* implement [`Lattice`](crate::Lattice),
//! and the engine's existing lattice-join-on-duplicate-key fixpoint computes the
//! provenance directly — no new machinery required.
//!
//! Non-absorptive semirings (e.g. [`Counting`], the bag/ℕ semiring) deliberately
//! do **not** implement [`Lattice`](crate::Lattice): their fixpoint may diverge
//! under recursion (a cyclic transitive closure has infinitely many
//! derivations), so the macro rejects them on recursive relations at compile
//! time. They remain usable for non-recursive / stratified programs.

use crate::Lattice;

pub mod tropical;
pub mod viterbi;
pub mod counting;
pub mod why;

#[cfg(test)]
mod proptests;

pub use counting::Counting;
pub use tropical::Trop;
pub use viterbi::Viterbi;
pub use why::Why;

/// A commutative semiring `(K, ⊕, ⊗, 0, 1)`: two associative, commutative
/// operations where `⊗` distributes over `⊕`, `0` is the unit of `⊕` and
/// annihilates `⊗`, and `1` is the unit of `⊗`.
///
/// See the [module documentation](self) for how `⊕`/`⊗`/`0`/`1` are used to
/// annotate derivations during Datalog evaluation.
pub trait Semiring: Clone {
   /// The additive identity `0` — annotation of a non-derivable tuple, and the
   /// annihilator of `⊗` (`0 ⊗ a = 0`).
   fn zero() -> Self;

   /// The multiplicative identity `1` — annotation of a trivial/empty
   /// derivation, and the unit of `⊗` (`1 ⊗ a = a`).
   fn one() -> Self;

   /// Semiring addition `⊕`: combines two *alternative* derivations of the same
   /// tuple.
   fn add(self, other: Self) -> Self;

   /// Semiring multiplication `⊗`: combines the body atoms of a *single*
   /// derivation.
   fn mul(self, other: Self) -> Self;

   /// Product of an iterator of annotations, `1` if empty. This is the operation
   /// the engine applies across the body atoms of one rule firing.
   fn product<I: IntoIterator<Item = Self>>(iter: I) -> Self {
      iter.into_iter().fold(Self::one(), Self::mul)
   }

   /// Sum of an iterator of annotations, `0` if empty.
   fn sum<I: IntoIterator<Item = Self>>(iter: I) -> Self {
      iter.into_iter().fold(Self::zero(), Self::add)
   }
}

/// Marker for semirings that are **absorptive**: `a ⊕ (a ⊗ b) = a` for all
/// `a, b` (equivalently `1 ⊕ b = 1`, i.e. `1` is the greatest element and `⊗` is
/// decreasing).
///
/// Absorption implies `⊕`-idempotence (`a ⊕ a = a`, taking `b = 1`) but is
/// strictly stronger. It is the key property that makes recursive re-derivations
/// redundant and so guarantees a **finite, terminating** provenance fixpoint
/// (Deutch, Milo, Roy & Tannen, *"Circuits for Datalog Provenance"*, ICDT 2014).
///
/// Every type implementing this trait should also implement
/// [`Lattice`](crate::Lattice) with `join ≡ add`, so that it can be used with
/// automatic provenance threading on recursive relations.
pub trait AbsorptiveSemiring: Semiring {}

// ── Boolean semiring 𝔹 = ({false, true}, ∨, ∧, false, true) ──────────────────
// `bool` already implements `Lattice` (join = max = ∨, meet = min = ∧), so set
// semantics / derivability tracking composes with automatic threading for free.

impl Semiring for bool {
   #[inline]
   fn zero() -> Self { false }
   #[inline]
   fn one() -> Self { true }
   #[inline]
   fn add(self, other: Self) -> Self { self || other }
   #[inline]
   fn mul(self, other: Self) -> Self { self && other }
}

impl AbsorptiveSemiring for bool {}

/// Debug-only sanity check that a value behaves like a semiring element with
/// respect to a sample of other elements. Intended for tests.
#[doc(hidden)]
pub fn check_semiring_laws<K: Semiring + PartialEq + std::fmt::Debug>(samples: &[K]) {
   for a in samples {
      // 0 and 1 units
      assert_eq!(a.clone().add(K::zero()), a.clone(), "a ⊕ 0 = a");
      assert_eq!(a.clone().mul(K::one()), a.clone(), "a ⊗ 1 = a");
      // 0 annihilates ⊗
      assert_eq!(a.clone().mul(K::zero()), K::zero(), "a ⊗ 0 = 0");
      for b in samples {
         // commutativity
         assert_eq!(a.clone().add(b.clone()), b.clone().add(a.clone()), "⊕ commutes");
         assert_eq!(a.clone().mul(b.clone()), b.clone().mul(a.clone()), "⊗ commutes");
         for c in samples {
            // associativity
            assert_eq!(
               a.clone().add(b.clone()).add(c.clone()),
               a.clone().add(b.clone().add(c.clone())),
               "⊕ associates"
            );
            assert_eq!(
               a.clone().mul(b.clone()).mul(c.clone()),
               a.clone().mul(b.clone().mul(c.clone())),
               "⊗ associates"
            );
            // distributivity
            assert_eq!(
               a.clone().mul(b.clone().add(c.clone())),
               a.clone().mul(b.clone()).add(a.clone().mul(c.clone())),
               "⊗ distributes over ⊕"
            );
         }
      }
   }
}

/// Debug-only check of the absorption law `a ⊕ (a ⊗ b) = a` over a sample.
#[doc(hidden)]
pub fn check_absorption<K: AbsorptiveSemiring + PartialEq + std::fmt::Debug>(samples: &[K]) {
   for a in samples {
      for b in samples {
         assert_eq!(
            a.clone().add(a.clone().mul(b.clone())),
            a.clone(),
            "absorption a ⊕ (a ⊗ b) = a"
         );
      }
   }
}

#[cfg(test)]
mod tests {
   use super::*;

   #[test]
   fn boolean_semiring() {
      let samples = [false, true];
      check_semiring_laws(&samples);
      check_absorption(&samples);
      assert_eq!(bool::zero(), false);
      assert_eq!(bool::one(), true);
      assert_eq!(true.add(false), true);
      assert_eq!(true.mul(false), false);
   }

   #[test]
   fn product_and_sum() {
      assert_eq!(bool::product([true, true, true]), true);
      assert_eq!(bool::product([true, false, true]), false);
      assert_eq!(bool::product::<[bool; 0]>([]), true); // empty product = 1
      assert_eq!(bool::sum::<[bool; 0]>([]), false); // empty sum = 0
   }
}
