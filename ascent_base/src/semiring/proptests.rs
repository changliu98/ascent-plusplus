//! Randomized and exhaustive property tests for the semiring library.
//!
//! These go well beyond the hand-picked cases in each type's own `tests` module:
//! they check the full semiring axioms over thousands of random elements, the
//! lattice/semiring bridge (`join ≡ ⊕`, order consistent with `⊕`), and — the
//! strongest check — that [`Why`] implements monotone Boolean functions exactly,
//! verified against brute-force truth tables over all assignments.

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt::Debug;

use super::{check_absorption, check_semiring_laws, Counting, Semiring, Trop, Viterbi, Why};
use crate::Lattice;

/// Tiny deterministic xorshift64 PRNG — reproducible, no dependencies.
struct Rng(u64);
impl Rng {
   fn new(seed: u64) -> Self {
      Rng(seed | 1)
   }
   fn next_u64(&mut self) -> u64 {
      let mut x = self.0;
      x ^= x << 13;
      x ^= x >> 7;
      x ^= x << 17;
      self.0 = x;
      x
   }
   fn below(&mut self, n: u64) -> u64 {
      self.next_u64() % n
   }
   fn flip(&mut self) -> bool {
      self.next_u64() & 1 == 1
   }
}

/// For an absorptive semiring that is also a lattice: `⊕` is idempotent, `join`
/// coincides with `⊕`, the natural order agrees with `⊕`, and `join` is the
/// least upper bound. Checked over all pairs of a sample.
fn check_lattice_bridge<K: Semiring + Lattice + PartialEq + Debug + Clone>(samples: &[K]) {
   for a in samples {
      assert_eq!(a.clone().add(a.clone()), a.clone(), "⊕ idempotent");
      for b in samples {
         let join = a.clone().join(b.clone());
         assert_eq!(join, a.clone().add(b.clone()), "join ≡ ⊕");

         // natural order: a ≤ b  ⇔  a ⊕ b = b
         let le = matches!(a.partial_cmp(b), Some(Ordering::Less | Ordering::Equal));
         assert_eq!(le, a.clone().add(b.clone()) == *b, "order vs ⊕ for {a:?},{b:?}");

         // join is an upper bound of both
         assert!(matches!(a.partial_cmp(&join), Some(Ordering::Less | Ordering::Equal)), "a ≤ a⊕b");
         assert!(matches!(b.partial_cmp(&join), Some(Ordering::Less | Ordering::Equal)), "b ≤ a⊕b");
      }
   }
}

fn random_trop(rng: &mut Rng) -> Trop<u32> {
   if rng.below(6) == 0 {
      Trop::Inf
   } else {
      Trop::Fin(rng.below(25) as u32)
   }
}

fn random_viterbi(rng: &mut Rng) -> Viterbi {
   // dyadic rationals k/8 ∈ [0,1] keep all products exact in f64.
   Viterbi(rng.below(9) as f64 / 8.0)
}

fn random_counting(rng: &mut Rng) -> Counting {
   // kept small so the saturating ops never saturate (laws stay exact).
   Counting(rng.below(6))
}

/// Build `Why<usize>` for a single clause (conjunction of the given vars).
fn why_clause(vars: &[usize]) -> Why<usize> {
   let mut w = Why::always();
   for &v in vars {
      w = w.mul(Why::token(v));
   }
   w
}

/// A random monotone DNF over variables `0..n`.
fn random_why(rng: &mut Rng, n: u32) -> Why<usize> {
   let mut w = Why::never();
   for _ in 0..rng.below(4) {
      let clause: Vec<usize> = (0..n).filter(|_| rng.flip()).map(|v| v as usize).collect();
      w = w.add(why_clause(&clause));
   }
   w
}

/// Evaluate a `Why<usize>` (interpreted as a monotone Boolean function over vars
/// `0..N`) on `assignment` (a bitmask of true variables).
fn why_eval(w: &Why<usize>, assignment: u32) -> bool {
   w.clauses().iter().any(|clause| clause.iter().all(|&v| assignment & (1 << v) != 0))
}

/// Assert the "⊆-minimal clauses only" invariant.
fn assert_minimal(w: &Why<usize>) {
   let clauses: Vec<&BTreeSet<usize>> = w.clauses().iter().collect();
   for (i, ci) in clauses.iter().enumerate() {
      for (j, cj) in clauses.iter().enumerate() {
         if i != j {
            assert!(!ci.is_subset(cj), "non-minimal clauses: {ci:?} ⊆ {cj:?}");
         }
      }
   }
}

#[test]
fn randomized_trop_laws() {
   let mut rng = Rng::new(0x7012_3456);
   for _ in 0..150 {
      let s: Vec<Trop<u32>> = (0..6).map(|_| random_trop(&mut rng)).collect();
      check_semiring_laws(&s);
      check_absorption(&s);
      check_lattice_bridge(&s);
   }
}

#[test]
fn randomized_viterbi_laws() {
   let mut rng = Rng::new(0x9988_7766);
   for _ in 0..150 {
      let s: Vec<Viterbi> = (0..6).map(|_| random_viterbi(&mut rng)).collect();
      check_semiring_laws(&s);
      check_absorption(&s);
      check_lattice_bridge(&s);
   }
}

#[test]
fn randomized_counting_laws() {
   // Counting is NOT absorptive and NOT a lattice — only the base semiring laws.
   let mut rng = Rng::new(0x1357_9bdf);
   for _ in 0..150 {
      let s: Vec<Counting> = (0..6).map(|_| random_counting(&mut rng)).collect();
      check_semiring_laws(&s);
   }
}

#[test]
fn randomized_bool_laws() {
   let s = [false, true];
   check_semiring_laws(&s);
   check_absorption(&s);
   check_lattice_bridge(&s);
}

#[test]
fn randomized_why_laws() {
   let mut rng = Rng::new(0xABCD_1234);
   for _ in 0..120 {
      let s: Vec<Why<usize>> = (0..5).map(|_| random_why(&mut rng, 4)).collect();
      check_semiring_laws(&s);
      check_absorption(&s);
      check_lattice_bridge(&s);
   }
}

/// The strongest `Why` check: `add`/`mul`/`zero`/`one` must implement Boolean
/// OR/AND/false/true exactly, verified on **every** assignment of the variables.
#[test]
fn why_is_exactly_a_boolean_function_algebra() {
   const N: u32 = 5; // 2^5 = 32 assignments, checked exhaustively
   let mut rng = Rng::new(0xFEED_FACE);

   for _ in 0..3000 {
      let a = random_why(&mut rng, N);
      let b = random_why(&mut rng, N);
      let sum = a.clone().add(b.clone());
      let prod = a.clone().mul(b.clone());

      assert_minimal(&a);
      assert_minimal(&sum);
      assert_minimal(&prod);

      for asg in 0..(1u32 << N) {
         let (ea, eb) = (why_eval(&a, asg), why_eval(&b, asg));
         assert_eq!(why_eval(&sum, asg), ea || eb, "⊕ ≠ OR");
         assert_eq!(why_eval(&prod, asg), ea && eb, "⊗ ≠ AND");
         assert!(!why_eval(&Why::<usize>::zero(), asg), "0 ≠ false");
         assert!(why_eval(&Why::<usize>::one(), asg), "1 ≠ true");
      }
   }
}

/// `Why` multiplication must be commutative and associative as a Boolean
/// function (cross-checked on truth tables), and distribute over `⊕`.
#[test]
fn why_mul_associative_and_distributive_as_boolean() {
   const N: u32 = 4;
   let mut rng = Rng::new(0x0BAD_F00D);
   for _ in 0..1500 {
      let a = random_why(&mut rng, N);
      let b = random_why(&mut rng, N);
      let c = random_why(&mut rng, N);

      let left = a.clone().mul(b.clone()).mul(c.clone());
      let right = a.clone().mul(b.clone().mul(c.clone()));
      let dist_l = a.clone().mul(b.clone().add(c.clone()));
      let dist_r = a.clone().mul(b.clone()).add(a.clone().mul(c.clone()));

      for asg in 0..(1u32 << N) {
         assert_eq!(why_eval(&left, asg), why_eval(&right, asg), "⊗ assoc");
         assert_eq!(why_eval(&dist_l, asg), why_eval(&dist_r, asg), "⊗ over ⊕");
      }
   }
}
