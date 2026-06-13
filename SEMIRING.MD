# Semiring provenance

Ascent can thread **semiring provenance** through your rules automatically. Tag a
relation with `#[semiring(K)]` and every derived tuple is annotated with a value
in a commutative semiring `K = (K, ⊕, ⊗, 0, 1)`, computed for free during
evaluation. This is the framework of Green, Karvounarakis & Tannen, *"Provenance
Semirings"* (PODS 2007): one mechanism that instantiates to shortest paths,
confidence scores, set/bag semantics, and "why is this fact here?" lineage.

```rust
use ascent::ascent;
use ascent::semiring::Trop;

ascent! {
    #[semiring(Trop<u32>)]      // tropical (min-plus) ⇒ shortest paths
    relation edge(Node, Node);
    #[semiring(Trop<u32>)]
    relation path(Node, Node);

    path(x, y) <-- edge(x, y);                  // ordinary rules — no annotations
    path(x, z) <-- edge(x, y), path(y, z);
}
```

See [`ascent/examples/ascent_semiring.rs`](ascent/examples/ascent_semiring.rs)
for a runnable demo.

## How it works

`#[semiring(K)]` lowers a relation to a `lattice` relation with a hidden trailing
`K` annotation column. During evaluation:

* **`⊗` (multiplication)** combines the body atoms of a *single* rule firing —
  "this derivation used all of these facts". The macro multiplies the
  annotations of every semiring body atom and stores the product on the head.
* **`⊕` (addition)** combines *alternative* derivations of the same tuple. This
  is the lattice join performed on duplicate keys — exactly the engine's existing
  fixpoint mechanism.

So `#[semiring(K)]` is sugar for "a lattice column plus the automatically
generated `⊗`". You write ordinary Datalog; the provenance algebra is threaded
for you.

### Supplying base annotations

Annotations enter through the **input** facts. A `#[semiring(K)]` relation stores
its annotation as a final tuple column, so you provide it when loading EDB facts:

```rust
prog.edge = vec![
    ("A", "B", Trop::Fin(1)),   // the weight is the annotation
    ("B", "C", Trop::Fin(2)),
];
```

A semiring head produced by a rule with no semiring body atoms gets the
annotation `K::one()`.

## The semiring library (`ascent::semiring`)

| Type | `⊕` | `⊗` | `0` | `1` | Use |
|------|-----|-----|-----|-----|-----|
| `bool` | ∨ | ∧ | `false` | `true` | set semantics / derivability |
| `Trop<T>` | min | + | `Inf` | `Fin(0)` | shortest path, least cost |
| `Viterbi` | max | × | `0.0` | `1.0` | best-derivation confidence |
| `Why<X>` | ∨ | ∧ | `{}` | `{∅}` | which input sets justify a fact |
| `Counting` | + | × | `0` | `1` | bag semantics, # derivations |

You can implement [`Semiring`](ascent_base/src/semiring.rs) for your own types.

## Termination: absorption is required for recursion

Threading a semiring through a **recursive** fixpoint only terminates when
re-deriving an already-known tuple eventually stops adding information. The
sufficient condition is **absorption** — `a ⊕ (a ⊗ b) = a` (equivalently
`1 ⊕ b = 1`). Absorption implies `⊕`-idempotence, and an idempotent commutative
semiring is a join-semilattice under its natural order with `join = ⊕`. The
absorptive types above therefore implement
[`Lattice`](ascent_base/src/lattice.rs) and reuse the engine's lattice fixpoint.

`Counting` (and full how-provenance polynomials `ℕ[X]`) are **not** absorptive:
under recursion a tuple can have infinitely many derivations (the transitive
closure of a cycle is `∞`), so the fixpoint would not converge. These types
deliberately do **not** implement `Lattice`, so using one on a recursive relation
is a **compile error**:

```text
error[E0277]: the trait bound `Counting: Lattice` is not satisfied
```

They are sound and useful for non-recursive / stratified programs.

> The theory: `Sorp(X) = ℕ[X]/~` (absorptive polynomials) is ω-continuous for
> finite `X` by Dickson's Lemma, giving terminating how-provenance; `Why<X>` is
> the positive-Boolean specialization. See Deutch, Milo, Roy & Tannen,
> *"Circuits for Datalog Provenance"* (ICDT 2014), and Dannert, Grädel, Naaf &
> Tannen, *"Semiring Provenance for Fixed-Point Logic"* (CSL 2021).

## Limitations

* **Negation / aggregation** over a `#[semiring(K)]` relation ignore the
  annotation column (it is matched with a wildcard). Threading a semiring through
  negation requires a monus operation and is out of scope here.
* **Where-provenance** (attribute/cell-level) is not expressible in the
  tuple-level semiring model and is not provided.
* Mixed-semiring programs thread each annotation type independently; a single
  rule's body annotations are grouped by type when forming each head's `⊗`.
