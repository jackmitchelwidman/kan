# The Kan Type System — Phase 2 (in progress)

The type layer is what lets a Kan program *state and verify* the properties that
`fill` is meant to satisfy: that a diagram commutes, that a construction is
universal, that an extension is unique up to equivalence (README §5). It is a
**dependent** type theory, kept deliberately thin — it exists to serve
extension, not to be the star (the Extension Test, README §3).

## Milestone 1 — a dependent core (done)

`lib/core.ml` implements a minimal λΠ calculus, the standard substrate every
dependently typed language is built on:

- **Dependent function types** (`Pi`), lambda, application, and a universe `U`.
- **Normalization by Evaluation** — terms evaluate to values with closures
  (`eval`), which are read back to normal forms (`quote`). This is how the type
  checker *computes*.
- **Definitional equality** (`conv`) by comparing values under fresh variables,
  with eta for functions.
- **Bidirectional type checking** — `check` against a known type, `infer` an
  unknown one; annotations (`Ann`) bridge the two.

Runnable check (`test/core_test.exe`): it type-checks the dependent identity
`id : (A : U) -> (x : A) -> A`, shows dependent application (`id U : (x:U) -> U`,
the return type depending on the argument), demonstrates NbE computing
(`id idty idtm` normalizes to `\A. \x. x`), and rejects ill-typed terms such as
`(U U)` and `(U : (x:U) -> x)` with messages.

Milestone 1 used Type-in-Type as a first step; that was replaced by a real
universe hierarchy in milestone 4 (below), so the core is now sound.

## Milestone 2 — equality (done)

`lib/core.ml` now also has **Σ-types** (dependent pairs: `(x:A) * B`, `pair`,
`.1`/`.2`) and the **identity type** `Id A a b` with `refl` and **transport**
(`transp A P x y p d : P y`, computing `transp .. refl d = d`). Together with Π
and Σ, that is the standard toolkit for stating universal properties.

The payoff: the checker mechanically accepts *proofs*.
`test/core_test.exe` type-checks

- `sym : (A:U)(a b:A)(p:Id A a b) -> Id A b a` — equality is symmetric,
- `ap  : (A:U)(B:U)(f:A->B)(a b:A)(p:Id A a b) -> Id B (f a)(f b)` — congruence:
  equal inputs give equal outputs (the workhorse for reasoning about composites),

both *derived from transport*, and shows they compute (`sym U U U refl ↝ refl`).
"This diagram commutes" is, concretely, an inhabitant of an `Id` type — which
this layer can now express and check.

## Milestone 3 — a surface you can write (done)

`lib/tt.ml` is a readable syntax for the core, run with `kan check file.ktt`.
It has named binders (elaborated to de Bruijn), `\x. t` lambdas, `(x:A) -> B`
and `A -> B`, Σ as `(x:A) * B`, `Id A a b`, `refl`, `transp`, `fst`/`snd`, and
top-level `def` / `check` / `eval` declarations.

`examples/proofs.ktt` — the proofs from milestone 2, now written in source:

```
def sym : (A : U) -> (a : A) -> (b : A) -> Id A a b -> Id A b a
  = \A a b p. transp A (\z. Id A z a) a b p refl
```

`kan check examples/proofs.ktt` elaborates and type-checks `id`, `sym`, `ap`,
`trans`, prints their (verified) types, and shows `sym U U U refl` normalizing
to `refl`. This is a self-contained dependently typed checker you can write
programs for — not yet connected to the `fill` kernel (that is the next step).

## Milestone 4 — soundness and a base type (done)

The core is now **sound**: a predicative **universe hierarchy** replaces
Type-in-Type. `U i : U (i+1)`, and `Pi`/`Sig`/`Id` land in the max of their
components' levels; `U : U` is now correctly *rejected*. A base type **`Bool`**
(`true`, `false`, `if`) gives closed values to compute with, so equality proofs
run on real data: `sym Bool true true refl` normalizes to `refl`.
`test/core_test.exe` is a positive+negative suite (nonzero exit if any
ill-typed term is wrongly accepted), and `examples/prelude.ktt` is a small
checked standard library (combinators, boolean ops, equality as an equivalence,
congruence on `Bool`). The hierarchy is non-cumulative for now — an ergonomic
refinement, not a soundness one.

## Phase 3, milestone 1 — inductive types & induction (done)

The first general inductive type: **`Nat`** (`zero`, `suc`) with its **dependent
eliminator** `natElim P z s n : P n`, which iota-reduces
(`natElim P z s zero = z`, `natElim P z s (suc m) = s m (natElim P z s m)`).
Numeric literals (`3`) are sugar for `suc (suc (suc zero))`.

This is the machinery — a motive `P`, a base, a step, and reduction — that
arbitrary inductive types generalize. It already lets Kan do real **proofs by
induction**. In `examples/nat.ktt`, `add` is defined by `natElim`, and

```
def add_n_zero : (n : Nat) -> Id Nat (add n zero) n
  = \n. natElim (\m. Id Nat (add m zero) m) refl
                (\k ih. ap Nat Nat (\x. suc x) (add k zero) k ih) n
```

type-checks — a genuine inductive proof (Id-type motive, congruence in the step,
`refl` in the base by computation). Note: motives are currently checked at
universe level 0 (`P : Nat -> U 0`), which covers `Nat`/`Bool`/`Id`-over-`U 0`
families — the common case.

## Phase 3, milestone 2 — user-declared inductive types (done)

`data` declarations in `.ktt`: you define your own inductive types and the
**dependent eliminator is generated automatically**. Declaring

```
data N { z : N, s : N -> N }
```

introduces `N`, its constructors `z`/`s`, and
`N_elim : (P : N -> U) -> P z -> ((k:N) -> P k -> P (s k)) -> (n:N) -> P n`,
which iota-reduces. In `examples/data.ktt`, `add` is defined by `N_elim`, and

```
def add_n_z : (n : N) -> Id N (add n z) n = \n. N_elim … 
```

type-checks — **a proof by induction over a user-declared type**. A `Tree` type
with a `size` recursion is also there. Constructor argument types may be
non-recursive or recursive occurrences of the datatype (first-order); the
eliminator's method for each constructor takes the arguments followed by an
induction hypothesis for each recursive argument.

Current limits (honest): non-parameterized (monomorphic — no `List A` yet, define
`List_N` etc.), first-order constructors, datatypes at `U 0`, motives at `U 0`,
and constructor names live in a global namespace (don't shadow them with local
binders). Parameters/indices are the next generalization.

## Where this is going

1. **Parameterized inductives** — `List A`, so polymorphic containers are one
   definition instead of one per element type.
2. **Cumulative universes** — so a term in `U i` is usable at `U j` for `j ≥ i`.
2. **A surface** for types in `.kan` (elaborating named binders to de Bruijn),
   so programs can *write* types, not just the OCaml AST.
3. **Identity / equality types** — the machinery to state "this diagram
   commutes" and "this extension is unique up to equivalence".
4. **Connect to the kernel** — give `fill`'s inputs and outputs types, so a
   universal property becomes a checkable proposition. This is the bridge from
   the Phase-1 computational kernel to a language that verifies its completions.

## Not the elaborator

Type *checking* (this) is distinct from program *completion* by synthesis
(Phase 3, the elaborator). The checker is the trustworthy core the elaborator
will target: search proposes, the checker verifies.
