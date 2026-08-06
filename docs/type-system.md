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

### Deliberate simplification, noted honestly

Milestone 1 uses **Type-in-Type** (`U : U`). That is inconsistent as a *logic*
(you could encode a paradox), but it is the correct small first step for a
*computational* core; adding a universe hierarchy (`U0 : U1 : …`) is a later,
mechanical refinement that does not change the architecture.

## Where this is going

1. **Universes** — replace Type-in-Type with a predicative hierarchy.
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
