# Unifying the Two Languages

Kan currently has two halves:

- **`.kan`** — the fill/compute language: builds categorical constructions
  concretely (in FinSet) and **compiles** to native code.
- **`.ktt`** — the dependent **type theory**: Π, Σ, identity types, universes,
  and user-declared (parameterized) inductives; it **checks and proves**, but
  does not compile.

The goal is one language: `.kan` programs that are **dependently typed** and
compile. The type theory supplies the *meaning* of what `fill` computes — a
product is not merely "the set `fill limit` enumerates" but "the object with the
universal property," and that universal property is a proposition the checker
verifies.

## The plan (incremental)

1. **Brick 1 — the categorical vocabulary, typed and proved (done).**
   Show that the exact universal properties `fill` computes are statable and
   provable in the type theory. `examples/category.ktt`: composition with its
   identity and associativity laws, and the **product's universal property** —
   the mediating map `⟨f,g⟩` and its commutation equations
   `fst ∘ ⟨f,g⟩ = f`, `snd ∘ ⟨f,g⟩ = g` — each a `def` returning an `Id`, i.e. a
   theorem whose type-checking is its proof. `fill limit` builds that mediating
   map concretely; here the same universal property is a checked theorem, and it
   *computes* (`fst (pair_map …)` reduces to `f t`, so the proof is `refl`).

2. **Brick 2 — one surface, one checker.** Merge the surfaces so a single
   program mixes typed definitions and categorical/computational constructs, all
   elaborated into the typed core (`lib/core.ml`). FinSet becomes one *model*
   expressed inside the theory rather than a separate hard-coded kernel.

3. **Brick 3 — `fill` as a typed operation.** Give `fill`'s inputs and outputs
   types so that requesting a universal completion produces both the value and a
   proof obligation of its universal property — the compiler as a categorical
   assistant (README §9), now type-directed.

4. **Brick 4 — compile the typed language.** Extend codegen (type-erase, then
   the existing `.kan → C` path) to the unified language; then add an OCaml
   backend.

Backends come last, deliberately: the language must stop moving before we
commit a compiler to it (README's "the philosophy chooses the implementation").

## Status

Brick 1 is done and checked (`examples/category.ktt`). The type theory is
expressive enough (Σ + Π + Id + parameterized inductives) to state and prove the
universal properties of the fill kernel — the conceptual connection is
established. Bricks 2–4 are the remaining work.
