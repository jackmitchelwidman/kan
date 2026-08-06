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

2. **Brick 2 — compile the typed language (type erasure).** *Re-scoped after
   brick 1:* the typed surface (`.ktt`) already **is** the unified surface — the
   fill language's `data`/`fold`/products are a strict special case of the type
   theory's parameterized inductives, eliminators, and Σ. So "merging surfaces"
   is mostly already true, and the real remaining gap is that the typed language
   does not compile. Brick 2 closes that: an **erasure** pass (`lib/erase.ml`)
   maps the dependent core to an untyped functional IR (types and proofs become
   a dummy value; eliminators become recursion), which a backend then compiles.
   The old fill pipeline stays green as the legacy FinSet *model* layer.

3. **Brick 3 — `fill` as a typed operation.** Give `fill`'s inputs and outputs
   types so that requesting a universal completion produces both the value and a
   proof obligation of its universal property — the compiler as a categorical
   assistant (README §9), now type-directed. (Also where `.ktt` and `.kan` merge
   into one extension.)

4. **Brick 4 — native backends.** Emit from the erased IR to a target: **OCaml
   first** (native closures make erasure near-transparent), then C via the same
   IR. Backends last, and the IR is target-independent so the choice does not
   block earlier work.

Backends come last, deliberately: the language must stop moving before we
commit a compiler to it (README's "the philosophy chooses the implementation").

## Status

- **Brick 1 done** (`examples/category.ktt`): the type theory states and proves
  the fill kernel's universal properties — the conceptual connection.
- **Brick 2 done** (`lib/erase.ml`, `kan exec`): type **erasure** maps the
  dependent core to an untyped IR (`iexpr`) with a reference runtime. Validated
  by running every example through erasure and matching the type checker's
  `eval` — `kan exec` == `kan check` on computational outputs. (Erased type
  parameters print as `_`, since they are gone: e.g. `cons _ false …`.) The IR
  is target-independent; brick 4 emits native code from it.

- **Brick 4 (OCaml) done** (`lib/ocaml_backend.ml`): `kan build foo.ktt -o foo`
  type-checks the program and compiles it — erased IR → OCaml source → `ocamlopt`
  → a **native binary**. The dependently-typed language now compiles and runs;
  every example's binary output matches `kan check`. `kan build` dispatches on
  extension (`.ktt` → OCaml, `.kan` → the legacy C fill-backend).

Remaining: brick 4 (a **C** backend from the same erased IR) and brick 3 (`fill`
as a typed operation; merge `.ktt`/`.kan` into one language).
