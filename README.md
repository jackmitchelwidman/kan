# Kan Programming Language

## A Language of Universal Extension

### Design Document — Version 0.3

---

> **A Kan program is a partial diagram awaiting universal completion.**

This is the guiding idea. Everything below is an unfolding of it.

### What Kan is today

**Kan is a dependently typed language, and its files are `.kan`.** It has
dependent function types, dependent pairs, identity types, a universe hierarchy
(`U`, `U1`, `U2`, …), user-declared inductive types with induction, a primitive
`String`, and an **unbounded `Integer`** (arbitrary precision, like Python's
`int`) — so you can write real programs, state their properties as types, and
*prove* them. It **type-checks and compiles to native binaries via two
backends** — OCaml and C — which produce identical results.

```
kan check foo.kan            # type-check and report the types
kan run   foo.kan            # type-check, then run
kan build foo.kan -o foo     # compile to a native binary (OCaml)
kan build -c foo.kan -o foo  # compile to a native binary (C)
```

Category theory lives *in* the language, not just in the philosophy.
[`std/category.kan`](std/category.kan) defines `Category`, `Functor`, and
`NatTrans` as dependent records whose **laws are fields** — so a value of type
`Category` is one the type-checker has verified really is a category. It ships
the terminal category, the opposite category `op`, the identity functor and
identity natural transformation, and functor composition, all lawful. And the
construction the language is named for, [`std/kan.kan`](std/kan.kan), states the
**Kan extension** universal property (left and right) as a Kan type — with the
extension along the identity constructed to prove the statement inhabited.

Two exact factorials, computed by native big-integer arithmetic:

```
def fac : Nat -> Integer                       -- Nat counter, Integer accumulator
        = \n. natElim (\_. Integer) 1z (\k ih. imul (fromNat (suc k)) ih) n
eval fac 50   -- 30414093201713378043612608166064768844377641568960512000000000000
```

**What a successful compile guarantees.** Type-checking certifies a program is
*well-typed and total*: it cannot perform an ill-typed operation, and it
terminates in principle. It does **not** promise the program is *feasible* — a
total program can still cost more steps than there is time to run them (`Nat` is
Peano, so its arithmetic is unary; that is what `Integer` is for). What used to
be an outright crash is gone: `natElim` reduces iteratively, so well-typed
programs no longer overflow the stack on large closed naturals. One known limit
remains: deep recursion over *user* inductive types can still exhaust the stack
(a structural version of the same issue) — see the roadmap.

The categorical vision below — *programs are diagrams, computation is universal
completion* — is realized in this type theory. The original `fill` calculus
lives on as an internal FinSet reference model
([`docs/core-calculus.md`](docs/core-calculus.md)).

Kan remains a *living design document*: the philosophy chooses the
implementation, not the other way around.

**Document map**

1. The Essence of Kan
2. The Central Computational Principle
3. The Extension Test — a criterion for every design decision
4. The Minimal Core Calculus — cells, faces, and fill
5. The Type System
6. The Notion of Program Completion
7. Pure Functional Foundations
8. Compiler Architecture
9. AI Agent Orchestration
10. On the Name
11. Examples of Kan Programs
12. Formal Semantics — sketch and open problems
13. Implementation Roadmap
14. The Fundamental Question

---

# 1. The Essence of Kan

Kan is built around a single foundational idea:

> A program is a partial categorical structure, and computation is the process of extending that structure canonically.

Traditional languages ask the programmer to describe a complete sequence of operations. Kan begins from a different premise.

A programmer rarely knows the complete structure of a complex system at the beginning. Instead they know:

* some objects,
* some relationships,
* some transformations,
* some constraints,
* some desired outcomes.

The missing pieces are not "unfinished code." They are **opportunities for universal construction**. Kan treats incompleteness as a first-class concept.

A Kan program is not necessarily a complete construction. It is a diagram with intentional gaps. The compiler's role is not merely to check whether the program is complete, but to ask:

> What is the canonical extension of this partial structure?

---

# 2. The Central Computational Principle

Every language has an underlying model of computation.

| Paradigm | Computation is… |
|---|---|
| Lambda calculus | function application and reduction |
| Turing machines | states and transitions |
| Logic programming | proof search |
| Relational / SQL | query resolution |
| **Kan** | **canonical extension of a partial diagram** |

The fundamental operation. Given a partial diagram

```
        A
       / \
      /   \
     B     C
```

find the universal object (or morphism) that completes the structure.

The wager of Kan is that **many programming tasks are secretly extension problems**:

* extending an incomplete algorithm,
* extending a local model into a global system,
* extending an interface into an implementation,
* extending a partial data transformation,
* extending the capabilities of one agent into a multi-agent workflow.

Kan is not "a dependently typed language with category-theory features." It is an investigation of a research question:

> **Can extension — the canonical completion of a partial diagram — serve as the fundamental computational model of a programming language?**

The reach of that one primitive is what makes Kan powerful for category theory:

> Because Kan's single primitive is the universal completion of a partial diagram, the deep constructions of category theory stop being separate theories and become one act seen at different shapes: a limit or colimit is a fill, a **sheaf** is the fill that glues compatible local sections into a unique global one, and a **fibration** is the fill that lifts a partial diagram along a map.

*(This is the design's conceptual reach. What the compiler runs today is that primitive at small scale — limits/colimits in FinSet, folds, and a dependent type theory; see the status below.)*

---

# 3. The Extension Test

Because Kan is organized around one idea, that idea becomes a decision procedure. Every proposed feature must pass:

> **The Extension Test.** A feature earns its place only if it is one of:
> **(a)** the extension primitive itself,
> **(b)** a way to *describe a partial diagram* to that primitive, or
> **(c)** something that *emerges* from a universal property.
>
> Anything else is mathematical ornament, and is left out.

Concretely:

* *Should this be a primitive?* → Does it express a fundamental extension operation?
* *Should this be syntax?* → Does it help the programmer describe a partial categorical structure?
* *Should this be inferred by the compiler?* → Should it emerge from a universal property?
* *Should this be in the language at all?* → Does it make extension easier, or is it decoration?

---

# 4. The Minimal Core Calculus — cells, faces, and fill

Every great computational paradigm has a tiny seed. The lambda calculus seeds a language in *application*; logic programming in *inference*. Kan needs its seed, and it must survive the Extension Test.

The seed of Kan is **one sort, one relation, one operation.**

## 4.1 One sort: the cell

Everything in Kan is a **cell** — a piece of a diagram. Cells come in dimensions:

* a **0-cell** is what other languages call an *object*,
* a **1-cell** is a *morphism*,
* a **2-cell** is a relation *between* morphisms,
* and so on upward.

These are not separate primitives. They are the *same* primitive at different dimensions. Objects and morphisms are not two things; they are cells of dimension 0 and 1.

## 4.2 One relation: faces

Every cell has **faces** — its boundary, the cells one dimension down. Crucially, **a boundary may exist without its interior.** That is what makes a diagram *partial*, and partiality is the normal state of a Kan program, not an error.

A cell whose boundary is present but missing exactly one face is a **horn**: a diagram that is *asking to be completed*.

## 4.3 One operation: fill

The single operation of Kan is **fill**:

> Given a horn, produce the cell that completes it.

That is the entire computational act. The programmer draws the boundary they understand; `fill` supplies the interior that must exist.

## 4.4 Composition is derived, not primitive

The decisive test of the seed: does it give back the things we thought were fundamental?

Take two composable arrows `f : A → B` and `g : B → C`. Together they form a horn — a diagram missing its long edge. **Fill it, and the new edge is exactly `g ∘ f`.**

So Kan does not take composition as a given the way categorical languages do. **Composition falls out of horn-filling.** Identities, associativity, and coherence follow the same way. This is the "even smaller core hiding underneath" that the seed was meant to expose: even the operation other categorical languages treat as bedrock is, in Kan, a special case of the one primitive.

## 4.5 The one primitive underneath the primitive

Filling has two faces, and understanding their relationship is the deepest point in the calculus.

Fix an inclusion `i : A ↪ B` — a sub-diagram sitting inside a larger one. **Restriction** along `i` sends a completed diagram to its boundary:

```
i*  :  maps out of B  ⟶  maps out of A        ( x ↦ x ∘ i )
```

An **extension problem** is the reverse: given `a` on `A`, find `x` on `B` with `i*(x) = a`. Fill in the interior given the boundary. *Both* of Kan's fillers are this one problem:

* **Horn-filling** is the extension problem for a horn inclusion `Λⁿₖ ↪ Δⁿ`.
* **Kan extension** is the extension problem for a functor `F`, whose solution is *universal* (the adjoints `Lan_F ⊣ F* ⊣ Ran_F`).

They are the same equation `i*(x) = a` asked at different **modalities** — different demands on the solution:

| Modality demanded | Construction | What it yields |
|---|---|---|
| **∃ some** solution | horn-filling (a lifting property) | composition, the categorical substrate |
| ∃ solution **unique up to homotopy** | quasicategory composite | *directed* composition |
| the **universal / best** solution | **Kan extension** | products, limits, adjoints, folds |

So `fill` is not really one operation — it is the **extension-problem operator, parameterized by the modality of solution it demands:**

```
fill[∃]                 →  build structure   (composition falls out)
fill[∃ up-to-homotopy]  →  directed composition
fill[universal]         →  compute           (products, folds, adapters, …)
```

The genuinely irreducible primitive of Kan is therefore:

> **Extend the boundary over the interior — solve an extension problem along an inclusion — at a stated modality.**

Horn-filling and the Kan extension are two settings of that single dial. This is smaller than either, and it makes the whole layering of the language fall out of one knob rather than a pile of bolted-on constructs.

## 4.6 Directed, not groupoidal

A design commitment: Kan uses **inner-horn filling** — the *directed* discipline (quasicategory-style). Morphisms are **not** forced to be invertible; computation keeps a direction. The fully symmetric alternative (a Kan complex, where every horn fills and everything becomes invertible) is mathematically beautiful but dissolves the arrow of computation, so Kan does not adopt it at the base. The *universal* fillers (Kan extensions) are the distinguished ones that do real work on top of this directed substrate.

## 4.7 Core and elaborator

The modality dial draws a sharp line through the language:

* **The core (`fill[universal]`, forced).** Where the universal property forces a unique answer, `fill` is a *total, effective reduction* — like normalization. This is the trustworthy kernel: it always computes, and it always terminates.
* **The elaborator (`fill` as search).** Where the completion must be *synthesized* — the compiler is asked to invent a morphism that isn't forced — `fill` becomes a (semi-)decidable search that may succeed, fail with a diagnostic, or need more constraints. This is the README's "compiler as collaborator."

The two are not two languages. They are the same operation at two ends of the modality dial, and the elaborator always elaborates *down to* the core.

## 4.8 Grammar sketch (provisional)

```
cell   ::=  0-cell  |  name : cell → cell            -- objects and morphisms are cells
diagram ::= { cell, … }                              -- a partial diagram
horn   ::=  ⌜ cell, … ⌝                              -- a diagram missing one face
term   ::=  fill horn                                -- the one operation
         |  complete diagram                         -- fill, at the universal modality
```

## 4.9 What a five-line Kan program looks like

**Composition falls out of the seed (the completion is *forced*):**

```
f : A → B
g : B → C
horn h = ⌜ f , g ⌝        -- inner horn: two composable edges
fill h                     -- universal filler; its new edge is  g ∘ f : A → C
```

No `compose` keyword exists. You fill a horn and read off the edge.

**The gap between two agents (the completion is a *search*):**

```
agent Analyze : Doc     → Findings
agent Decide  : Rulings → Action
diagram Review = Analyze ⟶ □ ⟶ Decide     -- □ is the gap: Findings → Rulings
complete Review                            -- fill □ as the canonical extension
```

The same operation, `complete = fill`. The only difference between the two programs is the *modality*: forced (total core) versus synthesized (search tier).

---

# 5. The Type System

Kan is dependently typed — but dependent types are not Kan's identity. They are the **mechanism for stating and verifying categorical structure**: the ambient logic in which a diagram's shape and its universal properties are written down.

Dependent types let a Kan program state:

* this diagram commutes,
* this construction satisfies a universal property,
* this morphism preserves structure,
* this extension is unique up to equivalence.

A type in Kan is not merely a classification. A type may denote an object, a morphism, a diagram, a functor, a natural transformation, or a universal construction. The substrate is kept **deliberately thin** — just enough Π-types, universes, and identity to *describe* diagrams to `fill`. Per the Extension Test, the type system exists to serve extension, not to be the star.

---

# 6. The Notion of Program Completion

Partial programs are not errors. They are the natural form of Kan programming.

Where a traditional language reads

```
function process(data):
    ???
```

as incomplete, Kan reads it as: *a partial morphism has been specified — find its canonical extension.* The questions become:

* What additional structure is required for this morphism to exist?
* Can it be derived? Can it be synthesized?
* Is there a unique universal solution?
* If several solutions exist, what constraint distinguishes them?

**Can every ordinary program be expressed this way?** In principle, yes:

* **function types** arrive as exponentials (universal fillers),
* **data** as sums, products, and recursive types (initial algebras — colimits are fillers),
* **structured recursion** as folds over those initial algebras.

Two honest caveats, both consequences of the core/elaborator split:

1. **General recursion.** A *forced, total* `fill` yields only terminating recursion. Unbounded, possibly-non-terminating computation needs an explicit fixpoint/partiality structure that is *not* automatically universal — so it lives in the elaboration/search tier, deliberately outside the guaranteed-total core.
2. **Effects.** IO, state, and concurrency are expressible, but only in their categorical shadow (as monads/comonads). A Kan program can do anything an imperative one can, but you write its categorical form, not a line-by-line transliteration. Universal — not always idiomatic.

---

# 7. Pure Functional Foundations

Kan is purely functional; this follows from the categorical worldview. Functions are morphisms, composition is fundamental (indeed derived from `fill`), and side effects must be represented explicitly as mathematical structure rather than hidden operational behavior. Purity buys compositional and equational reasoning, predictable semantics, and compatibility with the categorical interpretation. Effects, when present, are themselves modeled categorically.

---

# 8. Compiler Architecture

Kan is a compiled language. The goal is not a theorem prover or a notation system, but a practical language that produces efficient software. The pipeline translates high-level categorical intent into executable computation:

```
Kan Program
      |
      v
Categorical Intermediate Representation      (diagrams + fill obligations)
      |
      v
Optimized Core Language                      (forced fillers, normalized)
      |
      v
Machine Code
```

The compiler is a **categorical assistant**, not merely an optimizer. Given a partial system it answers: What morphisms are missing? What structures are required? Which completion is universal? Programming becomes an interactive process of specifying and completing structures — the elaborator proposing, the core verifying.

---

# 9. AI Agent Orchestration

A primary motivation for Kan. Modern AI systems require enormous explicit glue: connecting agents, translating representations, managing context, resolving incompatible outputs, maintaining consistency. Kan views this as a categorical extension problem.

Given

```
Agent A  ----\
              \
               ?
              /
Agent B  ----/
```

the programmer should not necessarily specify the missing communication pathway. Instead: *find the universal extension that lets these agents cooperate.* The `□` gap in §4.9 is exactly this, and the language should naturally support multi-agent systems, knowledge integration, semantic translation, distributed reasoning, and consistency maintenance — all as fillers.

---

# 10. On the Name

The fundamental concept of Kan is not, strictly, *the Kan extension* — it is the more general "extension along an inclusion, at a modality" of §4.5. The name still fits, and fits twice over:

> **Kan is named for Daniel Kan, whose extension and complex both express one idea — a partial diagram has a canonical filler. The language takes that idea, extension along an inclusion, as its seed. The Kan extension is its universal form, not its whole.**

Both of the language's fillers — horn-filling (the Kan *complex*) and universal completion (the Kan *extension*) — are Daniel Kan's. The general primitive is precisely what *fuses* his two contributions. Naming the language after the mathematician whose fingerprints are on the whole region is the honest move, exactly as Turing machines and Church's λ are named for people, not mechanisms.

As of now the namesake is not only the philosophy but a definition you can check: [`std/kan.kan`](std/kan.kan) states the left and right Kan extension universal properties as Kan types, resting on the lawful `Category`/`Functor`/`NatTrans` of [`std/category.kan`](std/category.kan). The extension along the identity is constructed, so the statement is inhabited — the language named for Kan extensions can express, and verify, a Kan extension.

---

# 11. Examples of Kan Programs

*(Placeholder — to grow as the surface syntax settles. Seeds so far, from §4.9: composition-as-horn-filling, and the two-agent adapter gap. Candidates to add: a product as a universal cone, a fold as a Kan extension along a shape functor, an interface completed into an implementation.)*

---

# 12. Formal Semantics — sketch and open problems

**Sketch.** The semantic domain is a directed structure (quasicategory-flavored) in which cells, faces, and horns live. `fill` is interpreted as solving an extension problem `i*(x) = a`; the forced core corresponds to cases where this solution is unique-up-to-iso (a genuine Kan extension / limit), the elaborator to cases where it must be searched for.

**Open problems (the research core of Kan):**

* Which class of horns admits *total, effective* filling — i.e. exactly how large is the trustworthy core?
* What is the right proof obligation for a *universal* fill, and when is it decidable?
* How is the directed (inner-horn) discipline reconciled with a computationally realistic identity/equality?
* Where precisely is the boundary between forced fill and searched fill, and can it be given a clean type-theoretic characterization?
* What is the smallest presentation of "cells + faces + fill" that still recovers composition, products, and folds?

---

# 13. Implementation Roadmap

Deliberately after the philosophy, never before it.

1. **Pin the core.** Formalize cells/faces/fill and prove composition, identities, products, and folds are derivable.
2. **Define the forced core.** Identify the total, effective fragment and its reduction rules.
3. **A minimal typechecker** for the thin dependent substrate that states diagrams.
4. **A first elaborator** for the simplest search fills (adapters between fixed interfaces).
5. **Categorical IR → core → machine code** for the forced fragment only.
6. **Agent-orchestration front end** built entirely as fills.

---

# 14. The Fundamental Question

The central research question of Kan:

> What is the smallest computational core from which extension emerges as the basic act of programming?

The current answer of this document: **cells, faces, and one `fill` operation — extension along an inclusion, at a stated modality.** Composition is a filler; the Kan extension is the universal filler; everything else is derived or synthesized.

Kan is not Haskell with category theory, Idris with more abstractions, or Lean as a programming language. Those are extraordinary, and they begin elsewhere. Kan begins here:

> Programs are diagrams.
>
> Computation is extension.
>
> The compiler fills the horn.

---

# License & Contributing

Kan is free and open source under the **Apache License 2.0** (see [`LICENSE`](LICENSE)).
Contributions are welcome and are accepted under the same license.

**Requirements:** OCaml ≥ 4.13 and dune ≥ 3.0. Kan compiles to native code via
two backends — OCaml (`ocamlopt`, default) and C (`cc`, with `kan build -c`).
No third-party libraries — Kan builds against the OCaml standard library only.
If you don't have dune: `opam install dune`.

**Try it now:**

```
git clone https://github.com/jackmitchelwidman/kan
cd kan
dune build

# type-check a dependently-typed program (proofs, inductive types, …):
dune exec bin/kan.exe -- check examples/nat.kan

# run it:
dune exec bin/kan.exe -- run examples/nat.kan

# COMPILE it to a native binary (this type-checks first) and run that:
dune exec bin/kan.exe -- build examples/nat.kan -o nat && ./nat        # via OCaml
dune exec bin/kan.exe -- build -c examples/nat.kan -o nat && ./nat     # via C

# unbounded integers — exact fac 50, identical from every runtime:
dune exec bin/kan.exe -- run examples/integer.kan

# category theory: the terminal & opposite categories, functors, nat-trans:
dune exec bin/kan.exe -- check examples/categories.kan

# the whole regression gate (check + tri-runtime output diff):
bash tests/run_all.sh
```

Every program in [`examples/`](examples/) is a `.kan` file: `nat.kan` (induction),
`list.kan` (polymorphic `List`), `data.kan` (user inductive types),
`integer.kan` (unbounded arithmetic), `categories.kan` (category theory via the
standard library), `category.kan` (universal properties as theorems),
`person.kan` (a type that depends on a value), `using_std.kan` (importing the
standard library).

Kan has an `import` mechanism and a small **standard library** in
[`std/`](std/) — combinators, boolean and natural-number arithmetic (with
proofs), polymorphic `List`, `Option`, and equality lemmas:

```
import "../std/nat.kan"
import "../std/list.kan"
def xs : List Nat = cons Nat 3 (cons Nat 1 (nil Nat))
eval add 2 (length Nat xs)
```

**Install `kan` on your PATH** (so you can run `kan build foo.kan` anywhere):

```
dune build
dune install --prefix ~/.local --sections bin    # installs `kan` to ~/.local/bin
# re-run the last line after any rebuild to update the installed binary
```

Layout: the type theory is `lib/core.ml` (kernel) and `lib/tt.ml` (surface);
type erasure is `lib/erase.ml`; the native backends are `lib/ocaml_backend.ml`
and `lib/c_backend.ml`; the CLI driver is `bin/kan.ml`. The original `fill`
calculus survives as the FinSet reference model (`lib/kernel.ml`,
`reference/kan_ref.ml`). Design decisions are logged in
[`DECISIONS.md`](DECISIONS.md); the type system is specified in
[`docs/type-system.md`](docs/type-system.md), the unification story in
[`docs/unification.md`](docs/unification.md), and the reference `fill` model in
[`docs/core-calculus.md`](docs/core-calculus.md).
