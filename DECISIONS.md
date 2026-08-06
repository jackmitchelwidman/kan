# Kan — Architecture Decision Record

A living log of the load-bearing decisions, newest at the bottom of each phase.
Lead: Claude. Sponsor: Jack. Reversible unless marked **[locked]**.

---

## Guiding constraint

Every decision is checked against the **Extension Test** (README §3) and the rule:
**the philosophy chooses the implementation, never the reverse.** Performance is a
hardening goal (Phase 4), never a Phase-1 design constraint.

---

## ADR-001 — Prove the thesis before chasing speed
**Decision.** Phase 1 delivers (a) a formal specification of the core calculus
(cells / faces / `fill`) and (b) an executable reference interpreter that
*demonstrably runs* two programs: composition emerging from horn-filling, and at
least one universal fill (a product or a fold) computing a concrete value.
**Why.** The novel risk in Kan is the semantics of `fill`, not codegen. If the
core is coherent and implementable, the language is real; prove that first.

## ADR-002 — Host language: OCaml **[locked]**
**Decision.** **OCaml** for the reference compiler/elaborator (Phases 1–3).
Sponsor asked for a merit-based choice (he writes Kan code, not necessarily the
compiler). Decisive factors for a dependently-typed elaborator with a novel core:
strict evaluation gives *predictable* space/time under heavy term rewriting (vs.
Haskell's laziness/space-leak risk); the deepest prior art (Coq, early Lean,
Kovács' elaboration-zoo) is OCaml/ML; module/functor system fits a small `fill`
kernel behind a signature with swappable semantic universes; fast iteration.
Haskell was a close 2nd (richer types, purity). Revisit only if we hit a wall
where Haskell's type system would change the design. Toolchain: opam switch
`kan` (ocaml-system 4.13.1) + dune 3.24.2; also runnable via bytecode `ocaml`.

## ADR-003 — Backend strategy
**Decision.** Native path: lower the *forced core* to **C**, then to a binary via
the system C compiler (the Lean4 / Idris-RefC route). Immediate execution comes
from the Phase-1 reference interpreter. Add a portable backend (wasm or Scheme)
after native works. **LLVM deferred** until C is outgrown.
**Why.** Shortest credible path to genuinely native, performant binaries with
easy FFI, without letting codegen distort the core.
→ **STATUS: first backend shipped early** (at sponsor's request). `kan build`
  lowers the FinSet fragment to C (an embedded categorical runtime: compose,
  finite limits by tuple enumeration, colimits by union–find) and calls `cc -O2`
  to produce a native ELF binary. It is a real compiler — the binary runs the
  fill algorithms — verified by diffing every example's binary output against
  the interpreter (all match). No IR yet (AST→C directly); that and the
  optimized core / LLVM path remain later phases. Spec: `docs/compiler.md`.

## ADR-004 — Open source, Apache-2.0 **[locked]**
**Decision.** Kan is open source under **Apache License 2.0** (`LICENSE`).
Sponsor confirmed public + open source. Apache-2.0 chosen over MIT because a
*language* is an ecosystem others build compilers/tooling on: its explicit
patent grant (and clear contribution terms) is the responsible default (cf.
Swift, Kotlin). Copyright line: "2026 Jack Widman and the Kan contributors".
Process unchanged: check in at **phase boundaries**; otherwise proceed.
Repo: **https://github.com/jackmitchelwidman/kan** (public).

---

## Phase plan (tracks README §13)

1. **Pin the core.** Formal spec of cells/faces/`fill`; prove composition,
   identities, products, and folds are derivable. Reference interpreter.
   → **STATUS: first milestone done.** `reference/kan_ref.ml` implements a single
     `fill : horn -> modality -> filler` kernel over FinSet. Demonstrated running
     (native binary + bytecode): composition = inner-horn fill; product,
     pullback, coproduct = universal fills, with mediating maps (universal
     property) computed. **Folds/recursion added** as initial-algebra fills
     (ℕ, List sum/length, Expr evaluator; reflection + fusion laws verified) —
     `fill_fold α Universal = cata α`, running in a finite-trees universe
     alongside FinSet. Spec: `docs/core-calculus.md`.
   → **Surface language shipped.** Repo restructured into a library (`lib/`,
     the `fill` kernel) + two executables: `reference/` (the 8 demos) and
     `bin/kan.ml` (the `kan` CLI: lexer + recursive-descent parser + evaluator
     for `.kan` files). You can now *write Kan and run it*: `examples/*.kan`
     cover compose/product/pullback/coproduct, each one kernel `fill`.
   → **Datatypes & folds in the surface.** `data`/`fold` now parse, interpret,
     AND compile: recursive datatypes become tree values, a `fold` is `cata`
     (a universal fill) and compiles to a recursive C function.
     `examples/{nat,list_sum,expr_eval}.kan` run; the expr evaluator compiles to
     a native binary. All 7 examples: interpreter output == native output.
     Grammar: `docs/surface-language.md`. Remaining in Phase 1: one typed kernel
     over both universes, richer fold carriers, formal reduction rules.
2. **Forced core + typechecker.** Identify the total, effective fragment and its
   reduction rules; minimal dependent-type substrate to state diagrams.
   → **STATUS: milestone 1 done.** `lib/core.ml` — a minimal dependent λΠ type
     theory: Pi/Lam/App/U, normalization-by-evaluation (eval→values→quote),
     definitional equality with eta, bidirectional check/infer. `test/core_test`
     type-checks the dependent identity, shows dependent application + NbE
     computing, and rejects ill-typed terms. Uses Type-in-Type for now (a
     universe hierarchy is a later mechanical step). Not yet wired to the surface
     or the kernel. Spec: `docs/type-system.md`.
   → **STATUS: milestone 2 done.** Added Σ-types and the IDENTITY type (`Id`,
     `refl`, `transport`) to `lib/core.ml`. The checker now accepts real proofs:
     `sym` (equality is symmetric) and `ap` (congruence), both derived from
     transport, and they compute (`sym U U U refl ↝ refl`). "A diagram commutes"
     = an inhabitant of an `Id` type, now expressible/checkable. Still
     Type-in-Type. Next: universes, a type surface in `.kan`, then connect types
     to `fill` so a universal property becomes a checkable proposition.
   → **STATUS: milestone 3 done — a surface you can write.** `lib/tt.ml` +
     `kan check file.ktt`: named binders elaborated to de Bruijn, `\x. t`,
     `(x:A)->B`, `A->B`, Σ `(x:A)*B`, `Id`, `refl`, `transp`, `fst`/`snd`,
     top-level `def`/`check`/`eval`. `examples/proofs.ktt` type-checks
     id/sym/ap/trans and computes.
   → **STATUS: milestone 4 done — SOUND type theory.** Replaced Type-in-Type
     with a predicative universe hierarchy (`U i : U (i+1)`; `U:U` now rejected)
     and added a base type `Bool` (true/false/if) for closed values. Equality
     proofs run on real data (`sym Bool true true refl ↝ refl`).
     `test/core_test.exe` = positive+negative suite (nonzero exit on any wrongly
     accepted term); `examples/prelude.ktt` = a small checked standard library.
     The dependent-type layer is now robust and a first-class part of the
     language (`kan check`).
   → **Phase 3, milestone 1 done — inductive types.** Added `Nat` (`zero`/`suc`)
     with a DEPENDENT eliminator `natElim` (iota-reduces), plus numeric-literal
     sugar. Enables real proofs by induction: `examples/nat.ktt` type-checks
     `add_n_zero : (n:Nat) -> Id Nat (add n zero) n`. Motives checked at level 0
     for now. This is the machinery arbitrary inductives generalize.
     Plan (agreed with Jack): (1)+(2) build the unified, richly-typed `.kan`
     language — make `.kan` dependently typed by UNIFYING around the type-theory
     core (FinSet becomes one model inside it), with general user-declared
     inductive types; then (3) backends: C first, then OCaml. Next: user-declared
     `data`, then connect types to `fill`.
3. **First elaborator.** Simplest *search* fills (adapters between fixed interfaces).
4. **Native backend + hardening.** Categorical IR → forced core → C → binary; perf.
5. **Agent-orchestration front end**, built entirely as fills.
