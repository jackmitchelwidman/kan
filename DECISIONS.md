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
     cover compose/product/pullback/coproduct, each one kernel `fill`. Grammar:
     `docs/surface-language.md`. Remaining in Phase 1: fold/signature syntax in
     the surface, one typed kernel over both universes, formal reduction rules.
2. **Forced core + typechecker.** Identify the total, effective fragment and its
   reduction rules; minimal dependent-type substrate to state diagrams.
3. **First elaborator.** Simplest *search* fills (adapters between fixed interfaces).
4. **Native backend + hardening.** Categorical IR → forced core → C → binary; perf.
5. **Agent-orchestration front end**, built entirely as fills.
