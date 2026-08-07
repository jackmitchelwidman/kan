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

## ADR-005 — One language: Kan is dependently typed, files are `.kan` **[locked]**
**Decision.** Kan *is* the dependent type theory. Its single file extension is
`.kan`. The CLI (`kan check|run|build|emit-ml`) operates on that language only.
The original `fill` calculus is **retired as a user-facing language**; it
survives as an internal FinSet **reference model** (`lib/kernel.ml`,
`reference/kan_ref.ml`) whose universal properties are now *proved as types*
in the language (`examples/category.kan`).
**Why.** Sponsor's directive: one language, done properly, no temporary split.
The typed surface already subsumed the fill language's computational content
(data/fold/products are a special case of inductives + Σ), so unifying loses
nothing and removes the confusing two-language split. Removed
`lib/{syntax,interp,compile}.ml` and the fill-language docs; migrated all
examples to `.kan`. Compilation is via OCaml (`ocamlopt`); a C backend from the
same erased IR is future additive work.

---

## ADR-006 — `Integer` is a separate, machine-backed, unbounded type
**Decision.** Add `Integer`: arbitrary-precision, signed, primitive (`iadd`,
`isub`, `imul`, `ieq`, `ilt`, and `fromNat : Nat -> Integer`). It is **distinct
from `Nat`**, which stays the inductive type for induction and proofs. Literals
carry a trailing `z` (for ℤ): `0z`, `120z`. The bignum is **hand-rolled**
(`lib/bigint.ml`, sign + base-10⁹ limbs) — no third-party dependency — and the
OCaml backend splices `bigint.ml`'s own source (via a dune rule) so there is one
source of truth; the C backend carries a twin bignum in C.
**Why.** `Nat`'s arithmetic is unary (cost ∝ value), so it cannot compute large
numbers; `Integer` gives Python-like unbounded arithmetic at native cost. Keeping
them separate preserves `Nat`'s definitional unfolding, which the proofs
(`add_n_zero`, …) depend on — never replace `add`/`mul`. Base 10⁹ keeps
single-limb products inside both a 63-bit OCaml int and a C int64, so one
algorithm ports to both backends. The idiom is a Nat counter driving an Integer
accumulator (see `std/integer.kan`). A type-directed numeric literal (so a bare
`50` is `Nat` or `Integer` by context) would be nicer but needs an elaboration
pass; deferred — the `z` suffix is the safe, unambiguous interim.

## ADR-007 — Universe literals `U1`, `U2`, …
**Decision.** The parser accepts `Ui` for `U i` (i ≥ 1), matching how the printer
already shows universes. **Why.** Needed to annotate higher-universe types (e.g.
`Category : U1`); the printer/parser are now inverse.

## ADR-008 — Category theory as dependent records (laws as fields)
**Decision.** Encode `Category`/`Functor`/`NatTrans` as Σ-records whose fields
include the laws as `Id`-proofs, with named accessor functions hiding the
`fst`/`snd` projections (`std/category.kan`). State Kan extensions as universal
properties (`std/kan.kan`). **Why.** This makes "is a category" a *checked*
proposition and keeps use-sites readable (`cmp C a b c g f`). A dedicated record
syntax would be more ergonomic than nested Σ + `fst/snd`, but the record encoding
is sound today and needs no kernel change; record syntax is a future ergonomic
refinement. Infix arithmetic (`+`, `*`) is deliberately **not** added: in a
dependent language `A * B` (Σ) and `a * b` (multiply) share one grammar, so a
clean fix must repurpose a core symbol — a sponsor-level call, left open.

## ADR-009 — What a successful compile guarantees
**Decision.** State the guarantee honestly: compilation certifies *well-typed and
total*, not *feasible*. Fix avoidable runtime crashes where cheap (done:
`natElim` now reduces iteratively, so large closed naturals no longer overflow
the stack); document the limits that remain (unary `Nat` cost; deep recursion
over user inductive types can still overflow — a structural version of the same
issue, whose fix is invasive and deferred). **Why.** The sponsor's north star is
"a successful compile should guarantee the program runs properly, as much as
possible." Totality plus a fixed crash-class is real progress; over-claiming a
blanket guarantee would be dishonest, since a total language can still be
astronomically costly.

## ADR-010 — Pattern-matching recursive functions, elaborated to eliminators
**Decision.** Add `match` and structural recursion as **surface sugar**, lowered
in the parser to the datatype's eliminator — no kernel change. `match e { | C x..
=> body | .. }` becomes the eliminator with motive `\_. R` (R = the def's result
type, threaded from its annotation by peeling one Pi per lambda binder; or given
explicitly via `match e return R { .. }`). Recursive calls `f ..k..` become the
induction hypothesis for the recursive-position binder `k`; the elaboration is
done entirely in name-land (the `ns` scope), avoiding de Bruijn surgery.
**Why.** This is the ergonomic "middle row" every total language occupies (Agda/
Coq/Lean): pleasant recursion without unrestricted general recursion. Elaborating
to eliminators keeps the kernel small and sound, and **totality is preserved by
construction** — the elaborated term *is* an eliminator, so it can only recurse on
structurally-smaller arguments. The subset (one decreasing matched argument;
exhaustive) is enforced by *rejecting* everything outside it (non-structural
recursion and non-exhaustive matches each have a gate rejection test). The more
general `fix`/`match`+guard-checker design (Coq-style, kernel-level) is deferred, as
is large elimination (motives above `U0`). The stdlib is **not** migrated to the
new syntax in this change — the hand-written eliminator forms produce different
stuck terms, and the proofs depend on them; migration is a separate, proof-gated
pass. Also lands: lexer `|`/`=>`, a de Bruijn `lift` in the kernel, and
parse-time per-constructor argument classification.

## ADR-011 — Accumulator-style recursion (motive-moving)
**Decision.** Lift the "other arguments passed unchanged" restriction of ADR-010:
a recursive `match` may now *change* an argument across the call. Arguments after
the decreasing (matched) one are moved into the eliminator's motive — the motive
becomes the def's return type as a function of those arguments (read off the
annotation and lifted into scope), each method re-abstracts them, and the
eliminator's result is applied to their outer binders (apply-after, so no de
Bruijn binder-commuting). The recursive call `f pre.. r acc..` becomes `(hyp r)
acc..`. When there are no such arguments it is exactly ADR-010's elaboration.
**Why.** Equality, ordering, and tail-recursive accumulators (`eqNat`, `leq`,
`sumAcc`) are natural and common; rejecting them was a real gap (a user hit it
immediately). Still elaborates to an eliminator, so totality is preserved. Two
guards: only a **tail-position** match on a def binder may claim the recursion —
this also fixes a *latent* wrong-code bug in ADR-010's shipped path, where a
nested match (under a non-binder scrutinee or wrapped in a constructor) could
silently bind the recursion to the inner eliminator's hypothesis (two new
rejection tests); and induction-hypothesis binder names are globally unique so a
nested match can't shadow an enclosing one. `add`/`mul`/`append` change elaborated
form but the proofs still check (the gate is the arbiter). **Cost:** motive-moving
functions lose the O(1)-stack reduction of a plain fold — `(natElim … m) n` forces
an m-deep closure chain at apply time; the raised-stack re-exec (ADR unlisted)
absorbs it, and it is inherent to the eliminator encoding. Still deferred:
accumulator recursion where the *motive type* would need large elimination.

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
     inductive types; then (3) backends: C first, then OCaml.
   → **Phase 3, milestone 2 done — USER-DECLARED inductive types.** `data`
     declarations in `.ktt` with an AUTO-GENERATED dependent eliminator
     (`D_elim`, iota-reduces). `examples/data.ktt`: a user `N` with `add`, a
     proof by induction over it (`add_n_z`), and a `Tree` with `size`. Core has
     a datatype registry + generated method types (`lib/core.ml`: Data/Con/Elim,
     `declare_data`). Limits: non-parameterized, first-order, `U 0`.
   → **Phase 3, milestone 3 done — PARAMETERIZED inductives.** `data List (A:U)
     { … }`: polymorphic containers. Type former/constructors/eliminator are typed
     heads with full dependent types computed once at declaration (scope-threaded
     builder); eliminator iota-rule fires on complete spine + constructor target.
     `examples/list.ktt`: `length`/`map` over `List Bool` and `List Nat` from one
     definition. Limits: first-order args (param / recursive / closed), no indices,
     `U 0`, constructor names global.
   → **Unification, brick 1 done.** `examples/category.ktt`: the categorical
     structure and UNIVERSAL PROPERTIES that `fill` computes, stated and proved
     in the type theory — composition + identity/associativity laws, and the
     product's universal property (mediating map `⟨f,g⟩` + commutation), each a
     `def : … Id …` proved by `refl`.
   → **Unification, brick 2 done — TYPE ERASURE.** Re-scoped after brick 1 (with
     advisor input): the typed `.ktt` surface already *is* the unified surface
     (the fill language's data/fold/products are a special case of the type
     theory), so the real gap was compilation. `lib/erase.ml` erases the
     dependent core → an untyped IR (`iexpr`; types/proofs → a dummy, eliminators
     → recursion) + a reference runtime; `kan exec` runs it. Validated: `kan
     exec` == `kan check` eval on every example (erased type params print `_`).
     The IR is target-independent. Plan (`docs/unification.md`): brick 3 = `fill`
     as a typed op + merge `.ktt`/`.kan`; brick 4 = native backends from the IR,
     **OCaml first** (native closures ⇒ near-transparent erasure), then C.
   → **Brick 4 (OCaml backend) done.** Jack confirmed OCaml-first. `lib/
     ocaml_backend.ml`: `kan build foo.ktt -o foo` type-checks AND compiles —
     erased IR → OCaml source (universal `ival` runtime + generated datatype
     registry) → `ocamlopt` → native binary. Every example's binary output
     matches `kan check`; build rejects ill-typed programs. `kan build`
     dispatches on extension (`.ktt`→OCaml, `.kan`→legacy C fill-backend).
     **Kan is now a dependently-typed language that compiles to native code.**
     Remaining: a C backend from the same IR; brick 3 (`fill` as a typed op).
3. **First elaborator.** Simplest *search* fills (adapters between fixed interfaces).
4. **Native backend + hardening.** Categorical IR → forced core → C → binary; perf.
5. **Agent-orchestration front end**, built entirely as fills.
