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
=> body | .. }` becomes the eliminator with motive `lambda _: R` (R = the def's result
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

## ADR-012 — Dependent-motive `match` (proofs by induction with match)
**Decision.** The motive of a decreasing `match` is the def's return type as a
*function of the scrutinee* — the annotation's Pi over the decreasing binder,
turned into a `Lam` and lifted into scope — rather than `lambda _: R`. So the result
type may mention the scrutinee, which is what proof-by-induction requires; the
recursive call supplies the induction hypothesis. **Why.** It lets `match` prove
theorems, retiring hand-written `natElim`/`Foo_elim` for the common (top-level
def) case: `std/nat.kan`'s `add_n_zero` and `add_assoc` are now `match` proofs
(the latter combining dependent motive + moved args + recursion). When the result
type does *not* mention the scrutinee, the new motive is alpha-equivalent to the
old `lambda _: R`, so every computational function is unchanged and the whole gate stays
green. **Limit:** the motive is read from the *def's* annotation, so a `match`
nested inside a data structure (e.g. the terminal category's law fields) has no
annotation to draw it from and still uses the eliminator; a `match e return
(motive) { .. }` form (explicit dependent motive anywhere) is the natural next
step. Transport-based proofs (`sym`/`trans`/`ap` in `std/logic.kan`) are not
inductions and stay as they are.

---

## ADR-013 — A verified integer tower for exact `Rational` (inductive `Int`)
**Decision.** A *type-enforced* `Rational` — one whose "denominator ≠ 0" and
coprimality invariants are **proof fields**, not merely maintained by a smart
constructor (the T1 `std/rational.kan`, ADR-unlisted, shipped alongside `idiv`/
`igcd`) — requires an *equational theory for integers*. The primitive `Integer`
(ADR-006) is an opaque bignum with **no induction principle**, so nothing about
`iadd`/`imul`/`idiv`/`igcd` is provable. Therefore: give integers an inductive
definition, `std/int.kan`'s `data Int { pos : Nat -> Int, negsuc : Nat -> Int }`
(unique representations ⇒ structural `Id`), with arithmetic by structural
recursion and its laws proved by induction — reducing facts about `Int` to facts
about `Nat`, which *are* provable. The primitive `Integer` and the T1
`std/rational.kan` stay **untouched** as the computational layer; the verified
tower grows underneath and will eventually *supply* the proofs a T2 `Rational`
needs. **No postulated axioms** at any point — for exactness, an axiom is the
most temporary thing there is dressed as permanent.

**Why nothing smaller is real.** Every escape route from "prove things about
integers" closes: (a) enforcing only `den ≠ 0` (via a `Not (Id Integer d 0z)`
witness, constructible for literals) dies at `mulQ`/`addQ`, whose output
denominator is `imul d1 d2` — "product of nonzeros is nonzero" is a lemma about
the primitive; (b) a **quotient** `Rational` doesn't dodge it — the
respect-the-relation proofs are semiring algebra over `iadd`/`imul`, the same
wall (quotient types *presuppose* this foundation, so they become a later ADR
that also depends on it); (c) a structurally-positive denominator (`den = suc k`)
makes zero unrepresentable but has no `toNat` and O(value) cost — a 10¹²
denominator is dead on arrival. Root cause in one line: **no induction over
`Integer` ⇒ no integer lemmas ⇒ no type-level rational invariant.**

**Precedent.** This is exactly the `Nat` architecture Kan already runs: `NUM 5`
is a `Suc` tower (inductive truth), stored as a machine int, `natElim` loops
(accelerated representation). ADR-006 deliberately kept `Integer` separate to
preserve that; ADR-013 adds the inductive *twin* for proofs, not a replacement —
milestone 3 will represent `Int`'s closed values by the existing bignum so the
primitives become fast paths of the *defined* functions.

**Status (this change).** `std/int.kan` lands: `Int`, `negI`/`diff`/`addI`/`subI`
/`mulI`, a `toInteger` bridge, and the first proofs — `natAbs_pos` and
`addI_zero`, the latter reducing an `Int` identity to `std/nat.kan`'s
`add_n_zero` through `ap`. Gate 37/0. **Next unlock:** even `negI` involution
needs a *nested* dependent motive (`match e return (motive)`, the ADR-012 "next
step") — the nested `match` can't currently refine the goal per sub-case — and so
will the gcd/div correctness proofs; that elaborator feature is milestone 1's
critical path. **Milestones:** (1) ring lemmas for `Int` (needs `add_comm` &c. in
`std/nat.kan`); (2) verified fuel-Euclid gcd/div on `Nat` with fuel-sufficiency
proved by induction — the load-bearing formalization; (3) kernel acceleration
(closed `Int` ↔ bignum); (4) the proof-carrying `Rational`. Milestones 2–3 are
multi-session; this ADR locks the direction, not a delivery date.

**Progress (2026-08-08).** Two rational types now ship, bracketing the design:
- `std/rational.kan` — EFFICIENT (primitive `Integer`), with an honest safe API:
  `recipQ`/`divQ` return `Option` (no silent divide-by-zero) and `mkQ` refuses a
  zero denominator. Not yet type-enforced against a hand-written `rational 3 0`.
- `std/rational_typed.kan` — TYPE-ENFORCED: `Frac`'s denominator is stored as
  `suc denPred`, so a zero denominator is *unrepresentable* and divide-by-zero is
  impossible by construction (no proofs needed); `Int` numerators. Practical only
  for modest values until acceleration — correctness first.
So **neither type permits a silent divide-by-zero today**, and one forbids it
structurally. The remaining goal — a single type that is BOTH efficient and
type-enforced — is gated on **milestone 3 (kernel acceleration of closed `Int`
values via the bignum)**, which is deliberately left for supervised work: it
touches the evaluator in all three runtimes and a subtle error there is
language-wide. Tower proofs advanced meanwhile (no axioms): `std/nat.kan`
`add_suc`/`add_comm`/`mul_comm`; `std/int.kan` `negI_negI` (i.e. `-(-i)=i`),
`addI_comm`, `mulI_comm`. And milestone 3 now has an **executable spec** to be
graded against: `examples/accel_spec.kan` pins the arithmetic results the fast
path must reproduce (tri-runtime), and `std/accel_defeq.kan` pins the definitional
reductions the conversion checker must preserve (all by `refl`). The fast path is
correct iff both stay green after the kernel change.

**Kernel acceleration — DONE (2026-08-08).** Milestone 3 landed, guarded by the
spec, in three increments:
- (1) The kernel represents closed `Nat` as a canonical bignum `VNatLit` (a `VSuc`
  only ever wraps a neutral; `VZero` deleted), fully inductive.
- (2a) Fast `nadd`/`nmul` kernel primitives with an O(1) bignum path, obeying the
  SAME recursion equations as inductive add/mul (so they are definitionally
  interchangeable). `nadd 10^12 …` / `nmul 10^6 10^6` now check instantly.
- (2b) `Nat` is bignum-backed in all three runtimes (`erase`, OCaml, C) — the C
  backend's 32-bit-`int` Nat is gone, closing the overflow/divergence trap.
- (2c) `std/nat.kan`'s `add`/`mul` DELEGATE to the primitives. The entire proof
  gate re-checks green — the agreement guarantee that the fast path equals the
  inductive definitions. `mul 100000 100000` (10^10) now computes O(1) and agrees
  across all three runtimes; before, it was infeasible unary.
The trust gap that Lean/Agda accept on faith is here narrowed to a checkable
one: `std/accel_defeq.kan` + `std/accel_ops.kan` + `examples/accel_spec.kan`
(tri-runtime) are re-verified on every commit, and all three runtimes splice the
same `bigint.ml`. **Consequence:** the inductive `Int`/`Rational` tower is now
efficient, so a single efficient AND type-enforced `Rational` (invariants as
proof fields) is no longer blocked on representation — only on the remaining
verified-gcd work (milestone 2). No axioms were added.

---

## ADR-014 — Indexed inductive families (`Vec`, `Fin`, indexed diagrams)
**Decision.** Add indexed inductive families — the marquee dependent-type feature
and, for a category-theory language, a necessity (length-indexed data, `Fin`,
`Hom`-families, diagrams indexed by shape, proof-relevant indexing). Today's
datatype mechanism is **parameter-only**: `arg_ty = AParam | ARec | AClosed`,
former `(params) -> U0`, eliminator motive `P : D params -> U0`, and `ARec`
hardcodes recursive occurrences at the *same* params (`lib/core.ml declare_data`).
Indexed families generalise all of these.

**Staging — eliminator first, `match`-on-indices later (mirrors ADR-010).**
- **Stage 1 (the capability):** the indexed **eliminator**. Motive ranges over
  the index telescope *and* the target (`Vec_elim : (A:U) -> (P:(n:Nat)->Vec A
  n->U0) -> P zero (vnil A) -> ((n:Nat)->(x:A)->(xs:Vec A n)->P n xs->P (suc n)
  (vcons A n x xs)) -> (n:Nat)->(v:Vec A n)->P n v`). This is **sound and
  complete** — `head` (total, nonempty by type), `append : Vec m -> Vec n -> Vec
  (add m n)`, and indexed proofs are all expressible via the eliminator. Clunkier
  than `match`, but the full capability.
- **Stage 2 (ergonomics, separate/ later):** dependent `match` on indices, which
  *refines* the index per branch (matching `vnil` forces the length to `zero`).
  This needs an **index-unification engine** (constructor injectivity,
  no-confusion, occurs-check) that Kan's current `match` — whose motive is read
  from the def annotation and cannot refine indices — does not have. Explicitly
  deferred. Prerequisite skill: the `match e return (motive)` feature (already
  identified as the verified-gcd unblock, ADR-013) is the smaller warm-up for the
  same elaborator muscle — build it first.

**Representation — replace, don't extend, `arg_ty`.** Bolting index expressions
onto `AParam|ARec|AClosed` would break its four load-bearing sites (declare_data,
the parser's arg classification, `velim`'s iota rule, erase/backend recursion
detection) each differently. Instead store a constructor as a **dependent
telescope ending in `Data name <params> <index-exprs>`**, and *derive* recursive-
argument positions by inspecting for `Data name` heads. Parameters stay uniform
(checked at declaration); indices are arbitrary terms in the return type. This
subsumes the current mechanism as the zero-index case.

**Soundness core (where the risk lives).** (1) The **iota rule with indices**:
when `velim` fires on `vcons A n x xs`, the motive is applied at the
*constructor's* index instantiation, recovered from its arguments — and the IH is
`P <recursive occurrence's indices> arg`. Declaration-time well-formedness:
recursive occurrences must be `Data name <params> <index-exprs>` (same `D`;
indices may vary). (2) **Conversion with indexed neutrals** — fortunately the
`VData`/`VCon`/`VElim` spine representation already compares full argument spines
structurally, so index arguments are compared *for free*; to be verified with a
defeq canary, not assumed.

**K / univalence.** Indexed families force a choice about whether Streicher's K
holds (it makes `match`-on-indices simpler but is incompatible with univalence).
For a category-theory language K is fine; the ADR records this as a *deliberate*
choice, revisitable if HoTT/univalent ambitions arise later.

**Erasure.** Indexed eliminators erase like the current ones — motives/indices
drop (`erase.ml` already discards the `NatElim` motive); the runtime recursion is
unchanged.

**Status.** Landed now: the acceptance spec (`docs/indexed-families-spec.kan` —
`Vec`/`Fin`, the eliminator types, `head`/`append` with `append`'s length-adding
type written out, and the iota defeq canaries) and this ADR. Nothing else — the
kernel work (representation -> checking -> iota -> the three runtimes) is
multi-session, and per the acceleration precedent the spec is written *first* so
every design question surfaces cheaply. When stage 1 checks the spec, it moves to
`examples/` and joins the gate.

---

## ADR-015 — Explicit dependent motives: `match e as x return T`
**Decision.** Add an explicit dependent motive to `match`: `match e as x return T
{ … }` binds the scrutinee value `x` and uses `\x. T` as the eliminator's motive.
This lets a **nested or non-leading** match *refine its scrutinee* — the gap that
plain `return T` (which gives the non-dependent `\_. T`) and the annotation-derived
motive (only the leading/decreasing binder, ADR-011/012) both left. `match` stays
sugar over the eliminator, and the kernel checker independently re-validates the
elaborated `Elim`, so a mis-elaboration **fails closed** (rejects valid programs,
never accepts invalid ones) — no soundness risk.

**Why.** This was the flagged next step in ADR-012 and the blocker for two things:
the witness-producing comparison `leDec : (b a) -> Either (Le b a) (Lt a b)`
(verified-gcd stage 3 — needs to case-split both arguments with a result
depending on both), and `match`-on-indexed-families (ADR-014 stage 2). It also
retires the helper-def workarounds (`negI_negI` is now written directly).

**Landed.** Parser change in `lib/tt.ml` (~15 lines); `std/int.kan`'s `negI_negI`
rewritten to the direct nested form; and **`leDec` now checks** in `std/order.kan`
— unblocking gcd stages 3–6. Gate green.

**Limits (deliberate, documented).** (1) Arm bodies under an explicit motive are
checked without a threaded expected type (the per-arm "motive applied to the
constructor" isn't auto-derived yet), so a *further* nested match inside such an
arm needs its own `return` (as `leDec`'s innermost `Either` match does).
Auto-propagating the per-arm expected is a follow-up ergonomic refinement. (2) An
explicit motive on a recursive/decreasing match errors — the def annotation
already supplies that motive; only non-decreasing matches take an explicit one.

---

## ADR-016 — verified Euclidean division (gcd milestone 2, stage 3)

**Decision.** `std/divmod.kan` proves, with no axioms:
`divmodI : (a b : Nat) -> Lt 0 b -> Σq Σr. (Id Nat (add (mul q b) r) a) × (Lt r b)`
— Euclidean division carrying its own correctness. Because Kan is
structural-recursion-only, it is a **fuel-Euclid**: `divmodF` recurses on `fuel`,
and fuel-sufficiency is threaded as the hypothesis `Le a fuel` and discharged at
the wrapper by `le_refl a` (fuel = a). The exposed API for the gcd stages is
`divmod_quot` (q·b + r = a) and `divmod_rem` (r < b).

**Toolkit built for it** (in `std/order.kan`, all via the ADR-015 explicit
motive): `leDec` (the b≤a vs a<b decision with witness), `le_zero_eq`
(a≤0 ⟹ a=0), `suc_ne_zero` (impossibility, via transport of a type-level
Void/Unit family — no large elimination needed), `sub_lt` (0<b≤a ⟹ a−b < a) and
`fuel_dec` (the decrease `Le a (suc f) ⟹ Le (a−b) f`).

**Elaborator note.** The recursion binds *only* `fuel` before the `match`, so
there are zero "moved" args; each arm binds `a b bpos enough` itself. An earlier
version that bound `a b bpos` (or `a b bpos enough`) ahead of the match hit a
de-Bruijn miscount in the moved-args motive lifting (it depends on the scrutinee
`fuel` via `enough : Le a fuel`). Sidestepping it (zero moved args) is the fix;
auto-handling scrutinee-dependent moved args is a possible future elaborator
refinement.

**KNOWN ISSUE (undiagnosed, recorded honestly).** Reducing `divmodI` to a
*numeral* is **exponential** — measured ~b^depth under `kan check` conversion
(14/7 depth-2 41ms; 28/7 depth-4 5.3s; 35/7 depth-5 >30s; but 30/1 depth-30
15ms — flat in depth when b=1). The quotient is only the `fst` spine, so this is
NOT inherent to the algorithm; suspected lost evaluation-sharing when reducing
through the fuel eliminator (recursive result / nested `enough` proof
re-evaluated per level). `kan run` on a `divI` main is worse (hangs >2min where
check takes 40ms). This does **not** block the tower: the proof type-checks and
is total, and stages 4–6 consume `divmod_quot`/`divmod_rem` *symbolically*. The
compute path remains the accelerated `ndiv` primitive (ADR-013). Fixing the
sharing is a separate kernel/evaluator task; **stage-5 gcd tests must keep inputs
tiny** until it is fixed. Gate green at 45/0.

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
     `kan check file.ktt`: named binders elaborated to de Bruijn, `lambda x: t`,
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
