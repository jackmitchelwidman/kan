# Design proposal: the `?`-elaborator (`fill`, Stage 2)

*Status: **Stage 2a shipped (v0.10.0)** — structural contractible fill + goal
reporting; see `examples/holes.kan`. Stages 2b (dispatch to `Universal` instances,
needs implicit arguments) and 2c (richer synthesis) remain. This is the operational
north star — "the compiler fills the horn" — made literal.*

## The one idea

A hole `?` is a **horn**: a gap in a program whose type is known but whose term is
not. The elaborator **fills it with the unique universal completion — when one
exists — and reports it as a goal otherwise.** The precise criterion for "a unique
completion exists" is exactly the category-theoretic one:

> **`?` at type `T` is fillable iff `T` is contractible** — it has exactly one
> inhabitant (up to the relevant equality). Terminal objects, mediating maps of
> universal properties, and identity proofs `Id A a a` are contractible; `Nat`,
> `Bool`, and coproducts are not.

So the rule *is* the philosophy: the compiler completes a partial diagram precisely
when the completion is universal (unique), and refuses to guess when it isn't.
Contractibility is undecidable in general, so the elaborator uses a **sound,
incomplete structural recognizer**: it fills only what it can *certify* contractible,
and reports everything else. Never a guess among alternatives.

## Surface & core

- New token `?` (anonymous hole) and optionally `?name` (named, for reporting).
- New core term `Hole`. Holes are **check-mode only**: a hole must appear where the
  expected type is known (a `def` with an annotation, an argument whose domain is
  known, a field of a typed record …). In infer mode (no goal) a bare `?` is an
  error — "this hole has no expected type."
- Holes never reach a backend: a def either elaborates (all its holes filled) or it
  fails to check (an unfilled hole is a reported goal = a check error, like an
  unmet proof obligation).

## The fill algorithm

`fill ctx T` (T already reduced to weak-head normal form):

| goal `T` | filler | why |
|---|---|---|
| `Unit` | `unit` | terminal — unique |
| `Σ (x:A). B` | `(fill A, fill B[x:=that])` | product of contractibles is contractible |
| `Π (x:A). B`, `A` ≠ `Void` | `λx. fill B` | contractible codomain ⇒ contractible (pointwise) |
| `Π (v:Void). C` | `λv. absurd C v` | unique map out of the initial object |
| `Id A a b`, `a ≡ b` | `refl` | identity proof — canonical |
| a registered `Universal`'s filler type | that instance's `fill` | the mediating map (Stage 2b) |
| anything else | **refuse** → report `⊢ ? : T` with the local context | no certified unique completion |

`check ctx Hole T = fill ctx T`. The filled term replaces the hole.

Note the fillers compose: `? : (A : U) -> A -> Unit` becomes `λA a. unit`; `? :
Unit * (Id Nat 3 3)` becomes `(unit, refl)`. The recognizer is small, structural,
and total (it either produces a term or reports a goal).

## The one real architectural cost

Kan currently **evaluates the parsed term** — `check`/`infer` verify but don't
rewrite. Filling a hole means the *elaborated* term (holes replaced) must be what
gets evaluated. So Stage 2 introduces a genuine **elaboration pass**: `check` (at
least for `def` bodies) returns the hole-filled term, which `run_decls`/the backends
then use. This is standard bidirectional elaboration, localized to def bodies, but
it is the substantive change — everything else is a recognizer.

## Staging

- **2a — structural fill + goal reporting (ships first, no new theory).** The table
  above minus the `Universal` row: `Unit`, `Σ`/`Π` of fillables, `Id`-refl,
  `Void`-domain, and — valuable on its own — **reporting** an unsolvable hole as a
  goal with its context (a proof-assistant "?goal" experience). This alone makes
  `?` a real interactive-development tool and delivers "the compiler fills the horn"
  for the contractible cases.
- **2b — dispatch to `Universal` instances.** `? : Cand h` resolves a registered
  `Universal` and returns its mediating map. This needs **instance resolution**
  (find the instance from the goal type) — i.e. it depends on implicit arguments /
  type classes. So this stage is **gated on the implicit-arguments feature**; I'd
  sequence that first.
- **2c — richer synthesis (later, speculative).** η for records, decidable-equality
  fills, small proof search. Each must preserve the "fill only when certifiably
  unique" discipline or it stops being universal completion and becomes guessing.

## Honest caveats

- **Sound but incomplete.** The recognizer refuses some genuinely-contractible
  types. That is the correct failure direction: it never fills a non-unique goal.
- **Uniqueness up to which equality?** Function fillers are unique *pointwise*
  (no funext), identity fillers up to proof handling, etc. — the same setoid caveat
  as everywhere else. The elaborator produces *a* canonical filler; the claim is
  "unique up to the relevant equality," and we can prove that per-recognizer.
- **Not a solver.** `? : Nat` has many inhabitants; the elaborator must *report*,
  never pick `zero`. The value of `?` for non-contractible goals is the *goal
  display*, not a filled term.
- **`eval` holes.** Since `eval` terms aren't type-checked, `?` there has no goal —
  an error. Holes live only in typed positions.

## Decisions I need from you

1. **Scope of "fillable" for 2a** — is *contractible-only* (fill iff unique) the
   right discipline, or do you want a broader "best-effort synthesis" mode? I
   strongly favor contractible-only: it keeps `?` = *universal* completion, honest.
2. **Sequencing 2b vs implicit arguments** — 2b needs instance resolution. Do
   implicit arguments first (they're independently valuable and unblock 2b), or
   keep 2b as an explicit `? using FoldUniversal` (no resolution) in the meantime?
3. **Goal reporting UX** — a printed `⊢ ? : T` with context on check failure (like a
   proof assistant), yes? This is cheap and makes `?` useful immediately.
4. **Is the elaboration-pass cost acceptable now?** It's the one real kernel-ward
   change (check returns an elaborated term). Everything else rides on it.
