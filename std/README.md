# The Kan standard library

A small, fully-checked library of common definitions. Every file here
type-checks, and the proof-carrying modules ship *theorems*, not just functions.

Import with a path relative to the importing file:

```
import "../std/nat.kan"
import "../std/list.kan"

def xs : List Nat = cons Nat 3 (cons Nat 1 (nil Nat))
eval length Nat xs        -- 2
eval add 2 (length Nat xs)
```

Each file is included at most once, even if reached through several imports.

Import **qualified** with `as` to keep a module's names in their own namespace —
useful when two modules would otherwise clash (both defining `Color`, say):

```
import "../std/nat.kan" as Nat

eval Nat::add 2 3          -- 5   (datatypes, constructors, and defs all namespaced)
```

A plain `import` is unqualified (equivalent to "open"). See `examples/namespaces.kan`.

## Modules

| Module | Contents |
|---|---|
| `prelude.kan` | `id`, `const`, `comp`, `flip` |
| `logic.kan` | equality is an equivalence: `sym`, `trans`, and congruence `ap` (proofs) |
| `bool.kan` | `not`, `and`, `or`, `xor` |
| `nat.kan` | `add`, `mul`, `sub`, `eqNat`, `leq`; and a growing theory proved by induction — `add_assoc`/`add_comm`, `mul_assoc`/`mul_comm`, right-distributivity over `+` and monus (`mul_add_distrib_r`, `mul_sub_distrib_r`), `suc_inj`, and the `sub` lemmas |
| `order.kan` | `≤`, `<`, and divisibility `∣` as Σ-**witnesses** (a proof of `Le m n` *is* the difference; of `Dvd d n` *is* the quotient); `le_trans`, the decision procedure `leDec`, and the divisibility algebra `dvd_add`/`dvd_mul_l`/`dvd_lin`/`dvd_sub` |
| `int.kan` | the **inductive** integers `Int` (`pos`/`negsuc`, unique representation) with `addI`/`subI`/`mulI`/`negI`, proven ring facts (`negI_negI`, `addI_comm`, `mulI_comm`, …), and a bridge to the fast primitive `Integer` |
| `divmod.kan` | **verified Euclidean division** `divmodI : (a b) → 0<b → Σq Σr. (q·b+r = a) × (r<b)` — division carrying its own correctness proof (fuel-Euclid, termination proved) — plus the Euclid step `dvd_mod_fwd`/`dvd_mod_bwd` |
| `gcd.kan` | **verified gcd** by Euclid (`gcdI`, computes), proven `gcd_dvd` (divides both) and `gcd_greatest` (maximal — every common divisor divides it), and `reduce_coprime`: dividing `a`,`b` by their gcd yields a **coprime** pair (a fraction reduced to lowest terms, proven) |
| `rational_reduced.kan` | the **type-ENFORCED** rational: `Reduced = (num:Int) * (den:Nat) * (Lt 0 den) * (Coprime (natAbs num) den)` — invariants as **proof fields**, so divide-by-zero is a type error and every value is provably in lowest terms. Smart constructor `reduce` discharges all four obligations; full exact arithmetic `addR`/`mulR`/`subR`/`negR` (total) and `recipR`/`divR` (`Option` — `none` exactly on the zero rational, so ÷0 is impossible), each result re-reduced to lowest terms. (Heavy to type-check — re-pays the gcd proofs; see ADR-016.) |
| `creal.kan` | **constructive reals** (complete) `CReal = Nat -> Rational` (`x n` within `1/2^n` of the value): a real is a *process* producing rational approximations. `addC`/`subC`/`negC`/`mulC`/`absC` with precision propagation, `recipC`/`divC` gated by an apartness-from-zero witness (`Apart0`), and the constants `sqrt2`, `piC` (Machin), `eC`, and a small robust math library `sqrtQ`/`expQ` (rational→real, argument-reduced so they're correct for all inputs) and `powNatC` (binary-exponentiation powers); read digits with `scaledFloor x d = ⌊x·10^d⌋`. Computes fast (on the primitive-`Integer` rational). No `eqC` (real equality is undecidable). See ADR-017. |
| `creal_proof.kan` | proof-**carrying** reals (research track): `CRealP = (Nat -> Frac) * regularity-proof`, with `fromQP` (every rational is one) and the triangle-inequality crux — built on `Frac` to route around the ADR-016 cost. See ADR-020. |
| `list.kan` | polymorphic `List A`: `length`, `map`, `append` |
| `option.kan` | `Option A`: `none`, `some`, `map_option` |
| `either.kan` | `Either A B`: `left`, `right`, `either` |
| `void.kan` | the empty type `Void` and `absurd` |
| `unit.kan` | the one-element type `Unit` |
| `string.kan` | `string_append`, `string_eq` (over the built-in `String`) |
| `integer.kan` | the unbounded `Integer`: `plus`/`minus`/`times`, `factorial`, `sumTo` (compute large values exactly) |
| `rational.kan` | `Rational` as normalized coprime `Integer` pairs, with **safe** division: `recipQ`/`divQ` return `Option` — there is no way to divide by zero (in progress; being put on the verified `divmod`/gcd tower) |
| `category.kan` | category theory: `SmallCategory` (laws and all — objects in `U`, so it houses the *small* categories: finite, posets, a monoid as one object, etc.), `Functor`, `NatTrans`; the terminal category `One`, the opposite category `op`, `idFunctor`, `idNat`, `compFunctor` — all lawful and checked. (*Large* categories like Grp/Set need a universe-polymorphic, setoid-based variant — see `docs/open-questions.md`.) |
| `kan.kan` | Kan extensions — `LeftKanExt`/`RightKanExt` stated as universal properties, with `lanAlongId` inhabiting the left extension along the identity |

See `examples/using_std.kan` for a program that imports and uses several of these.

## Not yet

Vectors (`Vec`) and `Fin` await **indexed inductive families** (in progress).
The library will grow with them.
