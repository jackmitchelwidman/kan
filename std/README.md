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

## Modules

| Module | Contents |
|---|---|
| `prelude.kan` | `id`, `const`, `comp`, `flip` |
| `logic.kan` | equality is an equivalence: `sym`, `trans`, and congruence `ap` (proofs) |
| `bool.kan` | `not`, `and`, `or`, `xor` |
| `nat.kan` | `add`, `mul`, `eqNat`, `leq`; and the theorems `add_n_zero` and `add_assoc`, proved by induction with `match` |
| `list.kan` | polymorphic `List A`: `length`, `map`, `append` |
| `option.kan` | `Option A`: `none`, `some`, `map_option` |
| `either.kan` | `Either A B`: `left`, `right`, `either` |
| `void.kan` | the empty type `Void` and `absurd` |
| `unit.kan` | the one-element type `Unit` |
| `string.kan` | `string_append`, `string_eq` (over the built-in `String`) |
| `integer.kan` | the unbounded `Integer`: `plus`/`minus`/`times`, `factorial`, `sumTo` (compute large values exactly) |
| `category.kan` | category theory: `Category` (laws and all), `Functor`, `NatTrans`; the terminal category `One`, the opposite category `op`, `idFunctor`, `idNat`, `compFunctor` — all lawful and checked |
| `kan.kan` | Kan extensions — `LeftKanExt`/`RightKanExt` stated as universal properties, with `lanAlongId` inhabiting the left extension along the identity |

See `examples/using_std.kan` for a program that imports and uses several of these.

## Not yet

Vectors (`Vec`) and `Fin` await **indexed inductive families** (in progress).
The library will grow with them.
