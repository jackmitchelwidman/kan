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
| `nat.kan` | `add`, `mul`, and `add_n_zero : (n : Nat) -> Id Nat (add n zero) n` (a proof by induction) |
| `list.kan` | polymorphic `List A`: `length`, `map`, `append` |
| `option.kan` | `Option A`: `none`, `some`, `map_option` |

See `examples/using_std.kan` for a program that imports and uses several of these.

## Not yet

Vectors (`Vec`), `Fin`, and a `String` module await language features still in
progress (indexed families, large elimination, a string type). The library will
grow with them.
