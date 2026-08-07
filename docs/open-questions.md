# Open questions — decisions I'd like Jack to make

These are the forks I deliberately did **not** decide autonomously, because each
changes the *feel* of the language and is yours to own. Each has a safe interim
in place, so nothing is blocked — but your call would improve the language.

## 1. Infix arithmetic, and the `*` collision (the big one)

Today arithmetic is prefix: `iadd a b`, `imul a b` (with friendlier `plus`/`times`
in `std/integer.kan`). Mathematicians will want `a + b`, `a * b`.

The obstacle is real and specific: Kan is dependently typed, so **types are
terms** and share one grammar. `A * B` already means the dependent pair (Σ) type.
So `a * b` (multiply) and `A * B` (Σ) cannot coexist as written — the parser can't
tell them apart without types it doesn't have yet.

Options:
- **(a)** Keep `*` for Σ; give multiplication a different symbol. Repurpose the
  product type to `×` or `&` and free `*` for multiply — clean, but changes a core
  symbol every existing file uses.
- **(b)** Keep prefix operators, add only infix `+`/`-` (no `*`). Half a loaf; I'd
  advise against shipping asymmetric arithmetic.
- **(c)** Leave as-is (prefix) for now.

My lean: (a), with `×` for products (it even reads better for category theorists),
but this is a taste-and-compatibility call that's yours. Until then: prefix.

## 2. Type-directed numeric literals (drop the `z` suffix)

`Integer` literals currently carry a `z`: `120z`. Ideally a bare `50` would be
`Nat` or `Integer` depending on the expected type (like most languages'
polymorphic numerals). That needs a small **elaboration pass** (the checker
rewriting a numeral to the right representation once it knows the target type) —
worth doing, but it touches the checker, so I left it for a careful daytime change
rather than a 3am one. The `z` suffix is the safe, unambiguous interim.

## 3. Record syntax for the category library

`std/category.kan` encodes `Category`/`Functor` as nested Σ with `fst`/`snd`
projections, hidden behind accessors (`obj C`, `cmp C a b c g f`). It works and is
sound. Named-field **record syntax** would make the library much nicer to read and
write. It's an additive surface feature (no kernel change) — a good next ergonomic
project if you like the direction.

## 4. Smaller, already-noted

- **Accumulator-style recursion** in `match` functions (e.g. `f k (suc acc)`,
  where an argument *changes* in the recursive call): currently rejected. The fix
  is to move the changing argument into the eliminator's motive (so the induction
  hypothesis becomes a function); a clean extension of the existing elaboration.
- **Integer division/modulo** (`idiv`/`imod`): bignum long division is the one
  arithmetic op I didn't hand-roll tonight (easy to get subtly wrong); add when
  needed.
- **Deep recursion over user inductive types** can still overflow the stack (the
  structural cousin of the `natElim` bug I fixed). The fix (an explicit control
  stack in `ielim`) is invasive; deferred, and documented in the README's
  guarantee section.
- **Indexed families** (`Vec`, `Fin`): still the biggest missing type-theory
  feature; a dedicated, careful milestone (unsound if rushed).
