# A tour of Kan

A short, hands-on walk through the language, aimed at someone who knows a little
programming and likes mathematics. Everything below type-checks and runs today.

```
kan run  file.kan      # type-check, then run (prints each `eval`)
kan check file.kan     # type-check and report types (no run)
kan build file.kan -o out   # compile to a native binary (add -c for the C backend)
```

## 1. Functions and types

Kan is dependently typed: the *same* language writes programs and their types.

```kan
def id : (A : U) -> A -> A = lambda A x: x        -- the polymorphic identity
eval id Bool true                            -- true
```

`U` is the universe of types; `(A : U) -> …` is a dependent function type. There
is a whole hierarchy `U : U1 : U2 : …` (no "type in type", so the logic is sound).

## 2. Numbers, two kinds

`Nat` is the *inductive* natural numbers — the type you do induction and proofs
over. `Integer` is the *machine* integer — arbitrary precision, like Python's
`int` — the type you compute large values with.

```kan
import "std/nat.kan"
import "std/integer.kan"

eval add 2 3            -- 5    (Nat)
eval factorial 50       -- 30414093201713378043612608166064768844377641568960512000000000000
```

The idiom for a big computation is a **Nat counter driving an Integer
accumulator** — structural recursion on the counter, native big-int arithmetic on
the value:

```kan
def fac : Nat -> Integer
        = lambda n: natElim (lambda _: Integer) 1z (lambda k ih: imul (fromNat (suc k)) ih) n
```

(Integer literals wear a `z`, for ℤ: `1z`, `120z`. Arithmetic is `iadd`, `isub`,
`imul`, `ieq`, `ilt`, with friendlier `plus`/`times`/… in `std/integer.kan`.)

## 3. Defining functions by pattern matching

Write functions with `match` and structural recursion — no hand-written
eliminators:

```kan
def add : Nat -> Nat -> Nat = lambda m n: match m { | zero => n | suc k => suc (add k n) }

data List (A : U) { nil : List A, cons : A -> List A -> List A }
def length : (A : U) -> List A -> Nat
  = lambda A xs: match (xs : List A) { | nil => zero | cons y ys => suc (length A ys) }
```

`match` elaborates to the datatype's eliminator. Recursion is allowed only when
it is **structural** — the recursive call is on a sub-part of the matched value —
so every function you can write this way is total: **if it compiles, it
terminates.** Try to loop on the whole value and the compiler refuses; other
arguments may change across the call (accumulator-style — `eqNat`, `leq`,
tail-recursive sums). (Parameterized scrutinees name their
type once: `match (xs : List A) { … }`.)

## 4. Proofs are programs

A proposition is a type; a proof is a term of that type; checking the term *is*
verifying the proof. `Id A x y` is the type of proofs that `x` equals `y`. You
prove things by induction with the **same `match`** you compute with — the
recursive call is the induction hypothesis:

```kan
-- for every n, add n 0 = n. Not true by computation — true by INDUCTION.
def add_n_zero : (n : Nat) -> Id Nat (add n zero) n
  = lambda n: match n { | zero  => refl                                          -- base
                | suc k => ap Nat Nat (lambda x: suc x) (add k zero) k (add_n_zero k) }  -- step
```

If it type-checks, the theorem holds. There is no separate proof language, and no
separate recursion principle — it is all `match`, all Kan.

## 5. Category theory, lawfully

`std/category.kan` defines a `Category` as a record whose fields include the
identity and associativity **laws** (as `Id`-proofs). So a value of type
`Category` is a structure the checker has verified really is a category.

```kan
import "std/category.kan"
-- One : the terminal category.  op C : the opposite category.  idFunctor C : identity.
def IdOne : Functor One One = idFunctor One
```

A concrete example: the natural numbers form a one-object category (the monoid
ℕ,+,0), where composition is addition — see
[`examples/monoid_category.kan`](../examples/monoid_category.kan). Its laws are
`add_n_zero`, `refl`, and `add_assoc`.

## 6. The namesake: Kan extensions

The construction Kan is named for is a definition you can check. `std/kan.kan`
states the left and right Kan extension as universal properties, and constructs
the extension along the identity — so the statement is inhabited, not empty.

```kan
def LeftKanExt : (A : Category) -> (B : Category) -> (D : Category)
                 -> Functor A B -> Functor A D -> U
  = lambda A B D p F:
      (L : Functor B D)                                    -- the extension
    * (unit : NatTrans A D F (compFunctor A B D p L))      -- F ⇒ L∘p
    * ((G : Functor B D) -> NatTrans A D F (compFunctor A B D p G) -> NatTrans B D L G)  -- universal
```

## Where to go next

- `examples/` — every file is a runnable `.kan` program.
- `std/` — the standard library (arithmetic, lists, logic, category theory).
- `README.md` — the design document and philosophy.
- `docs/open-questions.md` — what's deliberately still open.
