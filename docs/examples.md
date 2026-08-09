# Kan by Example — the gallery

A large, browsable collection of Kan programs, from one-liners to category
theory. **Everything here type-checks.** Each snippet is drawn from a runnable
file under [`examples/`](../examples/) or [`std/`](../std/), and the whole set is
checked on every commit by `bash tests/run_all.sh` (which also verifies that the
runnable programs produce identical output from all three runtimes — `kan run`,
the OCaml backend, and the C backend).

Lambdas are written `lambda x: …` below; `\x. …` and `λx: …` are the same thing.

### Contents

**Part I — Everyday programming**
[Values](#values) · [Functions](#functions) · [Booleans](#booleans) ·
[Naturals](#naturals) · [Comparison](#comparison) · [Integers](#integers) ·
[Strings](#strings) · [Pairs](#pairs) · [Options](#options) · [Either](#either) ·
[Lists](#lists) · [Trees](#trees) · [Records](#records) · [Dictionaries](#dictionaries) ·
[Recursion](#recursion)

**Part II — Types, proofs, dependency**
[Polymorphism](#polymorphism) · [Dependent types](#dependent-types) ·
[Dependent pairs](#dependent-pairs) · [Equality](#equality) · [Induction](#induction) ·
[Invariants](#invariants)

**Part III — Category theory**
[Categories](#categories) · [Concrete categories](#concrete-categories) ·
[Functors](#functors) · [Natural transformations](#natural-transformations) ·
[Adjunctions](#adjunctions) · [Monads](#monads) · [Kan extensions](#kan-extensions) ·
[Presheaves, sites, sheaves](#presheaves-sites-and-sheaves)

---

# Part I — Everyday programming

<a name="values"></a>
## Values and `eval`

```kan
eval "hello, Kan"      -- "hello, Kan"
eval 42                -- 42
eval true              -- true
```

<a name="functions"></a>
## Functions and higher-order functions

```kan
def id      : (A : U) -> A -> A                          = lambda A x: x
def const   : (A : U) -> (B : U) -> A -> B -> A          = lambda A B x y: x
def compose : (A : U) -> (B : U) -> (C : U) -> (B -> C) -> (A -> B) -> A -> C
            = lambda A B C g f x: g (f x)
def flip    : (A : U) -> (B : U) -> (C : U) -> (A -> B -> C) -> B -> A -> C
            = lambda A B C f b a: f a b
def twice   : (A : U) -> (A -> A) -> A -> A              = lambda A f x: f (f x)

eval twice Nat (add 3) 10     -- 16   (add 3 applied twice to 10)
```

<a name="booleans"></a>
## Booleans

```kan
def not : Bool -> Bool          = lambda b:   match b { | true => false | false => true }
def and : Bool -> Bool -> Bool  = lambda a b: match a { | true => b     | false => false }
def or  : Bool -> Bool -> Bool  = lambda a b: match a { | true => true  | false => b }
def xor : Bool -> Bool -> Bool  = lambda a b: match a { | true => not b | false => b }

eval and true (or false true)   -- true
```

<a name="naturals"></a>
## Natural numbers

```kan
def add    : Nat -> Nat -> Nat = lambda m n: match m { | zero => n    | suc k => suc (add k n) }
def mul    : Nat -> Nat -> Nat = lambda m n: match m { | zero => zero | suc k => add n (mul k n) }
def pred   : Nat -> Nat  = lambda n: match n { | zero => zero | suc k => k }
def even   : Nat -> Bool = lambda n: match n { | zero => true | suc k => not (even k) }
def sub    : Nat -> Nat -> Nat = lambda m n: match n { | zero => m | suc k => pred (sub m k) }
def pow    : Nat -> Nat -> Nat = lambda b e: match e { | zero => suc zero | suc k => mul b (pow b k) }

eval add 20 22     -- 42
eval pow 2 10      -- 1024
eval even 10       -- true
```

<a name="comparison"></a>
## Comparison and equality

Recursion that shrinks *both* arguments (accumulator-style):

```kan
def eqNat : Nat -> Nat -> Bool
  = lambda m n: match m { | zero  => match n { | zero => true  | suc k => false }
                        | suc j => match n { | zero => false | suc k => eqNat j k } }
def leq : Nat -> Nat -> Bool
  = lambda m n: match m { | zero => true | suc j => match n { | zero => false | suc k => leq j k } }

eval eqNat 5 5     -- true
eval leq 3 5       -- true
```

<a name="integers"></a>
## Unbounded integers

`Integer` is arbitrary precision (like Python's `int`); literals wear a `z`.

```kan
def factorial : Nat -> Integer
  = lambda n: match n { | zero => 1z | suc k => imul (fromNat (suc k)) (factorial k) }

eval factorial 50   -- 30414093201713378043612608166064768844377641568960512000000000000
eval imul 999999999z 999999999z   -- 999999998000000001
```

<a name="strings"></a>
## Strings

```kan
def greet : String -> String = lambda who: strcat "hello, " who
eval greet "world"          -- "hello, world"
eval streq "kan" "kan"      -- true
```

<a name="pairs"></a>
## Pairs and products

```kan
def swap : (A : U) -> (B : U) -> (A * B) -> (B * A) = lambda A B p: (snd p, fst p)
def p : Nat * Bool = (5, true)
eval fst p                  -- 5
eval swap Nat Bool p        -- (true, 5)
```

<a name="options"></a>
## Options (`Maybe`)

```kan
data Option (A : U) { none : Option A, some : A -> Option A }
def getOrElse : (A : U) -> A -> Option A -> A
  = lambda A d o: match (o : Option A) { | none => d | some x => x }
eval getOrElse Nat 0 (some Nat 7)   -- 7
eval getOrElse Nat 0 (none Nat)     -- 0
```

<a name="either"></a>
## Either (tagged sums)

```kan
data Either (A : U) (B : U) { left : A -> Either A B, right : B -> Either A B }
def either : (A : U) -> (B : U) -> (C : U) -> (A -> C) -> (B -> C) -> Either A B -> C
  = lambda A B C f g e: match (e : Either A B) { | left a => f a | right b => g b }
```

<a name="lists"></a>
## Lists — a mini-library

```kan
data List (A : U) { nil : List A, cons : A -> List A -> List A }

def length : (A : U) -> List A -> Nat
  = lambda A xs: match (xs : List A) { | nil => zero | cons y ys => suc (length A ys) }
def map : (A : U) -> (B : U) -> (A -> B) -> List A -> List B
  = lambda A B f xs: match (xs : List A) { | nil => nil B | cons y ys => cons B (f y) (map A B f ys) }
def append : (A : U) -> List A -> List A -> List A
  = lambda A xs ys: match (xs : List A) { | nil => ys | cons z zs => cons A z (append A zs ys) }
def foldr : (A : U) -> (B : U) -> (A -> B -> B) -> B -> List A -> B
  = lambda A B f z xs: match (xs : List A) { | nil => z | cons y ys => f y (foldr A B f z ys) }
def filter : (A : U) -> (A -> Bool) -> List A -> List A
  = lambda A p xs: match (xs : List A) { | nil => nil A | cons y ys => if (p y) (cons A y (filter A p ys)) (filter A p ys) }
def reverse : (A : U) -> List A -> List A
  = lambda A xs: match (xs : List A) { | nil => nil A | cons y ys => append A (reverse A ys) (cons A y (nil A)) }
def take : (A : U) -> Nat -> List A -> List A          -- decrease on n; the list rides along
  = lambda A n xs: match n { | zero => nil A | suc k => match (xs : List A) { | nil => nil A | cons y ys => cons A y (take A k ys) } }

def nums : List Nat = cons Nat 1 (cons Nat 2 (cons Nat 3 (cons Nat 4 (nil Nat))))
eval length Nat nums              -- 4
eval reverse Nat nums             -- (4 3 2 1)
eval filter Nat even nums         -- (2 4)
eval take Nat 2 nums              -- (1 2)
```

See [`examples/cookbook.kan`](../examples/cookbook.kan) for more (`all`, `any`,
`elem`, `sumL`, …).

<a name="trees"></a>
## Binary trees

```kan
data Tree (A : U) { leaf : Tree A, node : Tree A -> A -> Tree A -> Tree A }
def size : (A : U) -> Tree A -> Nat
  = lambda A t: match (t : Tree A) { | leaf => zero | node l x r => add (add (size A l) (suc zero)) (size A r) }
def mirror : (A : U) -> Tree A -> Tree A
  = lambda A t: match (t : Tree A) { | leaf => leaf A | node l x r => node A (mirror A r) x (mirror A l) }

-- `node` has two recursive positions, so the match gets two induction hypotheses.
```

<a name="records"></a>
## Enums and records ("objects")

Kan has no methods on objects — a "method" is just a function that takes the
value and pattern-matches on it.

```kan
data Color { red : Color, green : Color, blue : Color }
def isGreen : Color -> Bool = lambda c: match c { | red => false | green => true | blue => false }

data Car { car : String -> String -> Car }        -- make, model
def make  : Car -> String = lambda c: match c { | car mk md => mk }
def model : Car -> String = lambda c: match c { | car mk md => md }
def myCar : Car = car "Toyota" "Corolla"
eval myCar           -- (car "Toyota" "Corolla")   <- the default print format
eval make myCar      -- "Toyota"
```

<a name="dictionaries"></a>
## Dictionaries

Kan is pure and total (and `String` is opaque, so keys can't be hashed) — the
idiomatic map is a persistent association list.

```kan
data Dict (V : U) { empty : Dict V, entry : String -> V -> Dict V -> Dict V }
def insert : (V : U) -> String -> V -> Dict V -> Dict V = lambda V k v d: entry V k v d
def lookup : (V : U) -> String -> Dict V -> Option V
  = lambda V k d: match (d : Dict V) { | empty => none V
                                     | entry k2 v rest => if (streq k k2) (some V v) (lookup V k rest) }
```

<a name="recursion"></a>
## Recursion patterns

Recursion is **structural** — a recursive call is on a sub-part of the matched
value, so a function that compiles is total. Three shapes:

```kan
-- (1) plain structural
def sumL : List Nat -> Nat = lambda xs: match (xs : List Nat) { | nil => zero | cons y ys => add y (sumL ys) }

-- (2) accumulator (an argument CHANGES across the call)
def sumAcc : Nat -> Nat -> Nat = lambda n acc: match n { | zero => acc | suc k => sumAcc k (suc acc) }

-- (3) course-of-values (needs `fib (n-2)`) — carry a pair to keep it structural
def fibPair : Nat -> Nat * Nat
  = lambda n: match n { | zero => (zero, suc zero) | suc k => (snd (fibPair k), add (fst (fibPair k)) (snd (fibPair k))) }
def fib : Nat -> Nat = lambda n: fst (fibPair n)
eval fib 10          -- 55
```

---

# Part II — Types, proofs, and dependency

<a name="polymorphism"></a>
## Polymorphism — `(A : U)` means "for any type"

`U` is the universe of types (`Nat : U`, `Bool : U`). Type arguments are explicit.

```kan
def id : (A : U) -> A -> A = lambda A x: x
eval id Nat 7        -- 7
eval id Bool true    -- true
```

<a name="dependent-types"></a>
## Dependent types — a type that depends on a value

```kan
-- `if b Nat String` is a TYPE that is Nat when b is true, String when false.
def Tagged : U = (b : Bool) * (if b Nat String)
def num : Tagged = (true, 99)              -- payload must be a Nat
def str : Tagged = (false, "ninety-nine")  -- payload must be a String
eval snd num         -- 99
eval snd str         -- "ninety-nine"
```

<a name="dependent-pairs"></a>
## Dependent pairs (Σ)

`(x : A) * B` is a dependent pair: the type of the second component may mention
the value of the first (as in `Tagged` above). Non-dependent, it is just `A * B`.

<a name="equality"></a>
## Equality is a type

`Id A x y` is the type of proofs that `x` equals `y`; `refl` proves anything that
holds by computation.

```kan
def two_squared : Id Nat (mul 2 2) 4 = refl              -- mul 2 2 computes to 4
def strings_eq  : Id String (strcat "ab" "c") "abc" = refl
```

<a name="induction"></a>
## Proof by induction — with the same `match` you compute with

```kan
def ap : (A : U) -> (B : U) -> (f : A -> B) -> (a : A) -> (b : A) -> Id A a b -> Id B (f a) (f b)
       = lambda A B f a b p: transp A (lambda z: Id B (f a) (f z)) a b p refl

-- for ALL n, add n 0 = n. Not true by computation — true by induction. The
-- recursive call is the induction hypothesis; that this def checks IS the proof.
def add_n_zero : (n : Nat) -> Id Nat (add n zero) n
  = lambda n: match n { | zero  => refl
                      | suc k => ap Nat Nat (lambda x: suc x) (add k zero) k (add_n_zero k) }
```

`add_assoc` (associativity of `+`) is the same idea with two extra arguments
riding along — see [`std/nat.kan`](../std/nat.kan).

<a name="invariants"></a>
## Invariants by construction

A type indexed by a value can enforce a property that can't be violated:

```kan
-- `User n` = a user at least n years old. It stores the years OVER the minimum,
-- so the actual age is (n + over) >= n — you cannot build one that is too young.
def User    : Nat -> U = lambda n: String * Nat
def userAge : (n : Nat) -> User n -> Nat = lambda n u: add n (snd u)
def alice   : User 18 = ("alice", 7)     -- at least 18; actually 25
eval userAge 18 alice        -- 25
```

---

# Part III — Category theory

All of the following are in [`std/category.kan`](../std/category.kan),
[`std/kan.kan`](../std/kan.kan), and [`examples/category_zoo.kan`](../examples/category_zoo.kan),
and every one type-checks.

<a name="categories"></a>
## Categories — with the laws as fields

A `SmallCategory` is a dependent record whose fields include the identity and
associativity **laws** (as `Id`-proofs). So a *value* of type `SmallCategory` is a
structure the type-checker has verified really is a category.

```kan
def SmallCategory
  = (Obj : U) * (Hom : Obj -> Obj -> U)
  * (idn : (a : Obj) -> Hom a a)
  * (cmp : (a : Obj) -> (b : Obj) -> (c : Obj) -> Hom b c -> Hom a b -> Hom a c)
  * (idl : (a : Obj) -> (b : Obj) -> (f : Hom a b) -> Id (Hom a b) (cmp a a b f (idn a)) f)
  * (idr : ...) * (assoc : ...)
```

Accessors hide the projections: you write `obj C`, `hom C a b`, `idn C a`,
`cmp C a b c g f`.

<a name="concrete-categories"></a>
## Concrete categories

```kan
def One : SmallCategory           -- the terminal category (one object, one arrow)
def op  : SmallCategory -> SmallCategory   -- the opposite category (arrows reversed)
def prod : SmallCategory -> SmallCategory -> SmallCategory   -- the product category C × D (lawful)
```

The natural numbers form a one-object category where composition is `+`
(the monoid ℕ,+,0) — [`examples/monoid_category.kan`](../examples/monoid_category.kan):

```kan
def NatPlus : SmallCategory = ( Unit , ( lambda a b: Nat , ( lambda a: zero
     , ( lambda a b c g f: add g f , ...the monoid laws as proofs... ) ) ) )
eval cmp NatPlus unit unit unit 3 4      -- 7   (composition is addition)
```

<a name="functors"></a>
## Functors

A `Functor C D` carries an action on objects and on arrows, *plus* proofs that it
preserves identities and composition.

```kan
def idFunctor   : (C : SmallCategory) -> Functor C C                                   -- identity
def compFunctor : (C : SmallCategory) -> (D : SmallCategory) -> (E : SmallCategory)
                  -> Functor C D -> Functor D E -> Functor C E                    -- G ∘ F
```

<a name="natural-transformations"></a>
## Natural transformations

```kan
def NatTrans : (C : SmallCategory) -> (D : SmallCategory) -> Functor C D -> Functor C D -> U
def idNat    : (C : SmallCategory) -> (D : SmallCategory) -> (F : Functor C D) -> NatTrans C D F F
```

`idNat`'s naturality square is exactly the target category's identity laws.

<a name="adjunctions"></a>
## Adjunctions

`F ⊣ G` — a unit `η : Id ⇒ G∘F` and a counit `ε : F∘G ⇒ Id`:

```kan
def Adjunction : (C : SmallCategory) -> (D : SmallCategory) -> Functor C D -> Functor D C -> U
  = lambda C D F G:
      (unit : NatTrans C C (idFunctor C) (compFunctor C D C F G))
    * (NatTrans D D (compFunctor D C D G F) (idFunctor D))

def idAdjunction : (C : SmallCategory) -> Adjunction C C (idFunctor C) (idFunctor C)
  = lambda C: ( idNat C C (idFunctor C) , idNat C C (idFunctor C) )
```

<a name="monads"></a>
## Monads and comonads

```kan
def Monad : (C : SmallCategory) -> Functor C C -> U
  = lambda C T:
      (unit : NatTrans C C (idFunctor C) T)            -- η : Id ⇒ T
    * (NatTrans C C (compFunctor C C C T T) T)         -- μ : T∘T ⇒ T

-- the identity functor is a monad (η = μ = the identity natural transformation)
def idMonad : (C : SmallCategory) -> Monad C (idFunctor C)
  = lambda C: ( idNat C C (idFunctor C) , idNat C C (idFunctor C) )
```

<a name="kan-extensions"></a>
## Kan extensions — the namesake

The construction Kan is named for, stated as a universal property. The left Kan
extension of `F` along the identity is `F` itself — constructed, so the statement
is provably non-empty:

```kan
def LeftKanExt : (A : SmallCategory) -> (B : SmallCategory) -> (D : SmallCategory)
                 -> Functor A B -> Functor A D -> U
  = lambda A B D p F:
      (L : Functor B D)                                    -- the extension
    * (unit : NatTrans A D F (compFunctor A B D p L))      -- F ⇒ L∘p
    * ((G : Functor B D) -> NatTrans A D F (compFunctor A B D p G) -> NatTrans B D L G)

def lanAlongId : (A : SmallCategory) -> (D : SmallCategory) -> (F : Functor A D)
                 -> LeftKanExt A A D (idFunctor A) F
  = lambda A D F: ( F , ( idNat A D F , lambda G gamma: gamma ) )
```

`RightKanExt` is the dual.

<a name="presheaves-sites-and-sheaves"></a>
## Presheaves, sites, and sheaves — vocabulary, not yet theorems

These give honest Kan **types** for the concepts, but not their substantive
conditions. Kan does not yet have a category of sets, (co)limits, or a subobject
classifier — so a presheaf's functoriality, a site's coverage axioms, and above
all a **sheaf's unique-gluing condition cannot yet be written out**. Read this as
"the language can already *name* these structures", not "sheaf theory is
formalized". Each definition says exactly what it does and doesn't impose.

```kan
-- a presheaf: a type at each object, with contravariant restriction maps
-- (the data; functoriality of the restriction is the remaining condition)
def Presheaf : SmallCategory -> U1
  = lambda C: (P0 : obj C -> U) * ((a : obj C) -> (b : obj C) -> hom C a b -> P0 b -> P0 a)

-- a sieve on a: a family selecting morphisms into a
def Sieve : (C : SmallCategory) -> obj C -> U1
  = lambda C a: (b : obj C) -> hom C b a -> U

-- a Grothendieck site: a category with a coverage (which sieves are covering)
-- (the coverage axioms are the conditions on `covers`)
def Site = (C : SmallCategory) * ((a : obj C) -> Sieve C a -> U)

-- NOT YET A SHEAF: this is *exactly* a presheaf on the site's category. The
-- defining sheaf condition (unique gluing over every covering sieve — a limit
-- over each cover) is NOT imposed here; it awaits (co)limits in Kan.
def Sheaf : Site -> U1 = lambda S: Presheaf (fst S)
```

---

**Want to run any of these?** Each lives in a real file:
[`examples/`](../examples/) and [`std/`](../std/). Start with the
[tutorial](../examples/tutorial.kan), or `bash tests/run_all.sh` to check them all.
