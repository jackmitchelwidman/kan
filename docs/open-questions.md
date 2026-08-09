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

`std/category.kan` encodes `SmallCategory`/`Functor` as nested Σ with `fst`/`snd`
projections, hidden behind accessors (`obj C`, `cmp C a b c g f`). It works and is
sound. Named-field **record syntax** would make the library much nicer to read and
write. It's an additive surface feature (no kernel change) — a good next ergonomic
project if you like the direction.

## 4. Large categories (universe polymorphism + setoid homs)

`std/category.kan`'s record is now honestly named `SmallCategory`: its objects live
in `U` (universe 0), so it houses finite categories, posets, a monoid as a
one-object category, `One`, `op`, products — everything whose object-collection is
small. It **cannot** house a *large* category like **Grp**, **Set**, or **Top**,
where the objects are themselves `U`-carrying structures (a group's carrier is
`: U`, so `Group : U1`, which does not fit `Obj : U`). Two independent gaps block it:

1. **Universe stratification.** `Obj : U` fixes the level. Grp needs `Obj : U1`.
2. **Morphism equality.** The laws (`idl`/`idr`/`assoc`) are `Id`-equations between
   morphisms. For Grp a morphism is a function bundled with a preservation proof, so
   proving two equal needs **function extensionality** + **proof irrelevance**.

A `Category` that holds the large examples wants to fix *both* — become
universe-polymorphic and replace `Id` on homs with an **explicit hom-equivalence**
(a setoid), so the laws are stated up to that equivalence rather than raw
identity. Sketch (needs universe polymorphism `{i j}`, which Kan does not have yet,
so this does not type-check today — it is a design target):

```
def Category {i j} : U(max i j + 1)
  = (Obj : U i)                                   -- objects at ANY level (Grp: i = 1)
  * (Hom : Obj -> Obj -> U j)
  * (eqH : (a b : Obj) -> Hom a b -> Hom a b -> U j)  -- hom-equivalence (setoid)
  * (eqH-refl/sym/trans …)                        -- eqH is an equivalence, per hom-set
  * (idn : (a : Obj) -> Hom a a)
  * (cmp : (a b c : Obj) -> Hom b c -> Hom a b -> Hom a c)
  * (cmp-cong : cmp respects eqH in both arguments)  -- composition is well-defined on classes
  * (idl : (a b) (f) -> eqH a b (cmp a a b f (idn a)) f)   -- laws up to eqH, NOT Id
  * (idr : … eqH …) * (assoc : … eqH …)
```

Grp then instantiates with `i = 1`, `Hom A B = GroupHom A B`, and
`eqH A B f g = (x : carrier A) -> Id (carrier B) (map f x) (map g x)` — pointwise
equality of the underlying maps. That definition of `eqH` is exactly what dodges
the funext requirement: instead of *proving* two homs `Id`-equal (which needs
funext), we *declare* the hom-equivalence to be pointwise agreement, and the laws
become provable from the group axioms alone. The `~/gleason/groups.kan` file
already builds the objects/morphisms/id/∘; wrapping them as a `Category` value
awaits this universe-polymorphic, setoid-based record. Both prerequisites
(universe-polymorphic definitions; a `cmp-cong` discipline) are additive to the
type theory — no soundness risk — but universe polymorphism is a real elaborator
feature, so this is a milestone, not a patch.

## 5. Smaller, already-noted

- **Integer division/modulo** (`idiv`/`imod`): bignum long division is the one
  arithmetic op I didn't hand-roll tonight (easy to get subtly wrong); add when
  needed.
- **Deep recursion over user inductive types** can still overflow the stack (the
  structural cousin of the `natElim` bug I fixed). The fix (an explicit control
  stack in `ielim`) is invasive; deferred, and documented in the README's
  guarantee section.
- **Indexed families** (`Vec`, `Fin`): still the biggest missing type-theory
  feature; a dedicated, careful milestone (unsound if rushed).
- **Namespaces / qualified imports.** Kan has one flat global namespace. As of
  v0.6.0 duplicate top-level names are a hard error (no more silent shadowing —
  see `Tt.check_unique`), which removes the footgun. The remaining ergonomic step,
  for when the library grows, is *qualified imports* (`import "std/nat.kan" as Nat`
  → `Nat.add`) so the same short name can live in two modules; then, later,
  export/visibility control so an `import` doesn't pull in a file's transitive
  names. Both are pure name-resolution features — no kernel change. Not needed yet:
  the stdlib currently has zero cross-file name collisions.
