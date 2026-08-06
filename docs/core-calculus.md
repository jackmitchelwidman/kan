# The Core Calculus of Kan — Phase 1 Specification

Status: **draft, tracking the reference interpreter** (`reference/kan_ref.ml`).
This document specifies exactly what is implemented and runnable today, and marks
what is deferred. It is the operational anchor for README §4 and §12.

---

## 1. What Phase 1 proves

The claim of README §4 is that Kan has one operation — `fill` — and that
composition and every universal construction are special cases of it. Phase 1
discharges that claim *concretely*, by exhibiting a single kernel

```
fill : horn -> modality -> filler
```

in which composition, products, pullbacks, and coproducts are all obtained by
calling `fill`, on real values, with the universal property **computed** (the
mediating morphism is produced), not merely asserted.

Phase 1 works in one **semantic universe**: **FinSet**, finite sets and
functions. FinSet is chosen because it is the smallest setting where both
composition and universal constructions are concrete and total — ideal for
pinning the mechanism before generalizing the universe.

---

## 2. Objects, morphisms, diagrams

A **cell** in Phase 1 appears at two dimensions:

- **0-cells (objects).** A finite set, represented by its cardinality `card`;
  its elements are the integers `0 … card-1`.
- **1-cells (morphisms).** A function `f : A → B`, represented by its table
  `tbl : int array` of length `|A|`, with `tbl.(x) ∈ [0,|B|)`.

A **diagram** `D` is a functor from a finite shape into FinSet, given by its
vertices `D(j)` and its arrows `(j,k,f)` with `f : D(j) → D(k)`.

A **cone** on `D` is an apex `T` with legs `l_j : T → D(j)`; a **cocone** is the
dual. These are the test data a universal fill must satisfy.

> Deferred to later phases: 2-cells as first-class data, general n-cells, shape
> categories presented syntactically, and dimensions above 1 in the surface
> language. Phase 1 keeps the shape implicit in the `diagram` value.

---

## 3. Horns and the modality dial

A **horn** is a partial diagram missing exactly one face. Phase 1 provides three:

| Horn | Missing face | Filled by |
|---|---|---|
| `Inner (f,g)` | the composite edge of two composable arrows (`Λ²₁`) | composition |
| `LimCone d` | the limiting cone of `d` | a limit (right Kan extension) |
| `ColCocone d` | the colimiting cocone of `d` | a colimit (left Kan extension) |

A **modality** states how strong a solution `fill` must return:

- `Exists` — *some* filler must exist (a lifting property). This is the
  substrate-building modality; it yields composition.
- `Universal` — the *best* filler, unique up to isomorphism (a Kan extension).
  This is the work-doing modality; it yields limits and colimits.

`fill` is total on the well-formed combinations and rejects the ill-typed ones
(asking an inner horn for a `Universal` filler, or a limit horn for mere
`Exists`, is an error).

---

## 4. Operational semantics (as implemented)

```
fill (Inner (f,g))   Exists     ⟶  Edge (g∘f)
fill (LimCone d)     Universal  ⟶  Limit { lobj; proj;  mediate  }
fill (ColCocone d)   Universal  ⟶  Colim { cobj; incl;  comediate }
```

**Inner-horn fill (composition).** For composable `f : A→B`, `g : B→C`, the
filler’s new edge is `g∘f : A→C`, `(g∘f).tbl.(x) = g.tbl.(f.tbl.(x))`. There is
no `compose` primitive; composition is *this* fill.

**Limit fill.** The limit of `D` is the set of compatible tuples

```
lim D  =  { (x_j)_j ∈ ∏_j D(j)  |  ∀ (u:j→k) ∈ D.  D(u)(x_j) = x_k }
```

with projections `proj.(j) : lim D → D(j)`. The universal property is realized
by `mediate : cone → mor`: given a cone `(T, l_j)`, it returns the unique
`u : T → lim D` with `proj.(j) ∘ u = l_j`, by sending `x ∈ T` to the index of
the tuple `(l_j(x))_j`. Special cases, all one operation:

- discrete 2-vertex diagram ⇒ **binary product** `A×B`
- empty diagram ⇒ **terminal object** `1`
- cospan `A→C←B` ⇒ **pullback** `A ×_C B`

**Colimit fill.** Dually, the colimit is `(∐_j D(j))` quotiented by the relation
the arrows generate (computed by union–find), with injections `incl.(j)` and a
`comediate` realizing the couniversal property. Special cases: discrete ⇒
**coproduct** `A+B`; empty ⇒ **initial object** `0`; span ⇒ **pushout**.

Both `mediate` and `comediate` are where a *universal property becomes an
algorithm*: the unique mediating morphism is not postulated, it is constructed.

---

## 5. The core / elaborator line

The modality dial draws README §4.7’s line precisely:

- `fill … Universal` on FinSet is a **total, effective reduction** — it always
  computes and terminates. This is the trustworthy kernel.
- Fills whose solution must be *searched for* rather than forced (adapters
  between fixed interfaces, README §9) are **not** in Phase 1; they belong to the
  elaborator (Phase 3) and will elaborate down to core fills like these.

---

## 6. Deferred (the honest edges)

Phase 1 deliberately omits, and later phases must supply:

1. **Folds / recursion** as initial-algebra fills (colimits over a shape
   functor) — the next Phase-1 addition.
2. **A general, syntactic shape language** for diagrams (currently a host-level
   `diagram` value).
3. **A dependent-type substrate** to *state* commutation and universal
   properties inside Kan rather than in OCaml (Phase 2).
4. **Semantic universes beyond FinSet**, introduced behind a functor so the
   `fill` kernel is universe-polymorphic.
5. **The formal reduction relation and its metatheory** (README §12 open
   problems): which horns admit total effective filling, and the exact core/
   elaborator boundary.

---

## 7. How to run

```
# instant (bytecode, no build):
ocaml reference/kan_ref.ml

# native binary (dune):
eval $(opam env --switch=kan)
dune build
dune exec reference/kan_ref.exe
```
