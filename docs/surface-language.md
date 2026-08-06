# The Kan Surface Language — Phase 1

A first, deliberately tiny concrete syntax for writing Kan programs that run on
the `fill` kernel. It centers on one keyword — **`fill`** — plus the sugar
`product` / `coproduct`. Interpreter: `bin/kan.ml`. Examples: `examples/*.kan`.

## Running

```
eval $(opam env --switch=kan)
dune build
dune exec bin/kan.exe -- examples/compose.kan
```

## Grammar

```
program ::= stmt*
stmt    ::= "set" name "=" int                                   -- a finite set (object)
          | "map" name ":" name "->" name "=" "[" int,… "]"      -- a function (morphism), by its table
          | "diagram" name "{" "vertices" name,… ("edge" i j map)* "}"
          | "let" name "=" expr
          | "show" expr
expr    ::= "fill" "inner" "(" f "," g ")"    -- composition: the (2,1)-horn's missing edge = g∘f
          | "fill" "limit"   D                -- the limiting cone of diagram D
          | "fill" "colimit" D                -- the colimiting cocone of diagram D
          | "product"   "[" name,… "]"        -- sugar for `fill limit`   of a discrete diagram
          | "coproduct" "[" name,… "]"        -- sugar for `fill colimit` of a discrete diagram
          | name                              -- a previously bound value
```

Comments run from `--` to end of line. Whitespace is insignificant.

Sets are `{0 … n-1}`. A `map f : A -> B = [..]` gives `f`'s image table; the
interpreter checks the table length against `|A|` and that every image lies in
`B`. In a `diagram`, `edge i j m` records that map `m` goes from vertex `i` to
vertex `j` (0-indexed into the `vertices` list); endpoints and cardinalities
are checked.

## What each construct *is*

| Surface | Kernel call | Meaning |
|---|---|---|
| `fill inner (f,g)` | `fill (Inner (f,g)) Exists` | composition `g∘f` |
| `fill limit D` | `fill (LimCone D) Universal` | limit (terminal / product / pullback …) |
| `fill colimit D` | `fill (ColCocone D) Universal` | colimit (initial / coproduct / pushout …) |
| `product [A,B,…]` | `fill limit` (discrete) | product |
| `coproduct [A,B,…]` | `fill colimit` (discrete) | coproduct |

Every surface form is exactly one kernel `fill`. Nothing else computes.

## Examples

- `examples/compose.kan` — composition as an inner-horn fill.
- `examples/product.kan` — `A×B` as a universal fill.
- `examples/pullback.kan` — the *same* `fill limit`, on a cospan.
- `examples/coproduct.kan` — `A+B` as a colimit fill.

## Not yet in the surface (deferred)

Folds/initial-algebras (the kernel supports them via `fill_fold`; a `signature`
/ `fold` syntax is next), naming the projections/injections as bindings,
diagrams with non-cospan shapes beyond what `edge` expresses, and the
dependent-type layer (Phase 2).
