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
          | "data" Name "{" ctor,… "}"                           -- a recursive datatype (initial algebra)
          | "fold" name ":" Name "->" "int" "{" clause,… "}"     -- a fold (catamorphism)
          | "let" name "=" expr
          | "show" expr
ctor    ::= Name field*            field ::= "int" (payload) | Name (recursive child)
clause  ::= Name var* "=" aexpr    -- var binds a payload int or an ALREADY-FOLDED child (int)
aexpr   ::= aexpr ("+"|"-") aexpr | aexpr "*" aexpr | int | var | "(" aexpr ")"
expr    ::= "fill" "inner" "(" f "," g ")"    -- composition: the (2,1)-horn's missing edge = g∘f
          | "fill" "limit"   D                -- the limiting cone of diagram D
          | "fill" "colimit" D                -- the colimiting cocone of diagram D
          | "product"   "[" name,… "]"        -- sugar for `fill limit`   of a discrete diagram
          | "coproduct" "[" name,… "]"        -- sugar for `fill colimit` of a discrete diagram
          | head "(" expr,… ")"               -- constructor build, or fold application
          | int
          | name                              -- a bound value, or a nullary constructor
```

### Datatypes and folds

A `data` declaration presents a signature functor; its values are finite trees
built with the constructors, e.g. `Cons(3, Nil)` or `Mul(Add(Lit(2),Lit(3)),Lit(4))`.
A `fold NAME : T -> int { … }` gives one clause per constructor; in a clause the
variables bind the payload (if any) followed by the **already-folded** children
(each an `int`, since folds run bottom-up — this is exactly `cata`). Applying a
fold, `sum(xs)`, is the unique homomorphism out of the initial algebra: a
universal fill. Both interpreter and compiler support datatypes and folds; a
fold compiles to a recursive C function.

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
- `examples/nat.kan` — `ℕ` and a fold to its value.
- `examples/list_sum.kan` — `List`, with `sum` and `length` folds.
- `examples/expr_eval.kan` — an expression datatype whose evaluator *is* a fold.

## Not yet in the surface (deferred)

Non-`int` fold carriers (folds targeting other datatypes, e.g. `map`), payloads
other than a single `int`, naming projections/injections as bindings, diagram
shapes beyond what `edge` expresses, and the dependent-type layer (Phase 2).
