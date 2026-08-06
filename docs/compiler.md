# The Kan Compiler — Phase 1 Backend

`kan build` compiles a `.kan` program to a **native binary** by generating C and
invoking the system C compiler. This realizes the first two hops of the README
pipeline (`Kan → … → C → machine code`).

It is a genuine compiler, not constant-folding: the emitted binary contains the
categorical runtime (composition; finite limits by tuple enumeration; colimits
by union–find) and **runs the fill algorithms itself** at runtime. Every
compiled example produces output byte-for-byte identical to the interpreter.

## Usage

```
eval $(opam env --switch=kan)
dune build

# compile to a native executable:
dune exec bin/kan.exe -- build examples/product.kan -o product
./product

# inspect the generated C:
dune exec bin/kan.exe -- emit-c examples/compose.kan

# interpret (no compile):
dune exec bin/kan.exe -- run examples/compose.kan
```

## Pipeline

```
.kan source
   │  Syntax.tokenize / parse        (lib/syntax.ml)
   ▼
 AST (stmt list)
   │  Compile.compile                (lib/compile.ml)
   ▼
 C translation unit  (categorical runtime + a main that builds the program's
   │                  sets/maps/diagrams and calls the runtime)
   │  cc -O2                          (bin/kan.ml drives this)
   ▼
 native ELF binary
```

## What the runtime provides

| C runtime | Kan meaning |
|---|---|
| `kan_compose(f,g)` | inner-horn fill: the composite `g∘f` |
| `kan_limit(...)` | universal fill: terminal / product / pullback (finite limit) |
| `kan_colimit(...)` | universal fill: initial / coproduct / pushout (finite colimit) |
| `kan_show_*` | the `show` statement |

The compiler tracks each binding's type (`Obj` / `Mor` / `Cone`) so it can emit
the correct construction and the correct `show`. Objects become `Obj`, maps
become `Mor` with a table array, diagrams become vertex/edge arrays, and each
`fill` / `product` / `coproduct` becomes one runtime call.

## Correctness check

`bin/kan.ml` has both an interpreter (`run`) and this compiler (`build`) over
the *same* front-end and the *same* semantics. Compiling every example and
diffing the binary's output against the interpreter is the backend's smoke test;
all four match.

## Datatypes and folds

Recursive datatypes compile too. A `data` declaration needs no runtime type; its
values become `KTree` nodes built by `kan_node`, and a `fold` compiles to a
**recursive C function** — a `switch` on the constructor tag that recurses on the
children (exactly `cata`). So `examples/expr_eval.kan` compiles to a native
binary whose `f_eval` is a real evaluator.

## Limits (Phase 1)

- The compiled subset covers the FinSet structural fragment (sets, maps,
  diagrams, limits, colimits, composition) **and** datatypes/folds over `int`.
- Codegen is straightforward C with a tree-walking runtime; the README's
  "Optimized Core" and LLVM path are later phases. No IR yet — we lower the AST
  directly. That is deliberate for a first backend.
- No redefinition of a name within one program (the compiler reports this).
