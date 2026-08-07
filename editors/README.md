# Editor support for Kan

Syntax highlighting for `.kan` files. Both integrations mirror the lexical
grammar in [`lib/tt.ml`](../lib/tt.ml): `--` line comments, `"…"` strings, `Nat`
(`123`) and `Integer` (`123z`) literals, the keywords `def data eval import match
lambda`, the built-in types (`U`/`U1`/…, `Type`, `Nat`, `Integer`, `String`,
`Bool`), the eliminators `natElim`/`fst`/`snd`, and heuristic coloring of type
names (capitalized identifiers) and constructors (the identifier after `|`).

- [`vscode/`](vscode/) — a VS Code extension (TextMate grammar).
- [`nvim/`](nvim/) — a Neovim/Vim syntax file.

These are regex-based, so type-vs-constructor coloring is heuristic (right ~95% of
real code). A structural [Tree-sitter](https://tree-sitter.github.io) grammar —
which parses `data`/`match`/binders and colors them exactly — is the natural next
step; it isn't here yet.
