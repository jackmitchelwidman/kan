# Kan for VS Code

Syntax highlighting for the Kan programming language (`.kan`).

## Try it locally (no packaging)

Symlink (or copy) this folder into your VS Code extensions directory, then
reload:

```sh
ln -s "$PWD/editors/vscode" ~/.vscode/extensions/kan-language
# then: VS Code → Command Palette → "Developer: Reload Window"
```

Open any `.kan` file (e.g. `examples/tutorial.kan`) and it highlights.

## Package it as a .vsix (to share)

```sh
npm install -g @vscode/vsce
cd editors/vscode
vsce package            # produces kan-language-0.1.0.vsix
code --install-extension kan-language-0.1.0.vsix
```

## What it covers

- `--` line comments, `"…"` strings
- `Nat` literals (`123`) and `Integer` literals (`123z`)
- keywords: `def data eval import match lambda`
- built-in types: `U`, `U1`, …, `Type`, `Nat`, `Integer`, `String`, `Bool`
- eliminators: `natElim`, `fst`, `snd`; constants: `zero suc refl true false`
- heuristic: capitalized identifiers → types; identifier after `|` → constructor
- `def NAME` / `data NAME` highlight the declared name

Type-vs-constructor coloring is heuristic (regex, not a parser). See
[`../README.md`](../README.md) for the Tree-sitter path to exact coloring.
