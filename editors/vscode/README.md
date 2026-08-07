# Kan for VS Code

Syntax highlighting for the Kan programming language (`.kan`).

## Install (recommended)

Package it into a `.vsix` and install through VS Code's normal flow — this is
the reliable path (needs Node/npm, which you already have if you use VS Code):

```sh
cd editors/vscode
npx --yes @vscode/vsce package --allow-missing-repository   # -> kan-language-0.1.0.vsix
code --install-extension kan-language-0.1.0.vsix
# then: Command Palette → "Developer: Reload Window"
```

Open any `.kan` file (e.g. `examples/tutorial.kan`) and it highlights; the status
bar should read **Kan**.

> **Don't** drop this folder (or a symlink to it) directly into
> `~/.vscode/extensions/` — modern VS Code's extension manager marks hand-placed
> extensions as "removed" on the next reload. Always install the `.vsix`.

## Live-editing the grammar (development)

If you're iterating on the grammar itself, open `editors/vscode/` in VS Code and
press **F5** to launch an Extension Development Host with it loaded — changes show
on reload without repackaging. (For everyday *use*, install the `.vsix` above.)

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
