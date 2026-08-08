# Kan for Neovim / Vim

Syntax highlighting for the Kan programming language (`.kan`).

## Install

**Recommended — works with ANY setup, including lazy.nvim** (copy two files into
your config directory, which is always on the runtimepath):

```sh
cp editors/nvim/syntax/kan.vim  ~/.config/nvim/syntax/
cp editors/nvim/plugin/kan.lua  ~/.config/nvim/plugin/
```

`plugin/kan.lua` registers the `.kan` extension via `vim.filetype.add`;
`syntax/kan.vim` does the highlighting. Open any `.kan` file (e.g.
`examples/tutorial.kan`) and it lights up.

> **lazy.nvim users:** don't use the native-package method below — lazy.nvim
> manages its own runtimepath and does **not** load `~/.config/nvim/pack/*/start/*`
> packages, so a native install is silently ignored. Use the two-file copy above.

**Native packages (vanilla Neovim, no lazy.nvim):**

```sh
mkdir -p ~/.config/nvim/pack/kan/start/kan
cp -r editors/nvim/* ~/.config/nvim/pack/kan/start/kan/
```

**Vim (classic):** copy `syntax/kan.vim` and `ftdetect/kan.vim` into `~/.vim/`.

**Vim (classic):** copy `syntax/kan.vim` and `ftdetect/kan.vim` into `~/.vim/`.

## What it covers

`--` comments, `"…"` strings, `Nat` (`123`) and `Integer` (`123z`) literals, the
keywords `def data eval import match lambda`, built-in types (`U`/`U1`/…, `Type`,
`Nat`, `Integer`, `String`, `Bool`), the eliminators `natElim`/`fst`/`snd`, the
constants `zero suc refl true false`, and heuristic coloring of type names
(capitalized) and constructors (after `|`). Highlight groups link to the standard
`Keyword`/`Type`/`Function`/`Constant`/`Comment`/`String`/`Number`/`Operator`, so
your colorscheme styles them automatically.

Coloring is regex-based (heuristic for type vs. constructor). A structural
Tree-sitter grammar is the next step — see [`../README.md`](../README.md).
