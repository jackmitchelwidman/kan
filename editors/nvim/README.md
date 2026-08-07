# Kan for Neovim / Vim

Syntax highlighting for the Kan programming language (`.kan`).

## Install

**Neovim (native packages):**

```sh
mkdir -p ~/.config/nvim/pack/kan/start/kan
cp -r editors/nvim/* ~/.config/nvim/pack/kan/start/kan/
```

**With a plugin manager** (point it at the repo, subdir `editors/nvim`):

```lua
-- lazy.nvim
{ "jackmitchelwidman/kan", config = function() end,
  init = function() vim.opt.rtp:append(vim.fn.stdpath("data") .. "/lazy/kan/editors/nvim") end }
```

```vim
" vim-plug — clone, then add the subdir to runtimepath
Plug 'jackmitchelwidman/kan', { 'rtp': 'editors/nvim' }
```

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
