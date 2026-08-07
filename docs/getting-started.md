# Getting Started with Kan

Kan is a dependently typed language. This page gets you from nothing to a running
program in a couple of minutes — on **macOS, Linux, or Windows**, with **no OCaml
toolchain to install**.

> **Why no OCaml?** `kan run` and `kan check` are fully self-contained in a single
> binary — the interpreter and type-checker are built in. You only need a compiler
> toolchain for the *optional* `kan build` (compile a `.kan` file to a standalone
> native executable), and even then only `cc` for the C backend.

There are three ways in. Pick one:

| | What you get | Needs |
|---|---|---|
| **1. One-line install** | the `kan` binary on your PATH | `curl`/`irm` |
| **2. Manual download** | the `kan` binary, placed by hand | a browser |
| **3. Build from source** | `kan` + native `kan build` | OCaml + dune |

---

## 1. One-line install (recommended)

**macOS / Linux:**

```sh
curl -fsSL https://raw.githubusercontent.com/jackmitchelwidman/kan/main/install.sh | sh
```

**Windows (PowerShell):**

```powershell
irm https://raw.githubusercontent.com/jackmitchelwidman/kan/main/install.ps1 | iex
```

The script detects your OS and CPU, downloads the matching prebuilt binary from
the [latest release](https://github.com/jackmitchelwidman/kan/releases/latest),
and puts `kan` on your PATH. Open a new terminal and jump to
[Your first program](#your-first-program).

<sub>Overrides: `KAN_VERSION=v0.1.0` for a specific release, `KAN_INSTALL_DIR=…`
(Unix) / `$env:KAN_INSTALL_DIR` (Windows) for a custom location.</sub>

---

## 2. Manual download

Prefer to see what you're running? Grab the binary for your platform from the
[**releases page**](https://github.com/jackmitchelwidman/kan/releases/latest):

| Platform | File |
|---|---|
| Linux (x86-64) | `kan-linux-x86_64` |
| macOS (Apple Silicon) | `kan-macos-arm64` |
| macOS (Intel) | `kan-macos-x86_64` |
| Windows (x86-64) | `kan-windows-x86_64.exe` |

Then make it runnable and put it on your PATH:

```sh
# macOS / Linux
chmod +x kan-*            # mark executable
mkdir -p ~/.local/bin
mv kan-* ~/.local/bin/kan
# ensure ~/.local/bin is on your PATH (add to ~/.profile if not):
export PATH="$HOME/.local/bin:$PATH"
```

On macOS, the first run may be blocked by Gatekeeper (unsigned binary). Allow it
with `xattr -d com.apple.quarantine ~/.local/bin/kan`, or right-click → Open once.

On Windows, rename the file to `kan.exe` and put it in a folder on your `Path`.

---

## 3. Build from source

This is the only path that also gives you native compilation (`kan build`), and
it's a good choice if you want to hack on Kan itself. It needs **OCaml ≥ 4.13**
and **dune ≥ 3.0** — no third-party libraries (Kan builds against the OCaml
standard library only).

```sh
git clone https://github.com/jackmitchelwidman/kan
cd kan
dune build

# put `kan` on your PATH:
dune install --prefix ~/.local --sections bin      # installs to ~/.local/bin
```

Don't have OCaml? The one-step way to get it is [opam](https://opam.ocaml.org/doc/Install.html),
then `opam install dune`. But if you only want to *run* Kan programs, use option
1 or 2 above instead — you don't need any of this.

---

## Your first program

Save this as `hello.kan` (`Nat`, `zero`, `suc`, and `match` are built in — no
imports needed, so this runs anywhere you have `kan`):

```kan
-- a total, structurally-recursive function
def double : Nat -> Nat = lambda n: match n { | zero => zero | suc k => suc (suc (double k)) }

eval double 21          -- 42
eval "hello, Kan"
```

Then:

```sh
kan check hello.kan     # type-check and report the types
kan run   hello.kan     # type-check, then run — prints 42 and "hello, Kan"
```

Want the standard library (`add`, `List`, `Option`, proofs, category theory)?
Clone the repo — every file under [`examples/`](../examples/) is then a runnable
program, and you can `import "std/nat.kan"` and friends:

```sh
git clone https://github.com/jackmitchelwidman/kan && cd kan
kan run examples/tutorial.kan     # a guided tour of the whole language
```

### Compiling to a native binary (optional)

If you built from source (or have a C compiler / `ocamlopt` on your PATH), you can
turn a `.kan` file into a standalone executable — it type-checks first, so a
binary that builds is a program that can't crash on a type error:

```sh
kan build hello.kan -o hello      # via the OCaml backend (needs ocamlopt)
kan build -c hello.kan -o hello   # via the C backend (needs cc)
./hello
```

Both backends produce **identical** output to `kan run` — that agreement is
checked on every commit.

---

## Where to go next

- **[The hands-on tour](tour.md)** — functions, dependent types, proofs, unbounded
  integers, and category theory in five short steps.
- **[Kan by Example](examples.md)** — a big, browsable gallery, from one-liners to
  presheaves and sheaves. Everything type-checks.
- **[The README](../README.md)** — the design document: what Kan is and why.

## Troubleshooting

- **`kan: command not found`** — the install directory isn't on your PATH. Either
  restart your terminal, or run the binary by its full path
  (`~/.local/bin/kan run …`). The installer prints the exact PATH line to add.
- **`download failed … 404`** — there is no published release yet. Build from
  source (option 3), or ask the maintainer to cut a release.
- **macOS “cannot be opened because the developer cannot be verified”** — the
  binary is unsigned; clear the quarantine flag as shown in
  [Manual download](#2-manual-download).
- **Windows: very large `Nat` literals** — deep numeric literals are bounded by
  the default stack on Windows; `check`/`run` are otherwise unaffected. Use the
  unbounded `Integer` type for big numbers.
