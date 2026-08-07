#!/usr/bin/env sh
# Kan installer — downloads a prebuilt `kan` binary. No OCaml required.
#
#   curl -fsSL https://raw.githubusercontent.com/jackmitchelwidman/kan/main/install.sh | sh
#
# Environment overrides:
#   KAN_VERSION=v0.1.0   install a specific tag (default: latest release)
#   KAN_INSTALL_DIR=DIR  install location (default: $HOME/.local/bin)
set -eu

REPO="jackmitchelwidman/kan"
INSTALL_DIR="${KAN_INSTALL_DIR:-$HOME/.local/bin}"

say()  { printf '%s\n' "$*"; }
err()  { printf 'kan install: %s\n' "$*" >&2; exit 1; }

# --- detect platform -------------------------------------------------------
os="$(uname -s)"
arch="$(uname -m)"
case "$os" in
  Linux)  os_tag=linux ;;
  Darwin) os_tag=macos ;;
  *) err "unsupported OS '$os'. Build from source: https://github.com/$REPO#from-source" ;;
esac
case "$arch" in
  x86_64|amd64) arch_tag=x86_64 ;;
  arm64|aarch64) arch_tag=arm64 ;;
  *) err "unsupported architecture '$arch'. Build from source: https://github.com/$REPO#from-source" ;;
esac

# Only the combinations the release workflow actually builds.
asset="kan-${os_tag}-${arch_tag}"
case "$asset" in
  kan-linux-x86_64|kan-macos-x86_64|kan-macos-arm64) : ;;
  kan-linux-arm64)
    err "no prebuilt binary for Linux/arm64 yet. Build from source (fast, one command): https://github.com/$REPO#from-source" ;;
  *) err "no prebuilt binary for $os_tag/$arch_tag. Build from source: https://github.com/$REPO#from-source" ;;
esac

# --- resolve the download URL ----------------------------------------------
if [ -n "${KAN_VERSION:-}" ]; then
  url="https://github.com/$REPO/releases/download/${KAN_VERSION}/${asset}"
else
  url="https://github.com/$REPO/releases/latest/download/${asset}"
fi

# --- download --------------------------------------------------------------
if command -v curl >/dev/null 2>&1; then
  fetch() { curl -fSL --proto '=https' --tlsv1.2 "$1" -o "$2"; }
elif command -v wget >/dev/null 2>&1; then
  fetch() { wget -qO "$2" "$1"; }
else
  err "need curl or wget to download."
fi

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
say "Downloading $asset ${KAN_VERSION:+($KAN_VERSION) }…"
fetch "$url" "$tmp" || err "download failed: $url
(If no release exists yet, ask the maintainer to push a tag, or build from source.)"

# --- install ---------------------------------------------------------------
mkdir -p "$INSTALL_DIR"
dest="$INSTALL_DIR/kan"
mv "$tmp" "$dest"
chmod +x "$dest"
trap - EXIT

say ""
say "Installed kan -> $dest"
say ""

# --- PATH hint -------------------------------------------------------------
case ":$PATH:" in
  *":$INSTALL_DIR:"*) say "You're ready. Try:  kan run examples/tutorial.kan" ;;
  *)
    say "Add it to your PATH (then restart your shell):"
    say ""
    say "  echo 'export PATH=\"$INSTALL_DIR:\$PATH\"' >> ~/.profile"
    say ""
    say "Or run it directly:  $dest run <file.kan>"
    ;;
esac
