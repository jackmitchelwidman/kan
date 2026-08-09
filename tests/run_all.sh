#!/usr/bin/env bash
# Kan regression gate.
#   • every examples/ and std/ file must `kan check`.
#   • every file with an `eval` must produce IDENTICAL output from all three
#     runtimes: `kan run`, the OCaml backend, and the C backend.
# Exits nonzero on the first failure. Run from the repo root:  bash tests/run_all.sh
#
# Default: FULL gate — checks everything (authoritative; run before committing).
# FAST=1 bash tests/run_all.sh  — skips the heavy verified-tower files (they
#   re-pay the gcd correctness proofs on import; see ADR-016) for a quick
#   iteration loop. The full gate remains the source of truth.
set -u
cd "$(dirname "$0")/.." || exit 2

# Files that are correct but expensive to type-check (the ADR-016 reduction-cost
# wart, re-paid on import). Skipped only when FAST=1.
SLOW_FILES="std/gcd.kan std/rational_reduced.kan"

KAN="${KAN:-kan}"
command -v "$KAN" >/dev/null 2>&1 || KAN="_build/default/bin/kan.exe"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

pass=0; fail=0
red()  { printf '\033[31m%s\033[0m\n' "$1"; }
green(){ printf '\033[32m%s\033[0m\n' "$1"; }

files=$(ls examples/*.kan std/*.kan 2>/dev/null)

for f in $files; do
  # FAST mode: skip the known-heavy files (still checked by the full gate).
  if [ "${FAST:-0}" = "1" ] && printf '%s\n' $SLOW_FILES | grep -qxF "$f"; then
    printf 'SKIP (FAST): %s\n' "$f"; continue
  fi
  # 1) must type-check
  if ! "$KAN" check "$f" >/dev/null 2>&1; then
    red "CHECK FAILED: $f"; fail=$((fail+1)); continue
  fi
  # 2) if it has evals, the three runtimes must agree
  if grep -qE '^[[:space:]]*eval[[:space:]]' "$f"; then
    r_run="$TMP/run.txt"; r_ml="$TMP/ml.txt"; r_c="$TMP/c.txt"
    "$KAN" run "$f" >"$r_run" 2>/dev/null
    if "$KAN" build   "$f" -o "$TMP/a_ml" >/dev/null 2>&1; then "$TMP/a_ml" >"$r_ml" 2>/dev/null; else red "OCAML BUILD FAILED: $f"; fail=$((fail+1)); continue; fi
    if "$KAN" build -c "$f" -o "$TMP/a_c"  >/dev/null 2>&1; then "$TMP/a_c"  >"$r_c"  2>/dev/null; else red "C BUILD FAILED: $f";     fail=$((fail+1)); continue; fi
    if diff -q "$r_run" "$r_ml" >/dev/null && diff -q "$r_run" "$r_c" >/dev/null; then
      green "OK (3 runtimes agree): $f"; pass=$((pass+1))
    else
      red "OUTPUT MISMATCH: $f"; echo "  run vs ocaml:"; diff "$r_run" "$r_ml" | head; echo "  run vs c:"; diff "$r_run" "$r_c" | head
      fail=$((fail+1))
    fi
  else
    green "OK (checks): $f"; pass=$((pass+1))
  fi
done

# 3) rejection tests: programs that MUST be refused (unsound / non-total).
#    Each heredoc is a one-line .kan the checker should reject.
reject() {
  local desc="$1" src="$2"
  printf '%s\n' "$src" > "$TMP/reject.kan"
  if "$KAN" check "$TMP/reject.kan" >/dev/null 2>&1; then
    red "SHOULD HAVE BEEN REJECTED: $desc"; fail=$((fail+1))
  else
    green "OK (correctly rejected): $desc"; pass=$((pass+1))
  fi
}
reject "non-structural recursion (loops on the whole value)" \
  'def f : Nat -> Nat = \n. match n { | zero => zero | suc k => f n }'
reject "non-exhaustive match (missing case)" \
  'def f : Nat -> Nat = \n. match n { | zero => zero }'
# a recursive `match` must be in TAIL position; a nested/wrapped one must not
# silently claim the recursion (these must be rejected, not miscompiled):
reject "recursion under a non-binder-scrutinee match" \
  'def f : Nat -> Nat = \n. match (suc n) { | zero => zero | suc m => match n { | zero => zero | suc k => f k } }'
reject "recursion wrapped by a constructor (non-tail match)" \
  'def f : Nat -> Nat = \n. suc (match n { | zero => zero | suc k => f k })'
# a single flat namespace: no name may be declared twice (def / data / ctor)
reject "duplicate top-level name (def vs def)" \
  'def d : Nat = 1 def d : Nat = 2'
reject "duplicate top-level name (constructor vs def)" \
  'data Age { age : Nat -> Age } def age : Age -> Nat = \a. match a { | age n => n }'
# qualified names (namespaces): an unknown qualified reference is a clean error
reject "unbound qualified name" \
  'def x : Nat = Foo::bar'

echo "--------------------------------------------"
echo "passed: $pass   failed: $fail"
[ "${FAST:-0}" = "1" ] && echo "(FAST mode — skipped: $SLOW_FILES; run the full gate before committing)"
[ "$fail" -eq 0 ] || exit 1
