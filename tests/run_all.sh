#!/usr/bin/env bash
# Kan regression gate.
#   • every examples/ and std/ file must `kan check`.
#   • every file with an `eval` must produce IDENTICAL output from all three
#     runtimes: `kan run`, the OCaml backend, and the C backend.
# Exits nonzero on the first failure. Run from the repo root:  bash tests/run_all.sh
set -u
cd "$(dirname "$0")/.." || exit 2

KAN="${KAN:-kan}"
command -v "$KAN" >/dev/null 2>&1 || KAN="_build/default/bin/kan.exe"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

pass=0; fail=0
red()  { printf '\033[31m%s\033[0m\n' "$1"; }
green(){ printf '\033[32m%s\033[0m\n' "$1"; }

files=$(ls examples/*.kan std/*.kan 2>/dev/null)

for f in $files; do
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
reject "accumulator-style recursion" \
  'def f : Nat -> Nat -> Nat = \n acc. match n { | zero => acc | suc k => f k (suc acc) }'
reject "non-structural recursion (loops on the whole value)" \
  'def f : Nat -> Nat = \n. match n { | zero => zero | suc k => f n }'
reject "non-exhaustive match (missing case)" \
  'def f : Nat -> Nat = \n. match n { | zero => zero }'

echo "--------------------------------------------"
echo "passed: $pass   failed: $fail"
[ "$fail" -eq 0 ] || exit 1
