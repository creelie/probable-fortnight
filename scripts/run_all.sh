#!/usr/bin/env bash
# run_all.sh -- re-run the checks of "The biplanar clique blow-ups of the five-cycle".
#
#   C       verification/c/drawings.c            exact integer tests: the 36 pairs of plane drawings of
#                                                Proposition 2.3 and their 8-colourings
#   C++     verification/cpp/reduction.cpp       Lemmas 2.1 and 2.2 by enumeration, the edge counts
#   Shell   verification/shell/check_lists.sh    Lemma 2.2 with awk alone
#   Python  verification/python/verify_c5.py     Lemmas 2.1 and 2.2, the drawings (exact tests and
#                                                networkx), the colourings, formula (1.1) on all 62 graphs
#           verification/python/odd_cycles.py    Section 7: formula (7.1) against an exact dynamic programme,
#                                                the colouring of Theorem 7.1, the arithmetic of Corollary 7.2
#   Julia   verification/julia/verify_c5.jl      Lemmas 2.1 and 2.2, the drawings and colourings
#                                                (if julia is on PATH or $JULIA is set)
#   Lean    verification/lean/                   Lean 4 v4.34.1: the encoder, Lemma 2.2, the enumeration
#                                                behind Lemma 2.1, the 36 drawings and colourings by kernel
#                                                evaluation; Check.lean audits the axioms (if lake is on
#                                                PATH; LEAN=0 skips it)
#
# The 26 certificates of Theorem 5.1 are checked by scripts/certify.sh, one weight vector at a time
# (CERTS="1,1,7,1,7 ..." runs them here as well).
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
V="$ROOT/verification"
D="$V/data"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }
last() { tail -n 1 "$1" | grep -q "$2"; }

echo "== C and C++"
cc -O2 -Wall -o "$BUILD/drawings" "$V/c/drawings.c" || fail "compile drawings.c"
c++ -O2 -Wall -std=c++17 -o "$BUILD/reduction" "$V/cpp/reduction.cpp" || fail "compile reduction.cpp"
"$BUILD/drawings" "$D/witnesses16.txt" > "$BUILD/c.txt" 2>&1 && last "$BUILD/c.txt" '^36 witnesses, 0 failures$' \
  && ok "drawings.c" || fail "drawings.c (see build/c.txt)"
"$BUILD/reduction" "$D" > "$BUILD/cpp.txt" 2>&1 && last "$BUILD/cpp.txt" '^ALL CHECKS PASSED$' \
  && ok "reduction.cpp" || fail "reduction.cpp (see build/cpp.txt)"

echo "== Shell"
bash "$V/shell/check_lists.sh" "$D" > "$BUILD/sh.txt" 2>&1 && last "$BUILD/sh.txt" '^ALL OK$' \
  && ok "check_lists.sh" || fail "check_lists.sh (see build/sh.txt)"

echo "== Python"
python3 "$V/python/verify_c5.py" > "$BUILD/py.txt" 2>&1 && last "$BUILD/py.txt" '^ALL CHECKS PASSED$' \
  && ok "verify_c5.py" || fail "verify_c5.py (see build/py.txt)"
python3 "$V/python/odd_cycles.py" > "$BUILD/py6.txt" 2>&1 && last "$BUILD/py6.txt" '^ALL CHECKS PASSED$' \
  && ok "odd_cycles.py" || fail "odd_cycles.py (see build/py6.txt)"

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  "$JULIA" "$V/julia/verify_c5.jl" "$D" > "$BUILD/jl.txt" 2>&1 && last "$BUILD/jl.txt" '^ALL CHECKS PASSED$' \
    && ok "verify_c5.jl" || fail "verify_c5.jl (see build/jl.txt)"
fi

echo "== Lean"
if [ "${LEAN:-1}" = 0 ] || ! command -v lake > /dev/null; then echo "lake not found or LEAN=0: skipping"; else
  out=$(cd "$V/lean" && lake build 2>&1 && lake env lean Check.lean 2>&1); st=$?
  echo "$out" > "$BUILD/lean.txt"
  if [ $st -eq 0 ] && ! grep -q "error\|declaration uses 'sorry'\|sorryAx\|native_decide" <<< "$out" \
       && grep -q "axiom audit: .* theorems, all within propext, Classical.choice, Quot.sound" <<< "$out"; then
    ok "Lean: $(grep -o 'axiom audit: [0-9]* theorems' <<< "$out")"
  else fail "Lean (see build/lean.txt)"; fi
  for w in ${CERTS:-}; do
    "$ROOT/scripts/certify.sh" "$w" > "$BUILD/cert-${w//,/_}.txt" 2>&1 \
      && ok "certificate $w" || fail "certificate $w (see build/cert-${w//,/_}.txt)"
  done
fi

if [ $FAILED -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAILED
