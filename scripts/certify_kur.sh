#!/usr/bin/env bash
# certify_kur.sh W -- refute Phi(W) together with Kuratowski clauses, and check the result in Lean.
#
#   1. the Lean encoder writes Phi(W) to build/cnf/W.cnf;
#   2. CaDiCaL 3.0.1 with the planarity propagator verification/propagator/bipprop.cpp searches for a
#      model; whenever the edges assigned to a layer contain a subdivision of K5 or K3,3 it adds the
#      clause "not all of these edges lie in this layer". These clauses K go to build/kur/W.kur;
#   3. CaDiCaL refutes Phi(W) followed by K again, with a binary LRAT proof, which lrat-trim checks
#      and trims to build/lrat/W.lrat;
#   4. Lean checks that every clause of K comes from a subdivision of K5 or K3,3 in C5[W]
#      (Biplanar.kurOK) and that the proof refutes Biplanar.withKur (Biplanar.encode W) K.
#
# Needs the tools of scripts/get_tools.sh, the Boost Graph Library headers (libboost-dev), and elan.
set -euo pipefail

W="$1"
TAG="${W//,/_}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN="$ROOT/verification/lean"
B="$ROOT/build"
mkdir -p "$B/cnf" "$B/lrat" "$B/log" "$B/kur" "$LEAN/Certs"
CADICAL="${CADICAL:-$B/tools/cadical/build/cadical}"
LRAT_TRIM="${LRAT_TRIM:-$B/tools/lrat-trim/lrat-trim}"
C="$B/tools/cadical"
[ -x "$B/bipprop" ] || g++ -O2 -std=c++17 -I"$C/src" -o "$B/bipprop" \
  "$ROOT/verification/propagator/bipprop.cpp" "$C/build/libcadical.a"
now() { date +%s.%N; }
since() { awk -v a="$1" -v b="$(now)" 'BEGIN { printf "%.1f", b - a }'; }

cd "$LEAN"
lake build > /dev/null
lake build biplanar-dump > /dev/null
lake exe biplanar-dump "$W" "$B/kur/$TAG.cnf" > /dev/null
# the variables lay l a b = 6n^2 + (l n + a) n + b of Biplanar.encode (DIMACS: plus one)
python3 -I - "$W" "$B/kur/$TAG.lits" <<'PYEOF'
import sys, itertools
w = [int(t) for t in sys.argv[1].split(',')]; K = len(w)
bag = [i for i, k in enumerate(w) for _ in range(k)]; n = len(bag)
E = [(a, b) for a, b in itertools.combinations(range(n), 2) if (bag[a] - bag[b]) % K in (0, 1, K - 1)]
with open(sys.argv[2], 'w') as f:
    f.write('%d %d\n' % (n, 2 * len(E)))
    for a, b in E:
        for l in (0, 1): f.write('%d %d %d %d\n' % (6 * n * n + (l * n + a) * n + b + 1, l, a, b))
PYEOF
t0=$(now)
set +e
"$B/bipprop" "$B/kur/$TAG" > "$B/log/${TAG}_prop.txt"
rc=$?
set -e
grep -v '^c ' "$B/log/${TAG}_prop.txt"
[ "$rc" = 20 ] || { echo "propagator exit code $rc on $W (expected 20 = unsatisfiable)"; exit 1; }
T_PROP=$(since "$t0")
read -r _ _ NV M < <(head -n 1 "$B/kur/$TAG.cnf")
NK=$(grep -c . "$B/kur/$TAG.kur")
{ echo "p cnf $NV $((M + NK))"; tail -n +2 "$B/kur/$TAG.cnf"; cat "$B/kur/$TAG.kur"; } > "$B/cnf/${TAG}_kur.cnf"
rm -f "$B/kur/$TAG.cnf"
t0=$(now)
set +e
"$CADICAL" -q --lrat=true --binary=true "$B/cnf/${TAG}_kur.cnf" "$B/lrat/$TAG.raw" > /dev/null
rc=$?
set -e
[ "$rc" = 20 ] || { echo "CaDiCaL exit code $rc on $W with its Kuratowski clauses"; exit 1; }
T_SOLVE=$(since "$t0"); t0=$(now)
set +e
"$LRAT_TRIM" -q -a "$B/cnf/${TAG}_kur.cnf" "$B/lrat/$TAG.raw" "$B/lrat/$TAG.lrat"
rc=$?
set -e
rm -f "$B/lrat/$TAG.raw" "$B/cnf/${TAG}_kur.cnf"
[ "$rc" = 20 ] || { echo "lrat-trim exit code $rc on $W"; exit 1; }
T_TRIM=$(since "$t0")

ln -sfn "$B/lrat" "$LEAN/Certs/lrat"
ln -sfn "$B/kur" "$LEAN/Certs/kur"
N="Biplanar.unsatK_$TAG"
cat > "Certs/Kur_$TAG.lean" <<LEANEOF
import BiplanarC5.Encode
import BiplanarC5.Kuratowski
open Std.Tactic.BVDecide

/-- The Kuratowski clauses found for \`Phi($W)\` (\`Certs/kur/$TAG.kur\`). -/
def Biplanar.kur_$TAG : List (List Int) := Biplanar.parseClauses (include_str "kur/$TAG.kur")

/-- Each of them comes from a subdivision of \`K₅\` or \`K₃,₃\` in \`C₅[$W]\` and one layer. -/
theorem Biplanar.kurOK_$TAG : Biplanar.kurOK [${W//,/, }] Biplanar.kur_$TAG = true := by
  native_decide

/-- \`Phi($W)\` with these clauses is unsatisfiable: the LRAT proof in \`Certs/lrat/$TAG.lrat\` is
accepted by the verified checker of the Lean standard library. -/
theorem $N :
    (Biplanar.withKur (Biplanar.encode [${W//,/, }]) Biplanar.kur_$TAG).Unsat :=
  Reflect.verifyCert_correct _ (include_str "lrat/$TAG.lrat") (by native_decide)

#print axioms Biplanar.kurOK_$TAG
#print axioms $N
LEANEOF
t0=$(now)
lake env lean "Certs/Kur_$TAG.lean" > "$B/log/${TAG}_kur.lean.txt" 2>&1 || true
T_LEAN=$(since "$t0")
cat "$B/log/${TAG}_kur.lean.txt"
if grep -q "error" "$B/log/${TAG}_kur.lean.txt"; then echo "Lean rejected the certificate for $W"; exit 1; fi
for name in "Biplanar.kurOK_$TAG" "$N"; do
  AX=$(tr '\n' ' ' < "$B/log/${TAG}_kur.lean.txt" | sed -n "s/.*'$name' depends on axioms: \[\([^]]*\)\].*/\1/p")
  [ -n "$AX" ] || { echo "no axiom report for $name"; exit 1; }
  for a in $(echo "$AX" | tr ',' ' '); do
    case "$a" in
      propext|Classical.choice|Quot.sound|"$name._native.native_decide.ax_"*) ;;
      *) echo "unexpected axiom $a in $name"; exit 1 ;;
    esac
  done
done
echo "certify_kur.sh: $W refuted with $NK Kuratowski clauses and checked in Lean (propagator ${T_PROP} s, solve ${T_SOLVE} s, trim ${T_TRIM} s, Lean ${T_LEAN} s; proof $(stat -c %s "$B/lrat/$TAG.lrat") bytes, clauses $(stat -c %s "$B/kur/$TAG.kur") bytes)"
