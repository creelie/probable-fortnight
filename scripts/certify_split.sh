#!/usr/bin/env bash
# certify_split.sh W [PART NPARTS] -- refute Phi(W) leaf by leaf along a decision tree.
#   Environment: LEAF_TIMEOUT (seconds per leaf, default none) and NOBUILD=1 (the Lean project and
#   build/cnf/W.cnf are already built, as when several copies run side by side).
#
#   verification/data/cubes/W.txt lists the leaves of a binary decision tree on the variables of
#   Phi(W), one per line as DIMACS literals ending in 0 (a "cube"). For every leaf c with index
#   i = PART mod NPARTS (default: all leaves), this script
#   1. writes Phi(W) followed by the unit clauses of c (the formula withCube (encode W) c);
#   2. refutes it with CaDiCaL 3.0.1 (binary LRAT), checks and trims the proof with lrat-trim;
#   3. has Lean check the trimmed proof with the verified LRAT checker of its standard library,
#      proving (Biplanar.withCube (Biplanar.encode W) c).Unsat, and deletes the proof.
#   A leaf that CaDiCaL does not refute within LEAF_TIMEOUT is appended to build/log/W_open.txt
#   (its index and literals) and skipped. Lean runs one proof at a time (flock).
#   With PART = tree it instead proves in Lean that the leaves form a complete decision tree and
#   that Phi(W) is unsatisfiable whenever every leaf formula is (Biplanar.unsat_of_leaves).
# Needs CADICAL and LRAT_TRIM (see scripts/get_tools.sh) and elan.
set -euo pipefail

W="$1"; PART="${2:-0}"; NPARTS="${3:-1}"
TAG="${W//,/_}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN="$ROOT/verification/lean"
LEAVES="${LEAVES:-$ROOT/verification/data/cubes/$TAG.txt}"
B="$ROOT/build"
mkdir -p "$B/cnf" "$B/lrat" "$B/log" "$LEAN/Certs"
CADICAL="${CADICAL:-$B/tools/cadical/build/cadical}"
LRAT_TRIM="${LRAT_TRIM:-$B/tools/lrat-trim/lrat-trim}"
ln -sfn "$B/lrat" "$LEAN/Certs/lrat"

cd "$LEAN"
if [ "${NOBUILD:-0}" != 1 ]; then
  lake build > /dev/null
  lake build biplanar-dump > /dev/null
fi
now() { date +%s.%N; }
since() { awk -v a="$1" -v b="$(now)" 'BEGIN { printf "%.1f", b - a }'; }
cube() { sed -n "$1p" "$LEAVES" | sed 's/ 0$//'; }
NL=$(grep -c . "$LEAVES")

axioms_ok() {  # axioms_ok LOG NAME : only the standard axioms and native_decide's own
  local AX
  AX=$(tr '\n' ' ' < "$1" | sed -n "s/.*'$2' depends on axioms: \[\([^]]*\)\].*/\1/p")
  [ -n "$AX" ] || { echo "no axiom report for $2"; return 1; }
  for a in $(echo "$AX" | tr ',' ' '); do
    case "$a" in
      propext|Classical.choice|Quot.sound|"$2._native.native_decide.ax_"*) ;;
      *) echo "unexpected axiom $a in $2"; return 1 ;;
    esac
  done
}

if [ "$PART" = tree ]; then
  D=$(awk '{ if (NF - 1 > d) d = NF - 1 } END { print d }' "$LEAVES")
  {
    echo "import BiplanarC5.Encode"
    echo "import BiplanarC5.Cubes"
    echo
    echo "/-- The $NL leaves of the decision tree for \`Phi($W)\`. -/"
    echo "def Biplanar.leaves_$TAG : List (List Int) := ["
    sed 's/ 0$//; s/ /, /g; s/^/  [/; s/$/],/' "$LEAVES" | sed '$ s/,$//'
    echo "]"
    echo
    echo "/-- \`Phi($W)\` is unsatisfiable if each of its $NL leaf formulas is. -/"
    echo "theorem Biplanar.unsat_${TAG}_of_leaves"
    echo "    (h : ∀ c ∈ Biplanar.leaves_$TAG, (Biplanar.withCube (Biplanar.encode [${W//,/, }]) c).Unsat) :"
    echo "    (Biplanar.encode [${W//,/, }]).Unsat :="
    echo "  Biplanar.unsat_of_leaves _ $D Biplanar.leaves_$TAG (by native_decide) h"
    echo
    echo "#print axioms Biplanar.unsat_${TAG}_of_leaves"
  } > "Certs/Tree_$TAG.lean"
  lake env lean "Certs/Tree_$TAG.lean" 2>&1 | tee "$B/log/${TAG}_tree.lean.txt"
  if grep -q "error" "$B/log/${TAG}_tree.lean.txt"; then echo "Lean rejected the tree for $W"; exit 1; fi
  axioms_ok "$B/log/${TAG}_tree.lean.txt" "Biplanar.unsat_${TAG}_of_leaves"
  echo "certify_split.sh: the $NL leaves of $W form a complete decision tree of depth $D (checked in Lean)"
  exit 0
fi

[ "${NOBUILD:-0}" = 1 ] || lake exe biplanar-dump "$W" "$B/cnf/$TAG.cnf" > /dev/null
read -r _ _ NV M < <(head -n 1 "$B/cnf/$TAG.cnf")
for ((i = 1; i <= NL; i++)); do
  [ $(( (i - 1) % NPARTS )) = "$PART" ] || continue
  c=$(cube "$i"); k=$(echo "$c" | wc -w)
  F="$B/cnf/${TAG}_$i.cnf"; P="$B/lrat/${TAG}_$i"
  { echo "p cnf $NV $((M + k))"; tail -n +2 "$B/cnf/$TAG.cnf"; for l in $c; do echo "$l 0"; done; } > "$F"
  t0=$(now)
  set +e
  if [ -n "${LEAF_TIMEOUT:-}" ]; then
    timeout "$LEAF_TIMEOUT" "$CADICAL" -q --lrat=true --binary=true "$F" "$P.raw" > /dev/null
  else
    "$CADICAL" -q --lrat=true --binary=true "$F" "$P.raw" > /dev/null
  fi
  rc=$?
  set -e
  if [ "$rc" = 124 ]; then
    rm -f "$P.raw" "$F"
    echo "$i $c" >> "$B/log/${TAG}_open.txt"
    echo "certify_split.sh: $W leaf $i of $NL open after $LEAF_TIMEOUT s"
    continue
  fi
  [ "$rc" = 20 ] || { echo "CaDiCaL exit code $rc on leaf $i of $W"; exit 1; }
  T_SOLVE=$(since "$t0"); t0=$(now)
  set +e
  "$LRAT_TRIM" -q -a "$F" "$P.raw" "$P.lrat"
  rc=$?
  set -e
  rm -f "$P.raw" "$F"
  [ "$rc" = 20 ] || { echo "lrat-trim exit code $rc on leaf $i of $W"; exit 1; }
  T_TRIM=$(since "$t0")
  N="Biplanar.leaf_${TAG}_$i"
  cat > "Certs/Leaf_${TAG}_$i.lean" <<LEANEOF
import BiplanarC5.Encode
import BiplanarC5.Cubes
open Std.Tactic.BVDecide

/-- Leaf $i of the decision tree for \`Phi($W)\` is unsatisfiable: the LRAT proof in
\`Certs/lrat/${TAG}_$i.lrat\` is accepted by the verified checker of the Lean standard library. -/
theorem $N :
    (Biplanar.withCube (Biplanar.encode [${W//,/, }]) [${c// /, }]).Unsat :=
  Reflect.verifyCert_correct _ (include_str "lrat/${TAG}_$i.lrat") (by native_decide)

#print axioms $N
LEANEOF
  t0=$(now)
  flock "$B/log/lean.lock" lake env lean "Certs/Leaf_${TAG}_$i.lean" > "$B/log/${TAG}_$i.lean.txt" 2>&1 || true
  T_LEAN=$(since "$t0")
  if grep -q "error" "$B/log/${TAG}_$i.lean.txt"; then cat "$B/log/${TAG}_$i.lean.txt"; echo "Lean rejected leaf $i of $W"; exit 1; fi
  axioms_ok "$B/log/${TAG}_$i.lean.txt" "$N"
  S=$(stat -c %s "$P.lrat")
  sha256sum "$P.lrat" | sed "s|$B/lrat/||" >> "$B/log/leaves.sha256"
  rm -f "$P.lrat"
  echo "certify_split.sh: $W leaf $i of $NL refuted and checked in Lean (solve $T_SOLVE s, trim $T_TRIM s, Lean $T_LEAN s; proof $S bytes)"
done
