#!/usr/bin/env bash
# certify.sh W -- refute the formula Phi(W) and check the refutation in Lean.
#
#   W is a weight vector such as 1,1,7,1,7 (one of verification/data/cands17.txt).
#   1. the Lean encoder writes Phi(W) to build/cnf/W.cnf;
#   2. CaDiCaL 3.0.1 refutes it and writes a binary LRAT proof;
#   3. lrat-trim checks and trims the proof and writes it as text to build/lrat/W.lrat;
#   4. Lean checks build/lrat/W.lrat against Biplanar.encode W with the verified LRAT checker of its
#      standard library (Std.Tactic.BVDecide.LRAT.check_sound) and proves (Biplanar.encode W).Unsat.
#
# If dist/certificates/W.lrat.xz exists (from the release assets), step 2 is skipped and that proof is used.
# Needs CADICAL and LRAT_TRIM (paths to the binaries; see scripts/get_tools.sh) and elan.
set -euo pipefail

W="$1"
TAG="${W//,/_}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN="$ROOT/verification/lean"
B="$ROOT/build"
mkdir -p "$B/cnf" "$B/lrat" "$B/log"
CADICAL="${CADICAL:-$B/tools/cadical/build/cadical}"
LRAT_TRIM="${LRAT_TRIM:-$B/tools/lrat-trim/lrat-trim}"

cd "$LEAN"
lake build biplanar-dump > /dev/null
lake exe biplanar-dump "$W" "$B/cnf/$TAG.cnf"

if [ -f "$ROOT/dist/certificates/$TAG.lrat.xz" ]; then
  xz -dc "$ROOT/dist/certificates/$TAG.lrat.xz" > "$B/lrat/$TAG.lrat"
else
  set +e
  "$CADICAL" -q --lrat=true --binary=true "$B/cnf/$TAG.cnf" "$B/lrat/$TAG.raw" > "$B/log/$TAG.cadical.txt"
  rc=$?
  set -e
  [ "$rc" = 20 ] || { echo "CaDiCaL exit code $rc on $W (expected 20 = unsatisfiable)"; exit 1; }
  set +e
  "$LRAT_TRIM" -q -a "$B/cnf/$TAG.cnf" "$B/lrat/$TAG.raw" "$B/lrat/$TAG.lrat"
  rc=$?
  set -e
  [ "$rc" = 20 ] || { echo "lrat-trim exit code $rc on $W (expected 20 = proof verified)"; exit 1; }
  rm -f "$B/lrat/$TAG.raw"
fi

mkdir -p "$LEAN/Certs"
ln -sfn "$B/lrat" "$LEAN/Certs/lrat"
cat > "$LEAN/Certs/Unsat_$TAG.lean" <<LEANEOF
import BiplanarC5.Encode
open Std.Tactic.BVDecide

/-- \`Phi($W)\` is unsatisfiable: the LRAT proof in \`Certs/lrat/$TAG.lrat\` is accepted by the verified
checker of the Lean standard library. -/
theorem Biplanar.unsat_$TAG : (Biplanar.encode [${W//,/, }]).Unsat :=
  Reflect.verifyCert_correct _ (include_str "lrat/$TAG.lrat") (by native_decide)

#print axioms Biplanar.unsat_$TAG
LEANEOF
lake env lean "Certs/Unsat_$TAG.lean" 2>&1 | tee "$B/log/$TAG.lean.txt"
if grep -q "error" "$B/log/$TAG.lean.txt"; then echo "Lean rejected the certificate for $W"; exit 1; fi
AX=$(tr '\n' ' ' < "$B/log/$TAG.lean.txt" | sed -n "s/.*'Biplanar.unsat_$TAG' depends on axioms: \[\([^]]*\)\].*/\1/p")
for a in $(echo "$AX" | tr ',' ' '); do
  case "$a" in
    propext|Classical.choice|Quot.sound|"Biplanar.unsat_$TAG._native.native_decide.ax_1_1") ;;
    *) echo "unexpected axiom $a"; exit 1 ;;
  esac
done
[ -n "$AX" ] || { echo "no axiom report"; exit 1; }
sha256sum "$B/lrat/$TAG.lrat" | sed "s|$B/lrat/||" >> "$B/log/certificates.sha256"
echo "certify.sh: $W refuted and checked in Lean"
