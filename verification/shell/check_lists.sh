#!/usr/bin/env bash
# check_lists.sh -- Lemma 2.2 and the counts of the introduction with awk alone.
#
#   bash verification/shell/check_lists.sh [verification/data]
#
# Enumerates w in {1,...,7}^5 with s(w) <= 8, reduces each vector to its least rotation or reflection,
# counts the classes with 16 and 17 vertices (36 and 26) and compares them with wits16.txt and
# cands17.txt; also checks the edge counts 71..80 of the seventeen-vertex graphs.
set -euo pipefail
DATA="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../data" && pwd)}"

canon_awk='
function canon(a,   r, f, i, s, best) {
  best = ""
  for (r = 0; r < 5; r++) for (f = 0; f < 2; f++) {
    s = ""
    for (i = 0; i < 5; i++) s = s (f ? a[(r - i + 10) % 5] : a[(r + i) % 5]) (i < 4 ? "," : "")
    if (best == "" || s < best) best = s
  }
  return best
}'

enum=$(awk "$canon_awk"'
BEGIN {
  for (a = 1; a <= 7; a++) for (b = 1; b <= 7; b++) for (c = 1; c <= 7; c++)
  for (d = 1; d <= 7; d++) for (e = 1; e <= 7; e++) {
    if (a + b > 8 || b + c > 8 || c + d > 8 || d + e > 8 || e + a > 8) continue
    n = a + b + c + d + e
    if (n != 16 && n != 17) continue
    w[0] = a; w[1] = b; w[2] = c; w[3] = d; w[4] = e
    print n, canon(w)
  }
}' | sort -u)

fromfile() {
  awk "$canon_awk"'!/^#/ && NF == 5 { for (i = 0; i < 5; i++) w[i] = $(i + 1); print canon(w) }' "$1" | sort -u
}

ok=1
check() { if [ "$1" = 1 ]; then echo "ok   $2"; else echo "FAIL $2"; ok=0; fi; }

k16=$(grep '^16 ' <<< "$enum" | cut -d' ' -f2)
k17=$(grep '^17 ' <<< "$enum" | cut -d' ' -f2)
check "$([ "$(wc -l <<< "$k16")" = 36 ] && [ "$k16" = "$(fromfile "$DATA/wits16.txt")" ] && echo 1)" \
  "36 classes with n = 16 equal wits16.txt"
check "$([ "$(wc -l <<< "$k17")" = 26 ] && [ "$k17" = "$(fromfile "$DATA/cands17.txt")" ] && echo 1)" \
  "26 classes with n = 17 equal cands17.txt"

range=$(awk '!/^#/ && NF == 5 {
  e = 0; for (i = 1; i <= 5; i++) { j = i % 5 + 1; e += $i * ($i - 1) / 2 + $i * $j }
  if (min == "" || e < min) min = e; if (e > max) max = e
} END { print min, max }' "$DATA/cands17.txt")
check "$([ "$range" = "71 80" ] && echo 1)" "the 17-vertex graphs have 71 to 80 edges (6n - 12 = 90)"

if [ "$ok" = 1 ]; then echo "ALL OK"; else echo "SOME CHECKS FAILED"; exit 1; fi
