#!/usr/bin/env bash
# build_paper.sh -- build the paper and its submission files into dist/.
#
#   dist/biplanar-c5-blowups.pdf           the compiled paper
#   dist/biplanar-c5-blowups-tex.zip       main.tex with the figures as PNG (and their TikZ sources)
#   dist/biplanar-c5-blowups-arxiv.tar.gz  main.tex and the PNG figures, ready for arXiv
#
# Needs pdflatex with amsart, tikz (3d library), booktabs, enumitem and hyperref; pdftoppm (poppler)
# for the PNG figures; zip and tar.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PAPER="$ROOT/preprint"
DIST="$ROOT/dist"
NAME=biplanar-c5-blowups
FIGS="layers contraction"
mkdir -p "$DIST"

latex() { pdflatex -interaction=nonstopmode -halt-on-error "$@" > /dev/null; }

echo "== figures"
cd "$PAPER/figures"
for f in $FIGS; do
  latex "$f.tex"
  pdftoppm -png -r 300 -singlefile "$f.pdf" "$f"
  rm -f "$f.aux" "$f.log" "$f.pdf"
done

echo "== paper"
cd "$PAPER"
latex main.tex
latex main.tex
latex main.tex
if grep -q "Overfull\|undefined\|Rerun to get" main.log; then
  grep "Overfull\|undefined\|Rerun to get" main.log
  echo "build_paper.sh: fix the warnings above" >&2
  exit 1
fi
cp main.pdf "$DIST/$NAME.pdf"

STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT

echo "== tex.zip (figures as PNG)"
mkdir -p "$STAGE/$NAME/figures"
cp main.tex "$STAGE/$NAME/"
for f in $FIGS; do cp "figures/$f.png" "figures/$f.tex" "$STAGE/$NAME/figures/"; done
( cd "$STAGE/$NAME" && latex main.tex && latex main.tex && rm -f main.aux main.log main.out main.pdf )
rm -f "$DIST/$NAME-tex.zip"
( cd "$STAGE" && zip -qr "$DIST/$NAME-tex.zip" "$NAME" )

echo "== arXiv tarball"
mkdir -p "$STAGE/arxiv/figures"
cp main.tex "$STAGE/arxiv/"
for f in $FIGS; do cp "figures/$f.png" "$STAGE/arxiv/figures/"; done
( cd "$STAGE/arxiv" && latex main.tex && latex main.tex && rm -f main.aux main.log main.out main.pdf )
tar -czf "$DIST/$NAME-arxiv.tar.gz" -C "$STAGE/arxiv" .

rm -f main.aux main.log main.out main.pdf
ls -l "$DIST"
