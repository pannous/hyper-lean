#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p tmp/pdfs/probability-build output/pdf
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory=tmp/pdfs/probability-build \
    paper/algebraic-probability.tex > "tmp/pdfs/probability-build/pass-${pass}.txt"
done
if rg -q 'undefined|Overfull|LaTeX Error|Emergency stop' tmp/pdfs/probability-build/algebraic-probability.log; then
  rg -n 'undefined|Overfull|LaTeX Error|Emergency stop' tmp/pdfs/probability-build/algebraic-probability.log
  exit 1
fi
cp tmp/pdfs/probability-build/algebraic-probability.pdf output/pdf/algebraic-probability.pdf
printf '%s\n' 'Built output/pdf/algebraic-probability.pdf'
