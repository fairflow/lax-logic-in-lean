#!/usr/bin/env bash
# Build a vanilla-Verso paper: HTML (one page and per section), TeX, and a PDF.
#
#   scripts/verso-paper.sh <lib> <Main.lean> <out-dir> <out.pdf>
#
# e.g.  scripts/verso-paper.sh CLPPaper CLPPaperMain.lean docs/clp-paper docs/clp-paper.pdf
#
# <out-dir> receives html-single/, html-multi/ and tex/ (Verso does not clean
# it; we do).  Outputs are build artefacts: keep them gitignored.  The library
# must be a `[[lean_lib]]` in lakefile.toml (outside defaultTargets, so an
# ordinary `lake build` never pulls verso in).  View the HTML over HTTP, never
# file:// (section links become directory listings).
set -euo pipefail
lib=$1; main=$2; out=$3; pdf=$4
cd "$(dirname "$0")/.."
lake build "$lib"
rm -rf "$out"
lake lean "$main" -- --run "$main" --output "$out" --with-html-single --with-tex \
  2>&1 | grep -v "allowMissing\|^$" | grep -v "^warning: .*is not documented" || true
test -f "$out/html-single/index.html"
test -f "$out/tex/main.tex"
scripts/verso-tex-pdf.sh "$out/tex" "$pdf"
du -sh "$out/html-single" "$out/html-multi" "$pdf" | sed 's/^/  /'
