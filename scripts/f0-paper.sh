#!/usr/bin/env bash
# The F0 paper (F0Paper/): HTML + PDF into docs/ (both gitignored).
#
#   scripts/f0-paper.sh                build docs/f0-paper/{html-single,html-multi,tex} and docs/f0-paper.pdf
#   scripts/f0-paper.sh --open         ...then open the PDF and the one-page HTML (macOS `open`)
#   scripts/f0-paper.sh --serve        ...then serve docs/ on http://127.0.0.1:8097/
#   scripts/f0-paper.sh --serve-only   serve what is already built, no build
#
# The reader's flow in their own checkout, after `git merge --ff-only` and
# `lake build` (which does not build F0Paper: it is outside defaultTargets):
#     scripts/f0-paper.sh --open
# Runs from any directory (it cds to the repo root); incremental after the
# first run.  The paper imports the wip/ modules listed in F0Paper/Math.lean
# (v0.7: the f0* modules of the sections, from f0Covers to f0FreePLL, and
# gapWidth, embedNeg, ladder8, floor), which `lake build F0Paper` builds as
# dependencies.  Sections are F0Paper/Sections/*.lean, in the order of
# F0Paper/Paper.lean; since v0.7 the last is Appendix.lean (Appendix A, the
# definitions the text does not mention), which one {include} line and one
# sentence of the Introduction attach.
#
# Served URLs:  http://127.0.0.1:8097/f0-paper.pdf
#               http://127.0.0.1:8097/f0-paper/html-single/   (one page)
#               http://127.0.0.1:8097/f0-paper/html-multi/    (per section)
# Stop the server with:  pkill -f "http.server 8097"
set -euo pipefail
cd "$(dirname "$0")/.."
PORT=${PORT:-8097}
if [ "${1:-}" != "--serve-only" ]; then
  # the figures (docs/f0-paper-figures/, gitignored), regenerated on every
  # build from data Lean computes (tools/F0/FigureData.lean): the paper inlines
  # the SVGs in the HTML and includes the PDFs in the TeX
  lake build wip.f0Covers wip.ladder8 wip.f0SelfSim
  scripts/f0-figures.py
  # the source links of the Lean statements and tables (F0Paper/Blocks.lean)
  # are made when the output is written, from these two variables
  F0_SRC_SHA=$(git rev-parse HEAD)
  F0_SRC_REPO=$(git remote get-url origin)
  F0_SRC_REPO=${F0_SRC_REPO%.git}
  F0_SRC_REPO=${F0_SRC_REPO/git@github.com:/https://github.com/}
  export F0_SRC_SHA F0_SRC_REPO
  # no blank recto pages in print (the rest of the layout is CLPPaper/Layout.lean);
  # graphicx for the figures, longtable for the tables (F0Paper/Blocks.lean);
  # ragged bottoms, so that the page before a large figure is not stretched;
  # a section that opens with a table ("Supporting declarations", and every
  # section of the appendix) needs ten lines left on the page, or starts the
  # next: longtable breaks the page when its first row does not fit, which
  # left the heading of 10.10 of v0.6 at the foot of a page (v0.7)
  VERSO_TEX_EXTRA='\let\cleardoublepage\clearpage\usepackage{graphicx}\usepackage{longtable}\raggedbottom\usepackage{etoolbox}\makeatletter\NewCommandCopy\fzOrigSection\section\RenewDocumentCommand\section{s o m}{\ifboolexpr{test {\ifstrequal{#3}{Supporting declarations}} or test {\ifdefequal{\@chapapp}{\appendixname}}}{\needspace{10\baselineskip}}{}\IfBooleanTF{#1}{\fzOrigSection*{#3}}{\IfValueTF{#2}{\fzOrigSection[#2]{#3}}{\fzOrigSection{#3}}}}\makeatother' \
    scripts/verso-paper.sh F0Paper F0PaperMain.lean docs/f0-paper docs/f0-paper.pdf
fi
case "${1:-}" in
  --open)
    echo "  pdf:       $PWD/docs/f0-paper.pdf"
    echo "  one page:  $PWD/docs/f0-paper/html-single/index.html"
    open docs/f0-paper.pdf
    open docs/f0-paper/html-single/index.html
    ;;
  --serve|--serve-only)
    test -f docs/f0-paper.pdf || { echo "nothing built yet: run without --serve-only"; exit 1; }
    pkill -f "http.server $PORT" 2>/dev/null || true
    ( cd docs && nohup python3 -m http.server "$PORT" --bind 127.0.0.1 >/dev/null 2>&1 & )
    sleep 1
    echo "  pdf:          http://127.0.0.1:$PORT/f0-paper.pdf"
    echo "  one page:     http://127.0.0.1:$PORT/f0-paper/html-single/"
    echo "  per section:  http://127.0.0.1:$PORT/f0-paper/html-multi/"
    echo "  stop:         pkill -f \"http.server $PORT\""
    ;;
esac
