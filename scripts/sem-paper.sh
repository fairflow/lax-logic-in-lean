#!/usr/bin/env bash
# The paper "Semantics and Decision for PLL" (SemPaper/): HTML + PDF into
# docs/ (both gitignored).
#
#   scripts/sem-paper.sh                build docs/sem-paper/{html-single,html-multi,tex} and docs/sem-paper.pdf
#   scripts/sem-paper.sh --open         ...then open the PDF and the one-page HTML (macOS `open`)
#   scripts/sem-paper.sh --serve        ...then serve docs/ on http://127.0.0.1:8098/
#   scripts/sem-paper.sh --serve-only   serve what is already built, no build
#
# The reader's flow in their own checkout, after `git merge --ff-only` and
# `lake build` (which does not build SemPaper: it is outside defaultTargets):
#     scripts/sem-paper.sh --open
# Runs from any directory (it cds to the repo root); incremental after the
# first run.  The paper imports library modules and one wip/ module
# (wip.f0Nuclear), which `lake build SemPaper` builds as dependencies.  The
# shared machinery (notation, blocks, figure helpers) is PaperKit/ and
# scripts/paperfig.py, shared with the F0 paper (scripts/f0-paper.sh).
#
# Served URLs:  http://127.0.0.1:8098/sem-paper.pdf
#               http://127.0.0.1:8098/sem-paper/html-single/   (one page)
#               http://127.0.0.1:8098/sem-paper/html-multi/    (per section)
# Stop the server with:  pkill -f "http.server 8098"
set -euo pipefail
cd "$(dirname "$0")/.."
PORT=${PORT:-8098}
if [ "${1:-}" != "--serve-only" ]; then
  # the figure (docs/sem-paper-figures/, gitignored), regenerated on every
  # build from data Lean computes (tools/SemPaper/FigureData.lean): the paper
  # inlines the SVG in the HTML and includes the PDF in the TeX
  lake build LaxLogic.PLL.SubTab.Facts LaxLogic.PLL.SubTab.Steps
  scripts/sem-figures.py
  # the source links of the Lean statements and tables (PaperKit/Blocks.lean)
  # are made when the output is written, from these two variables
  F0_SRC_SHA=$(git rev-parse HEAD)
  F0_SRC_REPO=$(git remote get-url origin)
  F0_SRC_REPO=${F0_SRC_REPO%.git}
  F0_SRC_REPO=${F0_SRC_REPO/git@github.com:/https://github.com/}
  export F0_SRC_SHA F0_SRC_REPO
  # no blank recto pages in print (the rest of the layout is CLPPaper/Layout.lean);
  # graphicx for the figure, longtable for the tables (PaperKit/Blocks.lean);
  # ragged bottoms, so that the page before a large figure is not stretched
  VERSO_TEX_EXTRA='\let\cleardoublepage\clearpage\usepackage{graphicx}\usepackage{longtable}\raggedbottom' \
    scripts/verso-paper.sh SemPaper SemPaperMain.lean docs/sem-paper docs/sem-paper.pdf
fi
case "${1:-}" in
  --open)
    echo "  pdf:       $PWD/docs/sem-paper.pdf"
    echo "  one page:  $PWD/docs/sem-paper/html-single/index.html"
    open docs/sem-paper.pdf
    open docs/sem-paper/html-single/index.html
    ;;
  --serve|--serve-only)
    test -f docs/sem-paper.pdf || { echo "nothing built yet: run without --serve-only"; exit 1; }
    pkill -f "http.server $PORT" 2>/dev/null || true
    ( cd docs && nohup python3 -m http.server "$PORT" --bind 127.0.0.1 >/dev/null 2>&1 & )
    sleep 1
    echo "  pdf:          http://127.0.0.1:$PORT/sem-paper.pdf"
    echo "  one page:     http://127.0.0.1:$PORT/sem-paper/html-single/"
    echo "  per section:  http://127.0.0.1:$PORT/sem-paper/html-multi/"
    echo "  stop:         pkill -f \"http.server $PORT\""
    ;;
esac
