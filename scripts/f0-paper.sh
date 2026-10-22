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
# first run.  The paper imports wip/ modules (wip.f0Covers, f0Indep, f0Dyadic,
# f0Rat, gapWidth, embedNeg, ladder8, floor), which `lake build F0Paper`
# builds as dependencies.
#
# Served URLs:  http://127.0.0.1:8097/f0-paper.pdf
#               http://127.0.0.1:8097/f0-paper/html-single/   (one page)
#               http://127.0.0.1:8097/f0-paper/html-multi/    (per section)
# Stop the server with:  pkill -f "http.server 8097"
set -euo pipefail
cd "$(dirname "$0")/.."
PORT=${PORT:-8097}
if [ "${1:-}" != "--serve-only" ]; then
  # no blank recto pages in print (the rest of the layout is CLPPaper/Layout.lean)
  VERSO_TEX_EXTRA='\let\cleardoublepage\clearpage' \
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
