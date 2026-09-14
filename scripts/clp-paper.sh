#!/usr/bin/env bash
# The CLP paper (CLPPaper/): HTML + PDF into docs/ (both gitignored).
#
#   scripts/clp-paper.sh                build docs/clp-paper/{html-single,html-multi,tex} and docs/clp-paper.pdf
#   scripts/clp-paper.sh --open         ...then open the PDF and the one-page HTML (macOS `open`)
#   scripts/clp-paper.sh --serve        ...then serve docs/ on http://127.0.0.1:8096/
#   scripts/clp-paper.sh --serve-only   serve what is already built, no build
#
# The reader's flow in their own checkout, after `git merge --ff-only` and
# `lake build` (which does not build CLPPaper: it is outside defaultTargets):
#     scripts/clp-paper.sh --open
# Runs from any directory (it cds to the repo root); incremental after the
# first run (the first run compiles Verso if that checkout never has).
#
# Served URLs:  http://127.0.0.1:8096/clp-paper.pdf
#               http://127.0.0.1:8096/clp-paper/html-single/   (one page)
#               http://127.0.0.1:8096/clp-paper/html-multi/    (per section)
# The server is a plain `python3 -m http.server` rooted at docs/; anyone on
# this machine can open the URLs, whichever checkout did the build.  Stop it
# with:  pkill -f "http.server 8096"
set -euo pipefail
cd "$(dirname "$0")/.."
PORT=${PORT:-8096}
if [ "${1:-}" != "--serve-only" ]; then
  scripts/verso-paper.sh CLPPaper CLPPaperMain.lean docs/clp-paper docs/clp-paper.pdf
fi
case "${1:-}" in
  --open)
    echo "  pdf:       $PWD/docs/clp-paper.pdf"
    echo "  one page:  $PWD/docs/clp-paper/html-single/index.html"
    open docs/clp-paper.pdf
    open docs/clp-paper/html-single/index.html
    ;;
  --serve|--serve-only)
    test -f docs/clp-paper.pdf || { echo "nothing built yet: run without --serve-only"; exit 1; }
    pkill -f "http.server $PORT" 2>/dev/null || true
    ( cd docs && nohup python3 -m http.server "$PORT" --bind 127.0.0.1 >/dev/null 2>&1 & )
    sleep 1
    echo "  pdf:          http://127.0.0.1:$PORT/clp-paper.pdf"
    echo "  one page:     http://127.0.0.1:$PORT/clp-paper/html-single/"
    echo "  per section:  http://127.0.0.1:$PORT/clp-paper/html-multi/"
    echo "  stop:         pkill -f \"http.server $PORT\""
    ;;
esac
