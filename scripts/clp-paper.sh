#!/usr/bin/env bash
# The CLP paper (CLPPaper/): HTML + PDF into docs/ (both gitignored).
#
#   scripts/clp-paper.sh                build docs/clp-paper/{html-single,html-multi,tex} and docs/clp-paper.pdf
#   scripts/clp-paper.sh --serve        ...then serve docs/ on http://127.0.0.1:8096/
#   scripts/clp-paper.sh --serve-only   serve what is already built, no build
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
