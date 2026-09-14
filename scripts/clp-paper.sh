#!/usr/bin/env bash
# The CLP paper (CLPPaper/): HTML + PDF into docs/ (both gitignored).
#
#   scripts/clp-paper.sh            build docs/clp-paper/{html-single,html-multi,tex} and docs/clp-paper.pdf
#   scripts/clp-paper.sh --serve    ...and serve the HTML on http://127.0.0.1:8096 (one page) / :8097 (per section)
set -euo pipefail
cd "$(dirname "$0")/.."
scripts/verso-paper.sh CLPPaper CLPPaperMain.lean docs/clp-paper docs/clp-paper.pdf
if [ "${1:-}" = "--serve" ]; then
  pkill -f "http.server 8096" 2>/dev/null || true
  pkill -f "http.server 8097" 2>/dev/null || true
  ( cd docs/clp-paper/html-single && nohup python3 -m http.server 8096 >/dev/null 2>&1 & )
  ( cd docs/clp-paper/html-multi  && nohup python3 -m http.server 8097 >/dev/null 2>&1 & )
  sleep 1
  echo "  one page:    http://127.0.0.1:8096/"
  echo "  per section: http://127.0.0.1:8097/"
fi
