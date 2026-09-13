#!/usr/bin/env bash
# Render the CLP Verso paper locally, and serve it.  Publishes nothing.
#
# Mirrors scripts/paper-render.sh (read its header: the site must be served over
# HTTP, every section needs lead prose, declarations are attached with
# `(lean := ...)`).  NOT part of the default build: CLPPaper is absent from
# defaultTargets, so an ordinary `lake build` never touches verso.
#
#   --with-html-single   A single-page version, for reading straight through.
#
# The output directory is REMOVED first: the renderer does not clean it.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
PORT_MULTI=${PORT_MULTI:-8097}
PORT_SINGLE=${PORT_SINGLE:-8096}

lake build CLPPaper
rm -rf _out/clp-paper
lake lean CLPPaperMain.lean -- --run CLPPaperMain.lean --output _out/clp-paper \
  --with-html-single
test -f _out/clp-paper/html-multi/index.html
test -f _out/clp-paper/html-single/index.html

pkill -f "http.server $PORT_MULTI" 2>/dev/null || true
pkill -f "http.server $PORT_SINGLE" 2>/dev/null || true
( cd "$ROOT/_out/clp-paper/html-multi"  && nohup python3 -m http.server "$PORT_MULTI"  >/dev/null 2>&1 & )
( cd "$ROOT/_out/clp-paper/html-single" && nohup python3 -m http.server "$PORT_SINGLE" >/dev/null 2>&1 & )
sleep 1

echo
echo "  per section: http://127.0.0.1:$PORT_MULTI/"
echo "  one page:    http://127.0.0.1:$PORT_SINGLE/"
echo
echo "  (open those URLs, not the files -- file:// turns each section link into"
echo "   a directory listing)"
