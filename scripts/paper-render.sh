#!/usr/bin/env bash
# Render the Verso paper locally, and serve it.  Publishes nothing.
#
# NOT part of the default build: the LaxPaper lean_lib is the only target that
# pulls verso into the import graph, and it is absent from defaultTargets, so
# an ordinary `lake build` never touches it.
#
# THE SITE MUST BE SERVED OVER HTTP, NOT OPENED AS A FILE.  Verso links a
# section as a directory (`The-machinery/`), which a web server resolves to that
# directory's `index.html` but a `file://` URL resolves to a DIRECTORY LISTING.
# Opening `_out/paper/html-multi/index.html` therefore appears to work and then
# lands on a bare file index at the first click.  That is why this script starts
# a server rather than telling you a path.
#
# On splitting.  The renderer splits at every heading, so each subsection gets
# its own page and each section page carries that section's LEAD PROSE plus
# links to its subsections.  A section with no lead prose therefore renders as a
# bare table of contents -- which is what "the links resolve to index pages"
# means.  The fix is prose, not `--depth`: every section file here has a lead
# paragraph between its `#doc` line and its first heading.  Keep it that way.
#
#   --with-html-single   A single-page version, for reading straight through.
#
# The output directory is REMOVED first: the renderer does not clean it, so
# pages from a previous run with different settings survive and are served
# alongside the new ones.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
PORT_MULTI=${PORT_MULTI:-8099}
PORT_SINGLE=${PORT_SINGLE:-8098}

lake build LaxPaper
rm -rf _out/paper
lake lean LaxPaperMain.lean -- --run LaxPaperMain.lean --output _out/paper \
  --with-html-single
test -f _out/paper/html-multi/index.html
test -f _out/paper/html-single/index.html

# Restart the servers: their working directory was just deleted and recreated,
# so an old one serves nothing.
pkill -f "http.server $PORT_MULTI" 2>/dev/null || true
pkill -f "http.server $PORT_SINGLE" 2>/dev/null || true
( cd "$ROOT/_out/paper/html-multi"  && nohup python3 -m http.server "$PORT_MULTI"  >/dev/null 2>&1 & )
( cd "$ROOT/_out/paper/html-single" && nohup python3 -m http.server "$PORT_SINGLE" >/dev/null 2>&1 & )
sleep 1

echo
echo "  per section: http://127.0.0.1:$PORT_MULTI/"
echo "  one page:    http://127.0.0.1:$PORT_SINGLE/"
echo
echo "  (open those URLs, not the files -- file:// turns each section link into"
echo "   a directory listing)"
