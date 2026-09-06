#!/usr/bin/env bash
# Render the Verso paper locally.  Publishes nothing.
#
# NOT part of the default build: the LaxPaper lean_lib is the only target that
# pulls verso into the import graph, and it is absent from defaultTargets, so
# an ordinary `lake build` never touches it.
#
# Two flags matter and both were learned the hard way.
#
#   --depth 1   Without it the renderer splits at EVERY heading, so a section
#               page becomes a bare table of contents and the prose is one more
#               click away.  At depth 1 each section is one page.
#
#   --with-html-single   A single-page version, which is what a paper wants for
#               reading straight through.
#
# The output directory is REMOVED first: the renderer does not clean it, so
# pages from a previous run with different settings survive and are served
# alongside the new ones.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build LaxPaper
rm -rf _out/paper
lake lean LaxPaperMain.lean -- --run LaxPaperMain.lean --output _out/paper \
  --depth 1 --with-html-single "$@"
test -f _out/paper/html-multi/index.html
test -f _out/paper/html-single/index.html
echo "paper (one page):   _out/paper/html-single/index.html"
echo "paper (per section): _out/paper/html-multi/index.html"
