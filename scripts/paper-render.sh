#!/usr/bin/env bash
# Render the Verso paper locally.  Publishes nothing.
#
# NOT part of the default build: the LaxPaper lean_lib is the only target that
# pulls verso into the import graph, and it is absent from defaultTargets, so
# an ordinary `lake build` never touches it.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build LaxPaper
lake lean LaxPaperMain.lean -- --run LaxPaperMain.lean --output _out/paper "$@"
test -f _out/paper/html-multi/index.html
echo "paper: _out/paper/html-multi/index.html"
