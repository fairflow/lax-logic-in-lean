#!/usr/bin/env bash
# Build the Verso Blueprint site.
#
# NOT part of the default build: the LaxBlueprint lean_lib is the only target
# that pulls verso into the import graph, and it is deliberately absent from
# defaultTargets.  Ordinary `lake build` never touches verso.
#
# We do NOT use `lake exe vbp build`: vbp derives its Lean target from the
# PACKAGE name, which here is `lax-logic`, not the blueprint library's root
# module.  This is the command vbp runs internally, per doc/GETTING_STARTED.md.
set -euo pipefail
lake build LaxBlueprint
lake lean LaxBlueprintMain.lean -- --run LaxBlueprintMain.lean --output _out/site "$@"
test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
echo "site: _out/site/html-multi/index.html"
