#!/bin/sh
# Run LaxLogic/QLL/CLPWolfram.lean: the CLP constraint solver backed by Wolfram
# through the Lean–Wolfram bridge (the sibling repository mathematica-in-lean).
# Local only: the bridge is put on LEAN_PATH here, not made a Lake dependency,
# so the library build never needs it.  Both repositories must pin the same
# toolchain and mathlib commit (checked below).  Bounded by a deadline.
set -eu
BRIDGE=${MATHEMATICA_IN_LEAN:-$HOME/Lean/mathematica-in-lean}
cd "$(dirname "$0")/.."
here=$(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])")
there=$(python3 -c "import json;print([p['rev'] for p in json.load(open('$BRIDGE/lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])")
[ "$here" = "$there" ] || { echo "mathlib commits differ: $here vs $there" >&2; exit 2; }
[ -f "$BRIDGE/.lake/build/lib/lean/Mathematica.olean" ] || { echo "build the bridge first (lake build in $BRIDGE)" >&2; exit 2; }
export MATHEMATICA_BRIDGE_KERNEL=${MATHEMATICA_BRIDGE_KERNEL:-/Applications/Wolfram14.app/Contents/MacOS/WolframKernel}
export MATHEMATICA_BRIDGE_LEANFORM="$BRIDGE/wolfram/lean_form.wl"
LP=$(lake env printenv LEAN_PATH)
TO=$(command -v gtimeout || command -v timeout || true)
LEAN_PATH="$LP:$BRIDGE/.lake/build/lib/lean" exec ${TO:+$TO ${CLP_WOLFRAM_DEADLINE:-900}} lean LaxLogic/QLL/CLPWolfram.lean
