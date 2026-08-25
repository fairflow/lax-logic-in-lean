#!/bin/sh
# Regenerate the scoped PLL Hasse diagram end to end:
#   sweep -> wip/rhocover_out.txt -> docs/rho-hasse-pll.svg
# Run whenever the order data changes (a new entry banked, a flag
# resolved, the catalogue extended).  The sweep carries its own control
# (the ρ6/ρ12 kernel theorem) and the drawer refuses a failed run.
set -e
cd "$(dirname "$0")/.."
lake build rhocover >&2
.lake/build/bin/rhocover "${1:-48}" > wip/rhocover_out.txt
python3 tools/rho-hasse-svg.py wip/rhocover_out.txt docs/rho-hasse-pll.svg
