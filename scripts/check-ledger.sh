#!/usr/bin/env bash
# The proof-status gate: regenerate the ledger from the built `.olean`s and
# compare it with the recorded one.
#
#     scripts/check-ledger.sh              # check; 0 clean, 1 regression, 2 stale
#     scripts/check-ledger.sh --update     # rewrite the record and the report
#     scripts/check-ledger.sh --built-only # check only the modules that are
#                                          # built here (for CI, which builds
#                                          # the default targets and no more)
#
# It reads what is BUILT.  Build first (`lake build`, plus any module of
# `docs/ledger-modules.txt` outside the default targets); a module in the list
# with no `.olean` makes the run fail rather than silently shrink the estate.
#
# Exit codes come from `scripts/ledger-diff.py`:
#   0  identical
#   1  REGRESSION — a new `sorryAx`, a new axiom, a new `native_decide` taint,
#      or a declaration that has vanished
#   2  STALE — additions or improvements only; regenerate with --update
#   3  the ledger could not be generated at all
set -uo pipefail
cd "$(dirname "$0")/.." || exit 3

MODS=docs/ledger-modules.txt
RECORD=docs/status-ledger.jsonl
REPORT=docs/status-ledger.md

TMP=$(mktemp -t ledger.XXXXXX) || exit 3
trap 'rm -f "$TMP"' EXIT

BUILT_ONLY=""
SCOPE=""
# `--built-only` is the CI mode, and in CI the checkout stamps every source
# newer than every cached `.olean`, so the mtime staleness proxy would fire on
# all of them.  Freshness there comes from `lake build` running in the same job.
if [ "${1:-}" = "--built-only" ]; then
  BUILT_ONLY="--built-only --no-stale-check"; SCOPE="--scope-fresh"
fi

python3 scripts/ledger-run.py "$MODS" "$TMP" $BUILT_ONLY || exit 3

if [ "${1:-}" = "--update" ]; then
  mv "$TMP" "$RECORD"
  # refresh the declared estate from what the record actually covers
  python3 -c "
import json, sys
mods = sorted({json.loads(l)['module'] for l in open('$RECORD', encoding='utf-8')})
open('$MODS', 'w', encoding='utf-8').write('\n'.join(mods) + '\n')
print(f'ledger: {len(mods)} modules recorded in $MODS')
" || exit 3
  trap - EXIT
  python3 scripts/ledger-report.py "$RECORD" "$REPORT" || exit 3
  echo "ledger: $RECORD and $REPORT updated"
  exit 0
fi

if [ ! -f "$RECORD" ]; then
  echo "ledger: no $RECORD recorded yet — run with --update" >&2
  exit 3
fi

python3 scripts/ledger-diff.py "$RECORD" "$TMP" $SCOPE
exit $?
