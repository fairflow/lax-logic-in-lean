#!/usr/bin/env bash
# The proof-status gate: regenerate the ledger from the built `.olean`s and
# compare it with the recorded one.
#
#     scripts/check-ledger.sh            # check; 0 clean, 1 regression, 2 stale
#     scripts/check-ledger.sh --update   # rewrite the record and the report
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

python3 scripts/ledger-run.py "$MODS" "$TMP" || exit 3

if [ "${1:-}" = "--update" ]; then
  mv "$TMP" "$RECORD"
  trap - EXIT
  python3 scripts/ledger-report.py "$RECORD" "$REPORT" || exit 3
  echo "ledger: $RECORD and $REPORT updated"
  exit 0
fi

if [ ! -f "$RECORD" ]; then
  echo "ledger: no $RECORD recorded yet — run with --update" >&2
  exit 3
fi

python3 scripts/ledger-diff.py "$RECORD" "$TMP"
exit $?
