#!/bin/sh
# WP12 Stage 0: run one decider batch under a hard deadline.  Every skip is
# reported by the timeout line itself.
set -u
DL=${DL:-300}
for spec in "$@"; do
  mode=${spec%%:*}
  fuel=${spec##*:}
  if [ "$mode" = "control" ]; then
    echo "=== control batch (deadline ${DL}s) ==="
    gtimeout "$DL" lake env lean --run _probe/r_stage0.lean control
  else
    echo "=== $mode fuel $fuel (deadline ${DL}s) ==="
    gtimeout "$DL" lake env lean --run _probe/r_stage0.lean "$mode" "$fuel"
  fi
  rc=$?
  if [ $rc -eq 124 ]; then echo "    TIMEOUT after ${DL}s -- SKIPPED, no verdict"; fi
  if [ $rc -ne 0 ] && [ $rc -ne 124 ]; then echo "    exit $rc"; fi
done
