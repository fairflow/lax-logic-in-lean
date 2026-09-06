#!/bin/sh
# WP10 Stage 0: run the designed cells at the given fuels, each under a
# hard deadline.  Every skip is reported by the timeout line itself.
set -u
DL=${DL:-300}
for spec in "$@"; do
  cellkey=${spec%%:*}
  fuel=${spec##*:}
  echo "=== $cellkey fuel $fuel (deadline ${DL}s) ==="
  gtimeout "$DL" lake env lean --run _probe/stage0.lean "$cellkey" "$fuel"
  rc=$?
  if [ $rc -eq 124 ]; then echo "    TIMEOUT after ${DL}s -- SKIPPED, no verdict"; fi
  if [ $rc -ne 0 ] && [ $rc -ne 124 ]; then echo "    exit $rc"; fi
done
