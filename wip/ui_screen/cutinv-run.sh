#!/bin/sh
# cutinv-run.sh <stratum> <alarm seconds> <out file> [budgets...]
#
# Run one stratum of the `CutInv` screen (`lean_exe cutinvscreen`), one
# line per cell, appended to <out file>.  The binary is exec'd under
# `perl -e 'alarm N; exec @ARGV'`, never `lake exe`, so a cell that
# outruns the bound kills the process rather than the run: the script
# then RESUMES at the cell after the one that hung and records the skip
# as `TIMEOUT@<N>s`.  No cell is ever dropped silently.
set -u
ST="$1"; T="$2"; OUT="$3"; shift 3
BIN="$(cd "$(dirname "$0")/../.." && pwd)/.lake/build/bin/cutinvscreen"
[ -x "$BIN" ] || { echo "no binary at $BIN" >&2; exit 2; }
i=0
while : ; do
  tmp=$(mktemp)
  perl -e "alarm $T; exec @ARGV" -- "$BIN" "$ST" "$i" "$@" > "$tmp" 2>&1
  cat "$tmp" >> "$OUT"
  if grep -q "^# END" "$tmp"; then rm -f "$tmp"; break; fi
  last=$(grep -c '^[0-9]' "$tmp")
  if [ "$last" -eq 0 ]; then
    # not even one cell finished at index i: record the skip and step over it
    echo "$i	$ST	TIMEOUT@${T}s	-	-	-	-	cell exceeded the bound	(not evaluated)" >> "$OUT"
    i=$((i + 1))
  else
    done_to=$(grep '^[0-9]' "$tmp" | tail -1 | cut -f1)
    echo "$((done_to + 1))	$ST	TIMEOUT@${T}s	-	-	-	-	cell exceeded the bound	(not evaluated)" >> "$OUT"
    i=$((done_to + 2))
  fi
  rm -f "$tmp"
done
