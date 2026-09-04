#!/bin/sh
# Focused kernel search on the cofinality instances at S1
# (docs/ui-ljfo-clause-table.md §4.12), one bounded process per cell.
# usage: esearch-run.sh <out.tsv> [bound-seconds]
# Cells: (delta, side) ∈ {(c,E), (X,E), (T,A), (c,A)} × eval fuel {12,16,20}
# × search fuel {16,32}.  A `true` is a derivation (search_sound); a
# `false` or an UNSETTLED certifies nothing.
OUT="$1"; T="${2:-900}"
BIN="$(dirname "$0")/../../.lake/build/bin/uifs"
: > "$OUT"
for spec in "c E" "X E" "T A" "c A"; do
  set -- $spec; delta="$1"; side="$2"
  for f in 12 16 20; do
    for sf in 16 32; do
      line=$(perl -e "alarm $T; exec @ARGV" -- "$BIN" esearch "$delta" "$side" "$f" "$sf" 2>&1 | grep "^esearch" | head -1)
      [ -z "$line" ] && line="esearch S1 delta=$delta side=$side evalfuel=$f sfuel=$sf UNSETTLED@${T}s"
      echo "$line" | tee -a "$OUT"
    done
  done
done
echo "DONE $(date '+%H:%M:%S')" | tee -a "$OUT"
