#!/bin/sh
# Focused-search cofinality cells across the §4.12 stations.
# usage: esearch-stations.sh <out.tsv> [bound-seconds]
# Cells: station ∈ {S6, S7} × Δ = c × side ∈ {E, A} × eval fuel {16, 20} × search fuel 16.
OUT="$1"; T="${2:-900}"
BIN="$(dirname "$0")/../../.lake/build/bin/uifs"
: > "$OUT"
for st in S6 S7; do
  for side in E A; do
    for f in 16 20; do
      line=$(perl -e "alarm $T; exec @ARGV" -- "$BIN" esearch "$st" c "$side" "$f" 16 2>&1 | grep "^esearch" | head -1)
      [ -z "$line" ] && line="esearch $st delta=c side=$side evalfuel=$f sfuel=16 UNSETTLED@${T}s"
      echo "$line" | tee -a "$OUT"
    done
  done
done
echo "DONE $(date '+%H:%M:%S')" | tee -a "$OUT"
