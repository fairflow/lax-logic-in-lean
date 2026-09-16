#!/bin/sh
# Run every cell TSV in $1 through the G4c oracle, one process per cell,
# each bounded by $2 seconds (exec of the binary, so the alarm kills it).
# Results (one line per cell) go to $1/results.tsv; unsettled cells are
# recorded as such, never dropped.
DIR="$1"; T="${2:-60}"
BIN="/Users/matthew/Lean/Sources/lax-logic-in-lean/LaxLogic/.claude/worktrees/intelligent-sanderson-cf631d/.lake/build/bin/pllbench"
: > "$DIR/results.tsv"
for f in "$DIR"/ctrl_*.tsv "$DIR"/suf_*.tsv; do
  name=$(basename "$f" .tsv)
  line=$(perl -e "alarm $T; exec @ARGV" -- "$BIN" --engine=g4c --cells="$f" 2>&1 | grep "^$name" | head -1)
  if [ -z "$line" ]; then line="$name	g4c	UNSETTLED@${T}s"; fi
  echo "$line" >> "$DIR/results.tsv"
done
echo "DONE $(date '+%H:%M:%S')" >> "$DIR/results.tsv"
