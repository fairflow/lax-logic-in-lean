#!/bin/bash
# 100-cell batch: pll on each formula, 10 s wall each, artefacts into batch/.
# Checking is OFF (the default since 2026-09-03) — the verdicts are certified
# in-process by checkClosed; the emitted .lean files can be batch-checked later.
cd /Users/matthew/Lean/Sources/lax-logic-in-lean/LaxLogic/.claude/worktrees/intelligent-sanderson-cf631d
BIN=.lake/build/bin/pll
OUT=batch
: > $OUT/results.tsv
while IFS=$'\t' read -r n tag f; do
  [ -z "$n" ] && continue
  start=$(python3 -c 'import time;print(int(time.time()*1000))')
  res=$(perl -e 'alarm 10; exec @ARGV' -- $BIN "$f" --out=$OUT/cell$n --view=both 2>&1)
  code=$?
  ms=$(( $(python3 -c 'import time;print(int(time.time()*1000))') - start ))
  if [ $code -ne 0 ] && [ -z "$(echo "$res" | grep -E 'verdict')" ]; then
    verdict="TIMEOUT/ERR"; detail=$(echo "$res" | tail -1 | cut -c1-60)
  else
    verdict=$(echo "$res" | grep -oE 'verdict   [A-Z-]+' | awk '{print $2}')
    [ -z "$verdict" ] && verdict=$(echo "$res" | grep -oE 'NOT CLOSED' | head -1)
    [ -z "$verdict" ] && verdict="UNKNOWN"
    detail=$(echo "$res" | grep -E '^model|^term' | head -1 | cut -c1-80)
  fi
  norm=$(echo "$res" | grep '^normalised' | head -1 | sed 's/^normalised *//; s/   *(certified.*//')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$n" "$tag" "$f" "$verdict" "$ms" "$detail" "$norm" >> $OUT/results.tsv
  echo "$n $verdict ${ms}ms  $f"
done < $OUT/formulas.txt
