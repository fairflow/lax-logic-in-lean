#!/bin/bash
# Like-for-like DP comparison, ONE ENGINE PER PROCESS, timed by the shell.
#
# Timing is NOT taken inside Lean: an in-process timer round a pure
# computation was optimised away (both branches of an `if` were equal, so
# the force was dead code and every cell read 0 ms, 2026-09-03).  The
# shell's wall clock round the whole process cannot be optimised away.
# Both engines pay the same process startup; STARTUP below measures it so
# it can be stated rather than pretended away.
cd /Users/matthew/Lean/Sources/lax-logic-in-lean/LaxLogic/.claude/worktrees/intelligent-sanderson-cf631d
LIM=${LIM:-20}
OUT=${OUT:-batch/bench.tsv}
BIN=.lake/build/bin/pllbench
now() { python3 -c 'import time;print(int(time.time()*1000))'; }

# Constant process startup: an empty cell selection does no logic work.
# Measure it WARM (the first load comes off disk and is ~15x slower) and
# take the minimum of several, so the figure is the floor every cell pays.
STARTUP=999999
for _ in 1 2 3 4 5; do
  s0=$(now); $BIN --cells=batch/formulas.txt --only=__none__ >/dev/null 2>&1; s1=$(now)
  d=$((s1-s0)); [ $d -lt $STARTUP ] && STARTUP=$d
done

echo "# pllbench: one engine per process, ${LIM}s wall cap each; process startup ~${STARTUP}ms (identical for both engines, NOT subtracted)" > $OUT
printf 'id\tclass\tformula\tfrjw\tfrjw_ms\tg4c\tg4c_ms\tnote\n' >> $OUT
while IFS=$'\t' read -r id cls f; do
  [ -z "$id" ] && continue
  run() { # $1 = engine
    local t0 t1 v
    t0=$(now)
    v=$(perl -e "alarm $LIM; exec @ARGV" -- $BIN --cells=batch/formulas.txt --only="$id" --engine="$1" 2>/dev/null | head -1 | cut -f3)
    t1=$(now)
    [ -z "$v" ] && v="timeout"
    echo "$v $((t1-t0))"
  }
  read -r fv fms <<< "$(run frjw)"
  read -r gv gms <<< "$(run g4c)"
  note=""
  if [ "$fv" != "timeout" ] && [ "$gv" != "timeout" ] && [ "$fv" != "$gv" ]; then
    note="*** DISAGREEMENT ***"
  elif [ "$fv" != "timeout" ] && [ "$gv" == "timeout" ]; then note="frjw decided, g4c did not"
  elif [ "$fv" == "timeout" ] && [ "$gv" != "timeout" ]; then note="g4c decided, frjw did not"
  elif [ "$fv" != "timeout" ] && [ "$fms" -lt "$gms" ]; then note="FRJW FASTER"
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$cls" "$f" "$fv" "$fms" "$gv" "$gms" "$note" >> $OUT
  printf '%s %-38s frjw=%-9s %6sms  g4c=%-9s %6sms %s\n' "$id" "${f:0:38}" "$fv" "$fms" "$gv" "$gms" "$note"
done < batch/formulas.txt
