#!/bin/zsh
# The nightly integrity build.
#
#     scripts/nightly-integrity.sh <checkout> <logdir>
#
# Matthew, 2026-10-28: "almost all the work we are doing is purely additive,
# ie we add a fresh set of files and then need to check them ... One build,
# preferably nightly, would be enough to check on integrity."  So agents build
# only the module they are developing, and this script builds EVERY library of
# a checkout once a night.  It is local: it runs on the machine, never on
# GitHub, and CI is unchanged.
#
# <checkout> is a dedicated worktree that the caller (a local launchd job) has
# already reset to origin/main.  This script reads git but never changes it.
#   1. It skips the run when the data volume has less than NIGHTLY_MIN_MB free
#      (default 30000): a full build writes fresh blocks for every module it
#      rebuilds, and on 2026-10-22 a full check filled the disk.
#   2. It builds every [[lean_lib]] of the checkout's lakefile.toml under
#      `nice` and `gtimeout` (NIGHTLY_TIMEOUT seconds, default 18000).  It
#      builds libraries only: linking the ~110 executables costs ~16 GB.
#   3. It runs scripts/check-ledger.sh if the checkout has it (0 clean,
#      1 REGRESSION, 2 stale, 3 broken).
#   4. It appends one row to <logdir>/summary.md and keeps the full log in
#      <logdir>/<repository>-<date>.log.  A failed build, a ledger regression
#      or a rise in `sorry` warnings posts a macOS notification.
# The exit code is the build's.
#
# The body is one { } block, which zsh parses whole before running it, so a
# checkout that replaces this file mid-run cannot change what is executing.
{
WT=${1:?usage: nightly-integrity.sh <checkout> <logdir>}
LOGDIR=${2:?usage: nightly-integrity.sh <checkout> <logdir>}
MIN_MB=${NIGHTLY_MIN_MB:-30000}
REPO=${WT:A:t}
DAY=$(date +%Y-%m-%d)
mkdir -p "$LOGDIR"
LOG="$LOGDIR/$REPO-$DAY.log"
SUM="$LOGDIR/summary.md"
if [[ ! -f "$SUM" ]]; then
  print -r -- "| date | repository | commit | build | minutes | errors | sorry warnings | ledger |" > "$SUM"
  print -r -- "|---|---|---|---|---|---|---|---|" >> "$SUM"
fi
COMMIT=$(git -C "$WT" rev-parse --short HEAD 2>/dev/null) || COMMIT="?"
print -r -- "nightly-integrity: $REPO @ $COMMIT, started $(date '+%Y-%m-%d %H:%M %Z')" > "$LOG"

row()    { print -r -- "| $DAY | $REPO | $COMMIT | $1 | $2 | $3 | $4 | $5 |" >> "$SUM" }
notify() { /usr/bin/osascript -e "display notification \"$1\" with title \"Nightly integrity\"" >/dev/null 2>&1 }

AVAIL=$(/bin/df -m /System/Volumes/Data | /usr/bin/awk 'NR==2 {print $4}')
if (( AVAIL < MIN_MB )); then
  print -r -- "SKIPPED: $AVAIL MB free, below $MIN_MB" >> "$LOG"
  row "skipped (disk: $AVAIL MB free)" - - - -
  notify "$REPO skipped: $AVAIL MB free"
  exit 0
fi

LIBS=( ${(f)"$(python3 -c '
import re, sys
text = open(sys.argv[1], "rb").read().decode("utf-8", "replace")
for block in re.finditer(r"\[\[lean_lib\]\]\n((?:[^\[\n][^\n]*\n|\n)*)", text):
    m = re.search(r"name\s*=\s*\"([^\"]+)\"", block.group(1))
    if m:
        print(m.group(1))
' "$WT/lakefile.toml")"} )
if (( ${#LIBS} == 0 )); then
  print -r -- "FAIL: no [[lean_lib]] parsed from $WT/lakefile.toml" >> "$LOG"
  row "FAIL (no libraries parsed)" - - - -
  notify "$REPO: no libraries parsed"
  exit 1
fi
print -r -- "libraries (${#LIBS}): ${LIBS[*]}" >> "$LOG"

T0=$SECONDS
nice -n 10 gtimeout "${NIGHTLY_TIMEOUT:-18000}" lake --dir "$WT" build "${LIBS[@]}" >> "$LOG" 2>&1
BRC=$?
MIN=$(( (SECONDS - T0) / 60 ))
case $BRC in
  0)   BUILD=ok ;;
  124) BUILD="TIMEOUT after $MIN min" ;;
  *)   BUILD="FAIL (exit $BRC)" ;;
esac

ERR=$(/usr/bin/grep -a -c '^error' "$LOG")
SOR=$(/usr/bin/grep -a -c 'declaration uses .sorry.' "$LOG")
PREV_FILE="$LOGDIR/.$REPO.sorry"
if [[ -f "$PREV_FILE" ]]; then
  PREV=$(<"$PREV_FILE")
  DELTA=$(( SOR - PREV ))
  (( DELTA > 0 )) && SORCELL="$SOR (+$DELTA)" || SORCELL="$SOR ($DELTA)"
else
  DELTA=0
  SORCELL="$SOR (first run)"
fi
(( BRC == 0 )) && print -r -- "$SOR" > "$PREV_FILE"

LEDGER="n/a"
if [[ -f "$WT/scripts/check-ledger.sh" ]]; then
  print -r -- "--- scripts/check-ledger.sh" >> "$LOG"
  /bin/bash "$WT/scripts/check-ledger.sh" >> "$LOG" 2>&1
  LRC=$?
  case $LRC in
    0) LEDGER=clean ;;
    1) LEDGER=REGRESSION ;;
    2) LEDGER="stale (an --update is owed)" ;;
    *) LEDGER="broken (exit $LRC)" ;;
  esac
fi

row "$BUILD" "$MIN" "$ERR" "$SORCELL" "$LEDGER"
print -r -- "finished $(date '+%Y-%m-%d %H:%M %Z'): build $BUILD, $MIN min, $ERR error lines, sorry warnings $SORCELL, ledger $LEDGER" >> "$LOG"
if (( BRC != 0 )) || [[ $LEDGER == REGRESSION || $LEDGER == broken* ]] || (( DELTA > 0 )); then
  notify "$REPO: build $BUILD, ledger $LEDGER, sorry warnings $SORCELL"
fi
exit $BRC
}
