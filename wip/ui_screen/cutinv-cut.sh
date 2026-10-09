#!/bin/sh
# cutinv-cut.sh <alarm seconds> <out file> <premise budget> <conclusion budget>
#
# Stratum vi — the DIRECT `CutInv` screen: search both premises
# `Γ ⊢ N` and `N, Δ ⊢ⱼ ψ`, and only when both are found (each hit
# certified by `LSeq.search_sound`) search the conclusion
# `Γ, Δ ⊢ⱼ ψ`.  A `flag` here is a candidate refutation of `CutInv`
# itself, not merely of `PolInv`.  Same alarm-and-resume discipline as
# `cutinv-run.sh`.
set -u
T="$1"; OUT="$2"; PB="${3:-12}"; CB="${4:-16}"
BIN="$(cd "$(dirname "$0")/../.." && pwd)/.lake/build/bin/cutinvscreen"
[ -x "$BIN" ] || { echo "no binary at $BIN" >&2; exit 2; }
i=0
while : ; do
  tmp=$(mktemp)
  perl -e "alarm $T; exec @ARGV" -- "$BIN" --cut "$i" "$PB" "$CB" > "$tmp" 2>&1
  cat "$tmp" >> "$OUT"
  if grep -q "^# END" "$tmp"; then rm -f "$tmp"; break; fi
  n=$(grep -c '^[0-9]' "$tmp")
  if [ "$n" -eq 0 ]; then
    echo "$i	vi	TIMEOUT@${T}s	-	-	-	-	cell exceeded the bound	(not evaluated)" >> "$OUT"
    i=$((i + 1))
  else
    done_to=$(grep '^[0-9]' "$tmp" | tail -1 | cut -f1)
    echo "$((done_to + 1))	vi	TIMEOUT@${T}s	-	-	-	-	cell exceeded the bound	(not evaluated)" >> "$OUT"
    i=$((done_to + 2))
  fi
  rm -f "$tmp"
done
