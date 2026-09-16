#!/bin/sh
# Batch-pin FRJ(◯) search hits on RN(◯,{}) dictionary cells.
#
#   sh tools/rn-cert-gen.sh <hits-file> <outdir>
#
# <hits-file> has one "<cell> <fwd|-> <bwd|->" line per hit (as extracted
# from a `lake exe rnfrj` log).  For each hit direction this runs
# `lake exe rnpin`, which searches, extracts the model the derivation
# builds, minimises it, and prints it as a `Tab`.  The certificates land
# one per file in <outdir>; `tools/rn-cert-asm.py` assembles them into
# wip/rnFRJCerts.lean.
set -e
HITS=${1:-hits.txt}
OUT=${2:-certs}
mkdir -p "$OUT"
while read -r cell fwd bwd; do
  [ -z "$cell" ] && continue
  for d in "$fwd" "$bwd"; do
    case "$d" in
      fwd) arrow="→"; tag="fwd" ;;
      bwd) arrow="←"; tag="bwd" ;;
      *) continue ;;
    esac
    echo "pinning $cell $tag..." >&2
    .lake/build/bin/rnpin "$cell" "$arrow" 10 > "$OUT/$cell.$tag.txt" 2>&1
    grep -q "BEGIN CERTIFICATE" "$OUT/$cell.$tag.txt" || echo "  NO CERTIFICATE for $cell $tag" >&2
  done
done < "$HITS"
echo "done" >&2
