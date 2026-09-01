#!/bin/sh
# Regenerate the version cells of TOOLS.md.
# Prints branch, HEAD, and `hash · date` of the last commit touching each
# registered tool path. Paste the output over the cells in TOOLS.md; a
# printed hash differing from the file means the register is stale.
cd "$(git rev-parse --show-toplevel)" || exit 1
echo "branch: $(git branch --show-current)"
echo "head:   $(git log -1 --format='%h · %ad' --date=short)"
echo
for p in \
  Rewrite \
  wip/ljfo_link.lean \
  LaxLogic/PLLSearch.lean \
  FRJ \
  LaxLogic/PLLCountermodelEmit.lean \
  LaxLogic/PLLSearchConf.lean \
  RNDB \
  tools/Cover.lean \
  tools/rho-hasse-svg.py \
  tools/Cert.lean \
  docs/rn-catalogue.html \
  Meta/Audit.lean \
; do
  printf '%-36s %s\n' "$p" "$(git log -1 --format='%h · %ad' --date=short -- "$p")"
done
