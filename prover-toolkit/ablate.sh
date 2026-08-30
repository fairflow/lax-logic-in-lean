#!/bin/sh
# Set up one condition of the retrieval ablation, and score the result.
#
# The experiment the toolkit's own README lists as NOT established: "whether
# the corpus index helps -- it is *used*, but never ablated".  Run every
# challenge twice, once with the index server up and once with it down, and
# compare.  With the server down `toolkit_cli.py search` fails and the loop
# degrades to `grep` plus whole-file reading, which is the honest control.
#
#   ./ablate.sh setup index      # server up
#   ./ablate.sh setup noindex    # server down
#   ./ablate.sh score <target> <index|noindex> <attempts> <searches> <cited>
#
# WHAT THIS SCRIPT DOES NOT DO: prove anything.  The proposer is an agent or a
# person, and the three counts above are self-reported by whoever ran the loop.
# A harness that could count them itself would have to be the proposer, which
# is the thing being measured.  Treat `attempts`, `searches` and `cited` as
# testimony; `closed` and `axioms` are checked.
set -e
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/.." && pwd)
port=$(cd "$repo" && python3 -c "import sys;sys.path.insert(0,'prover-toolkit');from toolkit_config import find_config;print(find_config().index_port)")
results="$repo/LaxLogic/ToolkitTest/ablation.jsonl"

case "$1" in
  setup)
    case "$2" in
      index)
        pkill -f "leansearch/server.py" 2>/dev/null || true
        sleep 1
        (cd "$repo" && nohup python3 prover-toolkit/leansearch/server.py \
            >/tmp/leansearch-ablate.log 2>&1 &)
        sleep 6
        curl -s --max-time 5 "localhost:$port/health" || {
          echo "server did not come up; run build_index.py first" >&2; exit 1; }
        echo "\ncondition: INDEX  (search available on $port)" ;;
      noindex)
        pkill -f "leansearch/server.py" 2>/dev/null || true
        sleep 1
        if curl -s --max-time 2 "localhost:$port/health" >/dev/null 2>&1; then
          echo "port $port still answering -- another server holds it" >&2; exit 1
        fi
        echo "condition: NOINDEX  (search unavailable; grep only)" ;;
      *) echo "usage: $0 setup index|noindex" >&2; exit 2 ;;
    esac ;;
  score)
    [ $# -eq 6 ] || { echo "usage: $0 score <target> <index|noindex> <attempts> <searches> <cited>" >&2; exit 2; }
    (cd "$repo" && python3 prover-toolkit/challenge.py score "$2") \
      | python3 -c "
import json,sys
d=json.load(sys.stdin)
d.update(condition='$3', attempts=int('$4'), searches=int('$5'),
         search_hits_cited=int('$6'))
print(json.dumps(d))" >> "$results"
    echo "recorded -> $results"
    tail -1 "$results" ;;
  *)
    echo "usage: $0 setup index|noindex" >&2
    echo "       $0 score <target> <index|noindex> <attempts> <searches> <cited>" >&2
    exit 2 ;;
esac
