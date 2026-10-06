#!/bin/bash
# Gates for claude_shim.py.  Run from anywhere:  bash prover-toolkit/test_claude_shim.sh
#
# Every gate here has been watched FAILING as well as passing: G3 was confirmed
# red by making answer_live ignore the command's exit status, and G2 by
# disabling BOTH cache reads -- disabling only the outer one leaves the
# fill-while-waiting re-check serving the cache, and the gate stayed green,
# which is exactly the sort of untested gate this file exists to avoid.
#
# No spend and no auth: the answer command is a stub.  Nothing here exercises a
# real `claude -p`; that needs a logged-in CLI and is a separate, manual check.
SHIM="$(cd "$(dirname "$0")" && pwd)/claude_shim.py"
PORT=8098
W=$(mktemp -d)
fail=0
ok(){ printf '  PASS  %s\n' "$1"; }
no(){ printf '  FAIL  %s -- %s\n' "$1" "$2"; fail=1; }

start(){ # start <workdir-suffix> <extra args...>
  D="$W/$1"; shift
  mkdir -p "$D"
  python3 "$SHIM" --port $PORT --workdir "$D" --killswitch "$D/STOP" "$@" \
      >"$D/out.log" 2>&1 &
  SHIMPID=$!
  for _ in $(seq 40); do
    curl -s -m 1 "localhost:$PORT/v1/models" >/dev/null 2>&1 && return 0
    sleep 0.25
  done
  echo "shim did not come up"; cat "$D/out.log"; return 1
}
stop(){ kill $SHIMPID 2>/dev/null; wait $SHIMPID 2>/dev/null; }

ask(){ # ask <prompt> -> prints "HTTPCODE<TAB>body"
  curl -s -m 60 -o "$W/body" -w '%{http_code}' \
    -H 'Content-Type: application/json' \
    -d "{\"model\":\"x\",\"messages\":[{\"role\":\"user\",\"content\":\"$1\"}]}" \
    "localhost:$PORT/v1/chat/completions"
}

echo "=== G1  live: a miss is answered by --answer-cmd, and cached ==="
start g1 --live --answer-cmd "sed -e 's/^/ECHO:/'"
c=$(ask "hello-one")
t=$(python3 -c "import json;print(json.load(open('$W/body'))['choices'][0]['message']['content'])" 2>/dev/null)
[ "$c" = 200 ] && [ -n "$t" ] && ok "200 with content: $(echo "$t"|head -1)" || no "live answer" "code=$c body=$(cat $W/body)"
ls "$W/g1/answers/"*.txt >/dev/null 2>&1 && ok "answer written back to answers/" || no "write-back" "no file"
grep -q '"event": "live_ok"' "$W/g1/ledger.jsonl" && ok "ledger records live_ok" || no "ledger" "no live_ok"
# the role tagging must reach the command
grep -q '<<<user>>>' "$W/g1/answers/"*.txt && ok "roles rendered to the command" || no "role render" "missing"
stop

echo "=== G2  cache replay: same prompt, fresh shim, NO command run ==="
start g2 --live --answer-cmd "sed -e 's/^/FIRST:/'"
ask "replay-me" >/dev/null; stop
start g2 --live --answer-cmd "sed -e 's/^/SECOND:/'"   # same workdir, new cmd
ask "replay-me" >/dev/null
t=$(python3 -c "import json;print(json.load(open('$W/body'))['choices'][0]['message']['content'])")
case "$t" in FIRST:*) ok "served from cache, second command NOT run";;
             *) no "cache replay" "got: $(echo "$t"|head -1)";; esac
stop

echo "=== G3  answer-cmd fails -> 502, not a silent empty answer ==="
start g3 --live --answer-cmd "cat >/dev/null; echo boom >&2; exit 3"
c=$(ask "will-fail")
[ "$c" = 502 ] && grep -q 'exit 3' "$W/body" && ok "502 carrying the exit status" || no "502 on failure" "code=$c body=$(cat $W/body)"
ls "$W/g3/answers/"*.txt >/dev/null 2>&1 && no "no write-back on failure" "a file was written" || ok "nothing cached on failure"
stop

echo "=== G4  answer-cmd empty output -> 502 ==="
start g4 --live --answer-cmd "cat >/dev/null; true"
c=$(ask "silent"); [ "$c" = 502 ] && ok "502 on empty output" || no "empty output" "code=$c"
stop

echo "=== G5  timeout -> 502 ==="
start g5 --live --answer-timeout 2 --answer-cmd "cat >/dev/null; sleep 30"
c=$(ask "slow"); grep -q 'timed out' "$W/body" && [ "$c" = 502 ] && ok "502 timed out" || no "timeout" "code=$c body=$(cat $W/body)"
stop

echo "=== G6  request cap -> 429 (containment holds in live mode) ==="
start g6 --live --max-requests 2 --answer-cmd "sed -e 's/^/E:/'"
ask a >/dev/null; ask b >/dev/null; c=$(ask c)
[ "$c" = 429 ] && ok "3rd request refused at cap 2" || no "request cap" "code=$c"
stop

echo "=== G7  killswitch -> 429 ==="
start g7 --live --answer-cmd "sed -e 's/^/E:/'"
c=$(ask before); [ "$c" = 200 ] && ok "answers before killswitch" || no "pre-kill" "code=$c"
touch "$W/g7/STOP"
c=$(ask after); [ "$c" = 429 ] && ok "refuses after killswitch" || no "killswitch" "code=$c"
stop

echo "=== G8  oversize answer -> 413 ==="
start g8 --live --max-answer-bytes 50 --answer-cmd "cat >/dev/null; python3 -c \"print('x'*500)\""
c=$(ask big); [ "$c" = 413 ] && ok "413 over per-answer cap" || no "oversize" "code=$c"
stop

echo "=== G9  file rendezvous (--answer-cmd '') ==="
start g9 --live --answer-cmd "" --answer-timeout 30
( sleep 3
  p=$(ls "$W/g9/pending/"*.prompt.txt 2>/dev/null | head -1)
  k=$(basename "$p" .prompt.txt)
  echo "HAND-WRITTEN ANSWER" > "$W/g9/answers/$k.txt" ) &
c=$(ask rendezvous)
grep -q 'HAND-WRITTEN' "$W/body" && [ "$c" = 200 ] && ok "rendezvous answered by dropped file" || no "rendezvous" "code=$c body=$(head -c 200 $W/body)"
stop

echo "=== G10  non-live modes unchanged ==="
start g10a
c=$(ask legacy); [ "$c" = 503 ] && ok "default mode still 503 on a miss" || no "default" "code=$c"
stop
start g10b --collect
c=$(ask legacy); [ "$c" = 503 ] && ok "--collect still misses everything" || no "collect" "code=$c"
ls "$W/g10b/pending/"*.json >/dev/null 2>&1 && ok "--collect still harvests the prompt" || no "collect harvest" "none"
stop
python3 "$SHIM" --collect --live --port $PORT 2>&1 | grep -q exclusive && ok "--collect --live rejected" || no "exclusivity" "accepted"

echo "=== G11  a request offering tools is REFUSED, not silently degraded ==="
askt(){ curl -s -m 30 -o "$W/body" -w '%{http_code}' \
    -H 'Content-Type: application/json' \
    -d '{"model":"x","messages":[{"role":"user","content":"find a lemma"}],
         "tools":[{"type":"function","function":{"name":"leansearch",
                   "description":"search","parameters":{"type":"object"}}}]}' \
    "localhost:$PORT/v1/chat/completions"; }
start g11 --live --answer-cmd "sed -e 's/^/E:/'"
c=$(askt)
[ "$c" = 400 ] && grep -q leansearch "$W/body" && ok "400 naming the offered tool" || no "tools refusal" "code=$c body=$(head -c 200 $W/body)"
grep -q '"event": "tools_refused"' "$W/g11/ledger.jsonl" && ok "ledger records tools_refused" || no "ledger" "no tools_refused"
stop
start g11b --live --ignore-tools --answer-cmd "sed -e 's/^/E:/'"
c=$(askt); [ "$c" = 200 ] && ok "--ignore-tools answers anyway" || no "ignore-tools" "code=$c"
grep -q '"tools"' "$W/g11b/pending/"*.json && ok "harvest records the offered tools" || no "harvest tools" "absent"
stop

echo
[ $fail = 0 ] && echo "ALL GATES PASS" || echo "SOME GATES FAILED"
echo "workdir: $W"
exit $fail
