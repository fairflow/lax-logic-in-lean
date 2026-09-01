#!/usr/bin/env python3
"""An OpenAI-compatible `/v1/chat/completions` endpoint whose model is Claude Code.

`harness.py --url` already points at a local endpoint — that is how it measures
local GGUF models — so nothing in the harness changes.  This serves that
endpoint from a directory of answers written by hand (in practice: by one fresh
Claude Code subagent per prompt, so the k samples are blind and independent).

Two passes:

  --collect   every request MISSES: the prompt is written to `pending/` and an
              error is returned at once.  Use this to harvest the exact prompts
              the harness builds.  NOT a measurement run.
  (default)   a request whose prompt is in `answers/` is served; a miss is an
              error.  This is the measured run.

Answers are keyed by sha256 of the prompt, so a served answer is provably the
answer to THAT prompt.

CONTAINMENT.  Three hard limits, all enforced here rather than reported:
`--max-requests`, `--max-answer-bytes`, and a killswitch file.  Exceeding any
of them returns an error to the harness (recorded as a failed sample) instead
of blocking, so a runaway cannot spend anything.  Every request appends a line
to `ledger.jsonl`.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()[:16]


class State:
    def __init__(self, args) -> None:
        self.args = args
        self.root = Path(args.workdir)
        self.pending = self.root / "pending"
        self.answers = self.root / "answers"
        self.ledger = self.root / "ledger.jsonl"
        for d in (self.pending, self.answers):
            d.mkdir(parents=True, exist_ok=True)
        self.n_requests = 0
        self.seen: dict[str, int] = {}
        self.n_served = 0
        self.n_missed = 0
        self.answer_bytes = 0
        self.t0 = time.time()

    def stopped(self) -> str | None:
        if self.args.killswitch and Path(self.args.killswitch).exists():
            return "killswitch present"
        if self.n_requests >= self.args.max_requests:
            return f"request cap reached ({self.args.max_requests})"
        if self.answer_bytes >= self.args.max_total_bytes:
            return f"answer-byte cap reached ({self.args.max_total_bytes})"
        return None

    def log(self, rec: dict) -> None:
        rec["t"] = round(time.time() - self.t0, 3)
        rec["n_requests"] = self.n_requests
        rec["n_served"] = self.n_served
        rec["n_missed"] = self.n_missed
        rec["answer_bytes"] = self.answer_bytes
        with self.ledger.open("a") as fh:
            fh.write(json.dumps(rec) + "\n")
        sys.stderr.write(
            f"[shim] {rec.get('event')} {rec.get('key','')} "
            f"served={self.n_served} missed={self.n_missed} "
            f"req={self.n_requests}/{self.args.max_requests} "
            f"bytes={self.answer_bytes}/{self.args.max_total_bytes}\n")
        sys.stderr.flush()


def handler_for(st: State):
    class H(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, *a):  # quiet
            pass

        def _json(self, code: int, body: dict) -> None:
            raw = json.dumps(body).encode()
            self.send_response(code)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)

        def do_POST(self) -> None:
            if not self.path.rstrip("/").endswith("/v1/chat/completions"):
                self._json(404, {"error": {"message": "no such endpoint"}})
                return
            n = int(self.headers.get("Content-Length", 0))
            try:
                body = json.loads(self.rfile.read(n) or b"{}")
            except json.JSONDecodeError:
                self._json(400, {"error": {"message": "bad json"}})
                return

            prompt = "".join(
                m.get("content", "") for m in body.get("messages", []))
            key = sha(prompt)

            stop = st.stopped()
            if stop is not None:
                st.log({"event": "refused", "key": key, "why": stop})
                self._json(429, {"error": {"message": f"contained: {stop}"}})
                return

            st.n_requests += 1
            (st.pending / f"{key}.json").write_text(json.dumps({
                "key": key, "model": body.get("model"),
                "temperature": body.get("temperature"),
                "max_tokens": body.get("max_tokens")
                              or body.get("max_completion_tokens"),
                "prompt": prompt}, indent=1))

            # k samples share a prompt, so the nth request for a key is served
            # the nth answer: the samples must be INDEPENDENT, not one cached
            # answer repeated k times.
            nth = st.seen.get(key, 0)
            st.seen[key] = nth + 1
            ans = st.answers / f"{key}-{nth}.txt"
            if st.args.collect or not ans.exists():
                st.n_missed += 1
                st.log({"event": "miss", "key": key, "nth": nth,
                        "mode": "collect" if st.args.collect else "run"})
                self._json(503, {"error": {"message": f"no answer for {key}"}})
                return

            text = ans.read_text()
            if len(text.encode()) > st.args.max_answer_bytes:
                st.log({"event": "oversize", "key": key,
                        "bytes": len(text.encode())})
                self._json(413, {"error": {"message": "answer over cap"}})
                return

            st.n_served += 1
            st.answer_bytes += len(text.encode())
            st.log({"event": "served", "key": key, "nth": nth,
                    "bytes": len(text.encode())})
            self._json(200, {
                "id": f"chatcmpl-{key}",
                "object": "chat.completion",
                "model": body.get("model", "claude-code"),
                "choices": [{"index": 0, "finish_reason": "stop",
                             "message": {"role": "assistant",
                                         "content": text}}],
                # Real byte counts; token counts are NOT available here and are
                # reported as null rather than invented.
                "usage": {"prompt_tokens": None, "completion_tokens": None,
                          "prompt_bytes": len(prompt.encode()),
                          "completion_bytes": len(text.encode())}})
    return H


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=8088)
    ap.add_argument("--workdir", default="runs/shim")
    ap.add_argument("--collect", action="store_true",
                    help="harvest prompts; every request misses")
    ap.add_argument("--max-requests", type=int, default=32,
                    help="hard cap on requests served or missed")
    ap.add_argument("--max-answer-bytes", type=int, default=20000,
                    help="hard cap on a single answer")
    ap.add_argument("--max-total-bytes", type=int, default=400000,
                    help="hard cap on cumulative served answer bytes")
    ap.add_argument("--killswitch", default="runs/shim/STOP",
                    help="path whose existence refuses all further requests")
    args = ap.parse_args()
    st = State(args)
    srv = ThreadingHTTPServer(("127.0.0.1", args.port), handler_for(st))
    sys.stderr.write(
        f"[shim] listening on 127.0.0.1:{args.port} "
        f"mode={'collect' if args.collect else 'run'} "
        f"cap={args.max_requests} killswitch={args.killswitch}\n")
    sys.stderr.flush()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
