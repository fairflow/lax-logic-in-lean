#!/usr/bin/env python3
"""An OpenAI-compatible `/v1/chat/completions` endpoint whose model is Claude Code.

Anything that speaks the OpenAI chat API can be pointed at this and will then be
driven by a Claude Code subscription rather than a metered API key.  Two callers
matter here:

  * `harness.py --url` — the ONE-SHOT harness.  Its prompt set is fixed in
    advance, so it can be served from a directory of pre-written answers.
  * **ax-prover** — the AGENTIC harness, via a config with
    `base_url: "http://127.0.0.1:8088/v1"`.  Its prompt *n+1* depends on its
    answer to *n*, so it CANNOT be pre-collected: it needs `--live`.

Three modes:

  --collect   every request MISSES: the prompt is written to `pending/` and an
              error is returned at once.  Harvests the exact prompts a caller
              builds.  NOT a measurement run.
  (default)   a request whose prompt is in `answers/` is served; a miss is an
              error.  Deterministic replay; spends nothing.
  --live      a hit in `answers/` is still served from cache; a MISS is answered
              by running `--answer-cmd` (default: a tool-free `claude -p`) with
              the prompt on stdin, and the answer is WRITTEN BACK to `answers/`
              so the same run replays offline afterwards.

Answers are keyed by sha256 of the prompt, so a served answer is provably the
answer to THAT prompt.

TOOL CALLS ARE NOT SUPPORTED, and a request carrying `tools` is REFUSED rather
than answered.  Answering it would degrade silently: langchain accepts a plain
text turn where it expected a tool call, does not error, and simply never uses
a tool -- so a tools-on run would look like an agent that found its tools
useless.  `--ignore-tools` downgrades the refusal to a warning if you want that
anyway.  Run the agentic caller tools-off instead (ax-prover:
`proposer_tools: {}` and a memoryless processor); that still exercises compiler
feedback, reviewer and retry, which is strictly more of the harness than the
one-shot route.

CONTAINMENT.  Four hard limits, all enforced here rather than reported:
`--max-requests`, `--max-answer-bytes`, `--max-total-bytes`, and a killswitch
file.  Exceeding any of them returns an error to the caller (recorded as a
failed sample) instead of blocking, so a runaway cannot spend anything.  In
`--live` mode answers are produced ONE AT A TIME under a lock, so the caps
cannot be raced past by concurrent requests.  Every request appends a line to
`ledger.jsonl`.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shlex
import subprocess
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

# A nested Claude Code that answers on behalf of a model must be a PURE TEXT
# COMPLETER: the agent loop belongs to the caller, not to it.  So every tool is
# denied and MCP config is skipped -- otherwise it would go off and act, slowly
# and unaccountably, inside a measurement run.
NO_TOOLS = ("Task Bash Glob Grep Read Edit Write NotebookEdit WebFetch "
            "WebSearch TodoWrite BashOutput KillShell SlashCommand Skill "
            "ExitPlanMode Artifact")
DEFAULT_ANSWER_CMD = (
    "claude -p --output-format text --model sonnet "
    "--strict-mcp-config --disallowed-tools " + shlex.quote(NO_TOOLS))


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()[:16]


def render(messages: list[dict]) -> str:
    """Role-tagged rendering, for what is actually SENT to the answer command.

    The cache key stays over the bare concatenation (see `do_POST`) so that
    adding live mode did not invalidate any previously collected answer.
    """
    out = []
    for m in messages:
        role = m.get("role", "user")
        out.append(f"<<<{role}>>>\n{m.get('content', '')}")
    return "\n\n".join(out)


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
        self.n_live = 0
        self.answer_bytes = 0
        self.t0 = time.time()
        # Guards the counters above: ThreadingHTTPServer means the cap check
        # and the increment must not interleave.
        self.lock = threading.Lock()
        # Serialises live answering: one nested Claude at a time.
        self.answer_lock = threading.Lock()

    def stopped(self) -> str | None:
        """Caller must hold self.lock."""
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
        rec["n_live"] = self.n_live
        rec["answer_bytes"] = self.answer_bytes
        with self.ledger.open("a") as fh:
            fh.write(json.dumps(rec) + "\n")
        sys.stderr.write(
            f"[shim] {rec.get('event')} {rec.get('key','')} "
            f"served={self.n_served} live={self.n_live} missed={self.n_missed} "
            f"req={self.n_requests}/{self.args.max_requests} "
            f"bytes={self.answer_bytes}/{self.args.max_total_bytes}\n")
        sys.stderr.flush()


def answer_live(st: State, key: str, nth: int, rendered: str) -> tuple[str | None, str]:
    """Obtain one answer.  Returns (text, why-if-None).

    Two routes.  `--answer-cmd CMD` runs CMD with the prompt on stdin and takes
    stdout as the completion.  `--answer-cmd ''` selects a FILE RENDEZVOUS
    instead: the prompt is written to `pending/`, and the shim waits for a human
    or another session to drop `answers/<key>-<nth>.txt`.  The rendezvous is the
    fallback for when no non-interactive Claude is available.
    """
    st.log({"event": "live_start", "key": key, "nth": nth,
            "prompt_bytes": len(rendered.encode())})
    t0 = time.time()

    if not st.args.answer_cmd.strip():
        target = st.answers / f"{key}-{nth}.txt"
        (st.pending / f"{key}-{nth}.prompt.txt").write_text(rendered)
        while time.time() - t0 < st.args.answer_timeout:
            if st.args.killswitch and Path(st.args.killswitch).exists():
                return None, "killswitch during rendezvous"
            if target.exists():
                return target.read_text(), ""
            time.sleep(2.0)
        return None, f"rendezvous timed out after {st.args.answer_timeout}s"

    try:
        proc = subprocess.run(
            st.args.answer_cmd, shell=True, input=rendered, text=True,
            capture_output=True, timeout=st.args.answer_timeout,
            cwd=st.args.answer_cwd)
    except subprocess.TimeoutExpired:
        return None, f"answer-cmd timed out after {st.args.answer_timeout}s"
    if proc.returncode != 0:
        return None, (f"answer-cmd exit {proc.returncode}: "
                      f"{(proc.stderr or '').strip()[:400]}")
    if not proc.stdout.strip():
        return None, f"answer-cmd produced no output; stderr: {(proc.stderr or '').strip()[:400]}"
    return proc.stdout, ""


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

        def _completion(self, key: str, body: dict, prompt: str, text: str) -> dict:
            return {
                "id": f"chatcmpl-{key}",
                "object": "chat.completion",
                "created": int(time.time()),
                "model": body.get("model", "claude-code"),
                # Tool calls are not expressible here; see the module docstring.
                "choices": [{"index": 0, "finish_reason": "stop",
                             "message": {"role": "assistant",
                                         "content": text}}],
                # Real byte counts; token counts are NOT available here and are
                # reported as null rather than invented.
                "usage": {"prompt_tokens": None, "completion_tokens": None,
                          "prompt_bytes": len(prompt.encode()),
                          "completion_bytes": len(text.encode())}}

        def do_GET(self) -> None:
            # Some OpenAI clients probe /v1/models before their first call.
            if self.path.rstrip("/").endswith("/v1/models"):
                self._json(200, {"object": "list", "data": [
                    {"id": "claude-code", "object": "model",
                     "owned_by": "claude_shim"}]})
                return
            self._json(404, {"error": {"message": "no such endpoint"}})

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

            messages = body.get("messages", [])
            tools = body.get("tools") or []
            if tools and not st.args.ignore_tools:
                names = [((t.get("function") or {}).get("name") or "?")
                         for t in tools if isinstance(t, dict)]
                st.log({"event": "tools_refused", "tools": names})
                self._json(400, {"error": {"message":
                    f"this endpoint cannot express a tool call, and {len(tools)} "
                    f"tool(s) were offered ({', '.join(names[:6])}). Answering "
                    "would silently produce a run in which no tool is ever "
                    "called. Run the caller tools-off, or pass --ignore-tools."}})
                return
            # Key over the bare concatenation, unchanged since the collect/serve
            # passes were written, so live mode invalidated no stored answer.
            prompt = "".join(m.get("content", "") for m in messages)
            key = sha(prompt)

            with st.lock:
                stop = st.stopped()
                if stop is None:
                    st.n_requests += 1
                    nth = st.seen.get(key, 0)
                    st.seen[key] = nth + 1
            if stop is not None:
                st.log({"event": "refused", "key": key, "why": stop})
                self._json(429, {"error": {"message": f"contained: {stop}"}})
                return

            (st.pending / f"{key}.json").write_text(json.dumps({
                "key": key, "model": body.get("model"),
                "temperature": body.get("temperature"),
                "max_tokens": body.get("max_tokens")
                              or body.get("max_completion_tokens"),
                "tools": [((t.get("function") or {}).get("name") or "?")
                          for t in tools if isinstance(t, dict)],
                "prompt": prompt}, indent=1))

            # k samples share a prompt, so the nth request for a key is served
            # the nth answer: the samples must be INDEPENDENT, not one cached
            # answer repeated k times.
            ans = st.answers / f"{key}-{nth}.txt"
            text: str | None = None
            if st.args.collect:
                pass
            elif ans.exists():
                text = ans.read_text()
            elif st.args.live:
                # One at a time: the caps are enforced per answer, and two
                # nested Claudes at once would race past them.
                with st.answer_lock:
                    if ans.exists():                      # filled while waiting
                        text = ans.read_text()
                    else:
                        text, why = answer_live(
                            st, key, nth, render(messages))
                        if text is None:
                            with st.lock:
                                st.n_missed += 1
                            st.log({"event": "live_fail", "key": key,
                                    "nth": nth, "why": why})
                            self._json(502, {"error": {"message": why}})
                            return
                        # Write back: the run replays offline from here on.
                        ans.write_text(text)
                        with st.lock:
                            st.n_live += 1
                        st.log({"event": "live_ok", "key": key, "nth": nth,
                                "bytes": len(text.encode())})

            if text is None:
                with st.lock:
                    st.n_missed += 1
                st.log({"event": "miss", "key": key, "nth": nth,
                        "mode": "collect" if st.args.collect else "run"})
                self._json(503, {"error": {"message": f"no answer for {key}"}})
                return

            if len(text.encode()) > st.args.max_answer_bytes:
                st.log({"event": "oversize", "key": key,
                        "bytes": len(text.encode())})
                self._json(413, {"error": {"message": "answer over cap"}})
                return

            with st.lock:
                st.n_served += 1
                st.answer_bytes += len(text.encode())
            st.log({"event": "served", "key": key, "nth": nth,
                    "bytes": len(text.encode())})
            self._json(200, self._completion(key, body, prompt, text))
    return H


def main() -> int:
    ap = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=__doc__)
    ap.add_argument("--port", type=int, default=8088)
    ap.add_argument("--workdir", default="runs/shim")
    ap.add_argument("--collect", action="store_true",
                    help="harvest prompts; every request misses")
    ap.add_argument("--live", action="store_true",
                    help="answer a cache miss by running --answer-cmd; "
                         "required for an AGENTIC caller such as ax-prover, "
                         "whose prompts cannot be collected in advance")
    ap.add_argument("--answer-cmd", default=DEFAULT_ANSWER_CMD,
                    help="shell command answering one prompt: prompt on stdin, "
                         "completion on stdout. Empty string selects a file "
                         "rendezvous instead (default: a tool-free claude -p)")
    ap.add_argument("--answer-cwd", default=".",
                    help="working directory for --answer-cmd")
    ap.add_argument("--answer-timeout", type=float, default=600.0,
                    help="seconds to allow one answer; the CALLER's own HTTP "
                         "timeout must exceed this")
    ap.add_argument("--ignore-tools", action="store_true",
                    help="answer a request offering tools anyway, as plain "
                         "text. The caller will then never call a tool and "
                         "will not be told why; off by default for that reason")
    ap.add_argument("--max-requests", type=int, default=32,
                    help="hard cap on requests served or missed")
    ap.add_argument("--max-answer-bytes", type=int, default=20000,
                    help="hard cap on a single answer")
    ap.add_argument("--max-total-bytes", type=int, default=400000,
                    help="hard cap on cumulative served answer bytes")
    ap.add_argument("--killswitch", default="runs/shim/STOP",
                    help="path whose existence refuses all further requests")
    args = ap.parse_args()
    if args.collect and args.live:
        sys.stderr.write("[shim] --collect and --live are exclusive\n")
        return 2
    st = State(args)
    srv = ThreadingHTTPServer(("127.0.0.1", args.port), handler_for(st))
    mode = "collect" if args.collect else ("live" if args.live else "run")
    sys.stderr.write(
        f"[shim] listening on 127.0.0.1:{args.port} "
        f"mode={mode} cap={args.max_requests} killswitch={args.killswitch}\n")
    if args.live:
        src = args.answer_cmd.strip() or "FILE RENDEZVOUS (drop answers/<key>-<nth>.txt)"
        sys.stderr.write(f"[shim] answer source: {src}\n")
    sys.stderr.flush()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
