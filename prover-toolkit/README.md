# ax-prover-cascade

*(directory name: `prover-toolkit`)*

A repository-independent toolkit for attempting Lean 4 goals with a language
model and **verifying the result properly**. Developed alongside
`lax-logic-in-lean` and published with it, but it depends on nothing in this
repository: point `toolkit.json` at any Lean project.

It is not a prover. The proving is done by
[ax-prover](https://github.com/Axiomatic-AI/ax-prover-base); this supplies the
parts that make its output trustworthy on a bespoke development.

The name is for the shape that came out of the field test below: retrieval is
not one lookup but a **cascade of three gates** over a private corpus, each
narrower and more expensive than the last, with an axiom check at the end.

## What it adds

**A corpus index.** ax-prover's `LeanSearch` tool searches *Mathlib*. For a
development with its own notation and inductive types that is the wrong corpus.
`leansearch/` serves the same API over your declarations — including **notation
as first-class entries**, because a model trained on Mathlib does not otherwise
know that `⋏` is a constructor of your formula type rather than Lean's
conjunction.

**An axiom gate.** ax-prover checks that a proof compiles and has no `sorry`.
It does not check axioms. `constructive_prove.py` compares against the axioms
of the proof being replaced and flags a **strict superset**, so a proof that
introduces a dependency the previous one did not have is surfaced rather than
silently accepted. Whether that baseline is the *right* standard is an open
question: it records what an existing proof happens to rest on, which is not
the same as what the statement requires.

**A paranoid checker.** `verify.py` splices the model's proof under the
benchmark's verbatim statement, so a weakened goal cannot score; catches
`sorry` via `#print axioms` rather than grep, so a `sorry` reached through a
helper is caught too; and rejects `native_decide`. It self-tests in both
directions — every ground-truth proof must replay, and six negative controls
must be rejected.

**A cost model.** `theorem_cost_model.py` reports cost per *verified theorem*
with Wilson intervals, not cost per token. The two disagree: in testing a model
costing 5× less per token proved 8% of attempts against another's 62%.

## The cascade

Retrieval runs as three gates, cheapest first. The point is that gate 1 is
paid for every candidate and gates 2-3 only for survivors, so the context a
proof attempt carries is the *judged* subset rather than everything that
matched.

| gate | command | returns | cost |
|---|---|---|---|
| 1 | `toolkit_cli.py search "<query>"` | names, signatures, **constructor lists**, docstrings | ~1 line/hit |
| 2 | (judgement — no tool) | which hits are worth opening | free |
| 3 | `toolkit_cli.py source <name>` | the declaration's body | tens of lines |
| — | `toolkit_cli.py check <file> <lemma>` | closed? on which axioms? | a Lean run |

Gate 1 indexes inductives, structures and classes **whole**, with their
constructor names lifted into a `constructors` field. That is the one thing
this index can report as an *absence*: "there is no rule of this shape" is
decidable from a complete constructor list and from nothing else retrieval
returns, and it is the question a stuck campaign turns on. Sorried
declarations are dropped from the corpus — a `sorry` asserts its statement, so
offering one as an available lemma presents an OPEN conjecture as a proved
one.

Measured on the FRJX campaign, four arms over the same eight open goals, same
model, same budget (`../docs/frjx-round3-three-arms.md`):

| arm | retrieval | goals closed | context consumed |
|---|---|---|---|
| A | none | 2/8 | — |
| B | gate 1 only | 4/8 | small |
| C | free `grep` of the sources | 4/8 | 3,625 lines |
| C′ | the full cascade | **6/8** | **413 lines** |

So on this one campaign the cascade closed the most goals on ~13× less
context than reading the sources directly. One arm, one development: it is
evidence, not a result.

## Setup

```bash
export AX_PROVER_HOME=~/src/ax-prover-base       # your ax-prover checkout
python3 prover-toolkit/leansearch/build_index.py    # required on a FRESH worktree
python3 prover-toolkit/leansearch/server.py &      # port comes from toolkit.json
python3 prover-toolkit/extract.py --config prover-toolkit/corpora/laxlogic.json \
        -o prover-toolkit/corpora/items.jsonl
```

`toolkit.json` in the project root holds every path; nothing is hardcoded. See
the docstring in `toolkit_config.py`.

## Two Claude Code skills

There are two routes, and they are not ranked. Install either or both:

```bash
cp -r prover-toolkit/skill/prove-lemma       ~/.claude/skills/   # hosted API, costs money
cp -r prover-toolkit/skill/prove-lemma-agent ~/.claude/skills/   # Claude proves it, with tools
```

- **`prove-lemma`** hands the goal to a hosted model through `ax-prover`. It is
  unattended and can grind through many lemmas; it costs money per attempt.
- **`prove-lemma-agent`** puts Claude in the proposer seat and uses the
  toolkit only for retrieval, goal states and verification. Free per attempt,
  and it can bring repository context a fixed prompt cannot carry. **Start
  here:** [`USING-THE-SKILL.md`](USING-THE-SKILL.md).

**`prove-lemma-agent` is not a cheap way of measuring `prove-lemma`**, and it
was never wired to be. The two share only the index server — not the harness,
not the prompt, not the sampling — and the in-loop skill is an agent with
tools, which greps, reads whole files and iterates against `check`. Its numbers
are not comparable with a one-shot hosted prover in either direction. For a
cheap measurement of the harness itself, use `claude_shim.py`: same harness,
same prompt, same retrieval, Claude behind the endpoint. See
[Measuring the harness with Claude instead of a paid
API](#measuring-the-harness-with-claude-instead-of-a-paid-api) below.

The installed copies do **not** track this repository — re-run the `cp` after
changing anything under `skill/`.

## Measuring the ONE-SHOT harness with Claude instead of a paid API

**Read this first: there are two harnesses, and the shim serves only one.**

| | driver | what it is | shim? |
|---|---|---|---|
| one-shot | `harness.py` | builds a prompt from a fixed template, posts it to an OpenAI-compatible endpoint, verifies the completion | **yes** |
| agentic | `constructive_prove.py` → `$AX_PROVER_HOME/.venv/bin/ax-prover` | ax-prover's own agent loop, tools and reviewer | **no — not built** |

`harness.py` never invokes ax-prover; its single mention of it is in a `--help`
string. So the measurement table above separates *one-shot* rows from
*agentic (ax-prover)* for a reason, and **`claude_shim.py` can reproduce only
the one-shot rows.** Putting Claude behind ax-prover — so that the agentic
`12/13` could be replicated without paying for gpt-5 — is **NOT IMPLEMENTED**;
see "The ax-prover substitution" below.

`claude_shim.py` puts Claude Code in the seat of a hosted **one-shot** model, so
the same one-shot harness, prompt and retrieval are measured — only the model
behind the endpoint changes. `harness.py --url` already defaults to
`http://127.0.0.1:8088` because that is how it measures local GGUF models, so
**nothing in the harness changes**.

This is the cheap substitute for a `prove-lemma` run. It is *not* what
`prove-lemma-agent` does: that skill is an agent with tools — it greps, reads
whole files and iterates against `check` — so its results are not comparable
with a one-shot hosted prover in either direction. If you want to know how the
harness would score, use the shim; if you want a lemma closed, use the skill.

### Three modes

`--collect` and the default serve mode are a **two-pass batch protocol**:
harvest the prompts, answer them, serve them. That works only when the
prompt set is fixed in advance, which is true of `harness.py` and false of
any agent loop. `--live` is the third mode, added for the latter; see "The
ax-prover substitution" below.

#### The two batch passes

Someone has to produce the answers between the passes. In practice that is one
fresh Claude Code subagent per prompt, which is what makes the k samples blind
and independent.

**Pass 1 — harvest the prompts.** Every request misses and is written to
`pending/`:

```bash
python3 prover-toolkit/claude_shim.py --collect &
python3 prover-toolkit/harness.py --items <items.jsonl> --out runs/pass1.jsonl \
    --model claude-code-opus-5 --url http://127.0.0.1:8088 -k 1 \
    --leansearch-url http://localhost:8081
```

Each `runs/shim/pending/<key>.json` holds the exact prompt the harness built,
`<key>` being the first 16 hex of its sha256.

**Pass 2 — answer, then serve.** Write each completion to
`runs/shim/answers/<key>-<n>.txt`, where `<n>` is the sample index from 0: the
*n*-th request for a prompt is served the *n*-th answer, so k samples are
independent rather than one answer repeated. Then run the shim without
`--collect` and re-run the same harness command. A miss is now an error, and
because answers are keyed by hash of the prompt, a served answer is provably
the answer to *that* prompt.

### Containment

Enforced by the shim, not merely reported — exceeding a limit returns an error
the harness records as a failed sample, so a runaway cannot spend anything.

| flag | default | |
|---|---|---|
| `--max-requests` | 32 | total requests served |
| `--max-answer-bytes` | 20000 | per answer |
| `--max-total-bytes` | 400000 | across the run |
| `--killswitch` | `runs/shim/STOP` | create the file to stop at once |
| `--port` | 8088 | matches `harness.py --url` |
| `--workdir` | `runs/shim` | holds `pending/`, `answers/`, `ledger.jsonl` |
| `--live` | off | answer a miss by running `--answer-cmd` |
| `--answer-cmd` | a tool-free `claude -p` | prompt on stdin, completion on stdout; `''` selects a file rendezvous |
| `--answer-cwd` | `.` | working directory for that command |
| `--answer-timeout` | 600s | per answer; the **caller's** HTTP timeout must exceed it |
| `--ignore-tools` | off | answer a tool-offering request anyway, as plain text |

Every request appends to `ledger.jsonl`. `runs/` is git-ignored.

Two runs done this way are recorded in
[`../docs/frjx-toolkit-run-1.md`](../docs/frjx-toolkit-run-1.md) and
[`run-2`](../docs/frjx-toolkit-run-2.md). The benchmark items they used are
derived data and are not committed — regenerate with `extract.py`.

### The ax-prover substitution — live mode BUILT, tool calls NOT

The standing requirement is to run **ax-prover itself** with Claude Code as its
model, so the agentic harness is tested without spending on gpt-5. Two of the
three pieces now exist.

**1. Pointing ax-prover at the shim — SOLVED, no code.** ax-prover accepts an
OpenAI-compatible endpoint, and `8088` is already the shim's default port. A
ready config is committed at
[`axprover/claude-shim-toolsoff.yaml`](axprover/claude-shim-toolsoff.yaml);
copy it into `ax-prover-base/configs/`, since `import:` resolves relative to
that directory.

**2. The live mode — BUILT.** `--live` blocks on a cache miss, runs
`--answer-cmd` with the prompt on stdin, and returns its stdout as the
completion. The answer is written back to `answers/<key>-<n>.txt`, so the run
**replays offline afterwards for free** and a re-run spends nothing. The
default answer command is a nested, tool-free `claude -p`: the agent loop
belongs to ax-prover, so the nested Claude must be a pure text completer, and
every tool is denied to it. `--answer-cmd ''` instead selects a **file
rendezvous** — the prompt lands in `pending/`, and the shim waits for anyone to
drop the answer file — which is the fallback when no non-interactive Claude is
available.

All four containment limits hold in live mode, and answers are produced one at
a time under a lock so concurrent requests cannot race past a cap. Gates in
[`test_claude_shim.sh`](test_claude_shim.sh) (17, no spend, stub answerer):

```bash
bash prover-toolkit/test_claude_shim.sh      # ALL GATES PASS
```

**3. Tool calls — NOT DONE, and this is the real work.** The shim always
returns `finish_reason: "stop"` with a text message. A faithful substitution
needs it to pass the request's `tools` through to whoever answers and to return
`tool_calls` with `finish_reason: "tool_calls"`. Until then, run tools-off.

A request that *offers* tools is therefore **refused with a 400**, not
answered. Measured, not assumed: with tools bound and the shim answering,
langchain does not error — it takes the plain text turn, reports
`tool_calls: []`, and the loop simply never calls a tool. A tools-on run would
have looked like an agent that found its tools useless. `--ignore-tools`
restores that behaviour for anyone who wants it; the refusal names the offered
tools and reaches the caller as an `OpenAIInvalidRequestError` carrying the
reason.

The endpoint is checked against the clients that will actually use it: the
`openai` SDK (`ChatCompletion` parses, `finish_reason` `stop`, `tool_calls`
`None`) and `langchain_openai.ChatOpenAI`, which ax-prover reaches it through
(`AIMessage`, and the null token counts are coerced to 0 rather than raising).

#### Running it, tools off

```bash
# terminal 1
python3 prover-toolkit/claude_shim.py --live --max-requests 40

# terminal 2, from ax-prover-base
ax-prover --config configs/claude-shim-toolsoff.yaml \
    prove LaxLogic/Foo.lean:my_theorem --folder <repo>
```

Tools-off still exercises compiler feedback, the reviewer and retry across
iterations — strictly more of the harness than `harness.py` tests, and the part
that has never been measured for free.

#### Two things block an actual run, neither of them design

- **`ax-prover` is not installed here.** Not on `PATH`, and nothing named
  `ax-prover*` under `~` to depth 6 (checked 2026-09-05). The configs staged
  elsewhere are configs, not a checkout.
- **The standalone `claude` CLI cannot authenticate.** `claude -p` exits with
  *"OAuth session expired and could not be refreshed"*. This is not a sandbox
  effect — it fails unsandboxed too. The desktop app refreshes its token via
  the host rather than through the Keychain copy the CLI reads, so a session
  running inside the app is authenticated while the CLI beside it is not. Fix
  by signing the CLI in once from a terminal. Until then, use
  `--answer-cmd ''` and answer by hand, or point `--answer-cmd` at any other
  command that reads a prompt and prints a completion.

Configuring ax-prover with an *Anthropic* model is already possible and is not
this requirement: it bills `ANTHROPIC_API_KEY`. The point of the shim is to
spend a Claude Code subscription instead.

## Known limitations

- **Mathlib cannot currently be used as a benchmark corpus.** Extraction works
  by prefix truncation — the file up to the target statement — which does not
  compose with Lean's new module system (`module` / `public import`). 99% of
  Mathlib now uses it; the 82 files that do not are tactic infrastructure with
  no usable theorems. Fixing this needs a different extraction strategy for
  library files, and is not done.
- The extractor mis-handles equation-compiler declarations (`| pat => rhs`)
  with no top-level `:=`, silently producing a malformed file. Validate that a
  generated file compiles with exactly one `sorry` before trusting it.
- The axiom gate has **no baseline for a genuinely open goal**, and falls back
  to accepting anything `sorry`-free. Check such proofs by hand.
- **The retrieval ablation has not been run on the fixtures.** `ablate.sh`
  sets up both conditions and `challenge.py retrieval-check` measures the half
  that needs no agent, but the with/without comparison over the challenge set
  needs an agent per target per condition and has not been done. It *has* been
  run once on a live campaign, four arms over eight open goals — the table
  under "The cascade" above. That is one development and one model.
- `exclude` entries in `toolkit.json` are matched as single **path
  components**, not relative paths; a path-shaped entry warns since 2026-08-30
  but still matches nothing.
- `corpora/items.jsonl` is derived data and not committed. If it is missing the
  gate warns and degrades; rebuild it with `extract.py`.

## What was measured

Small samples, one corpus, no controlled comparisons. Indicative only.

| setting | verified |
|---|---|
| one-shot, Goedel-Prover-V2-8B (local) | 6/46 |
| one-shot, gpt-4o-mini | 6/72 |
| one-shot, gpt-5 | 15/24 |
| agentic (ax-prover), gpt-5 | 12/13 |

Reasonably supported: general capability beat Lean-specific training; the
agentic loop beats one-shot on harder lemmas; ~97% of an agentic round is model
thinking, not Lean (6 s of 145 s).

A first bound on the index's usefulness, from
`challenge.py retrieval-check` over the five-target challenge set: of 22
external citations the targets need, **12 are off-corpus** (Lean core and
Mathlib, which this index does not cover), and of the 10 in-corpus ones a
statement-shaped query surfaces **2 at k=10**. For that set the index has
little to offer, and it is an absence problem rather than a ranking one.

**Not** established: any ranking between models run on different lemmas, or
anything beyond this one development. Whether the corpus index helps was open
here until the FRJX field test; the four-arm table above is the only
measurement, and it is n=1. One hypothesis was tested and **refuted**:
truncating the prompt context was *not* suppressing one-shot results.

## The challenge set

`challenge.py` builds a challenge set from the corpus that is not a
walkthrough ending at the answer. The first set was bare prefix truncation,
which guarantees that everything the ground-truth proof used sits above the
cut; of its four files, one had its answer in a sibling file and two more had
every ingredient in the prefix.

```bash
python3 prover-toolkit/challenge.py report                       # filter verdicts
python3 prover-toolkit/challenge.py build --punch -o LaxLogic/ToolkitTest/Challenge
python3 prover-toolkit/challenge.py score <target>               # closed? on what axioms?
python3 prover-toolkit/challenge.py retrieval-check              # can the index deliver?
```

`--punch` writes a copy of each source module with its targets *deleted* under
`LaxLogic/ToolkitTest/Punched/`, and a short challenge file that imports it —
so the challenge can be read in full without learning anything. Build the
punched modules with `lake build ToolkitPunched`.

To start a campaign session on real work rather than the fixtures, use the
template in [`CAMPAIGN-KICKOFF.md`](CAMPAIGN-KICKOFF.md) — plan first, by hand,
then close the lemmas one at a time.

Rationale, filters and what testing them changed:
[`../docs/toolkit-test-design.md`](../docs/toolkit-test-design.md).

