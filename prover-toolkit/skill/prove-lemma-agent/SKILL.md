---
name: prove-lemma-agent
description: Prove a Lean 4 `sorry` yourself — you are the proving agent, with grep, whole-file reading and repeated `check` — using the prover toolkit for corpus search, goal states and axiom-checked verification. Use when asked to prove or close a `sorry` without spending on a hosted prover API, or when the goal needs judgement, repository context, or reading more than one file. NOT a measurement of `prove-lemma`: for that use `claude_shim.py`, which runs the real harness.
---

# prove-lemma-agent

**You are the proposer.** The toolkit supplies retrieval, goal states, and
verification; the mathematics is yours.

This is the alternative to `prove-lemma`, which hands the goal to a hosted
model through `ax-prover`. Use this one when the goal needs context a fixed
prompt cannot carry — a proof pattern established elsewhere in the repository,
a definition three files away, an argument the docstring only gestures at — or
simply when you would rather not spend per attempt.

Neither route is better in general. The API route is unattended and can grind
through many lemmas; this one is free per attempt and can bring judgement.

**This is not a cheap way of measuring `prove-lemma`.** The two share only the
index server — not the harness, not the prompt, not the sampling — and you here
are an agent with tools, so the numbers are not comparable in either direction.
To measure the harness cheaply, put Claude behind its endpoint with
`prover-toolkit/claude_shim.py`; see the toolkit README.

*(Named `prove-lemma-inloop` until 2026-09-02. Renamed because "in loop" read
as "the same thing, cheaply", which is exactly what it is not.)*

## Setup

```bash
# Optional: the config is found automatically by walking up from the
# working directory. Set it only to override.
export PROVER_TOOLKIT_CONFIG=/path/to/prover-toolkit/toolkit.json

# `index.jsonl` is derived data and git-ignored, so a FRESH WORKTREE has none
# and the server dies with FileNotFoundError. Build it first.
python3 prover-toolkit/leansearch/build_index.py
python3 prover-toolkit/leansearch/server.py &   # port comes from toolkit.json
curl -s localhost:$(python3 -c 'import sys;sys.path.insert(0,"prover-toolkit");from toolkit_config import find_config;print(find_config().index_port)')/health
```

Port 8080 may be a launchd service over a *different* corpus; always take the
port from the config, never assume it.

## The loop

**1. Read the goal as Lean sees it** — not as you imagine it from the source.

```bash
python3 prover-toolkit/toolkit_cli.py goals path/to/File.lean
```

**2. Find what already exists.** Nearly every proof in a mature development has
a precedent. Search before inventing.

```bash
python3 prover-toolkit/toolkit_cli.py search "p-bisimulation variant" -n 8
```

Then read the precedent properly with `Read` — the index gives you signatures
and a location, not the argument. Also `grep` for the definitions the goal
mentions; understanding what `force`, `Rᵢ`, or `⋏` actually *are* prevents the
commonest failure, which is treating an object-level constructor as if it were
Lean's own connective.

**3. Write the proof.** Edit the file directly, replacing `sorry`.

**4. Check it.** This is not optional and not the same as "it compiled".

```bash
python3 prover-toolkit/toolkit_cli.py check path/to/File.lean my_theorem
```

Reports compile errors, whether `sorryAx` survives, and which axioms the proof
rests on. Pass `--baseline propext,Quot.sound` to be told about anything beyond
a set you expect.

**5. Iterate** on the reported errors, from step 1.

## Reporting

State what was proved, what it depends on, and what you did not attempt. Quote
the axioms. If you gave up, say so plainly and say where it broke — a partial
result with an honest boundary is worth more than a proof you have not checked.

## Cautions

- **Never leave a `sorry` you have not flagged.** `check` catches it via
  `sorryAx`; report it as a failure, not a proof.
- An open conjecture may be open because it is **false**. If the argument will
  not close, consider looking for a countermodel before assuming you are
  missing a trick.
- Commit before editing, so `git diff` shows exactly what you changed.
- The axiom report is a change-detector, not a verdict. An axiom can enter
  through a library lemma rather than from mathematical need.
