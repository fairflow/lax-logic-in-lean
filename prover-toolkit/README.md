# prover-toolkit

A repository-independent toolkit for attempting Lean 4 goals with a language
model and **verifying the result properly**. Developed alongside
`lax-logic-in-lean` and published with it, but it depends on nothing in this
repository: point `toolkit.json` at any Lean project.

It is not a prover. The proving is done by
[ax-prover](https://github.com/Axiomatic-AI/ax-prover-base); this supplies the
parts that make its output trustworthy on a bespoke development.

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
cp -r prover-toolkit/skill/prove-lemma        ~/.claude/skills/   # hosted API
cp -r prover-toolkit/skill/prove-lemma-inloop ~/.claude/skills/   # Claude proposes
```

- **`prove-lemma`** hands the goal to a hosted model through `ax-prover`. It is
  unattended and can grind through many lemmas; it costs money per attempt.
- **`prove-lemma-inloop`** puts Claude in the proposer seat and uses the
  toolkit only for retrieval, goal states and verification. Free per attempt,
  and it can bring repository context a fixed prompt cannot carry. **Start
  here:** [`USING-THE-SKILL.md`](USING-THE-SKILL.md).

The installed copies do **not** track this repository — re-run the `cp` after
changing anything under `skill/`.

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
- **The retrieval ablation has still not been run.** `ablate.sh` sets up both
  conditions and records results, and `challenge.py retrieval-check` measures
  the half that needs no agent, but the with/without-index comparison itself
  needs an agent per target per condition and has not been done. Until it is,
  "whether the corpus index helps" remains open — see below.
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

**Not** established: whether the corpus index helps — it is *used*, but never
ablated; any ranking between models run on different lemmas; or anything
beyond this one development. One hypothesis was tested and **refuted**:
truncating the prompt context was *not* suppressing one-shot results.\n
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

