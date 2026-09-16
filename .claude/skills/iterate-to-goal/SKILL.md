---
name: iterate-to-goal
description: Run a mechanisation campaign as a loop that converges on one stated goal — plan in Lean, screen the statements for refutation, close them with prove-lemma-inloop, report the denominator, re-frame from what the round found, repeat. Use when a proof effort is too large for one pass, when a goal needs many lemmas whose shapes are not yet known, or when asked to prove, mechanise or complete something that will take rounds rather than a sitting.
---

# Iterate to a goal

A campaign is not a long proof attempt. It is a **loop**: state, screen,
close, report, re-frame. Each turn of the loop ends with a smaller and
better-understood distance to the goal, or with a refutation that changes
the goal — and a refutation is a result, not a setback.

The loop terminates on one of four conditions, and naming which one it
was is part of the report:

| | |
|---|---|
| **closed** | the goal is proved, sorry-free, axioms pinned |
| **refuted** | the goal is false; the countermodel is the deliverable |
| **re-scoped** | a round forced a change the owner must approve (a rule change, a weakened statement) — HAND BACK, do not decide it yourself |
| **dry** | a round closed nothing new and refuted nothing new; say so and stop rather than grinding |

## The round

### 1. State the plan, in Lean, before proving anything

Every lemma and every main result of the round, in dependency order, with
`:= by sorry` bodies and a docstring on each. Three checkable
requirements: the file ELABORATES (zero errors, only `sorry` warnings);
every lemma carries a docstring saying what it is for; and **the
statements are surfaced to the owner before any proving begins**.

A `sorry`ed lemma ASSERTS its statement. That has two consequences the
loop must honour:

* **A refuted statement is DELETED, not left sorried.** Leaving it is an
  assertion of something known false — the worst thing the file can do.
* An `open` question gets no declaration at all. Status lives in prose or
  data, never in a sorried theorem.

### 2. Screen before you scope

Statement failures, not proof failures, are the recurring fault. Before
committing a round's proof effort, attack the statements:

* Pick the test point most likely to FAIL — the boundary, the degenerate
  case, the cell some existing result already nearly settles. Do not
  enumerate, and do not brute-force a countermodel search when one
  well-chosen instance would do.
* Look for the sharpest cell the repository ALREADY contains, and modify
  it minimally to reach your hypothesis. A cell that motivated an
  existing rule is usually one small change from refuting your statement.
* Screening that refutes a statement has saved the whole round. Screening
  that finds nothing costs one lemma's effort.

### 3. Close them, one at a time, with `prove-lemma-inloop`

Read `prover-toolkit/USING-THE-SKILL.md`, then work the cascade:

    search   what might help? — names, signatures, docstrings
    (judge)  discard on the signature; do NOT fetch what you can reject
    source   show me THAT one's body, and only that one
    check    compile and report axioms — the verification that matters

Field-tested over four arms on identical sources: nothing → 2 closed;
signatures only → 4; free whole-file reading → 4 at 3 625 lines of
context; the full cascade → **6 closed at 413 lines**. Discarding at gate
2 is where the economy lives — in that run ~30 of ~33 candidates were
rejected on signature alone.

Closed means: `lake env lean` reports zero errors AND `#print axioms`
shows no `sorryAx`. A `Classical.choice` in the pin is a DEFECT to
report, not a footnote — decidability is a consequence to be proved, not
a hypothesis to be filled in classically.

### 4. Report the denominator

*n* of *m* planned lemmas closed. For each closed one, its axioms. For
each unclosed one, **the goal you could not discharge**, not a summary.
Three of forty with an honest boundary is a result; the same run
described as progress is not.

Report the loop's own instruments too: how many searches, how many body
fetches, how many lines of context. Context, not tokens, is the binding
constraint, and a method that cannot show its context cost cannot be
compared with another.

### 5. Re-frame, and only then loop

The next round's plan is written FROM this round's findings, not from the
last plan with the closed lines struck out. A round that refutes a lemma
usually invalidates the argument that motivated its neighbours; re-derive
them rather than inheriting them.

## Standing rules for the whole loop

1. **Never change a statement to make it provable** without saying so
   prominently and separately. Weakening is legitimate; silent weakening
   is not.
2. **A rule change goes to the owner first**, as a displayed rule with
   its side conditions and its soundness obligation. Implementing it and
   asking afterwards is the failure this rule exists to prevent.
3. **No unused hypotheses.** A lemma with hypotheses its proof does not
   use is weaker than it should be, and "I will have them at the call
   site" is not a reason to keep them.
4. **Verify independently of any agent that reports to you.** Re-run the
   build, re-print the axioms, re-read the statement. Subagents report in
   good faith and are sometimes wrong.
5. **Leave the trail**: a dated section per round, the denominator, the
   refutations, and the named termination condition.

## Running rounds in parallel arms

When a round's method is itself in question, run it as arms from an
IDENTICAL start — same sources, same brief, same verifier, differing in
exactly one variable — and diff the outcomes. Two arms reaching the same
closed set independently is strong evidence the finding is real; two arms
reaching the same BLOCK independently is strong evidence the block is
structural rather than a proof-effort shortfall.

Keep the arms' directories out of any corpus index, or the answer is in
the corpus.

## The blind spot to design around

Retrieval returns presences. It cannot return an ABSENCE — "no rule of
this shape exists" is exactly what a campaign turns on when it is stuck,
and no query yields it. Fetch the whole inductive and do the case
analysis, or index types WITH their constructor lists so the absence is
visible inside a returned entry.
