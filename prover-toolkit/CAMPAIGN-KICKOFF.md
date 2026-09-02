# Kickoff instruction — applying the toolkit to a live campaign

A template for starting a new session that will use `prove-lemma-agent` on real
work rather than on the benchmark fixtures. Fill in the four bracketed fields
and paste the whole thing as the session's first message.

The order matters. **The plan is written before any proving is attempted**, and
the plan is the part that is not delegated: it fixes the statements, and a wrong
statement costs more than a hard proof.

---

## The instruction

> **Campaign:** [NAME — e.g. "FRJW stage W3: the disprovability transfer"]
> **Branch:** [BRANCH — e.g. `frjw-dev`]
> **Plan file:** [PATH — e.g. `wip/frjw_w3_plan.lean`]
> **Goal:** [ONE SENTENCE — the main result the campaign is meant to reach]
>
> Work in your own worktree cut from that branch; do not work in the main
> checkout. Clone the build cache before building:
> `/bin/cp -Rc <repo-root>/.lake .lake`.
>
> ### Stage 1 — the plan, before any proving
>
> Write the plan file. It states, in Lean, **every lemma and every main result
> of the campaign, in dependency order, with `sorry` bodies**:
>
> ```lean
> /-- What this lemma is for, in one sentence. -/
> theorem step_one (…) : … := by
>   sorry
> ```
>
> Three requirements, all checkable:
>
> 1. **The file elaborates.** Every statement type-correct, every name in
>    scope, zero errors. Only `sorry` warnings. A plan that does not compile is
>    not yet a plan.
> 2. **Every lemma carries a docstring** saying what it is for. Retrieval here
>    is lexical BM25 over name, signature and docstring — a lemma with no
>    docstring is reachable only by a query that already contains its
>    identifiers, which is no help to whoever comes next.
> 3. **The statements are surfaced for review before Stage 2 begins.** Inline
>    them in full in your reply. Do not start proving on unreviewed statements.
>
> Be aware that a `sorry`ed lemma **asserts** its statement. Statement failures,
> not proof failures, are this development's recurring fault. If a lemma might
> be false, say so and look for a countermodel before proving anything that
> depends on it.
>
> ### Stage 2 — close them, one at a time
>
> Use the `prove-lemma-agent` skill. Read
> `prover-toolkit/USING-THE-SKILL.md` first; it has the setup, the three
> commands, and how to write a query the index can serve.
>
> ```bash
> python3 prover-toolkit/leansearch/build_index.py     # required in a fresh worktree
> python3 prover-toolkit/leansearch/server.py &
> python3 prover-toolkit/toolkit_cli.py goals  <plan.lean>
> python3 prover-toolkit/toolkit_cli.py search "<query>" -n 15
> python3 prover-toolkit/toolkit_cli.py check  <plan.lean> <lemma>
> ```
>
> You do **not** need one `sorry` per file. `goals` reports every open goal;
> `check` judges the named declaration alone and reports the others as still
> open. `check` passing means that lemma is closed *and* rests on nothing still
> open — `sorryAx` propagates through helpers — so any order is safe.
>
> Prefer the order of the plan anyway: a lemma proved before its dependencies
> tells you less.
>
> ### Stage 3 — report
>
> For each lemma: **closed or not**, its axioms, and if not closed, **where it
> broke** — the goal you could not discharge, not a summary. Give the
> denominator: *n of m planned lemmas closed*. Three of forty with an honest
> boundary is a result; the same run described as progress is not.
>
> Also report, because it is the thing being tested and nobody has measured it:
> how many `search` calls you made, and whether any search result was actually
> used in a proof that worked.
>
> **Do not**: mark an unproved lemma as `sorry`ed-but-fine, report `check`
> output you have not run, or leave a `sorry` unflagged. Verify independently of
> `check` before claiming a result: `lake env lean <file>` must show zero errors,
> and pin the axioms with `#print axioms <Namespace>.<lemma>`.

---

## Why this shape

**Plan first, by hand.** The toolkit's value is closing stated goals; it has no
opinion about whether a statement is worth proving or even true. Handing it an
unreviewed plan spends effort on the wrong things and can bank a false lemma.

**Docstrings in the plan.** 43% of this development's theorems have none, and
those are the ones retrieval cannot find. A campaign that writes them as it goes
leaves the corpus better than it found it.

**The denominator.** The first challenge set closed four of four, which sounded
like a result and was not — three of the four contained everything their proof
needed. A campaign that reports only its successes is unfalsifiable in the same
way.

**The search counts.** Whether the corpus index helps is listed as *not
established* in the toolkit's own README, and remains so. Live campaigns are the
cheapest place to find out, but only if someone records it.
