# METHOD-F0.md — developing proof search and the F0 database

**DRAFT (spike S0, 2026-10-21).** A scaffold for Matthew to edit; §1 is his,
and nothing below binds until he has approved it.

`METHOD.md` answers a request for a proof: conjecture → statement → test →
proof.  This file covers the other kind of work: building **infrastructure
that answers questions** about F0 (the variable-free fragment of PLL,
formerly written RN(◯,∅)) and the low-variable fragments: the database
RNDB, the certified simp set, and the search tools that use them.  The risk
there is not a false theorem but **drift**: tools and data accumulating in
directions nobody chose.  Everything here is meant to make the work
steerable.

## 1 · The vision (Matthew)

*To be written by Matthew.  Prompts, to be deleted:*

- What is the F0 work for: which questions should be answerable, by whom
  (a reader, a proof, an agent), and how quickly?
- What does "systematic" mean here, as opposed to today's ad-hoc use?
- Which forms are the accepted representatives of the classes, and who may
  add one?
- What must never happen?
- What would count as success in three months?

## 2 · Invariants

1. **Every answer is certified or labelled unknown.**  A producer may be
   untrusted; a verdict may not.  A search that finds nothing is no verdict
   (the G4c failure memo, #70, is the lesson); a negative answer is a
   countermodel certificate.
2. **Data in a database, truth in the kernel.**  Every row of RNDB carries a
   Lean certificate that the kernel checks in CI.  Any index, export or
   query layer is derived from the rows and is never the authority.
3. **Coverage is measured, never assumed.**  F0 is PROVED infinite, so no
   finite table closes.  Exhaustion over known classes refutes only
   relative to those classes, and is reported with that scope.
   Completeness of a tool is claimed only when proved.
4. **Identities are append-only.**  Entry ids, q-indices and ρ-indices never
   change meaning.  A superseded row is marked as superseded, never deleted.
5. **The accepted forms are a decision.**  The list of class
   representatives is fixed by Matthew (gate G3).  Changing it is a
   decision, not a refactor.
6. **Private stays private.**  Results developed in the private repository
   enter the public database only when Matthew releases them.

## 3 · Steering gates

| | Gate | Decided by Matthew before … |
|---|---|---|
| G1 | vision and scope | any campaign under this file (§1) |
| G2 | statements | any proof, checker specification or certifier (lean-certify R10) |
| G3 | accepted forms and keys | any tool that maps formulas to classes |
| G4 | comparison design | any engine comparison: the designed cells, budgets and measures are fixed *before* the runs, so the comparison is fair |
| G5 | supersession | any tool or data set that replaces another (the `constraint-supersession-check` skill first) |
| G6 | release | anything private becoming public, and any Pages publication |

## 4 · Units of work

- **Spike**: at most half a day, one question, read-only wherever possible.
  It ends with a written result: question, method, numbers, recommendation.
  Nothing is built on a spike until its result has been read.
- **Campaign**: the `iterate-to-goal` loop, with its goal approved at G2.
- Every unit names its gate and its deliverable before it starts, and
  reports which of closed / refuted / re-scoped / dry it ended in.

## 5 · Measures, reported every time

- **Database**: entries by kind and source; duplicate clusters;
  contradictions (must be 0); frontier size and staleness; which entry
  files can be regenerated from a committed script.
- **Coverage**: on a designed test set, the fraction settled by lookup, by
  certified rewriting, by a decider, and left unknown, with times.
- **Tools**: on designed cells, verdict agreement across engines, time,
  certificate size and kernel time; every failure and cap reported.
- **Drift**: per batch, each piece of work set against the goals of §1.
  Anything that maps to no goal is flagged for Matthew.

## 6 · Rules for building search tools

- **Design first** (CLAUDE.md rule 9): answer design questions with a few
  designed cells, never a sweep.
- **Look for the existing emitter before building one.**  `rnDictGen`,
  `rcellsgen`, `rhocover emit`, `frjcert` and lean-certify's `Engine` are
  this repo's generator family; a new pipeline that duplicates one is the
  costliest recurring waste on record.
- **Compiled for search, bounded always** (CLAUDE.md, 2026-10-21):
  `lake build <exe>`, then run under `gtimeout`.
- **Every generated file is reproducible**: a committed generator, and a
  regenerate-and-diff check.
- **Register every tool** in `TOOLS.md` with its version cell, in the same
  commit as any change in its behaviour.

## 7 · Where things stand (2026-10-21)

From the survey of `origin/main` that preceded this draft:

- RNDB: 1874 entries; the schema is proof-carrying (`Entry.ok`).
- Formulas are stored raw, with no keys and no list of accepted forms
  beyond the 22 ρ- and 16 q-representatives (two numberings).
- Most entry files have no generator in the repo, and the DB's import
  closure enters `wip/`.
- The simp set (681 rules) is not derived from RNDB.
- The proving harness's search index does not include RNDB.
- Spike S1 (an audit and export of RNDB) is done:
  `docs/rndb-audit-2026-10-21.md` (branch `rndb-audit`, 32c33eb).  No
  contradictions; no `⊢` entries, so the order is not stored; no content
  key; scope by reference; seven of eight generated files have no
  generator; the closure reaches `wip/` and four sorried declarations.
- Matthew's verdict on the result: the current build is a mess and
  basically unworkable.  The response is `docs/f0-reimplementation-plan.md`:
  a new library beside the old one, on stated principles, replacing it
  only at gate G5.  Spike S2 (accepted forms and keys) is its first step.

## 8 · Questions for Matthew

1. §1, in your words.
2. Is the scope F0 only, or F0 and the one-variable fragment F1 from the
   start?
3. Who are the database's users: you reading it, proofs in Lean, agents
   searching, or all three?  The answer decides how much query layer is
   worth building.
4. Are the gates of §3 the right ones, and are any missing?
