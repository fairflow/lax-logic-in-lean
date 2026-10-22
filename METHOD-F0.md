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

*To be written by Matthew.  Prompts, to be deleted as needed:*

- What is the F0 work for: which questions should be answerable, by whom
  (a reader, a proof, an agent), and how quickly?
  A: All three.  A reader will go through the RN(◯,∅) explorer which needs a
  thorough upgrade after this rebuild process is complete.  A proof will
  use a tactic that refers to the database.  Suppose we have u ⋖ v ⋖ w in
  the db (wrt the current state of the db).  Then we need the tactic to use
  transitivity of < via transport from a single ⋖ step to <, in order to use
  a kernel-checked fact that u < w in the current proof.  A tactic seems
  the only sensible way.  An agent needs to know how to use the database for
  those or additional purposes, so it needs to have a clear and complete
  table of tools.
- What does "systematic" mean here, as opposed to today's ad-hoc use?
  B: use of tables; if some tools are better than other for some tasks, there
  needs to be a record of this in the table of tools.  
- Which forms are the accepted representatives of the classes, and who may
  add one?
  C: authorised agents, or those which obtain permission.  The forms should
  be minimal in some sense, formula length is the first proxy, ◯ nesting
  depth is probably the most important factor in that.  A weighted size
  function seems sensible: you can design tests provided we end up with a
  single clear choice.
- What must never happen?
  D: a random choice of tool, that requires further proof effort and/or a
  major rebuild, for no clear gain.
- What would count as success in three months?
  E: the explorer is updated, corrected, browsable, and links between the
  classes can be followed to a Lean proof and/or countermodel.
  A representative of each class will be shown on hover or in another
  convenient way.  the classes are numbered, in an extensible and systematic
  way, that is reflected in the way Lean searches the db. 
  The current boundary of the db is clearly and graphically illustrated.
  Comments and explanations in the tool are limited to how to use the tool
  and what is needed to understand the families, the RN embedding and the
  purpose of the tool.
  The operation table is consistent with the db, cells can be clicked to
  view the resulting class in a clear and consistent way.
  The ∨-free fragment is also highlighted or displayed in a consistent way.

## 2 · Invariants

1. **Every answer is certified or labelled unknown.**  A producer may be
   untrusted; a verdict may not.  A search that finds nothing is no verdict
   (the G4c failure memo, #70, is the lesson); a negative answer is a
   countermodel certificate.
2. **Data in a database, truth in the kernel.**  Every row of RNDB carries a
   Lean certificate that the kernel checks in CI.  Any index, export or
   query layer is derived from the rows and is never the authority.
   The same goes for the links u ⋖ v and u < w.  
3. **Coverage is measured, never assumed.**  F0 is PROVED infinite, so no
   finite table closes.  Exhaustion over known classes refutes only
   relative to those classes, and is reported with that scope.
   Completeness of a tool is claimed only when proved.
4. **Identities are append-only.**  Entry ids, q-indices and ρ-indices never
   change meaning.  A superseded row is marked as superseded, never deleted.
5. **The accepted forms follow a rule** (§1 C; agreed 2026-10-22).
   * A class has a stable **name**, its number, which denotes the class
     and never a particular formula.
   * Its **representative** is the minimal known member under the order
     (◯-depth, size), compared lexicographically.  Ties go to the
     incumbent; for a new class, a fixed syntactic order decides.  The
     tie rule is *proposed* after the 2026-10-22 test, and awaits Matthew.
   * A representative is replaced only by a **strictly** smaller member.
     The replacement is an append-only event backed by a certified `⊣⊢`
     row.  The old representative stays a recorded member.
   * Within this rule, **authorised agents, or agents that obtain
     permission**, add classes and replace representatives.  Every change
     is reported to Matthew.  The rule itself is his (gate G3).
6. **Private stays private.**  Results developed in the private repository
   enter the public database only when Matthew releases them.

## 3 · Steering gates

| | Gate | Decided by Matthew before … |
|---|---|---|
| G1 | vision and scope | any campaign under this file (§1) |
| G2 | statements | any proof, checker specification or certifier (lean-certify R10) |
| G3 | the rule for accepted forms (invariant 5: the order that defines minimality, the tie rule, who may add) and the keys | any tool that maps formulas to classes.  Applying the rule is not gated: authorised agents, or agents that obtain permission, add classes and replace representatives under it, and report each change |
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
- **Every tool is adopted as a lean-certify `Engine`** (DRAFT, 2026-10-22).
  An engine is the tool's API: an untrusted producer, plus a certifier for
  each side, each proved sound.  Tools are invoked only through the decider
  settings (prover/disprover pairs and fallback pairs).  A pre-registered
  comparison (G4) sets the order of the pairs, and its result is recorded in
  the table of tools (§1 B), so no tool is chosen at random (§1 D).

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

1. §1, in your words.  *Answered 2026-10-22 (§1 A–E).*
2. Is the scope F0 only, or F0 and the one-variable fragment F1 from the
   start?
3. Who are the database's users: you reading it, proofs in Lean, agents
   searching, or all three?  *Answered: all three (§1 A).*
4. Are the gates of §3 the right ones, and are any missing?  (G3
   rewritten 2026-10-22 to §1 C: Matthew sets the rule, agents apply it.)
5. The tie rule of invariant 5 (the incumbent wins on equal
   (◯-depth, size)).  The test of 2026-10-22
   (`docs/f0-minimal-forms-test-2026-10-22.md`) found 14 of the 22 ρ tied
   with another known member.  13 of the ties are only a reordering of
   `∨`; under a purely syntactic tie-break, all 14 would be re-pointed for
   no gain (§1 D).
