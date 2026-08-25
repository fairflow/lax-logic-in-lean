---
name: constraint-supersession-check
description: Before marking any design, remedy, rule-table presentation, encoding, module, or development path as superseded, archived, replaced, redundant, subsumed, or obsolete — enumerate every constraint the retired artefact discharged and verify the survivor discharges each one, recording the check in the verdict itself. Use whenever writing a reassessment or verdict table, whenever a strategy pivot abandons one path for another (fresh rebuild vs in-place extension, parallel directory vs base), whenever archiving a parallel development, and also before BUILDING ON a prior verdict that retired something — a bare "superseded" in an old document is a claim to re-check, not a fact. Fires even when the supersession seems obvious; the failure mode this closes was committed by careful people with the constraint written down in front of them.
---

# The constraint-supersession check

## The failure mode this closes

Constraints attach to **goals**. Remedies are how a particular design meets
them, and a remedy often discharges more constraints than the one it was
named for. A supersession verdict — "A is superseded by B" — is almost
always argued against *the problem currently in view*: A and B both solve
it, B is already load-bearing, so A is redundant. That argument is valid
for one constraint and silent about the rest. If A also discharged a
second constraint that B does not touch, the verdict quietly re-opens it,
and it re-opens **unrecorded**, because the verdict reads as due diligence.
Nobody is ignorant at the moment of loss; the check is simply never run.

The specimen, from this repository's own history (2026-08-16,
`docs/frjlax-reassessment.md` §1): the membership-equality (`≐`) rule
table was marked "**superseded**" by `nf`-canonical contexts. Both
discharge *index transport* (same members ⇒ interchangeable indices). But
the `≐` presentation also discharged the **no-green-slime constraint** of
the handoff's §4.1 — every constructor return-type index a variable —
which `nf` does not: `nf G (...)` is still a computed index. The
constraint died in that verdict table. The surviving path inherited the
slime, every subsequent rule addition was locally cheapest in the slimy
style, and the cost surfaced only in aggregate: six ~130-line clone cases
in a 1,981-line soundness file for what the paper proves in one
induction, and an extension declared blocked until the base is repaired.
The no-slime constraint was written down, cited, and mechanically
checkable the whole time.

## When to run it

* You are about to write "superseded", "archived", "replaced",
  "redundant", "subsumed", or "no longer needed" about any artefact —
  a design, an encoding, a rule presentation, a lemma, a module, a
  worktree, a whole parallel development.
* A strategy pivot abandons one path for another. Constraints attach to
  the goal, not the path: when a path is archived, sweep its entire
  constraint set against the surviving path, not just the constraint
  that motivated the pivot.
* You are about to **rely on** a supersession verdict someone else (or an
  earlier session) recorded. If the verdict document contains no
  supersession table, run the check before building on the decision.

## The procedure

1. **Name the retirement.** One line: retired artefact → survivor, and
   the problem the verdict is being argued from.

2. **Enumerate the constraints the retired artefact discharged.** Not
   "the problem it solved" — the plural is the whole point. Sources, in
   order: the brief or handoff sections that motivated the artefact; the
   artefact's own header comments; fidelity and design docs that mention
   it; then grep the artefact's name across `docs/` and read every
   "so that / because / which is what / the reason" sentence naming it.
   The test question for each candidate: *if this artefact vanished
   tonight, which sentences elsewhere in the record become false?* Cite
   a source for every constraint listed.

3. **Give each constraint a three-valued verdict against the survivor**,
   mirroring the repo's PROVED/REFUTED/OPEN discipline:

   * **DISCHARGED** — the survivor meets it. Say *how*, checkably: a
     theorem, a mechanical test, a doc section. "Obviously fine" is not
     a how.
   * **RE-OPENED** — the survivor does not meet it. The constraint
     returns to OPEN and must be re-assigned: either the supersession is
     blocked, or the re-opened constraint is listed at the head of the
     verdict with a stage or owner. A constraint may never be dropped
     *silently* by retiring its remedy.
   * **LAPSED** — the constraint's motivating **requirement** is gone;
     cite what changed in the goal. A constraint never lapses merely
     because its remedy changed, and never because it is inconvenient.

4. **Record the table inside the verdict document itself** — the
   reassessment, the HANDOFF section, the commit message body — because
   that is where the next reader meets the decision. A supersession
   verdict without its table is incomplete, and a verdict with any
   RE-OPENED row must read "superseded **except** ⟨constraints⟩", never
   bare "superseded".

## The table

```
## Supersession check: <retired artefact> → <survivor>

| constraint | source | retired artefact | survivor | verdict |
|---|---|---|---|---|
| ... | doc § | how it discharged it | how / why not | DISCHARGED / RE-OPENED / LAPSED |

Re-opened constraints: <each with stage/owner> — or "none".
```

## The specimen, as it should have read

| constraint | source | `≐` rule table | `nf` canonical contexts | verdict |
|---|---|---|---|---|
| index transport: same members ⇒ interchangeable derivation indices | handoff §4.3 | membership hypotheses; no zone is pinned | `nf_ext`: same members ⇒ literally the same list | DISCHARGED |
| no green slime: every constructor return-type index a variable | handoff §4.1; plan §3.1 (the McBride test, "checkable mechanically before any proof is attempted") | all computed contexts enter through `≐`/`⊆`/`∈` hypotheses | **not met** — `nf G (...)`, `joinCtx…`, `rm (gAt G) F` remain computed indices | **RE-OPENED** |

Correct verdict: *superseded for transport only; §4.1 re-opens — either
carry the `≐` presentation into the surviving path or schedule de-sliming
as a stage boundary before any rule is added.* The actual verdict was
bare "superseded"; the bill arrived at the promise-join round.

## Keeping it cheap

The check is minutes, not a campaign. If the enumeration honestly yields
one constraint, say so in one line and the check degenerates gracefully to
one row — do not manufacture constraints to fill a table. The discipline
is the enumeration question and the refusal to write bare "superseded",
not the size of the output.
