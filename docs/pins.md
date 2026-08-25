# "Pins" — the concept, precisely

Written 2026-08-24 at Matthew's request, because the word is used across
several contexts and does not just mean "a Lean proof".

## The definition

A **pin** is a build-enforced, machine-transcribed record of a result's
**provenance**, placed so that any later drift fails the build at the
point of record.

A Lean proof settles whether a theorem is true.  A pin settles a
different question: **what the theorem rests on** — and keeps the answer
under guard.  The two are independent: a theorem can be kernel-accepted
and still rest on `sorryAx` (a `sorry` ASSERTS: it inhabits the type and
is indistinguishable *by name* from a proved theorem), or on
`Classical.choice` where constructive content was wanted, or on
`native_decide`'s trusted evaluator.  None of that is visible in the
statement or the proof script; it is visible only to `collectAxioms`,
which is the repo's one sound oracle for it.

## The canonical form: the axiom pin

Three lines, and all three are load-bearing:

    /-- info: 'Foo.bar' depends on axioms: [propext, Quot.sound] -/
    #guard_msgs in
    #print axioms Foo.bar

* `#print axioms` alone is **not a pin**.  It prints into the build log
  and checks nothing — a pin in appearance only.  (A 2026-08-21 repo
  scan found 1,457 `#print axioms`, of which 142 were bare; the largest
  block, 39, sat in the certificate corpus itself.)
* `#guard_msgs` turns the record into a **failing check**: if the axiom
  set ever changes — a refactor drags in `Classical.choice`, a
  dependency acquires a `sorry` — the build goes red HERE, at the
  record, not silently somewhere downstream.
* The docstring is **transcribed from Lean's own output, never
  authored**.  A hand-written expected string is a claim; a transcribed
  one is a measurement.  Practically: emit the pin unguarded, compile,
  capture what Lean actually printed, re-emit guarded
  (`tools/pin-backfill.py`; `lake exe frjcert` does the two passes
  itself).  Pins are re-transcribed verbatim, never paraphrased.

## The second sense: discover-then-pin

For objects an untrusted engine *finds* (countermodels, derivations),
"to pin" means to fix the discovered object into a **self-contained,
kernel-checkable restatement in which the discovery process appears
nowhere**.  A search hit becomes a finite table plus `decide`-checked
facts about it (`rnpin`, `rhobank`); the searcher's code, budgets and
bugs are all irrelevant to the artifact's validity.  The axiom pin (sense
one) is then placed on the restatement.  This is the repo's standing
engine discipline: discovery untrusted, results pinned.

## Placement: pin where the fact is consumed

A pin next to the theorem checks the theorem.  A pin in a **consumer**
(`Certified/Register.lean`, the entry-list pins in `RNDB/`) re-checks the
same fact from the citing side, so that drift surfaces at the place that
relies on it, once, rather than as a silently weakened guarantee spread
over hundreds of entries.  The register's copy of the string is for
reading; its `#guard_msgs` is the check.

## What pins do NOT do

* **They check taint, not reachability.**  A module can be pin-clean
  (nothing it declares depends on a sorry) while its import closure
  REACHES sorried modules — two different properties, and
  publication/core's `core-audit` gates on the second
  (2026-08-24 peer correction; see `HANDOFF.md` §2026-08-24).
* **They do not validate statements.**  A pinned theorem can state the
  wrong thing perfectly soundly; statement failures are a testing
  problem (extensional attack before proof), not a pin problem.
* **They are not evidence until watched failing.**  A gate nobody has
  seen go red is decoration: inject a false expected string, confirm the
  build fails, restore (standing rule, 2026-08-20).

## One-line summary

A proof says *this is true*; a pin says *and it rests on exactly this,
checked on every build, recorded in the oracle's own words, at the point
where someone depends on it*.
