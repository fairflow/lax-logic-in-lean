# Simplifying the proofs that go through — a tactic-extraction plan

2026-09-16. Written after the four-line merge, from a mechanical survey of
every proof body in `LaxLogic/`, `FRJ/` and `LJF/`: 2,618 proofs, 50,489 proof
lines. The evidence tables are in the session scratchpad (`proof-clusters.tsv`,
`prefixes.tsv`, `simpsets.tsv`, `families.tsv`, `subblocks.tsv`); the numbers
quoted below come from them.

The rule this plan obeys: **a simplification must not change what is proved.**
Every step is a refactor of a proof whose statement stays byte-identical, and
each step is finished only when the module builds and
`scripts/check-ledger.sh` reports no regression — the ledger names any
declaration that gained an axiom or a `sorryAx`, which is exactly the failure
mode a proof refactor can hide.

## What the survey found

141 proof bodies are byte-identical to another modulo whitespace and comments
(2,757 lines). Fuzzy clusters at similarity ≥ 0.85 account for 9,720 duplicated
lines. The duplication is not evenly spread: it sits in five places, and four
of them are the *same construction proved three times* — once for each of a
family of calculi that were developed in sequence.

| # | duplication | lines | shape of the fix |
|---|---|--:|---|
| 1 | `FRJ/Sound.lean` ↔ `SoundV.lean` ↔ `SoundW.lean` | 1,906 | one lemma over an abstract join, instantiated three times |
| 2 | `LJF/OCore.aSound` ↔ `OFuelSound.aSoundF` ↔ `OFuelPSound.aSoundP` | ~1,900 | parameterise over the interpretation; merge the 0.97 pair first |
| 3 | `G4UITrunc.itp_fuel_mono` ↔ `itp_budget_mono` | ~551 | one lemma over the step relation |
| 4 | `FRJ/Saturate.lean` ↔ `SaturateV.lean` | 825 | hoist the 21 shared declarations into the base module |
| 5 | G4 / G4H / G4P triplication (`inv`, `identity_mpt`, `impR_inv`, `weaken`, `toSC`) | 886 | a structure over the three calculi |
| 6 | list-membership bookkeeping, repo-wide | ≥1,500 | a `mem_bash`-style tactic + ~6 named lemmas |
| 7 | `simp only / split at / cases` in the three UI interpolation files | ~700 | characterisation lemmas, or one tactic |
| 8 | the LJF weakening-argument triple, 84 identical sites | ~700 | one packaging lemma |
| 9 | the 12-case `LaxND` congruence split, 13 proofs | ~400 | `LaxND.mapCtx`, or a tactic leaving `iden`/`laxIntro` |
| 10 | the `enumOf`/cover preamble in `FRJ/Gbu` | ~540 | a `coverOf` lemma |

Two findings are as useful as the candidates. First, the survey rejects the
obvious targets: the `nil`/`cons` and `zero`/`succ` splits (174 and 87 sites)
are generic inductions with unrelated bodies, and the `revert`-then-`induct`
opening (82 sites) is already as short as it can be. Second, explicit `simp`
lemma lists are a weak signal — only 25 lists of ≥ 3 lemmas recur at ≥ 3
sites — while five project-local definitions dominate those lists
(`Form.size` 93 sites, `gHat` 78, `ConstraintModel.force` 77,
`PLLFormula.weight` 75, `pGuard` 58). Marking those `@[simp]` (or giving each a
small named equation set) is a bigger lever than any simp-set extraction.

## Order of work, and why

The order is by *risk*, not by size: the cheapest-to-verify refactors first, so
that the ledger gate and the build loop are proved out on easy cases before
they are trusted on `aSound`.

**Stage A — lemma extraction inside one module.** Candidates 8, 10, 9.
Each is a packaging lemma next to its uses, no cross-module movement, no
statement changes. Success criterion: the module rebuilds, the ledger shows the
same axioms for every declaration in it, and the line count falls.

**Stage B — hoisting within a family.** Candidate 4 (`Saturate` ↔
`SaturateV`): `SaturateV` already imports `Saturate` and declares in `FRJ.V`,
so the 21 shared declarations move down, not sideways. This is the test case
for "does the ledger notice a hoist?" — it must show the declarations moving
module, and nothing else.

**Stage C — abstraction over a family.** Candidates 1, 5, 3. Here a proof is
stated once over an abstract parameter and instantiated. The constraint that
decides the design: the three `joinAtP` proofs never mention their calculus
except in the statement, so the abstraction takes the premodel equations as
**explicit hypotheses** rather than relying on `rfl` — the three
`FRJr/FRJVr/FRJWr.joinAtP` definitions are not definitionally equal.

**Stage D — tactics.** Candidates 7 and 6, in that order. 7 is the highest
confidence tactic in the repo (232 token-identical sites in exactly three
files); 6 is the largest but saves two lines in four, because the shapes match
while the leaf terms differ — the honest form is a `solve_by_elim`-backed
tactic that is *slower* than the explicit terms it replaces, so it is adopted
only where the explicit term is longer than three lines.

**Stage E — candidate 2**, last, alone. It is 1,900 lines of
`termination_by`/`decreasing_by` mutual recursion; the 0.88 pair genuinely
diverges. Merge the 0.97 pair (`OCore` ↔ `OFuelSound`) or nothing.

## Progress

**Stage A, done 2026-09-16.**

* `Enum.f_mem` (`FRJ/Minimal.lean`). Every proof that takes an `enumOf` needs
  "every value of the enumeration is a member", and all 25 sites wrote the same
  term out by hand. 25 sites rewritten, `FRJ/{Saturate,SaturateV}.lean` and
  `FRJ/Gbu/{Circ,DB,W/CircDB,W/Corner,W/DB}.lean`.
* **One induction over `Clo`, not five.** `clo_trans` (Cl6) is the general
  transport; `clo_mono` (Cl4) and the four `clo_*_cons` lemmas of
  `FRJ/Gbu/Base.lean` each repeated its five-case induction, differing only in
  what they do with a base member. All five now supply that map and call
  `clo_trans`, which is reordered to come first in `FRJ/Basic.lean`.

Verified: `lake build FRJGbu FRJ` 8626 jobs, `lake build` 8746 jobs, and the
ledger gate reports **one addition and no axiom change anywhere** —

```
ledger: 1 addition(s)/improvement(s)
  NEW         FRJ.Enum.f_mem  (FRJ.Minimal)
gate exit 2
```

which is the evidence the refactor changed no proof's content.

**Stage C, the FRJ soundness triple, designed.** The three `join*_case`
families are not the same lemma eight times: five (`joinAtP`, `joinAtF`,
`joinOrP`, `joinOrF`, `joinCircP`) differ across the three calculi only in type
names, while `joinAt`/`joinOr` differ by V/W's `kept` zone and `joinCirc` is
three genuinely different proofs. So the target is the five, all three
calculi — 2,523 duplicated lines down to about 1,395.

The design constraint, and it is the whole difficulty: **the abstraction cannot
quantify over the derivation `d`.** The proofs do not use `preR d` through an
interface, they use it through *reduction* — `cases w` on inhabitants of
`(preR d).W`, `none` fed where a world is expected, `join_force_comp` whose
statement mentions `PreModel.join` syntactically. A record field
`preR (joinAtP …) = PreModel.join …` is a propositional equation between
structures whose first field is a `Type`, and every such step would need a
`cast`. The escape is to state the core lemma directly about the
`PreModel.join` term, with six ordinary hypotheses in place of the definitional
facts (`preR_root_lbl`, `wfR`, `wfI`, `lhs_clo_of_steps`, and the two
closedness proofs); each wrapper then discharges the unfolding by `rfl`,
because `preR (FRJr.joinAtP …)` *is* that term.

The risk is exactly that `rfl`: it asks the elaborator to unify an
18-field `PreModel.join` literal against the `whnf` of `preR (…)`. **One
wrapper is compiled before the other fourteen are written** — that build
decides the design.

**Stage C, done 2026-09-16.** The `rfl` holds. It was tested first in
isolation, as a one-line probe (`preR (FRJr.joinAtP …) = PreModel.join … :=
rfl`), before any core lemma was written; then `joinAtP` alone, all the way
through a wrapper, before the other four were touched.

`FRJ/SoundCore.lean` now holds two pre-model constructions — `joinPModel` for a
promise join, `joinFModel` for a fallible one, the context being a parameter —
and five calculus-free lemmas: `joinAtP_core`, `joinOrP_core`, `joinAtF_core`,
`joinOrF_core`, `joinCircP_core`. It also holds the 308 lines of context and
forcing lemmas that were the first third of `FRJ/Sound.lean` and mention no
calculus at all.

Each of the fifteen proofs (five cases × `FRJr`, `FRJVr`, `FRJWr`) is now a
twelve-line wrapper. The statements of `join*_case` are untouched, in all three
files.

| | before | after |
|---|--:|--:|
| `FRJ/Sound.lean` | 1,921 | 1,079 |
| `FRJ/SoundV.lean` | 1,948 | 1,272 |
| `FRJ/SoundW.lean` | 1,963 | 1,287 |
| `FRJ/SoundCore.lean` | — | 1,191 |
| total | 5,832 | 4,829 |

Verified: `lake build FRJ FRJGbu` green, and the ledger gate reports the five
new core lemmas and the 308 moved helpers as additions and MOVES, with no axiom
change anywhere.

Two hypotheses had to be named explicitly, and they are the interesting
residue: `hwfR` is `wfR d` composed with the context equation `hΓ`, and `hlhs`
is `lhs_clo_of_steps` applied to the single `Step.join*` of the rule. Both were
definitional in the original and are ordinary arguments now — which is what
"abstract over the calculus" costs here, and it is six lines, not a design.

**A gate improvement fell out of this.** Hoisting 308 declarations into a new
module made every one of them vanish from `FRJ.Sound` and appear in
`FRJ.SoundCore`, which the gate called a regression (a vanished declaration is
the shape of a lost proof). It now distinguishes a MOVE — same name, same
axioms, different module — from a loss, and a move whose axioms *changed* is
still a regression, reported as `MOVED*`. Both cases are in
`scripts/test-ledger-diff.py`, and both were watched failing.

## Stage B, done 2026-09-16: `SaturateV` said 21 things twice

The survey called `FRJ/Saturate.lean` ↔ `FRJ/SaturateV.lean` 825 duplicated
lines. Examining it declaration by declaration gives a smaller and much more
interesting number.

The two files share **72** declaration names, 55 of them byte-identical — but
byte-identical text is not the same theorem. Five base structures (`IrrWit`,
`MRWit`, `FRWit`, `OWit`, `PledgeFam`) differ in exactly one field, `FRJr`
against `FRJVr`, and **34 of the 55 identical declarations mention one of
them**, so they are genuinely different statements that happen to be spelled
alike. Deleting those would silently retype the V layer to the paper calculus.

**21 are redundant outright**: byte-identical, and nothing in their statements
mentions a doubled name. Since `FRJ.V` is nested inside `FRJ`, every use in the
V file resolves to the original once the copy is gone; no site anywhere refers
to them as `FRJ.V.…`, and no axiom pin names one. Deleted — 291 lines — with a
note in place listing what was removed and why.

The lesson for the rest of this plan: **similarity measured on text overstates
what can be shared.** The number that matters is how many of the "identical"
declarations mention something that is itself doubled — here 34 of 55, and that
is what the 825 collapses to 291 against.

## Refused: the G4 / G4H / G4P triplication (candidate 5, 886 lines)

Examined 2026-09-16 and **not attempted**. The five families (`inv`,
`identity_mpt`, `impR_inv`, `weaken`, `toSC`) are rename-only between `G4` and
`G4p` and genuinely different for `G4h`, and the reason they cannot be shared is
the mirror image of what made `SoundCore` work.

`SoundCore` succeeded because the proofs reduced a constructor applied to an
object, so the lemma could be restated about the object. Here four of the five
families are **eliminations** — they open with `induction d` — and an
elimination cannot be abstracted over a record of operations: a record supplies
introduction forms, and the only field that would support the induction is the
recursor, a different dependent type for each of the three constructor sets.
There is no underlying object to restate the lemma about, because here the
derivation *is* the object. A single parameterised inductive type-checks on
paper and buys nothing: every goal then carries a stuck context function, and
the diverging lines are exactly the permutation arithmetic that re-exposes a
formula past `[X]`, past `[F, X]`, or past nothing — the same three proofs,
relocated.

And the duplication is load-bearing, which matters more than the line count:

* `G4` is the object of a published separation (`G4Gap.sc_but_not_G4`,
  `contraction_not_admissible`), machine-checked *about Iemhoff's Figure 2.3 as
  transcribed*. Make `G4` an instance of a parameterised family and a reader
  checking fidelity to the paper must check the instantiation too.
* `G4ipComplete.completeness_isIPL` is the rule-8 fragment result, and its point
  is to locate the defect in exactly `laxL`, `impLLax`, `impLLaxLax` — the three
  constructors an abstraction would blur.
* `G4h.inv` is height-**preserving**; `G4.inv` has no height. They are different
  theorems, not two copies of one.

One bounded exception exists and is left for Matthew: `identity_mpt` never
eliminates a derivation (it inducts on `Nat` and matches on the formula), so it
would fit a record of the 17 introduction rules — about 140 lines, with the same
"compile one instantiation first" discipline. Small, and it touches the ladder
documents; his call, not mine.

## The rules that keep this honest

1. **No statement moves.** If a refactor would change a theorem's statement, it
   is not part of this plan; it goes on the list for Matthew.
2. **The ledger is the gate.** `scripts/check-ledger.sh` after every stage; a
   REGRESSION line stops the stage. A refactor that silently routes a proof
   through `Classical.choice` is exactly what the gate is for.
3. **Watch each new tactic fail** before it is used anywhere (CLAUDE.md
   discipline): a tactic that silently closes the wrong goal is worse than the
   duplication it removes.
4. **Extraction is not generalisation.** A lemma is extracted with the weakest
   hypotheses that the existing call sites supply, never with the hypotheses
   that would make it pretty.
5. **Archive, don't delete** the superseded proof when a merge is not
   byte-exact: the old body goes in the commit message, so a bisect can read
   it.

## What this is not

It is not a speed campaign. Build time is not measured here and no step is
justified by it. It is not a re-proof: nothing is re-derived, only re-arranged.
And it does not touch `wip/`, the frozen four-arm `wipa/…/wipx` records, or
`Archive/` — those are the record of how the development happened.
