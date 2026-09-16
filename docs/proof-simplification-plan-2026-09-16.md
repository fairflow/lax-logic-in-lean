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
