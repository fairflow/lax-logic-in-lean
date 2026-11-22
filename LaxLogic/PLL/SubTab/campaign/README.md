# The subframe tableau: campaign folder

The subframe tableau (`SubTab`) is a signed tableau for propositional lax
logic over subframe models: a decision procedure with a certificate either
way.  This folder holds the record of its campaign, in the sense of
[proof-tools](https://github.com/fairflow/proof-tools) (`docs/campaign.md`).

## Status

| stage | state | where |
|---|---|---|
| 0. Survey | none: the tableau was built on request (2026-10-15), not adopted from a source | [record.md](record.md) §1 |
| 1. Adopt | done: the twelve rules, as a checker of whole trees; since 2026-11-19 also a move at a time | [record.md](record.md) §2, `../Sound.lean`, `../Explore.lean` |
| 2. Prove | done: soundness, dichotomy, completeness, translation to natural deduction | [record.md](record.md) §5 |
| 3. Run | done: search, engine, negative tests, 29 facts, the tools | [record.md](record.md) §6, `TOOLS.md` |
| 4. Explore | in progress: the first instance is built and waits for its test; the full exploration is not started | [report-2026-11-19.md](report-2026-11-19.md) |

## Files here

* [record.md](record.md): the five questions as they turned out, the
  rules, the reading of a signed sequent, the measure, the truth lemma,
  the statements, what runs.
* [report-2026-11-19.md](report-2026-11-19.md): the tableau as an instance
  of the proof explorer; the test.

## Files of the explorer instance

* `../Explore.lean`: the moves, `step`, soundness, derivations and closed
  tableaux each from the other, scripts as certificates.  Within
  `[propext, Quot.sound]`.
* `../ExploreEngine.lean`: the engine whose yes side is a script.
* `../ExploreTactic.lean`: the tactic `subtab`.  Code for the editor.
* `../ExploreTest.lean`: tests, with every message pinned.  Since
  2026-11-20 also walks: `#walk d m₁ m₂ …` (proof-tools) shows a named
  attempt or derivation at the position the motions `up`, `down i`,
  `left`, `right`, `top`, `goal k` reach, and changes nothing.  Since
  2026-11-21 it offers, after its last view, the motions that can be made
  from there: a click writes one after the last motion.
* `../ExploreTerm.lean` (2026-11-20, a spike): from a derivation to its
  proof term (`tm`) and to that term's normal form (`nf`), through the
  normalisation of `LaxLogic/PLL/Normalisation/`.  The four laws of `◯`
  have the terms of the monad as normal forms; two derivations of one
  sequent can have proof terms that are not convertible.
* `Play/SubTab.lean` (at the repository's root): exercises to type.
* `Play/SubTabExploreTerm.lean`: a derivation built, walked by typing
  motions and by clicking them, and its proof term and normal form; an
  attempt stopped and looked at; what the search found, walked.
* `Play/SubTabPanel.lean`: the panel of `#walk`, a trial (proof-tools'
  pull request 5): the attempt drawn as a tree in the infoview.

Build: `lake build SubTabExplore`.
