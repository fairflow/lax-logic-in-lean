/-
# Worked examples for the RNDB schema

Moved out of `RNDB/Types.lean` on 2026-08-24 (peer finding): the examples
cite `wip/rnSep.lean` / `wip/rnSepColl.lean`, and through them the
sorried `wip/rnDict.lean` — so while they lived in the schema file,
EVERY RNDB module was `wip`-rooted through its own types.  Here they keep
their full documentation value (branch coverage of `Rel` and `Evidence`,
the three attack attempts recorded in the Types docstring) at closure
cost to nobody: nothing imports this file.

The pins are the machine check that no example reaches a sorried cell.
-/
import RNDB.Types
import wip.rnSep
import wip.rnSepColl

namespace RNDB

open PLLFormula
open PLLND
open PLLND.SemUI

/-! ## 6. Worked examples

Four entries, from theorems that already exist in the repository.  They
exercise every constructor of `Rel` and every constructor of `Evidence`,
which is the branch-coverage minimum for showing the types inhabitable.

The material:

* `PLLND.SemUI.RND.d_w1_w2 : Deriv [w1] w2` and
  `PLLND.SemUI.RND.coll_w1_w2 : Interd w1 w2` (`wip/rnSepColl.lean`,
  hand-authored, sorry-free);
* `PLLND.SemUI.RND.sep_0_16 : ¬ Interd q0 w2` (`wip/rnSep.lean`,
  generated, sorry-free, a pinned one-world countermodel);

where `w1 = q8 ∧ q10` and `w2 = q9 ⊃ q4` are the §40 witnesses and
`w2` is the representative of the sixteenth class, `q15`. -/

section Examples

open PLLND.SemUI.RND

/-- `q0` is `⊥`, so it proves everything.  This is what lets the
one-directional non-entailment be read off the separation `sep_0_16`:
the direction `q0 ⊢ w2` holds trivially, so all of the content of
`¬ Interd q0 w2` sits in the other direction. -/
theorem deriv_q0 (ψ : PLLFormula) : Deriv [q0] ψ :=
  Deriv.falsoElim ψ (Deriv.iden (by simp [q0]))

/-- `w2 ⊬ q0`, at the strength the certificate actually has.  Extracted
from `sep_0_16 : ¬ Interd q0 w2` by `deriv_q0`. -/
theorem nle_w2_q0 : ¬ Deriv [w2] q0 :=
  fun h => sep_0_16 ⟨deriv_q0 w2, h⟩

/-- The scope every negative example below is relative to: the sixteen
representatives of `wip/rnSepColl.lean`, `q0 … q14` together with
`w2 = q15`.

The list is CITED, not transcribed.  When `LaxLogic/RN/Reps.lean` lands
on this branch its `RNReps.reps` is the same sixteen formulas and should
replace this line; a second transcription of the representatives is the
duplication that module exists to end. -/
def scope16 : List PLLFormula := RNReps.reps
-- REPOINTED 2026-08-24: was `repsL16` (wip/rnSepColl.lean), cited because
-- the authoring worktree's base predated LaxLogic/RN/Reps.lean gaining
-- `q15`.  This branch has it, and the shared dictionary is the one
-- registry a scope should ever name.

/-- `w1 ⊢ w2` — one direction only, hand-authored. -/
def eLeW1W2 : Entry where
  id := "rndb-0001"
  claim := ⟨w1, w2, Rel.le, none⟩
  ev := Evidence.proof Engine.hand
  ok := ⟨Claim.wellScoped_of_pos (by decide), by decide, d_w1_w2⟩

/-- `w1 ⊣⊢ w2` — the collapse of two of the four §40 witnesses. -/
def eInterdW1W2 : Entry where
  id := "rndb-0002"
  claim := ⟨w1, w2, Rel.interd, none⟩
  ev := Evidence.proof Engine.hand
  ok := ⟨Claim.wellScoped_of_pos (by decide), by decide, coll_w1_w2⟩

/-- `w2 ⊣⊢ w1`, DERIVED from `rndb-0002` by symmetry.  The parent list
and the rule are provenance; `ok` still carries the proof. -/
def eInterdW2W1 : Entry where
  id := "rndb-0003"
  claim := ⟨w2, w1, Rel.interd, none⟩
  ev := Evidence.derived ["rndb-0002"] DerivRule.symm
  ok := ⟨Claim.wellScoped_of_pos (by decide), rfl, coll_w1_w2.symm⟩

/-- `w2 ⊬ q0`, refuted by a one-world countermodel, asked against the
sixteen representatives.

This is the entry the round-1 record could not express.  `w2` is one of
the four cells `Rewrite/Catalogue.lean` marks REFUTED; what was refuted
is the collapse `w2 ⊣⊢ q0` asked against `q0 … q14`, and the scope field
is where that "asked against" now lives. -/
def eNleW2Q0 : Entry where
  id := "rndb-0004"
  claim := ⟨w2, q0, Rel.nle, some scope16⟩
  ev := Evidence.countermodel Engine.finCM 1
  ok := ⟨Claim.wellScoped_some, rfl, Nat.one_pos, nle_w2_q0⟩

/-- The worked entries. -/
def exampleEntries : List Entry :=
  [eLeW1W2, eInterdW1W2, eInterdW2W1, eNleW2Q0]

/-- Two of the 87 open cells of `wip/rnDict.lean` — `cAnd_4_14` and
`cAnd_8_11` — recorded the way an open question is supposed to be
recorded: as data.

In `wip/rnDict.lean` these are

    theorem cAnd_4_14 : Interd (q4.and q14) q4 := sorry
    theorem cAnd_8_11 : Interd (q8.and q11) q8 := sorry

which ASSERT them.  Here they are `Claim` values, which assert nothing:
there is no proof term, no inhabitant of the proposition, and nothing
downstream can cite them as facts. -/
def exampleFrontier : Frontier :=
  [ ⟨q4.and q14, q4, Rel.interd, none⟩,
    ⟨q8.and q11, q8, Rel.interd, none⟩ ]

end Examples

/-! ## Axiom pins (transcribed from Lean's own output) -/


/-- info: 'RNDB.eLeW1W2' does not depend on any axioms -/
#guard_msgs in
#print axioms eLeW1W2

/-- info: 'RNDB.eInterdW1W2' does not depend on any axioms -/
#guard_msgs in
#print axioms eInterdW1W2

/-- info: 'RNDB.eInterdW2W1' does not depend on any axioms -/
#guard_msgs in
#print axioms eInterdW2W1

/-- info: 'RNDB.eNleW2Q0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eNleW2Q0

/-- info: 'RNDB.exampleEntries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exampleEntries

/-- info: 'RNDB.exampleFrontier' does not depend on any axioms -/
#guard_msgs in
#print axioms exampleFrontier

end RNDB
