/-
THE CATALOGUE SIMPSET — 236 CERTIFIED rules, harvested.

Source: `wip/rnDict.lean`, the operation table of the variable-free
dictionary (the explorer's "Operation tables" tab).  Each entry is a
theorem `Interd (qi ⊙ qj) qk`: a binary combination of dictionary
classes collapsing to a class REPRESENTATIVE.  That is exactly a
rewrite rule, already oriented compound → representative, and already
kernel-checked.

**The 87 unproved cells are EXCLUDED, and this is not cosmetic.**
`wip/rnDict.lean` holds exactly its 236 PROVED cell theorems (the
sorried statements and the refuted closure layer were deleted
2026-08-25, Matthew's directive — the reference set is the ρ-catalogue
R, open-ended);
the other 87 are `sorry`.  Four of them state a collapse that is FALSE:

    cAnd_8_10 : Interd (q8 ∧ q10)  q0      -- FALSE AS STATED
    cImp_9_4  : Interd (q9  ⊃ q4)  q0      -- FALSE AS STATED
    cImp_12_4 : Interd (q12 ⊃ q4)  q0      -- FALSE AS STATED
    cImp_14_4 : Interd (q14 ⊃ q4)  q0      -- FALSE AS STATED

The first cut of this file (2026-08-14, commit 8bb7ef4) harvested all
323 names indiscriminately, so `rndSet` carried `sorryAx` and four
rules that rewrite a formula to a NON-interderivable one.  A `sorry`ed
`RwRule` defeats the type-level guarantee the design relies on: the
`ok` field is what makes `norm_interd` unconditional, so an
unproved `ok` makes the whole normaliser unsound, silently.  The
`#print axioms rndSet` pin below is the standing guard against a
repeat: any future harvest that picks up an unproved cell fails the
build here rather than in the results.

CORRECTION, 2026-08-21.  This header previously called those four cells
REFUTED.  They are not.  What is refuted is the collapse **to `q0`**.
All four formulas collapse to each other, and their common class is
`q15 := q9 ⊃ q4`, appended to `LaxLogic/RN/Reps.lean` on 2026-08-21:

    cAnd_8_10 : Interd (q8 ∧ q10) q15   PROVED   wip/rnDict2.lean:136
    cImp_9_4  : Interd (q9  ⊃ q4) q15   PROVED   `Interd.refl` — q15 IS q9 ⊃ q4
    cImp_12_4 : Interd (q12 ⊃ q4) q15   PROVED   wip/rnDict2.lean:519
    cImp_14_4 : Interd (q14 ⊃ q4) q15   PROVED   wip/rnDict2.lean:585

`wip/rnSep.lean` separates `q15` from all fifteen earlier representatives
(`sep_0_16 … sep_14_16`, sorry-free), so this is a new class rather than a
renaming.  The EXCLUSION from `rndSet` stands unchanged and for the same
reason — the rule as written here is unsound — but the diagnosis was
wrong, and the way it was wrong is the disease itself: **status is not a
property of a cell.**  It is a property of a cell together with the
representative set it was asked about, and of the engine that asked.  A
cell "refuted" against fifteen representatives is proved against sixteen.

CORRECTED 2026-08-25 (v18 audit + the purge): of the 87 once-excluded
cells, 42 are settled against `q15` (41 proved in `wip/rnDict2.lean`,
plus `cImp_9_4` which needs no theorem) and the remaining 45 are
REFUTED CELLS with sorry-free `refute_*` theorems — NONE is open; the
former "target list" is empty, and the sorried statements themselves
were deleted in the 2026-08-25 purge.  Harvesting
the 42 means re-stating them in the shared numbering, which is database
work, not a docstring fix, so `rndSet` is unchanged by this correction.

Composition (proved cells only):
  ∧-table 64   ∨-table 46   ⊃-table 121   ◯-table 5

Orientation is screened by `lean_exe rwscreen`, not asserted: by
`norm_interd` the correctness of `norm` does not depend on it.
-/
import Rewrite.Core
import Rewrite.Set
import Rewrite.Canon
import wip.rnDict
import wip.rcells

namespace Rewrite

open PLLND PLLND.SemUI

/-- The dictionary operation table as rewrite rules — the
kernel-checked cells only. -/
def rndSet : List RwRule :=
  [ ⟨_, _, RND.cAnd_2_3⟩,
  ⟨_, _, RND.cAnd_2_4⟩,
  ⟨_, _, RND.cAnd_2_5⟩,
  ⟨_, _, RND.cAnd_2_6⟩,
  ⟨_, _, RND.cAnd_2_7⟩,
  ⟨_, _, RND.cAnd_2_8⟩,
  ⟨_, _, RND.cAnd_2_9⟩,
  ⟨_, _, RND.cAnd_2_10⟩,
  ⟨_, _, RND.cAnd_2_11⟩,
  ⟨_, _, RND.cAnd_2_12⟩,
  ⟨_, _, RND.cAnd_2_13⟩,
  ⟨_, _, RND.cAnd_2_14⟩,
  ⟨_, _, RND.cAnd_3_4⟩,
  ⟨_, _, RND.cAnd_3_5⟩,
  ⟨_, _, RND.cAnd_3_6⟩,
  ⟨_, _, RND.cAnd_3_7⟩,
  ⟨_, _, RND.cAnd_3_8⟩,
  ⟨_, _, RND.cAnd_3_9⟩,
  ⟨_, _, RND.cAnd_3_10⟩,
  ⟨_, _, RND.cAnd_3_11⟩,
  ⟨_, _, RND.cAnd_3_12⟩,
  ⟨_, _, RND.cAnd_3_13⟩,
  ⟨_, _, RND.cAnd_3_14⟩,
  ⟨_, _, RND.cAnd_4_5⟩,
  ⟨_, _, RND.cAnd_4_6⟩,
  ⟨_, _, RND.cAnd_4_7⟩,
  ⟨_, _, RND.cAnd_4_8⟩,
  ⟨_, _, RND.cAnd_4_9⟩,
  ⟨_, _, RND.cAnd_4_10⟩,
  ⟨_, _, RND.cAnd_4_11⟩,
  ⟨_, _, RND.cAnd_4_12⟩,
  ⟨_, _, RND.cAnd_4_13⟩,
  ⟨_, _, RND.cAnd_5_6⟩,
  ⟨_, _, RND.cAnd_5_7⟩,
  ⟨_, _, RND.cAnd_5_8⟩,
  ⟨_, _, RND.cAnd_5_9⟩,
  ⟨_, _, RND.cAnd_5_10⟩,
  ⟨_, _, RND.cAnd_5_11⟩,
  ⟨_, _, RND.cAnd_5_12⟩,
  ⟨_, _, RND.cAnd_5_13⟩,
  ⟨_, _, RND.cAnd_5_14⟩,
  ⟨_, _, RND.cAnd_6_7⟩,
  ⟨_, _, RND.cAnd_6_8⟩,
  ⟨_, _, RND.cAnd_6_9⟩,
  ⟨_, _, RND.cAnd_6_10⟩,
  ⟨_, _, RND.cAnd_6_11⟩,
  ⟨_, _, RND.cAnd_6_12⟩,
  ⟨_, _, RND.cAnd_6_13⟩,
  ⟨_, _, RND.cAnd_6_14⟩,
  ⟨_, _, RND.cAnd_7_8⟩,
  ⟨_, _, RND.cAnd_7_9⟩,
  ⟨_, _, RND.cAnd_7_10⟩,
  ⟨_, _, RND.cAnd_7_11⟩,
  ⟨_, _, RND.cAnd_7_12⟩,
  ⟨_, _, RND.cAnd_7_13⟩,
  ⟨_, _, RND.cAnd_7_14⟩,
  ⟨_, _, RND.cAnd_8_9⟩,
  ⟨_, _, RND.cAnd_8_13⟩,
  ⟨_, _, RND.cAnd_9_10⟩,
  ⟨_, _, RND.cAnd_9_11⟩,
  ⟨_, _, RND.cAnd_9_12⟩,
  ⟨_, _, RND.cAnd_10_11⟩,
  ⟨_, _, RND.cAnd_10_12⟩,
  ⟨_, _, RND.cAnd_11_12⟩,
  ⟨_, _, RND.cOr_2_4⟩,
  ⟨_, _, RND.cOr_2_5⟩,
  ⟨_, _, RND.cOr_2_6⟩,
  ⟨_, _, RND.cOr_2_7⟩,
  ⟨_, _, RND.cOr_2_8⟩,
  ⟨_, _, RND.cOr_2_9⟩,
  ⟨_, _, RND.cOr_2_10⟩,
  ⟨_, _, RND.cOr_2_11⟩,
  ⟨_, _, RND.cOr_2_12⟩,
  ⟨_, _, RND.cOr_3_4⟩,
  ⟨_, _, RND.cOr_3_5⟩,
  ⟨_, _, RND.cOr_3_7⟩,
  ⟨_, _, RND.cOr_3_8⟩,
  ⟨_, _, RND.cOr_3_9⟩,
  ⟨_, _, RND.cOr_3_10⟩,
  ⟨_, _, RND.cOr_3_11⟩,
  ⟨_, _, RND.cOr_3_12⟩,
  ⟨_, _, RND.cOr_4_5⟩,
  ⟨_, _, RND.cOr_4_6⟩,
  ⟨_, _, RND.cOr_4_7⟩,
  ⟨_, _, RND.cOr_4_8⟩,
  ⟨_, _, RND.cOr_4_9⟩,
  ⟨_, _, RND.cOr_4_10⟩,
  ⟨_, _, RND.cOr_4_11⟩,
  ⟨_, _, RND.cOr_4_12⟩,
  ⟨_, _, RND.cOr_4_13⟩,
  ⟨_, _, RND.cOr_5_7⟩,
  ⟨_, _, RND.cOr_5_9⟩,
  ⟨_, _, RND.cOr_5_10⟩,
  ⟨_, _, RND.cOr_5_11⟩,
  ⟨_, _, RND.cOr_5_12⟩,
  ⟨_, _, RND.cOr_5_13⟩,
  ⟨_, _, RND.cOr_6_7⟩,
  ⟨_, _, RND.cOr_6_8⟩,
  ⟨_, _, RND.cOr_6_9⟩,
  ⟨_, _, RND.cOr_6_11⟩,
  ⟨_, _, RND.cOr_6_12⟩,
  ⟨_, _, RND.cOr_7_8⟩,
  ⟨_, _, RND.cOr_7_9⟩,
  ⟨_, _, RND.cOr_7_10⟩,
  ⟨_, _, RND.cOr_7_11⟩,
  ⟨_, _, RND.cOr_7_12⟩,
  ⟨_, _, RND.cOr_9_10⟩,
  ⟨_, _, RND.cOr_9_11⟩,
  ⟨_, _, RND.cOr_9_12⟩,
  ⟨_, _, RND.cOr_10_11⟩,
  ⟨_, _, RND.cImp_2_3⟩,
  ⟨_, _, RND.cImp_2_4⟩,
  ⟨_, _, RND.cImp_2_5⟩,
  ⟨_, _, RND.cImp_2_6⟩,
  ⟨_, _, RND.cImp_2_7⟩,
  ⟨_, _, RND.cImp_2_8⟩,
  ⟨_, _, RND.cImp_2_9⟩,
  ⟨_, _, RND.cImp_2_10⟩,
  ⟨_, _, RND.cImp_2_11⟩,
  ⟨_, _, RND.cImp_2_12⟩,
  ⟨_, _, RND.cImp_2_13⟩,
  ⟨_, _, RND.cImp_2_14⟩,
  ⟨_, _, RND.cImp_3_2⟩,
  ⟨_, _, RND.cImp_3_4⟩,
  ⟨_, _, RND.cImp_3_5⟩,
  ⟨_, _, RND.cImp_3_6⟩,
  ⟨_, _, RND.cImp_3_7⟩,
  ⟨_, _, RND.cImp_3_8⟩,
  ⟨_, _, RND.cImp_3_9⟩,
  ⟨_, _, RND.cImp_3_10⟩,
  ⟨_, _, RND.cImp_3_11⟩,
  ⟨_, _, RND.cImp_3_12⟩,
  ⟨_, _, RND.cImp_3_13⟩,
  ⟨_, _, RND.cImp_3_14⟩,
  ⟨_, _, RND.cImp_4_0⟩,
  ⟨_, _, RND.cImp_4_2⟩,
  ⟨_, _, RND.cImp_4_3⟩,
  ⟨_, _, RND.cImp_4_5⟩,
  ⟨_, _, RND.cImp_4_6⟩,
  ⟨_, _, RND.cImp_4_7⟩,
  ⟨_, _, RND.cImp_4_8⟩,
  ⟨_, _, RND.cImp_4_9⟩,
  ⟨_, _, RND.cImp_4_10⟩,
  ⟨_, _, RND.cImp_4_11⟩,
  ⟨_, _, RND.cImp_4_12⟩,
  ⟨_, _, RND.cImp_4_13⟩,
  ⟨_, _, RND.cImp_4_14⟩,
  ⟨_, _, RND.cImp_5_0⟩,
  ⟨_, _, RND.cImp_5_2⟩,
  ⟨_, _, RND.cImp_5_3⟩,
  ⟨_, _, RND.cImp_5_6⟩,
  ⟨_, _, RND.cImp_5_7⟩,
  ⟨_, _, RND.cImp_5_8⟩,
  ⟨_, _, RND.cImp_5_9⟩,
  ⟨_, _, RND.cImp_5_10⟩,
  ⟨_, _, RND.cImp_5_11⟩,
  ⟨_, _, RND.cImp_5_12⟩,
  ⟨_, _, RND.cImp_5_13⟩,
  ⟨_, _, RND.cImp_5_14⟩,
  ⟨_, _, RND.cImp_6_0⟩,
  ⟨_, _, RND.cImp_6_3⟩,
  ⟨_, _, RND.cImp_6_4⟩,
  ⟨_, _, RND.cImp_6_5⟩,
  ⟨_, _, RND.cImp_6_7⟩,
  ⟨_, _, RND.cImp_6_8⟩,
  ⟨_, _, RND.cImp_6_9⟩,
  ⟨_, _, RND.cImp_6_10⟩,
  ⟨_, _, RND.cImp_6_11⟩,
  ⟨_, _, RND.cImp_6_12⟩,
  ⟨_, _, RND.cImp_6_13⟩,
  ⟨_, _, RND.cImp_6_14⟩,
  ⟨_, _, RND.cImp_7_0⟩,
  ⟨_, _, RND.cImp_7_2⟩,
  ⟨_, _, RND.cImp_7_3⟩,
  ⟨_, _, RND.cImp_7_4⟩,
  ⟨_, _, RND.cImp_7_5⟩,
  ⟨_, _, RND.cImp_7_6⟩,
  ⟨_, _, RND.cImp_7_8⟩,
  ⟨_, _, RND.cImp_7_9⟩,
  ⟨_, _, RND.cImp_7_10⟩,
  ⟨_, _, RND.cImp_7_11⟩,
  ⟨_, _, RND.cImp_7_12⟩,
  ⟨_, _, RND.cImp_7_13⟩,
  ⟨_, _, RND.cImp_7_14⟩,
  ⟨_, _, RND.cImp_8_0⟩,
  ⟨_, _, RND.cImp_8_2⟩,
  ⟨_, _, RND.cImp_8_3⟩,
  ⟨_, _, RND.cImp_8_6⟩,
  ⟨_, _, RND.cImp_8_13⟩,
  ⟨_, _, RND.cImp_9_0⟩,
  ⟨_, _, RND.cImp_9_2⟩,
  ⟨_, _, RND.cImp_9_3⟩,
  ⟨_, _, RND.cImp_9_5⟩,
  ⟨_, _, RND.cImp_9_6⟩,
  ⟨_, _, RND.cImp_9_7⟩,
  ⟨_, _, RND.cImp_9_10⟩,
  ⟨_, _, RND.cImp_9_11⟩,
  ⟨_, _, RND.cImp_9_12⟩,
  ⟨_, _, RND.cImp_9_13⟩,
  ⟨_, _, RND.cImp_9_14⟩,
  ⟨_, _, RND.cImp_10_0⟩,
  ⟨_, _, RND.cImp_10_2⟩,
  ⟨_, _, RND.cImp_10_3⟩,
  ⟨_, _, RND.cImp_10_6⟩,
  ⟨_, _, RND.cImp_10_11⟩,
  ⟨_, _, RND.cImp_11_0⟩,
  ⟨_, _, RND.cImp_11_2⟩,
  ⟨_, _, RND.cImp_11_3⟩,
  ⟨_, _, RND.cImp_11_5⟩,
  ⟨_, _, RND.cImp_11_6⟩,
  ⟨_, _, RND.cImp_11_10⟩,
  ⟨_, _, RND.cImp_12_0⟩,
  ⟨_, _, RND.cImp_12_2⟩,
  ⟨_, _, RND.cImp_12_3⟩,
  ⟨_, _, RND.cImp_12_5⟩,
  ⟨_, _, RND.cImp_12_6⟩,
  ⟨_, _, RND.cImp_12_10⟩,
  ⟨_, _, RND.cImp_12_13⟩,
  ⟨_, _, RND.cImp_12_14⟩,
  ⟨_, _, RND.cImp_13_0⟩,
  ⟨_, _, RND.cImp_13_2⟩,
  ⟨_, _, RND.cImp_13_3⟩,
  ⟨_, _, RND.cImp_13_4⟩,
  ⟨_, _, RND.cImp_13_6⟩,
  ⟨_, _, RND.cImp_13_7⟩,
  ⟨_, _, RND.cImp_13_10⟩,
  ⟨_, _, RND.cImp_14_0⟩,
  ⟨_, _, RND.cImp_14_2⟩,
  ⟨_, _, RND.cImp_14_3⟩,
  ⟨_, _, RND.cImp_14_6⟩,
  ⟨_, _, RND.cImp_14_10⟩,
  ⟨_, _, RND.cBox_1⟩,
  ⟨_, _, RND.cBox_4⟩,
  ⟨_, _, RND.cBox_6⟩,
  ⟨_, _, RND.cBox_9⟩,
  ⟨_, _, RND.cBox_10⟩ ]

/-- The R-increment rules (`wip/rcells.lean`, GENERATED — the classed
R-table cells involving ρ13–ρ21, G4c-certificate route; the R-peg
standing rule, 2026-08-26).  442 rules; grows with R, never shrinks. -/
def rcSet : List RwRule := RCX.rcSet

/-- The full PLL simpset: the modal laws, the table, and the
R-increment. -/
def fullSet : List RwRule := pllSet ++ rndSet ++ rcSet

/-- **The canonicalised simpset — use THIS in a sweep.**  Computed
once here rather than per goal; the rules are stated in the
dictionary's argument order, so without this pass the canonicaliser
sorts goals out of their reach. -/
def fullSetC : List RwRule := canonSet fullSet

/-! ## Pins — the standing guard against harvesting an unproved cell -/

/-- info: 'Rewrite.rndSet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rndSet

/-- info: 'Rewrite.fullSet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullSet

/-- info: 'Rewrite.fullSetC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fullSetC

end Rewrite
