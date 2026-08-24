/-
# Round-R2 dictionary cells as DATABASE ENTRIES

GENERATED 2026-08-24; regenerate rather than hand-edit.  Each entry cites
a kernel-checked `Interd` theorem from `wip/rnDict2.lean` — every cell of round 2 whose proof is sorry-free (byte-level check, comments stripped).  The claims are
stated in the SHARED vocabulary (`LaxLogic/RN/Reps.lean`); the cited
theorems live in the dictionary's own namespace, and the two agree
definitionally or this file does not compile.

Provenance `Engine.hand`: these are tactic/hand proofs from the
dictionary campaign, not engine output.  The dictionary's WITHDRAWN
bookkeeping (tags, tallies, sorried statements) is not consulted:
the name list here is exactly the sorry-free subset, re-measured at generation time.
-/
import RNDB.Types
import LaxLogic.RN.Reps
import wip.rnDict2

open PLLND PLLND.SemUI

namespace RNDB

/-- Closed, so `decide` applies; under the constructor's binders the
same goal mentions free variables and `decide` refuses it.  The literal's
`.rel` projection is definitionally `Rel.interd`, so this one proof
serves every entry. -/
theorem relInterdPosR2 : Rel.interd.IsPositive := by decide

/-- A positive interderivability entry: no scope needed (`wellScoped`
holds for every positive relation however the field is filled). -/

def interdEntryR2 (id : EntryId) (a b : PLLFormula)
    (h : Interd a b) : Entry where
  id := id
  claim := ⟨a, b, Rel.interd, none⟩
  ev := Evidence.proof Engine.hand
  ok := ⟨Claim.wellScoped_of_pos relInterdPosR2, relInterdPosR2, h⟩

def d2_cAnd_10_14 : Entry := interdEntryR2 "d2-0000" ((RNReps.q10).and (RNReps.q14)) (RNReps.q5) PLLND.SemUI.RND2.cAnd_10_14
def d2_cAnd_10_15 : Entry := interdEntryR2 "d2-0001" ((RNReps.q10).and (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_10_15
def d2_cAnd_11_14 : Entry := interdEntryR2 "d2-0002" ((RNReps.q11).and (RNReps.q14)) (RNReps.q9) PLLND.SemUI.RND2.cAnd_11_14
def d2_cAnd_11_15 : Entry := interdEntryR2 "d2-0003" ((RNReps.q11).and (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_11_15
def d2_cAnd_12_13 : Entry := interdEntryR2 "d2-0004" ((RNReps.q12).and (RNReps.q13)) (RNReps.q12) PLLND.SemUI.RND2.cAnd_12_13
def d2_cAnd_12_14 : Entry := interdEntryR2 "d2-0005" ((RNReps.q12).and (RNReps.q14)) (RNReps.q12) PLLND.SemUI.RND2.cAnd_12_14
def d2_cAnd_12_15 : Entry := interdEntryR2 "d2-0006" ((RNReps.q12).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_12_15
def d2_cAnd_13_15 : Entry := interdEntryR2 "d2-0007" ((RNReps.q13).and (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_13_15
def d2_cAnd_14_15 : Entry := interdEntryR2 "d2-0008" ((RNReps.q14).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_14_15
def d2_cAnd_2_15 : Entry := interdEntryR2 "d2-0009" ((RNReps.q2).and (RNReps.q15)) (RNReps.q2) PLLND.SemUI.RND2.cAnd_2_15
def d2_cAnd_3_15 : Entry := interdEntryR2 "d2-0010" ((RNReps.q3).and (RNReps.q15)) (RNReps.q3) PLLND.SemUI.RND2.cAnd_3_15
def d2_cAnd_4_14 : Entry := interdEntryR2 "d2-0011" ((RNReps.q4).and (RNReps.q14)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_4_14
def d2_cAnd_4_15 : Entry := interdEntryR2 "d2-0012" ((RNReps.q4).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_4_15
def d2_cAnd_5_15 : Entry := interdEntryR2 "d2-0013" ((RNReps.q5).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_5_15
def d2_cAnd_6_15 : Entry := interdEntryR2 "d2-0014" ((RNReps.q6).and (RNReps.q15)) (RNReps.q2) PLLND.SemUI.RND2.cAnd_6_15
def d2_cAnd_7_15 : Entry := interdEntryR2 "d2-0015" ((RNReps.q7).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_7_15
def d2_cAnd_8_10 : Entry := interdEntryR2 "d2-0016" ((RNReps.q8).and (RNReps.q10)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_8_10
def d2_cAnd_8_15 : Entry := interdEntryR2 "d2-0017" ((RNReps.q8).and (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_8_15
def d2_cAnd_9_13 : Entry := interdEntryR2 "d2-0018" ((RNReps.q9).and (RNReps.q13)) (RNReps.q9) PLLND.SemUI.RND2.cAnd_9_13
def d2_cAnd_9_14 : Entry := interdEntryR2 "d2-0019" ((RNReps.q9).and (RNReps.q14)) (RNReps.q9) PLLND.SemUI.RND2.cAnd_9_14
def d2_cAnd_9_15 : Entry := interdEntryR2 "d2-0020" ((RNReps.q9).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_9_15
def d2_cBox_14 : Entry := interdEntryR2 "d2-0021" ((RNReps.q14).somehow) (RNReps.q14) PLLND.SemUI.RND2.cBox_14
def d2_cImp_10_12 : Entry := interdEntryR2 "d2-0022" ((RNReps.q10).ifThen (RNReps.q12)) (RNReps.q14) PLLND.SemUI.RND2.cImp_10_12
def d2_cImp_10_14 : Entry := interdEntryR2 "d2-0023" ((RNReps.q10).ifThen (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cImp_10_14
def d2_cImp_10_15 : Entry := interdEntryR2 "d2-0024" ((RNReps.q10).ifThen (RNReps.q15)) (RNReps.q8) PLLND.SemUI.RND2.cImp_10_15
def d2_cImp_10_8 : Entry := interdEntryR2 "d2-0025" ((RNReps.q10).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_10_8
def d2_cImp_10_9 : Entry := interdEntryR2 "d2-0026" ((RNReps.q10).ifThen (RNReps.q9)) (RNReps.q14) PLLND.SemUI.RND2.cImp_10_9
def d2_cImp_11_12 : Entry := interdEntryR2 "d2-0027" ((RNReps.q11).ifThen (RNReps.q12)) (RNReps.q14) PLLND.SemUI.RND2.cImp_11_12
def d2_cImp_11_14 : Entry := interdEntryR2 "d2-0028" ((RNReps.q11).ifThen (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cImp_11_14
def d2_cImp_11_15 : Entry := interdEntryR2 "d2-0029" ((RNReps.q11).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_11_15
def d2_cImp_11_4 : Entry := interdEntryR2 "d2-0030" ((RNReps.q11).ifThen (RNReps.q4)) (RNReps.q4) PLLND.SemUI.RND2.cImp_11_4
def d2_cImp_11_8 : Entry := interdEntryR2 "d2-0031" ((RNReps.q11).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_11_8
def d2_cImp_11_9 : Entry := interdEntryR2 "d2-0032" ((RNReps.q11).ifThen (RNReps.q9)) (RNReps.q14) PLLND.SemUI.RND2.cImp_11_9
def d2_cImp_12_15 : Entry := interdEntryR2 "d2-0033" ((RNReps.q12).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_12_15
def d2_cImp_12_4 : Entry := interdEntryR2 "d2-0034" ((RNReps.q12).ifThen (RNReps.q4)) (RNReps.q15) PLLND.SemUI.RND2.cImp_12_4
def d2_cImp_12_8 : Entry := interdEntryR2 "d2-0035" ((RNReps.q12).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_12_8
def d2_cImp_13_15 : Entry := interdEntryR2 "d2-0036" ((RNReps.q13).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_13_15
def d2_cImp_13_8 : Entry := interdEntryR2 "d2-0037" ((RNReps.q13).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_13_8
def d2_cImp_14_15 : Entry := interdEntryR2 "d2-0038" ((RNReps.q14).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_14_15
def d2_cImp_14_4 : Entry := interdEntryR2 "d2-0039" ((RNReps.q14).ifThen (RNReps.q4)) (RNReps.q15) PLLND.SemUI.RND2.cImp_14_4
def d2_cImp_14_5 : Entry := interdEntryR2 "d2-0040" ((RNReps.q14).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND2.cImp_14_5
def d2_cImp_14_8 : Entry := interdEntryR2 "d2-0041" ((RNReps.q14).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_14_8
def d2_cImp_15_0 : Entry := interdEntryR2 "d2-0042" ((RNReps.q15).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND2.cImp_15_0
def d2_cImp_15_10 : Entry := interdEntryR2 "d2-0043" ((RNReps.q15).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND2.cImp_15_10
def d2_cImp_15_11 : Entry := interdEntryR2 "d2-0044" ((RNReps.q15).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND2.cImp_15_11
def d2_cImp_15_13 : Entry := interdEntryR2 "d2-0045" ((RNReps.q15).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND2.cImp_15_13
def d2_cImp_15_2 : Entry := interdEntryR2 "d2-0046" ((RNReps.q15).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND2.cImp_15_2
def d2_cImp_15_3 : Entry := interdEntryR2 "d2-0047" ((RNReps.q15).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND2.cImp_15_3
def d2_cImp_15_6 : Entry := interdEntryR2 "d2-0048" ((RNReps.q15).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND2.cImp_15_6
def d2_cImp_15_8 : Entry := interdEntryR2 "d2-0049" ((RNReps.q15).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND2.cImp_15_8
def d2_cImp_2_15 : Entry := interdEntryR2 "d2-0050" ((RNReps.q2).ifThen (RNReps.q15)) (RNReps.q1) PLLND.SemUI.RND2.cImp_2_15
def d2_cImp_3_15 : Entry := interdEntryR2 "d2-0051" ((RNReps.q3).ifThen (RNReps.q15)) (RNReps.q1) PLLND.SemUI.RND2.cImp_3_15
def d2_cImp_4_15 : Entry := interdEntryR2 "d2-0052" ((RNReps.q4).ifThen (RNReps.q15)) (RNReps.q1) PLLND.SemUI.RND2.cImp_4_15
def d2_cImp_5_15 : Entry := interdEntryR2 "d2-0053" ((RNReps.q5).ifThen (RNReps.q15)) (RNReps.q8) PLLND.SemUI.RND2.cImp_5_15
def d2_cImp_6_15 : Entry := interdEntryR2 "d2-0054" ((RNReps.q6).ifThen (RNReps.q15)) (RNReps.q10) PLLND.SemUI.RND2.cImp_6_15
def d2_cImp_7_15 : Entry := interdEntryR2 "d2-0055" ((RNReps.q7).ifThen (RNReps.q15)) (RNReps.q10) PLLND.SemUI.RND2.cImp_7_15
def d2_cImp_8_10 : Entry := interdEntryR2 "d2-0056" ((RNReps.q8).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND2.cImp_8_10
def d2_cImp_8_15 : Entry := interdEntryR2 "d2-0057" ((RNReps.q8).ifThen (RNReps.q15)) (RNReps.q10) PLLND.SemUI.RND2.cImp_8_15
def d2_cImp_9_15 : Entry := interdEntryR2 "d2-0058" ((RNReps.q9).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_9_15
def d2_cImp_9_8 : Entry := interdEntryR2 "d2-0059" ((RNReps.q9).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_9_8
def d2_cOr_10_15 : Entry := interdEntryR2 "d2-0060" ((RNReps.q10).or (RNReps.q15)) (RNReps.q10) PLLND.SemUI.RND2.cOr_10_15
def d2_cOr_11_15 : Entry := interdEntryR2 "d2-0061" ((RNReps.q11).or (RNReps.q15)) (RNReps.q11) PLLND.SemUI.RND2.cOr_11_15
def d2_cOr_12_13 : Entry := interdEntryR2 "d2-0062" ((RNReps.q12).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_12_13
def d2_cOr_12_14 : Entry := interdEntryR2 "d2-0063" ((RNReps.q12).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_12_14
def d2_cOr_13_15 : Entry := interdEntryR2 "d2-0064" ((RNReps.q13).or (RNReps.q15)) (RNReps.q13) PLLND.SemUI.RND2.cOr_13_15
def d2_cOr_2_13 : Entry := interdEntryR2 "d2-0065" ((RNReps.q2).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_2_13
def d2_cOr_2_14 : Entry := interdEntryR2 "d2-0066" ((RNReps.q2).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_2_14
def d2_cOr_2_15 : Entry := interdEntryR2 "d2-0067" ((RNReps.q2).or (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cOr_2_15
def d2_cOr_3_13 : Entry := interdEntryR2 "d2-0068" ((RNReps.q3).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_3_13
def d2_cOr_3_14 : Entry := interdEntryR2 "d2-0069" ((RNReps.q3).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_3_14
def d2_cOr_3_15 : Entry := interdEntryR2 "d2-0070" ((RNReps.q3).or (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cOr_3_15
def d2_cOr_4_14 : Entry := interdEntryR2 "d2-0071" ((RNReps.q4).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_4_14
def d2_cOr_4_15 : Entry := interdEntryR2 "d2-0072" ((RNReps.q4).or (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cOr_4_15
def d2_cOr_5_14 : Entry := interdEntryR2 "d2-0073" ((RNReps.q5).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_5_14
def d2_cOr_6_13 : Entry := interdEntryR2 "d2-0074" ((RNReps.q6).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_6_13
def d2_cOr_6_14 : Entry := interdEntryR2 "d2-0075" ((RNReps.q6).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_6_14
def d2_cOr_7_13 : Entry := interdEntryR2 "d2-0076" ((RNReps.q7).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_7_13
def d2_cOr_7_14 : Entry := interdEntryR2 "d2-0077" ((RNReps.q7).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_7_14
def d2_cOr_8_13 : Entry := interdEntryR2 "d2-0078" ((RNReps.q8).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_8_13
def d2_cOr_8_15 : Entry := interdEntryR2 "d2-0079" ((RNReps.q8).or (RNReps.q15)) (RNReps.q8) PLLND.SemUI.RND2.cOr_8_15
def d2_cOr_9_13 : Entry := interdEntryR2 "d2-0080" ((RNReps.q9).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_9_13
def d2_cOr_9_14 : Entry := interdEntryR2 "d2-0081" ((RNReps.q9).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_9_14

def dictEntriesR2 : List Entry :=
  [ d2_cAnd_10_14,
    d2_cAnd_10_15,
    d2_cAnd_11_14,
    d2_cAnd_11_15,
    d2_cAnd_12_13,
    d2_cAnd_12_14,
    d2_cAnd_12_15,
    d2_cAnd_13_15,
    d2_cAnd_14_15,
    d2_cAnd_2_15,
    d2_cAnd_3_15,
    d2_cAnd_4_14,
    d2_cAnd_4_15,
    d2_cAnd_5_15,
    d2_cAnd_6_15,
    d2_cAnd_7_15,
    d2_cAnd_8_10,
    d2_cAnd_8_15,
    d2_cAnd_9_13,
    d2_cAnd_9_14,
    d2_cAnd_9_15,
    d2_cBox_14,
    d2_cImp_10_12,
    d2_cImp_10_14,
    d2_cImp_10_15,
    d2_cImp_10_8,
    d2_cImp_10_9,
    d2_cImp_11_12,
    d2_cImp_11_14,
    d2_cImp_11_15,
    d2_cImp_11_4,
    d2_cImp_11_8,
    d2_cImp_11_9,
    d2_cImp_12_15,
    d2_cImp_12_4,
    d2_cImp_12_8,
    d2_cImp_13_15,
    d2_cImp_13_8,
    d2_cImp_14_15,
    d2_cImp_14_4,
    d2_cImp_14_5,
    d2_cImp_14_8,
    d2_cImp_15_0,
    d2_cImp_15_10,
    d2_cImp_15_11,
    d2_cImp_15_13,
    d2_cImp_15_2,
    d2_cImp_15_3,
    d2_cImp_15_6,
    d2_cImp_15_8,
    d2_cImp_2_15,
    d2_cImp_3_15,
    d2_cImp_4_15,
    d2_cImp_5_15,
    d2_cImp_6_15,
    d2_cImp_7_15,
    d2_cImp_8_10,
    d2_cImp_8_15,
    d2_cImp_9_15,
    d2_cImp_9_8,
    d2_cOr_10_15,
    d2_cOr_11_15,
    d2_cOr_12_13,
    d2_cOr_12_14,
    d2_cOr_13_15,
    d2_cOr_2_13,
    d2_cOr_2_14,
    d2_cOr_2_15,
    d2_cOr_3_13,
    d2_cOr_3_14,
    d2_cOr_3_15,
    d2_cOr_4_14,
    d2_cOr_4_15,
    d2_cOr_5_14,
    d2_cOr_6_13,
    d2_cOr_6_14,
    d2_cOr_7_13,
    d2_cOr_7_14,
    d2_cOr_8_13,
    d2_cOr_8_15,
    d2_cOr_9_13,
    d2_cOr_9_14 ]

set_option maxRecDepth 8192 in
theorem dictEntriesR2_length : dictEntriesR2.length = 82 := rfl

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.dictEntriesR2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dictEntriesR2

/-- info: 'RNDB.dictEntriesR2_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dictEntriesR2_length

end RNDB