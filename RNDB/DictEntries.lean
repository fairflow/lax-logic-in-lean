/-
# Round-R1 dictionary cells as DATABASE ENTRIES

GENERATED 2026-08-24; regenerate rather than hand-edit.  Each entry cites
a kernel-checked `Interd` theorem from `wip/rnDict.lean` — the 236 cells the pin-guarded `Rewrite.rndSet` harvests.  The claims are
stated in the SHARED vocabulary (`LaxLogic/RN/Reps.lean`); the cited
theorems live in the dictionary's own namespace, and the two agree
definitionally or this file does not compile.

Provenance `Engine.hand`: these are tactic/hand proofs from the
dictionary campaign, not engine output.  The dictionary's WITHDRAWN
bookkeeping (tags, tallies, sorried statements) is not consulted:
the name list here is exactly the `rndSet` literal of `Rewrite/Catalogue.lean`.
-/
import RNDB.Types
import LaxLogic.RN.Reps
import wip.rnDict

open PLLND PLLND.SemUI

namespace RNDB

/-- Closed, so `decide` applies; under the constructor's binders the
same goal mentions free variables and `decide` refuses it.  The literal's
`.rel` projection is definitionally `Rel.interd`, so this one proof
serves every entry. -/
theorem relInterdPosR1 : Rel.interd.IsPositive := by decide

/-- A positive interderivability entry: no scope needed (`wellScoped`
holds for every positive relation however the field is filled). -/

def interdEntryR1 (id : EntryId) (a b : PLLFormula)
    (h : Interd a b) : Entry where
  id := id
  claim := ⟨a, b, Rel.interd, none⟩
  ev := Evidence.proof Engine.hand
  ok := ⟨Claim.wellScoped_of_pos relInterdPosR1, relInterdPosR1, h⟩

def d1_cAnd_10_11 : Entry := interdEntryR1 "d1-0000" ((RNReps.q10).and (RNReps.q11)) (RNReps.q10) PLLND.SemUI.RND.cAnd_10_11
def d1_cAnd_10_12 : Entry := interdEntryR1 "d1-0001" ((RNReps.q10).and (RNReps.q12)) (RNReps.q5) PLLND.SemUI.RND.cAnd_10_12
def d1_cAnd_11_12 : Entry := interdEntryR1 "d1-0002" ((RNReps.q11).and (RNReps.q12)) (RNReps.q9) PLLND.SemUI.RND.cAnd_11_12
def d1_cAnd_2_10 : Entry := interdEntryR1 "d1-0003" ((RNReps.q2).and (RNReps.q10)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_10
def d1_cAnd_2_11 : Entry := interdEntryR1 "d1-0004" ((RNReps.q2).and (RNReps.q11)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_11
def d1_cAnd_2_12 : Entry := interdEntryR1 "d1-0005" ((RNReps.q2).and (RNReps.q12)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_12
def d1_cAnd_2_13 : Entry := interdEntryR1 "d1-0006" ((RNReps.q2).and (RNReps.q13)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_13
def d1_cAnd_2_14 : Entry := interdEntryR1 "d1-0007" ((RNReps.q2).and (RNReps.q14)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_14
def d1_cAnd_2_3 : Entry := interdEntryR1 "d1-0008" ((RNReps.q2).and (RNReps.q3)) (RNReps.q0) PLLND.SemUI.RND.cAnd_2_3
def d1_cAnd_2_4 : Entry := interdEntryR1 "d1-0009" ((RNReps.q2).and (RNReps.q4)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_4
def d1_cAnd_2_5 : Entry := interdEntryR1 "d1-0010" ((RNReps.q2).and (RNReps.q5)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_5
def d1_cAnd_2_6 : Entry := interdEntryR1 "d1-0011" ((RNReps.q2).and (RNReps.q6)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_6
def d1_cAnd_2_7 : Entry := interdEntryR1 "d1-0012" ((RNReps.q2).and (RNReps.q7)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_7
def d1_cAnd_2_8 : Entry := interdEntryR1 "d1-0013" ((RNReps.q2).and (RNReps.q8)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_8
def d1_cAnd_2_9 : Entry := interdEntryR1 "d1-0014" ((RNReps.q2).and (RNReps.q9)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_9
def d1_cAnd_3_10 : Entry := interdEntryR1 "d1-0015" ((RNReps.q3).and (RNReps.q10)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_10
def d1_cAnd_3_11 : Entry := interdEntryR1 "d1-0016" ((RNReps.q3).and (RNReps.q11)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_11
def d1_cAnd_3_12 : Entry := interdEntryR1 "d1-0017" ((RNReps.q3).and (RNReps.q12)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_12
def d1_cAnd_3_13 : Entry := interdEntryR1 "d1-0018" ((RNReps.q3).and (RNReps.q13)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_13
def d1_cAnd_3_14 : Entry := interdEntryR1 "d1-0019" ((RNReps.q3).and (RNReps.q14)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_14
def d1_cAnd_3_4 : Entry := interdEntryR1 "d1-0020" ((RNReps.q3).and (RNReps.q4)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_4
def d1_cAnd_3_5 : Entry := interdEntryR1 "d1-0021" ((RNReps.q3).and (RNReps.q5)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_5
def d1_cAnd_3_6 : Entry := interdEntryR1 "d1-0022" ((RNReps.q3).and (RNReps.q6)) (RNReps.q0) PLLND.SemUI.RND.cAnd_3_6
def d1_cAnd_3_7 : Entry := interdEntryR1 "d1-0023" ((RNReps.q3).and (RNReps.q7)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_7
def d1_cAnd_3_8 : Entry := interdEntryR1 "d1-0024" ((RNReps.q3).and (RNReps.q8)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_8
def d1_cAnd_3_9 : Entry := interdEntryR1 "d1-0025" ((RNReps.q3).and (RNReps.q9)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_9
def d1_cAnd_4_10 : Entry := interdEntryR1 "d1-0026" ((RNReps.q4).and (RNReps.q10)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_10
def d1_cAnd_4_11 : Entry := interdEntryR1 "d1-0027" ((RNReps.q4).and (RNReps.q11)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_11
def d1_cAnd_4_12 : Entry := interdEntryR1 "d1-0028" ((RNReps.q4).and (RNReps.q12)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_12
def d1_cAnd_4_13 : Entry := interdEntryR1 "d1-0029" ((RNReps.q4).and (RNReps.q13)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_13
def d1_cAnd_4_5 : Entry := interdEntryR1 "d1-0030" ((RNReps.q4).and (RNReps.q5)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_5
def d1_cAnd_4_6 : Entry := interdEntryR1 "d1-0031" ((RNReps.q4).and (RNReps.q6)) (RNReps.q2) PLLND.SemUI.RND.cAnd_4_6
def d1_cAnd_4_7 : Entry := interdEntryR1 "d1-0032" ((RNReps.q4).and (RNReps.q7)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_7
def d1_cAnd_4_8 : Entry := interdEntryR1 "d1-0033" ((RNReps.q4).and (RNReps.q8)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_8
def d1_cAnd_4_9 : Entry := interdEntryR1 "d1-0034" ((RNReps.q4).and (RNReps.q9)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_9
def d1_cAnd_5_10 : Entry := interdEntryR1 "d1-0035" ((RNReps.q5).and (RNReps.q10)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_10
def d1_cAnd_5_11 : Entry := interdEntryR1 "d1-0036" ((RNReps.q5).and (RNReps.q11)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_11
def d1_cAnd_5_12 : Entry := interdEntryR1 "d1-0037" ((RNReps.q5).and (RNReps.q12)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_12
def d1_cAnd_5_13 : Entry := interdEntryR1 "d1-0038" ((RNReps.q5).and (RNReps.q13)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_13
def d1_cAnd_5_14 : Entry := interdEntryR1 "d1-0039" ((RNReps.q5).and (RNReps.q14)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_14
def d1_cAnd_5_6 : Entry := interdEntryR1 "d1-0040" ((RNReps.q5).and (RNReps.q6)) (RNReps.q2) PLLND.SemUI.RND.cAnd_5_6
def d1_cAnd_5_7 : Entry := interdEntryR1 "d1-0041" ((RNReps.q5).and (RNReps.q7)) (RNReps.q4) PLLND.SemUI.RND.cAnd_5_7
def d1_cAnd_5_8 : Entry := interdEntryR1 "d1-0042" ((RNReps.q5).and (RNReps.q8)) (RNReps.q4) PLLND.SemUI.RND.cAnd_5_8
def d1_cAnd_5_9 : Entry := interdEntryR1 "d1-0043" ((RNReps.q5).and (RNReps.q9)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_9
def d1_cAnd_6_10 : Entry := interdEntryR1 "d1-0044" ((RNReps.q6).and (RNReps.q10)) (RNReps.q2) PLLND.SemUI.RND.cAnd_6_10
def d1_cAnd_6_11 : Entry := interdEntryR1 "d1-0045" ((RNReps.q6).and (RNReps.q11)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_11
def d1_cAnd_6_12 : Entry := interdEntryR1 "d1-0046" ((RNReps.q6).and (RNReps.q12)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_12
def d1_cAnd_6_13 : Entry := interdEntryR1 "d1-0047" ((RNReps.q6).and (RNReps.q13)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_13
def d1_cAnd_6_14 : Entry := interdEntryR1 "d1-0048" ((RNReps.q6).and (RNReps.q14)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_14
def d1_cAnd_6_7 : Entry := interdEntryR1 "d1-0049" ((RNReps.q6).and (RNReps.q7)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_7
def d1_cAnd_6_8 : Entry := interdEntryR1 "d1-0050" ((RNReps.q6).and (RNReps.q8)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_8
def d1_cAnd_6_9 : Entry := interdEntryR1 "d1-0051" ((RNReps.q6).and (RNReps.q9)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_9
def d1_cAnd_7_10 : Entry := interdEntryR1 "d1-0052" ((RNReps.q7).and (RNReps.q10)) (RNReps.q4) PLLND.SemUI.RND.cAnd_7_10
def d1_cAnd_7_11 : Entry := interdEntryR1 "d1-0053" ((RNReps.q7).and (RNReps.q11)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_11
def d1_cAnd_7_12 : Entry := interdEntryR1 "d1-0054" ((RNReps.q7).and (RNReps.q12)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_12
def d1_cAnd_7_13 : Entry := interdEntryR1 "d1-0055" ((RNReps.q7).and (RNReps.q13)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_13
def d1_cAnd_7_14 : Entry := interdEntryR1 "d1-0056" ((RNReps.q7).and (RNReps.q14)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_14
def d1_cAnd_7_8 : Entry := interdEntryR1 "d1-0057" ((RNReps.q7).and (RNReps.q8)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_8
def d1_cAnd_7_9 : Entry := interdEntryR1 "d1-0058" ((RNReps.q7).and (RNReps.q9)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_9
def d1_cAnd_8_13 : Entry := interdEntryR1 "d1-0059" ((RNReps.q8).and (RNReps.q13)) (RNReps.q8) PLLND.SemUI.RND.cAnd_8_13
def d1_cAnd_8_9 : Entry := interdEntryR1 "d1-0060" ((RNReps.q8).and (RNReps.q9)) (RNReps.q7) PLLND.SemUI.RND.cAnd_8_9
def d1_cAnd_9_10 : Entry := interdEntryR1 "d1-0061" ((RNReps.q9).and (RNReps.q10)) (RNReps.q5) PLLND.SemUI.RND.cAnd_9_10
def d1_cAnd_9_11 : Entry := interdEntryR1 "d1-0062" ((RNReps.q9).and (RNReps.q11)) (RNReps.q9) PLLND.SemUI.RND.cAnd_9_11
def d1_cAnd_9_12 : Entry := interdEntryR1 "d1-0063" ((RNReps.q9).and (RNReps.q12)) (RNReps.q9) PLLND.SemUI.RND.cAnd_9_12
def d1_cBox_1 : Entry := interdEntryR1 "d1-0064" ((RNReps.q1).somehow) (RNReps.q1) PLLND.SemUI.RND.cBox_1
def d1_cBox_10 : Entry := interdEntryR1 "d1-0065" ((RNReps.q10).somehow) (RNReps.q10) PLLND.SemUI.RND.cBox_10
def d1_cBox_4 : Entry := interdEntryR1 "d1-0066" ((RNReps.q4).somehow) (RNReps.q5) PLLND.SemUI.RND.cBox_4
def d1_cBox_6 : Entry := interdEntryR1 "d1-0067" ((RNReps.q6).somehow) (RNReps.q6) PLLND.SemUI.RND.cBox_6
def d1_cBox_9 : Entry := interdEntryR1 "d1-0068" ((RNReps.q9).somehow) (RNReps.q12) PLLND.SemUI.RND.cBox_9
def d1_cImp_10_0 : Entry := interdEntryR1 "d1-0069" ((RNReps.q10).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_10_0
def d1_cImp_10_11 : Entry := interdEntryR1 "d1-0070" ((RNReps.q10).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_10_11
def d1_cImp_10_2 : Entry := interdEntryR1 "d1-0071" ((RNReps.q10).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND.cImp_10_2
def d1_cImp_10_3 : Entry := interdEntryR1 "d1-0072" ((RNReps.q10).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_10_3
def d1_cImp_10_6 : Entry := interdEntryR1 "d1-0073" ((RNReps.q10).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_10_6
def d1_cImp_11_0 : Entry := interdEntryR1 "d1-0074" ((RNReps.q11).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_11_0
def d1_cImp_11_10 : Entry := interdEntryR1 "d1-0075" ((RNReps.q11).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_11_10
def d1_cImp_11_2 : Entry := interdEntryR1 "d1-0076" ((RNReps.q11).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_11_2
def d1_cImp_11_3 : Entry := interdEntryR1 "d1-0077" ((RNReps.q11).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_11_3
def d1_cImp_11_5 : Entry := interdEntryR1 "d1-0078" ((RNReps.q11).ifThen (RNReps.q5)) (RNReps.q5) PLLND.SemUI.RND.cImp_11_5
def d1_cImp_11_6 : Entry := interdEntryR1 "d1-0079" ((RNReps.q11).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_11_6
def d1_cImp_12_0 : Entry := interdEntryR1 "d1-0080" ((RNReps.q12).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_12_0
def d1_cImp_12_10 : Entry := interdEntryR1 "d1-0081" ((RNReps.q12).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_12_10
def d1_cImp_12_13 : Entry := interdEntryR1 "d1-0082" ((RNReps.q12).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_12_13
def d1_cImp_12_14 : Entry := interdEntryR1 "d1-0083" ((RNReps.q12).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_12_14
def d1_cImp_12_2 : Entry := interdEntryR1 "d1-0084" ((RNReps.q12).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_12_2
def d1_cImp_12_3 : Entry := interdEntryR1 "d1-0085" ((RNReps.q12).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_12_3
def d1_cImp_12_5 : Entry := interdEntryR1 "d1-0086" ((RNReps.q12).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND.cImp_12_5
def d1_cImp_12_6 : Entry := interdEntryR1 "d1-0087" ((RNReps.q12).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_12_6
def d1_cImp_13_0 : Entry := interdEntryR1 "d1-0088" ((RNReps.q13).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_13_0
def d1_cImp_13_10 : Entry := interdEntryR1 "d1-0089" ((RNReps.q13).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_13_10
def d1_cImp_13_2 : Entry := interdEntryR1 "d1-0090" ((RNReps.q13).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_13_2
def d1_cImp_13_3 : Entry := interdEntryR1 "d1-0091" ((RNReps.q13).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_13_3
def d1_cImp_13_4 : Entry := interdEntryR1 "d1-0092" ((RNReps.q13).ifThen (RNReps.q4)) (RNReps.q4) PLLND.SemUI.RND.cImp_13_4
def d1_cImp_13_6 : Entry := interdEntryR1 "d1-0093" ((RNReps.q13).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_13_6
def d1_cImp_13_7 : Entry := interdEntryR1 "d1-0094" ((RNReps.q13).ifThen (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cImp_13_7
def d1_cImp_14_0 : Entry := interdEntryR1 "d1-0095" ((RNReps.q14).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_14_0
def d1_cImp_14_10 : Entry := interdEntryR1 "d1-0096" ((RNReps.q14).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_14_10
def d1_cImp_14_2 : Entry := interdEntryR1 "d1-0097" ((RNReps.q14).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_14_2
def d1_cImp_14_3 : Entry := interdEntryR1 "d1-0098" ((RNReps.q14).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_14_3
def d1_cImp_14_6 : Entry := interdEntryR1 "d1-0099" ((RNReps.q14).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_14_6
def d1_cImp_2_10 : Entry := interdEntryR1 "d1-0100" ((RNReps.q2).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_10
def d1_cImp_2_11 : Entry := interdEntryR1 "d1-0101" ((RNReps.q2).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_11
def d1_cImp_2_12 : Entry := interdEntryR1 "d1-0102" ((RNReps.q2).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_12
def d1_cImp_2_13 : Entry := interdEntryR1 "d1-0103" ((RNReps.q2).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_13
def d1_cImp_2_14 : Entry := interdEntryR1 "d1-0104" ((RNReps.q2).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_14
def d1_cImp_2_3 : Entry := interdEntryR1 "d1-0105" ((RNReps.q2).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_2_3
def d1_cImp_2_4 : Entry := interdEntryR1 "d1-0106" ((RNReps.q2).ifThen (RNReps.q4)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_4
def d1_cImp_2_5 : Entry := interdEntryR1 "d1-0107" ((RNReps.q2).ifThen (RNReps.q5)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_5
def d1_cImp_2_6 : Entry := interdEntryR1 "d1-0108" ((RNReps.q2).ifThen (RNReps.q6)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_6
def d1_cImp_2_7 : Entry := interdEntryR1 "d1-0109" ((RNReps.q2).ifThen (RNReps.q7)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_7
def d1_cImp_2_8 : Entry := interdEntryR1 "d1-0110" ((RNReps.q2).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_8
def d1_cImp_2_9 : Entry := interdEntryR1 "d1-0111" ((RNReps.q2).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_9
def d1_cImp_3_10 : Entry := interdEntryR1 "d1-0112" ((RNReps.q3).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_10
def d1_cImp_3_11 : Entry := interdEntryR1 "d1-0113" ((RNReps.q3).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_11
def d1_cImp_3_12 : Entry := interdEntryR1 "d1-0114" ((RNReps.q3).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_12
def d1_cImp_3_13 : Entry := interdEntryR1 "d1-0115" ((RNReps.q3).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_13
def d1_cImp_3_14 : Entry := interdEntryR1 "d1-0116" ((RNReps.q3).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_14
def d1_cImp_3_2 : Entry := interdEntryR1 "d1-0117" ((RNReps.q3).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND.cImp_3_2
def d1_cImp_3_4 : Entry := interdEntryR1 "d1-0118" ((RNReps.q3).ifThen (RNReps.q4)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_4
def d1_cImp_3_5 : Entry := interdEntryR1 "d1-0119" ((RNReps.q3).ifThen (RNReps.q5)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_5
def d1_cImp_3_6 : Entry := interdEntryR1 "d1-0120" ((RNReps.q3).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_3_6
def d1_cImp_3_7 : Entry := interdEntryR1 "d1-0121" ((RNReps.q3).ifThen (RNReps.q7)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_7
def d1_cImp_3_8 : Entry := interdEntryR1 "d1-0122" ((RNReps.q3).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_8
def d1_cImp_3_9 : Entry := interdEntryR1 "d1-0123" ((RNReps.q3).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_9
def d1_cImp_4_0 : Entry := interdEntryR1 "d1-0124" ((RNReps.q4).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_4_0
def d1_cImp_4_10 : Entry := interdEntryR1 "d1-0125" ((RNReps.q4).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_10
def d1_cImp_4_11 : Entry := interdEntryR1 "d1-0126" ((RNReps.q4).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_11
def d1_cImp_4_12 : Entry := interdEntryR1 "d1-0127" ((RNReps.q4).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_12
def d1_cImp_4_13 : Entry := interdEntryR1 "d1-0128" ((RNReps.q4).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_13
def d1_cImp_4_14 : Entry := interdEntryR1 "d1-0129" ((RNReps.q4).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_14
def d1_cImp_4_2 : Entry := interdEntryR1 "d1-0130" ((RNReps.q4).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND.cImp_4_2
def d1_cImp_4_3 : Entry := interdEntryR1 "d1-0131" ((RNReps.q4).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_4_3
def d1_cImp_4_5 : Entry := interdEntryR1 "d1-0132" ((RNReps.q4).ifThen (RNReps.q5)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_5
def d1_cImp_4_6 : Entry := interdEntryR1 "d1-0133" ((RNReps.q4).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_4_6
def d1_cImp_4_7 : Entry := interdEntryR1 "d1-0134" ((RNReps.q4).ifThen (RNReps.q7)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_7
def d1_cImp_4_8 : Entry := interdEntryR1 "d1-0135" ((RNReps.q4).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_8
def d1_cImp_4_9 : Entry := interdEntryR1 "d1-0136" ((RNReps.q4).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_9
def d1_cImp_5_0 : Entry := interdEntryR1 "d1-0137" ((RNReps.q5).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_5_0
def d1_cImp_5_10 : Entry := interdEntryR1 "d1-0138" ((RNReps.q5).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_10
def d1_cImp_5_11 : Entry := interdEntryR1 "d1-0139" ((RNReps.q5).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_11
def d1_cImp_5_12 : Entry := interdEntryR1 "d1-0140" ((RNReps.q5).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_12
def d1_cImp_5_13 : Entry := interdEntryR1 "d1-0141" ((RNReps.q5).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_13
def d1_cImp_5_14 : Entry := interdEntryR1 "d1-0142" ((RNReps.q5).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_14
def d1_cImp_5_2 : Entry := interdEntryR1 "d1-0143" ((RNReps.q5).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND.cImp_5_2
def d1_cImp_5_3 : Entry := interdEntryR1 "d1-0144" ((RNReps.q5).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_5_3
def d1_cImp_5_6 : Entry := interdEntryR1 "d1-0145" ((RNReps.q5).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_5_6
def d1_cImp_5_7 : Entry := interdEntryR1 "d1-0146" ((RNReps.q5).ifThen (RNReps.q7)) (RNReps.q8) PLLND.SemUI.RND.cImp_5_7
def d1_cImp_5_8 : Entry := interdEntryR1 "d1-0147" ((RNReps.q5).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cImp_5_8
def d1_cImp_5_9 : Entry := interdEntryR1 "d1-0148" ((RNReps.q5).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_9
def d1_cImp_6_0 : Entry := interdEntryR1 "d1-0149" ((RNReps.q6).ifThen (RNReps.q0)) (RNReps.q3) PLLND.SemUI.RND.cImp_6_0
def d1_cImp_6_10 : Entry := interdEntryR1 "d1-0150" ((RNReps.q6).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_6_10
def d1_cImp_6_11 : Entry := interdEntryR1 "d1-0151" ((RNReps.q6).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_11
def d1_cImp_6_12 : Entry := interdEntryR1 "d1-0152" ((RNReps.q6).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_12
def d1_cImp_6_13 : Entry := interdEntryR1 "d1-0153" ((RNReps.q6).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_13
def d1_cImp_6_14 : Entry := interdEntryR1 "d1-0154" ((RNReps.q6).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_14
def d1_cImp_6_3 : Entry := interdEntryR1 "d1-0155" ((RNReps.q6).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_6_3
def d1_cImp_6_4 : Entry := interdEntryR1 "d1-0156" ((RNReps.q6).ifThen (RNReps.q4)) (RNReps.q10) PLLND.SemUI.RND.cImp_6_4
def d1_cImp_6_5 : Entry := interdEntryR1 "d1-0157" ((RNReps.q6).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND.cImp_6_5
def d1_cImp_6_7 : Entry := interdEntryR1 "d1-0158" ((RNReps.q6).ifThen (RNReps.q7)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_7
def d1_cImp_6_8 : Entry := interdEntryR1 "d1-0159" ((RNReps.q6).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_8
def d1_cImp_6_9 : Entry := interdEntryR1 "d1-0160" ((RNReps.q6).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_9
def d1_cImp_7_0 : Entry := interdEntryR1 "d1-0161" ((RNReps.q7).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_7_0
def d1_cImp_7_10 : Entry := interdEntryR1 "d1-0162" ((RNReps.q7).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_7_10
def d1_cImp_7_11 : Entry := interdEntryR1 "d1-0163" ((RNReps.q7).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_11
def d1_cImp_7_12 : Entry := interdEntryR1 "d1-0164" ((RNReps.q7).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_12
def d1_cImp_7_13 : Entry := interdEntryR1 "d1-0165" ((RNReps.q7).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_13
def d1_cImp_7_14 : Entry := interdEntryR1 "d1-0166" ((RNReps.q7).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_14
def d1_cImp_7_2 : Entry := interdEntryR1 "d1-0167" ((RNReps.q7).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_7_2
def d1_cImp_7_3 : Entry := interdEntryR1 "d1-0168" ((RNReps.q7).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_7_3
def d1_cImp_7_4 : Entry := interdEntryR1 "d1-0169" ((RNReps.q7).ifThen (RNReps.q4)) (RNReps.q10) PLLND.SemUI.RND.cImp_7_4
def d1_cImp_7_5 : Entry := interdEntryR1 "d1-0170" ((RNReps.q7).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND.cImp_7_5
def d1_cImp_7_6 : Entry := interdEntryR1 "d1-0171" ((RNReps.q7).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_7_6
def d1_cImp_7_8 : Entry := interdEntryR1 "d1-0172" ((RNReps.q7).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_8
def d1_cImp_7_9 : Entry := interdEntryR1 "d1-0173" ((RNReps.q7).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_9
def d1_cImp_8_0 : Entry := interdEntryR1 "d1-0174" ((RNReps.q8).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_8_0
def d1_cImp_8_13 : Entry := interdEntryR1 "d1-0175" ((RNReps.q8).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_8_13
def d1_cImp_8_2 : Entry := interdEntryR1 "d1-0176" ((RNReps.q8).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_8_2
def d1_cImp_8_3 : Entry := interdEntryR1 "d1-0177" ((RNReps.q8).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_8_3
def d1_cImp_8_6 : Entry := interdEntryR1 "d1-0178" ((RNReps.q8).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_8_6
def d1_cImp_9_0 : Entry := interdEntryR1 "d1-0179" ((RNReps.q9).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_9_0
def d1_cImp_9_10 : Entry := interdEntryR1 "d1-0180" ((RNReps.q9).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_9_10
def d1_cImp_9_11 : Entry := interdEntryR1 "d1-0181" ((RNReps.q9).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_9_11
def d1_cImp_9_12 : Entry := interdEntryR1 "d1-0182" ((RNReps.q9).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_9_12
def d1_cImp_9_13 : Entry := interdEntryR1 "d1-0183" ((RNReps.q9).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_9_13
def d1_cImp_9_14 : Entry := interdEntryR1 "d1-0184" ((RNReps.q9).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_9_14
def d1_cImp_9_2 : Entry := interdEntryR1 "d1-0185" ((RNReps.q9).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_9_2
def d1_cImp_9_3 : Entry := interdEntryR1 "d1-0186" ((RNReps.q9).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_9_3
def d1_cImp_9_5 : Entry := interdEntryR1 "d1-0187" ((RNReps.q9).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND.cImp_9_5
def d1_cImp_9_6 : Entry := interdEntryR1 "d1-0188" ((RNReps.q9).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_9_6
def d1_cImp_9_7 : Entry := interdEntryR1 "d1-0189" ((RNReps.q9).ifThen (RNReps.q7)) (RNReps.q8) PLLND.SemUI.RND.cImp_9_7
def d1_cOr_10_11 : Entry := interdEntryR1 "d1-0190" ((RNReps.q10).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_10_11
def d1_cOr_2_10 : Entry := interdEntryR1 "d1-0191" ((RNReps.q2).or (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cOr_2_10
def d1_cOr_2_11 : Entry := interdEntryR1 "d1-0192" ((RNReps.q2).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_2_11
def d1_cOr_2_12 : Entry := interdEntryR1 "d1-0193" ((RNReps.q2).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_2_12
def d1_cOr_2_4 : Entry := interdEntryR1 "d1-0194" ((RNReps.q2).or (RNReps.q4)) (RNReps.q4) PLLND.SemUI.RND.cOr_2_4
def d1_cOr_2_5 : Entry := interdEntryR1 "d1-0195" ((RNReps.q2).or (RNReps.q5)) (RNReps.q5) PLLND.SemUI.RND.cOr_2_5
def d1_cOr_2_6 : Entry := interdEntryR1 "d1-0196" ((RNReps.q2).or (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cOr_2_6
def d1_cOr_2_7 : Entry := interdEntryR1 "d1-0197" ((RNReps.q2).or (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cOr_2_7
def d1_cOr_2_8 : Entry := interdEntryR1 "d1-0198" ((RNReps.q2).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_2_8
def d1_cOr_2_9 : Entry := interdEntryR1 "d1-0199" ((RNReps.q2).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_2_9
def d1_cOr_3_10 : Entry := interdEntryR1 "d1-0200" ((RNReps.q3).or (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cOr_3_10
def d1_cOr_3_11 : Entry := interdEntryR1 "d1-0201" ((RNReps.q3).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_3_11
def d1_cOr_3_12 : Entry := interdEntryR1 "d1-0202" ((RNReps.q3).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_3_12
def d1_cOr_3_4 : Entry := interdEntryR1 "d1-0203" ((RNReps.q3).or (RNReps.q4)) (RNReps.q4) PLLND.SemUI.RND.cOr_3_4
def d1_cOr_3_5 : Entry := interdEntryR1 "d1-0204" ((RNReps.q3).or (RNReps.q5)) (RNReps.q5) PLLND.SemUI.RND.cOr_3_5
def d1_cOr_3_7 : Entry := interdEntryR1 "d1-0205" ((RNReps.q3).or (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cOr_3_7
def d1_cOr_3_8 : Entry := interdEntryR1 "d1-0206" ((RNReps.q3).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_3_8
def d1_cOr_3_9 : Entry := interdEntryR1 "d1-0207" ((RNReps.q3).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_3_9
def d1_cOr_4_10 : Entry := interdEntryR1 "d1-0208" ((RNReps.q4).or (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cOr_4_10
def d1_cOr_4_11 : Entry := interdEntryR1 "d1-0209" ((RNReps.q4).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_4_11
def d1_cOr_4_12 : Entry := interdEntryR1 "d1-0210" ((RNReps.q4).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_4_12
def d1_cOr_4_13 : Entry := interdEntryR1 "d1-0211" ((RNReps.q4).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND.cOr_4_13
def d1_cOr_4_5 : Entry := interdEntryR1 "d1-0212" ((RNReps.q4).or (RNReps.q5)) (RNReps.q5) PLLND.SemUI.RND.cOr_4_5
def d1_cOr_4_6 : Entry := interdEntryR1 "d1-0213" ((RNReps.q4).or (RNReps.q6)) (RNReps.q7) PLLND.SemUI.RND.cOr_4_6
def d1_cOr_4_7 : Entry := interdEntryR1 "d1-0214" ((RNReps.q4).or (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cOr_4_7
def d1_cOr_4_8 : Entry := interdEntryR1 "d1-0215" ((RNReps.q4).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_4_8
def d1_cOr_4_9 : Entry := interdEntryR1 "d1-0216" ((RNReps.q4).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_4_9
def d1_cOr_5_10 : Entry := interdEntryR1 "d1-0217" ((RNReps.q5).or (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cOr_5_10
def d1_cOr_5_11 : Entry := interdEntryR1 "d1-0218" ((RNReps.q5).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_5_11
def d1_cOr_5_12 : Entry := interdEntryR1 "d1-0219" ((RNReps.q5).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_5_12
def d1_cOr_5_13 : Entry := interdEntryR1 "d1-0220" ((RNReps.q5).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND.cOr_5_13
def d1_cOr_5_7 : Entry := interdEntryR1 "d1-0221" ((RNReps.q5).or (RNReps.q7)) (RNReps.q9) PLLND.SemUI.RND.cOr_5_7
def d1_cOr_5_9 : Entry := interdEntryR1 "d1-0222" ((RNReps.q5).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_5_9
def d1_cOr_6_11 : Entry := interdEntryR1 "d1-0223" ((RNReps.q6).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_6_11
def d1_cOr_6_12 : Entry := interdEntryR1 "d1-0224" ((RNReps.q6).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_6_12
def d1_cOr_6_7 : Entry := interdEntryR1 "d1-0225" ((RNReps.q6).or (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cOr_6_7
def d1_cOr_6_8 : Entry := interdEntryR1 "d1-0226" ((RNReps.q6).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_6_8
def d1_cOr_6_9 : Entry := interdEntryR1 "d1-0227" ((RNReps.q6).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_6_9
def d1_cOr_7_10 : Entry := interdEntryR1 "d1-0228" ((RNReps.q7).or (RNReps.q10)) (RNReps.q11) PLLND.SemUI.RND.cOr_7_10
def d1_cOr_7_11 : Entry := interdEntryR1 "d1-0229" ((RNReps.q7).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_7_11
def d1_cOr_7_12 : Entry := interdEntryR1 "d1-0230" ((RNReps.q7).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_7_12
def d1_cOr_7_8 : Entry := interdEntryR1 "d1-0231" ((RNReps.q7).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_7_8
def d1_cOr_7_9 : Entry := interdEntryR1 "d1-0232" ((RNReps.q7).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_7_9
def d1_cOr_9_10 : Entry := interdEntryR1 "d1-0233" ((RNReps.q9).or (RNReps.q10)) (RNReps.q11) PLLND.SemUI.RND.cOr_9_10
def d1_cOr_9_11 : Entry := interdEntryR1 "d1-0234" ((RNReps.q9).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_9_11
def d1_cOr_9_12 : Entry := interdEntryR1 "d1-0235" ((RNReps.q9).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_9_12

def dictEntriesR1 : List Entry :=
  [ d1_cAnd_10_11,
    d1_cAnd_10_12,
    d1_cAnd_11_12,
    d1_cAnd_2_10,
    d1_cAnd_2_11,
    d1_cAnd_2_12,
    d1_cAnd_2_13,
    d1_cAnd_2_14,
    d1_cAnd_2_3,
    d1_cAnd_2_4,
    d1_cAnd_2_5,
    d1_cAnd_2_6,
    d1_cAnd_2_7,
    d1_cAnd_2_8,
    d1_cAnd_2_9,
    d1_cAnd_3_10,
    d1_cAnd_3_11,
    d1_cAnd_3_12,
    d1_cAnd_3_13,
    d1_cAnd_3_14,
    d1_cAnd_3_4,
    d1_cAnd_3_5,
    d1_cAnd_3_6,
    d1_cAnd_3_7,
    d1_cAnd_3_8,
    d1_cAnd_3_9,
    d1_cAnd_4_10,
    d1_cAnd_4_11,
    d1_cAnd_4_12,
    d1_cAnd_4_13,
    d1_cAnd_4_5,
    d1_cAnd_4_6,
    d1_cAnd_4_7,
    d1_cAnd_4_8,
    d1_cAnd_4_9,
    d1_cAnd_5_10,
    d1_cAnd_5_11,
    d1_cAnd_5_12,
    d1_cAnd_5_13,
    d1_cAnd_5_14,
    d1_cAnd_5_6,
    d1_cAnd_5_7,
    d1_cAnd_5_8,
    d1_cAnd_5_9,
    d1_cAnd_6_10,
    d1_cAnd_6_11,
    d1_cAnd_6_12,
    d1_cAnd_6_13,
    d1_cAnd_6_14,
    d1_cAnd_6_7,
    d1_cAnd_6_8,
    d1_cAnd_6_9,
    d1_cAnd_7_10,
    d1_cAnd_7_11,
    d1_cAnd_7_12,
    d1_cAnd_7_13,
    d1_cAnd_7_14,
    d1_cAnd_7_8,
    d1_cAnd_7_9,
    d1_cAnd_8_13,
    d1_cAnd_8_9,
    d1_cAnd_9_10,
    d1_cAnd_9_11,
    d1_cAnd_9_12,
    d1_cBox_1,
    d1_cBox_10,
    d1_cBox_4,
    d1_cBox_6,
    d1_cBox_9,
    d1_cImp_10_0,
    d1_cImp_10_11,
    d1_cImp_10_2,
    d1_cImp_10_3,
    d1_cImp_10_6,
    d1_cImp_11_0,
    d1_cImp_11_10,
    d1_cImp_11_2,
    d1_cImp_11_3,
    d1_cImp_11_5,
    d1_cImp_11_6,
    d1_cImp_12_0,
    d1_cImp_12_10,
    d1_cImp_12_13,
    d1_cImp_12_14,
    d1_cImp_12_2,
    d1_cImp_12_3,
    d1_cImp_12_5,
    d1_cImp_12_6,
    d1_cImp_13_0,
    d1_cImp_13_10,
    d1_cImp_13_2,
    d1_cImp_13_3,
    d1_cImp_13_4,
    d1_cImp_13_6,
    d1_cImp_13_7,
    d1_cImp_14_0,
    d1_cImp_14_10,
    d1_cImp_14_2,
    d1_cImp_14_3,
    d1_cImp_14_6,
    d1_cImp_2_10,
    d1_cImp_2_11,
    d1_cImp_2_12,
    d1_cImp_2_13,
    d1_cImp_2_14,
    d1_cImp_2_3,
    d1_cImp_2_4,
    d1_cImp_2_5,
    d1_cImp_2_6,
    d1_cImp_2_7,
    d1_cImp_2_8,
    d1_cImp_2_9,
    d1_cImp_3_10,
    d1_cImp_3_11,
    d1_cImp_3_12,
    d1_cImp_3_13,
    d1_cImp_3_14,
    d1_cImp_3_2,
    d1_cImp_3_4,
    d1_cImp_3_5,
    d1_cImp_3_6,
    d1_cImp_3_7,
    d1_cImp_3_8,
    d1_cImp_3_9,
    d1_cImp_4_0,
    d1_cImp_4_10,
    d1_cImp_4_11,
    d1_cImp_4_12,
    d1_cImp_4_13,
    d1_cImp_4_14,
    d1_cImp_4_2,
    d1_cImp_4_3,
    d1_cImp_4_5,
    d1_cImp_4_6,
    d1_cImp_4_7,
    d1_cImp_4_8,
    d1_cImp_4_9,
    d1_cImp_5_0,
    d1_cImp_5_10,
    d1_cImp_5_11,
    d1_cImp_5_12,
    d1_cImp_5_13,
    d1_cImp_5_14,
    d1_cImp_5_2,
    d1_cImp_5_3,
    d1_cImp_5_6,
    d1_cImp_5_7,
    d1_cImp_5_8,
    d1_cImp_5_9,
    d1_cImp_6_0,
    d1_cImp_6_10,
    d1_cImp_6_11,
    d1_cImp_6_12,
    d1_cImp_6_13,
    d1_cImp_6_14,
    d1_cImp_6_3,
    d1_cImp_6_4,
    d1_cImp_6_5,
    d1_cImp_6_7,
    d1_cImp_6_8,
    d1_cImp_6_9,
    d1_cImp_7_0,
    d1_cImp_7_10,
    d1_cImp_7_11,
    d1_cImp_7_12,
    d1_cImp_7_13,
    d1_cImp_7_14,
    d1_cImp_7_2,
    d1_cImp_7_3,
    d1_cImp_7_4,
    d1_cImp_7_5,
    d1_cImp_7_6,
    d1_cImp_7_8,
    d1_cImp_7_9,
    d1_cImp_8_0,
    d1_cImp_8_13,
    d1_cImp_8_2,
    d1_cImp_8_3,
    d1_cImp_8_6,
    d1_cImp_9_0,
    d1_cImp_9_10,
    d1_cImp_9_11,
    d1_cImp_9_12,
    d1_cImp_9_13,
    d1_cImp_9_14,
    d1_cImp_9_2,
    d1_cImp_9_3,
    d1_cImp_9_5,
    d1_cImp_9_6,
    d1_cImp_9_7,
    d1_cOr_10_11,
    d1_cOr_2_10,
    d1_cOr_2_11,
    d1_cOr_2_12,
    d1_cOr_2_4,
    d1_cOr_2_5,
    d1_cOr_2_6,
    d1_cOr_2_7,
    d1_cOr_2_8,
    d1_cOr_2_9,
    d1_cOr_3_10,
    d1_cOr_3_11,
    d1_cOr_3_12,
    d1_cOr_3_4,
    d1_cOr_3_5,
    d1_cOr_3_7,
    d1_cOr_3_8,
    d1_cOr_3_9,
    d1_cOr_4_10,
    d1_cOr_4_11,
    d1_cOr_4_12,
    d1_cOr_4_13,
    d1_cOr_4_5,
    d1_cOr_4_6,
    d1_cOr_4_7,
    d1_cOr_4_8,
    d1_cOr_4_9,
    d1_cOr_5_10,
    d1_cOr_5_11,
    d1_cOr_5_12,
    d1_cOr_5_13,
    d1_cOr_5_7,
    d1_cOr_5_9,
    d1_cOr_6_11,
    d1_cOr_6_12,
    d1_cOr_6_7,
    d1_cOr_6_8,
    d1_cOr_6_9,
    d1_cOr_7_10,
    d1_cOr_7_11,
    d1_cOr_7_12,
    d1_cOr_7_8,
    d1_cOr_7_9,
    d1_cOr_9_10,
    d1_cOr_9_11,
    d1_cOr_9_12 ]

set_option maxRecDepth 8192 in
theorem dictEntriesR1_length : dictEntriesR1.length = 236 := rfl

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.dictEntriesR1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dictEntriesR1

/-- info: 'RNDB.dictEntriesR1_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dictEntriesR1_length

end RNDB