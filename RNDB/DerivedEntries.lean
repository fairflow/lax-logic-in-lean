/-
# DERIVED entries — the evidence DAG's first edges

GENERATED 2026-08-24.  Two waves:

1. The SYMM closure of every interd entry (318): `Interd a b ⇒ Interd b a`
   by `Interd.symm`, each recording its parent's EntryId under
   `DerivRule.symm`.  Lookups can now consult either orientation without
   knowing which one the dictionary happened to state.
2. A trans demonstration over the q15 class: the three compounds that
   collapse to `q15` (`q8∧q10`, `q12⊃q4`, `q14⊃q4`) are pairwise
   interderivable THROUGH `q15`, each edge citing its two parents under
   `DerivRule.trans`.  This is the shape proof-simplification will walk.

Provenance discipline: `parents` is DATA (the schema checks only
`ps.length = rule.arity`); the Holds obligation is discharged directly
from the parent theorems, so a wrong parent id could mislabel provenance
but can never fake a fact.
-/
import RNDB.DictEntries
import RNDB.Dict2Entries

open PLLND PLLND.SemUI

namespace RNDB

/-- Closed positivity witness, as in the interd modules. -/
theorem relInterdPosD : Rel.interd.IsPositive := by decide

/-- A symm-derived interd entry. -/
def symmEntry (id : EntryId) (parent : EntryId) (a b : PLLFormula)
    (h : Interd a b) : Entry where
  id := id
  claim := ⟨b, a, Rel.interd, none⟩
  ev := Evidence.derived [parent] DerivRule.symm
  ok := ⟨Claim.wellScoped_of_pos relInterdPosD, rfl, h.symm⟩

/-- A trans-derived interd entry (two parents). -/
def transEntry (id : EntryId) (p₁ p₂ : EntryId) (a b c : PLLFormula)
    (h₁ : Interd a b) (h₂ : Interd b c) : Entry where
  id := id
  claim := ⟨a, c, Rel.interd, none⟩
  ev := Evidence.derived [p₁, p₂] DerivRule.trans
  ok := ⟨Claim.wellScoped_of_pos relInterdPosD, rfl, h₁.trans h₂⟩

def s_d1_cAnd_10_11 : Entry := symmEntry "ds-0000" "d1-0000" ((RNReps.q10).and (RNReps.q11)) (RNReps.q10) PLLND.SemUI.RND.cAnd_10_11
def s_d1_cAnd_10_12 : Entry := symmEntry "ds-0001" "d1-0001" ((RNReps.q10).and (RNReps.q12)) (RNReps.q5) PLLND.SemUI.RND.cAnd_10_12
def s_d1_cAnd_11_12 : Entry := symmEntry "ds-0002" "d1-0002" ((RNReps.q11).and (RNReps.q12)) (RNReps.q9) PLLND.SemUI.RND.cAnd_11_12
def s_d1_cAnd_2_10 : Entry := symmEntry "ds-0003" "d1-0003" ((RNReps.q2).and (RNReps.q10)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_10
def s_d1_cAnd_2_11 : Entry := symmEntry "ds-0004" "d1-0004" ((RNReps.q2).and (RNReps.q11)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_11
def s_d1_cAnd_2_12 : Entry := symmEntry "ds-0005" "d1-0005" ((RNReps.q2).and (RNReps.q12)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_12
def s_d1_cAnd_2_13 : Entry := symmEntry "ds-0006" "d1-0006" ((RNReps.q2).and (RNReps.q13)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_13
def s_d1_cAnd_2_14 : Entry := symmEntry "ds-0007" "d1-0007" ((RNReps.q2).and (RNReps.q14)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_14
def s_d1_cAnd_2_3 : Entry := symmEntry "ds-0008" "d1-0008" ((RNReps.q2).and (RNReps.q3)) (RNReps.q0) PLLND.SemUI.RND.cAnd_2_3
def s_d1_cAnd_2_4 : Entry := symmEntry "ds-0009" "d1-0009" ((RNReps.q2).and (RNReps.q4)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_4
def s_d1_cAnd_2_5 : Entry := symmEntry "ds-0010" "d1-0010" ((RNReps.q2).and (RNReps.q5)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_5
def s_d1_cAnd_2_6 : Entry := symmEntry "ds-0011" "d1-0011" ((RNReps.q2).and (RNReps.q6)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_6
def s_d1_cAnd_2_7 : Entry := symmEntry "ds-0012" "d1-0012" ((RNReps.q2).and (RNReps.q7)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_7
def s_d1_cAnd_2_8 : Entry := symmEntry "ds-0013" "d1-0013" ((RNReps.q2).and (RNReps.q8)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_8
def s_d1_cAnd_2_9 : Entry := symmEntry "ds-0014" "d1-0014" ((RNReps.q2).and (RNReps.q9)) (RNReps.q2) PLLND.SemUI.RND.cAnd_2_9
def s_d1_cAnd_3_10 : Entry := symmEntry "ds-0015" "d1-0015" ((RNReps.q3).and (RNReps.q10)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_10
def s_d1_cAnd_3_11 : Entry := symmEntry "ds-0016" "d1-0016" ((RNReps.q3).and (RNReps.q11)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_11
def s_d1_cAnd_3_12 : Entry := symmEntry "ds-0017" "d1-0017" ((RNReps.q3).and (RNReps.q12)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_12
def s_d1_cAnd_3_13 : Entry := symmEntry "ds-0018" "d1-0018" ((RNReps.q3).and (RNReps.q13)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_13
def s_d1_cAnd_3_14 : Entry := symmEntry "ds-0019" "d1-0019" ((RNReps.q3).and (RNReps.q14)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_14
def s_d1_cAnd_3_4 : Entry := symmEntry "ds-0020" "d1-0020" ((RNReps.q3).and (RNReps.q4)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_4
def s_d1_cAnd_3_5 : Entry := symmEntry "ds-0021" "d1-0021" ((RNReps.q3).and (RNReps.q5)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_5
def s_d1_cAnd_3_6 : Entry := symmEntry "ds-0022" "d1-0022" ((RNReps.q3).and (RNReps.q6)) (RNReps.q0) PLLND.SemUI.RND.cAnd_3_6
def s_d1_cAnd_3_7 : Entry := symmEntry "ds-0023" "d1-0023" ((RNReps.q3).and (RNReps.q7)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_7
def s_d1_cAnd_3_8 : Entry := symmEntry "ds-0024" "d1-0024" ((RNReps.q3).and (RNReps.q8)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_8
def s_d1_cAnd_3_9 : Entry := symmEntry "ds-0025" "d1-0025" ((RNReps.q3).and (RNReps.q9)) (RNReps.q3) PLLND.SemUI.RND.cAnd_3_9
def s_d1_cAnd_4_10 : Entry := symmEntry "ds-0026" "d1-0026" ((RNReps.q4).and (RNReps.q10)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_10
def s_d1_cAnd_4_11 : Entry := symmEntry "ds-0027" "d1-0027" ((RNReps.q4).and (RNReps.q11)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_11
def s_d1_cAnd_4_12 : Entry := symmEntry "ds-0028" "d1-0028" ((RNReps.q4).and (RNReps.q12)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_12
def s_d1_cAnd_4_13 : Entry := symmEntry "ds-0029" "d1-0029" ((RNReps.q4).and (RNReps.q13)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_13
def s_d1_cAnd_4_5 : Entry := symmEntry "ds-0030" "d1-0030" ((RNReps.q4).and (RNReps.q5)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_5
def s_d1_cAnd_4_6 : Entry := symmEntry "ds-0031" "d1-0031" ((RNReps.q4).and (RNReps.q6)) (RNReps.q2) PLLND.SemUI.RND.cAnd_4_6
def s_d1_cAnd_4_7 : Entry := symmEntry "ds-0032" "d1-0032" ((RNReps.q4).and (RNReps.q7)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_7
def s_d1_cAnd_4_8 : Entry := symmEntry "ds-0033" "d1-0033" ((RNReps.q4).and (RNReps.q8)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_8
def s_d1_cAnd_4_9 : Entry := symmEntry "ds-0034" "d1-0034" ((RNReps.q4).and (RNReps.q9)) (RNReps.q4) PLLND.SemUI.RND.cAnd_4_9
def s_d1_cAnd_5_10 : Entry := symmEntry "ds-0035" "d1-0035" ((RNReps.q5).and (RNReps.q10)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_10
def s_d1_cAnd_5_11 : Entry := symmEntry "ds-0036" "d1-0036" ((RNReps.q5).and (RNReps.q11)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_11
def s_d1_cAnd_5_12 : Entry := symmEntry "ds-0037" "d1-0037" ((RNReps.q5).and (RNReps.q12)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_12
def s_d1_cAnd_5_13 : Entry := symmEntry "ds-0038" "d1-0038" ((RNReps.q5).and (RNReps.q13)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_13
def s_d1_cAnd_5_14 : Entry := symmEntry "ds-0039" "d1-0039" ((RNReps.q5).and (RNReps.q14)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_14
def s_d1_cAnd_5_6 : Entry := symmEntry "ds-0040" "d1-0040" ((RNReps.q5).and (RNReps.q6)) (RNReps.q2) PLLND.SemUI.RND.cAnd_5_6
def s_d1_cAnd_5_7 : Entry := symmEntry "ds-0041" "d1-0041" ((RNReps.q5).and (RNReps.q7)) (RNReps.q4) PLLND.SemUI.RND.cAnd_5_7
def s_d1_cAnd_5_8 : Entry := symmEntry "ds-0042" "d1-0042" ((RNReps.q5).and (RNReps.q8)) (RNReps.q4) PLLND.SemUI.RND.cAnd_5_8
def s_d1_cAnd_5_9 : Entry := symmEntry "ds-0043" "d1-0043" ((RNReps.q5).and (RNReps.q9)) (RNReps.q5) PLLND.SemUI.RND.cAnd_5_9
def s_d1_cAnd_6_10 : Entry := symmEntry "ds-0044" "d1-0044" ((RNReps.q6).and (RNReps.q10)) (RNReps.q2) PLLND.SemUI.RND.cAnd_6_10
def s_d1_cAnd_6_11 : Entry := symmEntry "ds-0045" "d1-0045" ((RNReps.q6).and (RNReps.q11)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_11
def s_d1_cAnd_6_12 : Entry := symmEntry "ds-0046" "d1-0046" ((RNReps.q6).and (RNReps.q12)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_12
def s_d1_cAnd_6_13 : Entry := symmEntry "ds-0047" "d1-0047" ((RNReps.q6).and (RNReps.q13)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_13
def s_d1_cAnd_6_14 : Entry := symmEntry "ds-0048" "d1-0048" ((RNReps.q6).and (RNReps.q14)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_14
def s_d1_cAnd_6_7 : Entry := symmEntry "ds-0049" "d1-0049" ((RNReps.q6).and (RNReps.q7)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_7
def s_d1_cAnd_6_8 : Entry := symmEntry "ds-0050" "d1-0050" ((RNReps.q6).and (RNReps.q8)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_8
def s_d1_cAnd_6_9 : Entry := symmEntry "ds-0051" "d1-0051" ((RNReps.q6).and (RNReps.q9)) (RNReps.q6) PLLND.SemUI.RND.cAnd_6_9
def s_d1_cAnd_7_10 : Entry := symmEntry "ds-0052" "d1-0052" ((RNReps.q7).and (RNReps.q10)) (RNReps.q4) PLLND.SemUI.RND.cAnd_7_10
def s_d1_cAnd_7_11 : Entry := symmEntry "ds-0053" "d1-0053" ((RNReps.q7).and (RNReps.q11)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_11
def s_d1_cAnd_7_12 : Entry := symmEntry "ds-0054" "d1-0054" ((RNReps.q7).and (RNReps.q12)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_12
def s_d1_cAnd_7_13 : Entry := symmEntry "ds-0055" "d1-0055" ((RNReps.q7).and (RNReps.q13)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_13
def s_d1_cAnd_7_14 : Entry := symmEntry "ds-0056" "d1-0056" ((RNReps.q7).and (RNReps.q14)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_14
def s_d1_cAnd_7_8 : Entry := symmEntry "ds-0057" "d1-0057" ((RNReps.q7).and (RNReps.q8)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_8
def s_d1_cAnd_7_9 : Entry := symmEntry "ds-0058" "d1-0058" ((RNReps.q7).and (RNReps.q9)) (RNReps.q7) PLLND.SemUI.RND.cAnd_7_9
def s_d1_cAnd_8_13 : Entry := symmEntry "ds-0059" "d1-0059" ((RNReps.q8).and (RNReps.q13)) (RNReps.q8) PLLND.SemUI.RND.cAnd_8_13
def s_d1_cAnd_8_9 : Entry := symmEntry "ds-0060" "d1-0060" ((RNReps.q8).and (RNReps.q9)) (RNReps.q7) PLLND.SemUI.RND.cAnd_8_9
def s_d1_cAnd_9_10 : Entry := symmEntry "ds-0061" "d1-0061" ((RNReps.q9).and (RNReps.q10)) (RNReps.q5) PLLND.SemUI.RND.cAnd_9_10
def s_d1_cAnd_9_11 : Entry := symmEntry "ds-0062" "d1-0062" ((RNReps.q9).and (RNReps.q11)) (RNReps.q9) PLLND.SemUI.RND.cAnd_9_11
def s_d1_cAnd_9_12 : Entry := symmEntry "ds-0063" "d1-0063" ((RNReps.q9).and (RNReps.q12)) (RNReps.q9) PLLND.SemUI.RND.cAnd_9_12
def s_d1_cBox_1 : Entry := symmEntry "ds-0064" "d1-0064" ((RNReps.q1).somehow) (RNReps.q1) PLLND.SemUI.RND.cBox_1
def s_d1_cBox_10 : Entry := symmEntry "ds-0065" "d1-0065" ((RNReps.q10).somehow) (RNReps.q10) PLLND.SemUI.RND.cBox_10
def s_d1_cBox_4 : Entry := symmEntry "ds-0066" "d1-0066" ((RNReps.q4).somehow) (RNReps.q5) PLLND.SemUI.RND.cBox_4
def s_d1_cBox_6 : Entry := symmEntry "ds-0067" "d1-0067" ((RNReps.q6).somehow) (RNReps.q6) PLLND.SemUI.RND.cBox_6
def s_d1_cBox_9 : Entry := symmEntry "ds-0068" "d1-0068" ((RNReps.q9).somehow) (RNReps.q12) PLLND.SemUI.RND.cBox_9
def s_d1_cImp_10_0 : Entry := symmEntry "ds-0069" "d1-0069" ((RNReps.q10).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_10_0
def s_d1_cImp_10_11 : Entry := symmEntry "ds-0070" "d1-0070" ((RNReps.q10).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_10_11
def s_d1_cImp_10_2 : Entry := symmEntry "ds-0071" "d1-0071" ((RNReps.q10).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND.cImp_10_2
def s_d1_cImp_10_3 : Entry := symmEntry "ds-0072" "d1-0072" ((RNReps.q10).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_10_3
def s_d1_cImp_10_6 : Entry := symmEntry "ds-0073" "d1-0073" ((RNReps.q10).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_10_6
def s_d1_cImp_11_0 : Entry := symmEntry "ds-0074" "d1-0074" ((RNReps.q11).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_11_0
def s_d1_cImp_11_10 : Entry := symmEntry "ds-0075" "d1-0075" ((RNReps.q11).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_11_10
def s_d1_cImp_11_2 : Entry := symmEntry "ds-0076" "d1-0076" ((RNReps.q11).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_11_2
def s_d1_cImp_11_3 : Entry := symmEntry "ds-0077" "d1-0077" ((RNReps.q11).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_11_3
def s_d1_cImp_11_5 : Entry := symmEntry "ds-0078" "d1-0078" ((RNReps.q11).ifThen (RNReps.q5)) (RNReps.q5) PLLND.SemUI.RND.cImp_11_5
def s_d1_cImp_11_6 : Entry := symmEntry "ds-0079" "d1-0079" ((RNReps.q11).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_11_6
def s_d1_cImp_12_0 : Entry := symmEntry "ds-0080" "d1-0080" ((RNReps.q12).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_12_0
def s_d1_cImp_12_10 : Entry := symmEntry "ds-0081" "d1-0081" ((RNReps.q12).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_12_10
def s_d1_cImp_12_13 : Entry := symmEntry "ds-0082" "d1-0082" ((RNReps.q12).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_12_13
def s_d1_cImp_12_14 : Entry := symmEntry "ds-0083" "d1-0083" ((RNReps.q12).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_12_14
def s_d1_cImp_12_2 : Entry := symmEntry "ds-0084" "d1-0084" ((RNReps.q12).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_12_2
def s_d1_cImp_12_3 : Entry := symmEntry "ds-0085" "d1-0085" ((RNReps.q12).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_12_3
def s_d1_cImp_12_5 : Entry := symmEntry "ds-0086" "d1-0086" ((RNReps.q12).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND.cImp_12_5
def s_d1_cImp_12_6 : Entry := symmEntry "ds-0087" "d1-0087" ((RNReps.q12).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_12_6
def s_d1_cImp_13_0 : Entry := symmEntry "ds-0088" "d1-0088" ((RNReps.q13).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_13_0
def s_d1_cImp_13_10 : Entry := symmEntry "ds-0089" "d1-0089" ((RNReps.q13).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_13_10
def s_d1_cImp_13_2 : Entry := symmEntry "ds-0090" "d1-0090" ((RNReps.q13).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_13_2
def s_d1_cImp_13_3 : Entry := symmEntry "ds-0091" "d1-0091" ((RNReps.q13).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_13_3
def s_d1_cImp_13_4 : Entry := symmEntry "ds-0092" "d1-0092" ((RNReps.q13).ifThen (RNReps.q4)) (RNReps.q4) PLLND.SemUI.RND.cImp_13_4
def s_d1_cImp_13_6 : Entry := symmEntry "ds-0093" "d1-0093" ((RNReps.q13).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_13_6
def s_d1_cImp_13_7 : Entry := symmEntry "ds-0094" "d1-0094" ((RNReps.q13).ifThen (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cImp_13_7
def s_d1_cImp_14_0 : Entry := symmEntry "ds-0095" "d1-0095" ((RNReps.q14).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_14_0
def s_d1_cImp_14_10 : Entry := symmEntry "ds-0096" "d1-0096" ((RNReps.q14).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_14_10
def s_d1_cImp_14_2 : Entry := symmEntry "ds-0097" "d1-0097" ((RNReps.q14).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_14_2
def s_d1_cImp_14_3 : Entry := symmEntry "ds-0098" "d1-0098" ((RNReps.q14).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_14_3
def s_d1_cImp_14_6 : Entry := symmEntry "ds-0099" "d1-0099" ((RNReps.q14).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_14_6
def s_d1_cImp_2_10 : Entry := symmEntry "ds-0100" "d1-0100" ((RNReps.q2).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_10
def s_d1_cImp_2_11 : Entry := symmEntry "ds-0101" "d1-0101" ((RNReps.q2).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_11
def s_d1_cImp_2_12 : Entry := symmEntry "ds-0102" "d1-0102" ((RNReps.q2).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_12
def s_d1_cImp_2_13 : Entry := symmEntry "ds-0103" "d1-0103" ((RNReps.q2).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_13
def s_d1_cImp_2_14 : Entry := symmEntry "ds-0104" "d1-0104" ((RNReps.q2).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_14
def s_d1_cImp_2_3 : Entry := symmEntry "ds-0105" "d1-0105" ((RNReps.q2).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_2_3
def s_d1_cImp_2_4 : Entry := symmEntry "ds-0106" "d1-0106" ((RNReps.q2).ifThen (RNReps.q4)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_4
def s_d1_cImp_2_5 : Entry := symmEntry "ds-0107" "d1-0107" ((RNReps.q2).ifThen (RNReps.q5)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_5
def s_d1_cImp_2_6 : Entry := symmEntry "ds-0108" "d1-0108" ((RNReps.q2).ifThen (RNReps.q6)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_6
def s_d1_cImp_2_7 : Entry := symmEntry "ds-0109" "d1-0109" ((RNReps.q2).ifThen (RNReps.q7)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_7
def s_d1_cImp_2_8 : Entry := symmEntry "ds-0110" "d1-0110" ((RNReps.q2).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_8
def s_d1_cImp_2_9 : Entry := symmEntry "ds-0111" "d1-0111" ((RNReps.q2).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_2_9
def s_d1_cImp_3_10 : Entry := symmEntry "ds-0112" "d1-0112" ((RNReps.q3).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_10
def s_d1_cImp_3_11 : Entry := symmEntry "ds-0113" "d1-0113" ((RNReps.q3).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_11
def s_d1_cImp_3_12 : Entry := symmEntry "ds-0114" "d1-0114" ((RNReps.q3).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_12
def s_d1_cImp_3_13 : Entry := symmEntry "ds-0115" "d1-0115" ((RNReps.q3).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_13
def s_d1_cImp_3_14 : Entry := symmEntry "ds-0116" "d1-0116" ((RNReps.q3).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_14
def s_d1_cImp_3_2 : Entry := symmEntry "ds-0117" "d1-0117" ((RNReps.q3).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND.cImp_3_2
def s_d1_cImp_3_4 : Entry := symmEntry "ds-0118" "d1-0118" ((RNReps.q3).ifThen (RNReps.q4)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_4
def s_d1_cImp_3_5 : Entry := symmEntry "ds-0119" "d1-0119" ((RNReps.q3).ifThen (RNReps.q5)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_5
def s_d1_cImp_3_6 : Entry := symmEntry "ds-0120" "d1-0120" ((RNReps.q3).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_3_6
def s_d1_cImp_3_7 : Entry := symmEntry "ds-0121" "d1-0121" ((RNReps.q3).ifThen (RNReps.q7)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_7
def s_d1_cImp_3_8 : Entry := symmEntry "ds-0122" "d1-0122" ((RNReps.q3).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_8
def s_d1_cImp_3_9 : Entry := symmEntry "ds-0123" "d1-0123" ((RNReps.q3).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_3_9
def s_d1_cImp_4_0 : Entry := symmEntry "ds-0124" "d1-0124" ((RNReps.q4).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_4_0
def s_d1_cImp_4_10 : Entry := symmEntry "ds-0125" "d1-0125" ((RNReps.q4).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_10
def s_d1_cImp_4_11 : Entry := symmEntry "ds-0126" "d1-0126" ((RNReps.q4).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_11
def s_d1_cImp_4_12 : Entry := symmEntry "ds-0127" "d1-0127" ((RNReps.q4).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_12
def s_d1_cImp_4_13 : Entry := symmEntry "ds-0128" "d1-0128" ((RNReps.q4).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_13
def s_d1_cImp_4_14 : Entry := symmEntry "ds-0129" "d1-0129" ((RNReps.q4).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_14
def s_d1_cImp_4_2 : Entry := symmEntry "ds-0130" "d1-0130" ((RNReps.q4).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND.cImp_4_2
def s_d1_cImp_4_3 : Entry := symmEntry "ds-0131" "d1-0131" ((RNReps.q4).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_4_3
def s_d1_cImp_4_5 : Entry := symmEntry "ds-0132" "d1-0132" ((RNReps.q4).ifThen (RNReps.q5)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_5
def s_d1_cImp_4_6 : Entry := symmEntry "ds-0133" "d1-0133" ((RNReps.q4).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_4_6
def s_d1_cImp_4_7 : Entry := symmEntry "ds-0134" "d1-0134" ((RNReps.q4).ifThen (RNReps.q7)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_7
def s_d1_cImp_4_8 : Entry := symmEntry "ds-0135" "d1-0135" ((RNReps.q4).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_8
def s_d1_cImp_4_9 : Entry := symmEntry "ds-0136" "d1-0136" ((RNReps.q4).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_4_9
def s_d1_cImp_5_0 : Entry := symmEntry "ds-0137" "d1-0137" ((RNReps.q5).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_5_0
def s_d1_cImp_5_10 : Entry := symmEntry "ds-0138" "d1-0138" ((RNReps.q5).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_10
def s_d1_cImp_5_11 : Entry := symmEntry "ds-0139" "d1-0139" ((RNReps.q5).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_11
def s_d1_cImp_5_12 : Entry := symmEntry "ds-0140" "d1-0140" ((RNReps.q5).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_12
def s_d1_cImp_5_13 : Entry := symmEntry "ds-0141" "d1-0141" ((RNReps.q5).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_13
def s_d1_cImp_5_14 : Entry := symmEntry "ds-0142" "d1-0142" ((RNReps.q5).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_14
def s_d1_cImp_5_2 : Entry := symmEntry "ds-0143" "d1-0143" ((RNReps.q5).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND.cImp_5_2
def s_d1_cImp_5_3 : Entry := symmEntry "ds-0144" "d1-0144" ((RNReps.q5).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_5_3
def s_d1_cImp_5_6 : Entry := symmEntry "ds-0145" "d1-0145" ((RNReps.q5).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_5_6
def s_d1_cImp_5_7 : Entry := symmEntry "ds-0146" "d1-0146" ((RNReps.q5).ifThen (RNReps.q7)) (RNReps.q8) PLLND.SemUI.RND.cImp_5_7
def s_d1_cImp_5_8 : Entry := symmEntry "ds-0147" "d1-0147" ((RNReps.q5).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cImp_5_8
def s_d1_cImp_5_9 : Entry := symmEntry "ds-0148" "d1-0148" ((RNReps.q5).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_5_9
def s_d1_cImp_6_0 : Entry := symmEntry "ds-0149" "d1-0149" ((RNReps.q6).ifThen (RNReps.q0)) (RNReps.q3) PLLND.SemUI.RND.cImp_6_0
def s_d1_cImp_6_10 : Entry := symmEntry "ds-0150" "d1-0150" ((RNReps.q6).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_6_10
def s_d1_cImp_6_11 : Entry := symmEntry "ds-0151" "d1-0151" ((RNReps.q6).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_11
def s_d1_cImp_6_12 : Entry := symmEntry "ds-0152" "d1-0152" ((RNReps.q6).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_12
def s_d1_cImp_6_13 : Entry := symmEntry "ds-0153" "d1-0153" ((RNReps.q6).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_13
def s_d1_cImp_6_14 : Entry := symmEntry "ds-0154" "d1-0154" ((RNReps.q6).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_14
def s_d1_cImp_6_3 : Entry := symmEntry "ds-0155" "d1-0155" ((RNReps.q6).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_6_3
def s_d1_cImp_6_4 : Entry := symmEntry "ds-0156" "d1-0156" ((RNReps.q6).ifThen (RNReps.q4)) (RNReps.q10) PLLND.SemUI.RND.cImp_6_4
def s_d1_cImp_6_5 : Entry := symmEntry "ds-0157" "d1-0157" ((RNReps.q6).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND.cImp_6_5
def s_d1_cImp_6_7 : Entry := symmEntry "ds-0158" "d1-0158" ((RNReps.q6).ifThen (RNReps.q7)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_7
def s_d1_cImp_6_8 : Entry := symmEntry "ds-0159" "d1-0159" ((RNReps.q6).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_8
def s_d1_cImp_6_9 : Entry := symmEntry "ds-0160" "d1-0160" ((RNReps.q6).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_6_9
def s_d1_cImp_7_0 : Entry := symmEntry "ds-0161" "d1-0161" ((RNReps.q7).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_7_0
def s_d1_cImp_7_10 : Entry := symmEntry "ds-0162" "d1-0162" ((RNReps.q7).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_7_10
def s_d1_cImp_7_11 : Entry := symmEntry "ds-0163" "d1-0163" ((RNReps.q7).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_11
def s_d1_cImp_7_12 : Entry := symmEntry "ds-0164" "d1-0164" ((RNReps.q7).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_12
def s_d1_cImp_7_13 : Entry := symmEntry "ds-0165" "d1-0165" ((RNReps.q7).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_13
def s_d1_cImp_7_14 : Entry := symmEntry "ds-0166" "d1-0166" ((RNReps.q7).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_14
def s_d1_cImp_7_2 : Entry := symmEntry "ds-0167" "d1-0167" ((RNReps.q7).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_7_2
def s_d1_cImp_7_3 : Entry := symmEntry "ds-0168" "d1-0168" ((RNReps.q7).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_7_3
def s_d1_cImp_7_4 : Entry := symmEntry "ds-0169" "d1-0169" ((RNReps.q7).ifThen (RNReps.q4)) (RNReps.q10) PLLND.SemUI.RND.cImp_7_4
def s_d1_cImp_7_5 : Entry := symmEntry "ds-0170" "d1-0170" ((RNReps.q7).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND.cImp_7_5
def s_d1_cImp_7_6 : Entry := symmEntry "ds-0171" "d1-0171" ((RNReps.q7).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_7_6
def s_d1_cImp_7_8 : Entry := symmEntry "ds-0172" "d1-0172" ((RNReps.q7).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_8
def s_d1_cImp_7_9 : Entry := symmEntry "ds-0173" "d1-0173" ((RNReps.q7).ifThen (RNReps.q9)) (RNReps.q1) PLLND.SemUI.RND.cImp_7_9
def s_d1_cImp_8_0 : Entry := symmEntry "ds-0174" "d1-0174" ((RNReps.q8).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_8_0
def s_d1_cImp_8_13 : Entry := symmEntry "ds-0175" "d1-0175" ((RNReps.q8).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_8_13
def s_d1_cImp_8_2 : Entry := symmEntry "ds-0176" "d1-0176" ((RNReps.q8).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_8_2
def s_d1_cImp_8_3 : Entry := symmEntry "ds-0177" "d1-0177" ((RNReps.q8).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_8_3
def s_d1_cImp_8_6 : Entry := symmEntry "ds-0178" "d1-0178" ((RNReps.q8).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_8_6
def s_d1_cImp_9_0 : Entry := symmEntry "ds-0179" "d1-0179" ((RNReps.q9).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND.cImp_9_0
def s_d1_cImp_9_10 : Entry := symmEntry "ds-0180" "d1-0180" ((RNReps.q9).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cImp_9_10
def s_d1_cImp_9_11 : Entry := symmEntry "ds-0181" "d1-0181" ((RNReps.q9).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND.cImp_9_11
def s_d1_cImp_9_12 : Entry := symmEntry "ds-0182" "d1-0182" ((RNReps.q9).ifThen (RNReps.q12)) (RNReps.q1) PLLND.SemUI.RND.cImp_9_12
def s_d1_cImp_9_13 : Entry := symmEntry "ds-0183" "d1-0183" ((RNReps.q9).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND.cImp_9_13
def s_d1_cImp_9_14 : Entry := symmEntry "ds-0184" "d1-0184" ((RNReps.q9).ifThen (RNReps.q14)) (RNReps.q1) PLLND.SemUI.RND.cImp_9_14
def s_d1_cImp_9_2 : Entry := symmEntry "ds-0185" "d1-0185" ((RNReps.q9).ifThen (RNReps.q2)) (RNReps.q2) PLLND.SemUI.RND.cImp_9_2
def s_d1_cImp_9_3 : Entry := symmEntry "ds-0186" "d1-0186" ((RNReps.q9).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND.cImp_9_3
def s_d1_cImp_9_5 : Entry := symmEntry "ds-0187" "d1-0187" ((RNReps.q9).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND.cImp_9_5
def s_d1_cImp_9_6 : Entry := symmEntry "ds-0188" "d1-0188" ((RNReps.q9).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cImp_9_6
def s_d1_cImp_9_7 : Entry := symmEntry "ds-0189" "d1-0189" ((RNReps.q9).ifThen (RNReps.q7)) (RNReps.q8) PLLND.SemUI.RND.cImp_9_7
def s_d1_cOr_10_11 : Entry := symmEntry "ds-0190" "d1-0190" ((RNReps.q10).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_10_11
def s_d1_cOr_2_10 : Entry := symmEntry "ds-0191" "d1-0191" ((RNReps.q2).or (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cOr_2_10
def s_d1_cOr_2_11 : Entry := symmEntry "ds-0192" "d1-0192" ((RNReps.q2).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_2_11
def s_d1_cOr_2_12 : Entry := symmEntry "ds-0193" "d1-0193" ((RNReps.q2).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_2_12
def s_d1_cOr_2_4 : Entry := symmEntry "ds-0194" "d1-0194" ((RNReps.q2).or (RNReps.q4)) (RNReps.q4) PLLND.SemUI.RND.cOr_2_4
def s_d1_cOr_2_5 : Entry := symmEntry "ds-0195" "d1-0195" ((RNReps.q2).or (RNReps.q5)) (RNReps.q5) PLLND.SemUI.RND.cOr_2_5
def s_d1_cOr_2_6 : Entry := symmEntry "ds-0196" "d1-0196" ((RNReps.q2).or (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND.cOr_2_6
def s_d1_cOr_2_7 : Entry := symmEntry "ds-0197" "d1-0197" ((RNReps.q2).or (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cOr_2_7
def s_d1_cOr_2_8 : Entry := symmEntry "ds-0198" "d1-0198" ((RNReps.q2).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_2_8
def s_d1_cOr_2_9 : Entry := symmEntry "ds-0199" "d1-0199" ((RNReps.q2).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_2_9
def s_d1_cOr_3_10 : Entry := symmEntry "ds-0200" "d1-0200" ((RNReps.q3).or (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cOr_3_10
def s_d1_cOr_3_11 : Entry := symmEntry "ds-0201" "d1-0201" ((RNReps.q3).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_3_11
def s_d1_cOr_3_12 : Entry := symmEntry "ds-0202" "d1-0202" ((RNReps.q3).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_3_12
def s_d1_cOr_3_4 : Entry := symmEntry "ds-0203" "d1-0203" ((RNReps.q3).or (RNReps.q4)) (RNReps.q4) PLLND.SemUI.RND.cOr_3_4
def s_d1_cOr_3_5 : Entry := symmEntry "ds-0204" "d1-0204" ((RNReps.q3).or (RNReps.q5)) (RNReps.q5) PLLND.SemUI.RND.cOr_3_5
def s_d1_cOr_3_7 : Entry := symmEntry "ds-0205" "d1-0205" ((RNReps.q3).or (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cOr_3_7
def s_d1_cOr_3_8 : Entry := symmEntry "ds-0206" "d1-0206" ((RNReps.q3).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_3_8
def s_d1_cOr_3_9 : Entry := symmEntry "ds-0207" "d1-0207" ((RNReps.q3).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_3_9
def s_d1_cOr_4_10 : Entry := symmEntry "ds-0208" "d1-0208" ((RNReps.q4).or (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cOr_4_10
def s_d1_cOr_4_11 : Entry := symmEntry "ds-0209" "d1-0209" ((RNReps.q4).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_4_11
def s_d1_cOr_4_12 : Entry := symmEntry "ds-0210" "d1-0210" ((RNReps.q4).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_4_12
def s_d1_cOr_4_13 : Entry := symmEntry "ds-0211" "d1-0211" ((RNReps.q4).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND.cOr_4_13
def s_d1_cOr_4_5 : Entry := symmEntry "ds-0212" "d1-0212" ((RNReps.q4).or (RNReps.q5)) (RNReps.q5) PLLND.SemUI.RND.cOr_4_5
def s_d1_cOr_4_6 : Entry := symmEntry "ds-0213" "d1-0213" ((RNReps.q4).or (RNReps.q6)) (RNReps.q7) PLLND.SemUI.RND.cOr_4_6
def s_d1_cOr_4_7 : Entry := symmEntry "ds-0214" "d1-0214" ((RNReps.q4).or (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cOr_4_7
def s_d1_cOr_4_8 : Entry := symmEntry "ds-0215" "d1-0215" ((RNReps.q4).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_4_8
def s_d1_cOr_4_9 : Entry := symmEntry "ds-0216" "d1-0216" ((RNReps.q4).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_4_9
def s_d1_cOr_5_10 : Entry := symmEntry "ds-0217" "d1-0217" ((RNReps.q5).or (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND.cOr_5_10
def s_d1_cOr_5_11 : Entry := symmEntry "ds-0218" "d1-0218" ((RNReps.q5).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_5_11
def s_d1_cOr_5_12 : Entry := symmEntry "ds-0219" "d1-0219" ((RNReps.q5).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_5_12
def s_d1_cOr_5_13 : Entry := symmEntry "ds-0220" "d1-0220" ((RNReps.q5).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND.cOr_5_13
def s_d1_cOr_5_7 : Entry := symmEntry "ds-0221" "d1-0221" ((RNReps.q5).or (RNReps.q7)) (RNReps.q9) PLLND.SemUI.RND.cOr_5_7
def s_d1_cOr_5_9 : Entry := symmEntry "ds-0222" "d1-0222" ((RNReps.q5).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_5_9
def s_d1_cOr_6_11 : Entry := symmEntry "ds-0223" "d1-0223" ((RNReps.q6).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_6_11
def s_d1_cOr_6_12 : Entry := symmEntry "ds-0224" "d1-0224" ((RNReps.q6).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_6_12
def s_d1_cOr_6_7 : Entry := symmEntry "ds-0225" "d1-0225" ((RNReps.q6).or (RNReps.q7)) (RNReps.q7) PLLND.SemUI.RND.cOr_6_7
def s_d1_cOr_6_8 : Entry := symmEntry "ds-0226" "d1-0226" ((RNReps.q6).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_6_8
def s_d1_cOr_6_9 : Entry := symmEntry "ds-0227" "d1-0227" ((RNReps.q6).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_6_9
def s_d1_cOr_7_10 : Entry := symmEntry "ds-0228" "d1-0228" ((RNReps.q7).or (RNReps.q10)) (RNReps.q11) PLLND.SemUI.RND.cOr_7_10
def s_d1_cOr_7_11 : Entry := symmEntry "ds-0229" "d1-0229" ((RNReps.q7).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_7_11
def s_d1_cOr_7_12 : Entry := symmEntry "ds-0230" "d1-0230" ((RNReps.q7).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_7_12
def s_d1_cOr_7_8 : Entry := symmEntry "ds-0231" "d1-0231" ((RNReps.q7).or (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND.cOr_7_8
def s_d1_cOr_7_9 : Entry := symmEntry "ds-0232" "d1-0232" ((RNReps.q7).or (RNReps.q9)) (RNReps.q9) PLLND.SemUI.RND.cOr_7_9
def s_d1_cOr_9_10 : Entry := symmEntry "ds-0233" "d1-0233" ((RNReps.q9).or (RNReps.q10)) (RNReps.q11) PLLND.SemUI.RND.cOr_9_10
def s_d1_cOr_9_11 : Entry := symmEntry "ds-0234" "d1-0234" ((RNReps.q9).or (RNReps.q11)) (RNReps.q11) PLLND.SemUI.RND.cOr_9_11
def s_d1_cOr_9_12 : Entry := symmEntry "ds-0235" "d1-0235" ((RNReps.q9).or (RNReps.q12)) (RNReps.q12) PLLND.SemUI.RND.cOr_9_12
def s_d2_cAnd_10_14 : Entry := symmEntry "ds-0236" "d2-0000" ((RNReps.q10).and (RNReps.q14)) (RNReps.q5) PLLND.SemUI.RND2.cAnd_10_14
def s_d2_cAnd_10_15 : Entry := symmEntry "ds-0237" "d2-0001" ((RNReps.q10).and (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_10_15
def s_d2_cAnd_11_14 : Entry := symmEntry "ds-0238" "d2-0002" ((RNReps.q11).and (RNReps.q14)) (RNReps.q9) PLLND.SemUI.RND2.cAnd_11_14
def s_d2_cAnd_11_15 : Entry := symmEntry "ds-0239" "d2-0003" ((RNReps.q11).and (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_11_15
def s_d2_cAnd_12_13 : Entry := symmEntry "ds-0240" "d2-0004" ((RNReps.q12).and (RNReps.q13)) (RNReps.q12) PLLND.SemUI.RND2.cAnd_12_13
def s_d2_cAnd_12_14 : Entry := symmEntry "ds-0241" "d2-0005" ((RNReps.q12).and (RNReps.q14)) (RNReps.q12) PLLND.SemUI.RND2.cAnd_12_14
def s_d2_cAnd_12_15 : Entry := symmEntry "ds-0242" "d2-0006" ((RNReps.q12).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_12_15
def s_d2_cAnd_13_15 : Entry := symmEntry "ds-0243" "d2-0007" ((RNReps.q13).and (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_13_15
def s_d2_cAnd_14_15 : Entry := symmEntry "ds-0244" "d2-0008" ((RNReps.q14).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_14_15
def s_d2_cAnd_2_15 : Entry := symmEntry "ds-0245" "d2-0009" ((RNReps.q2).and (RNReps.q15)) (RNReps.q2) PLLND.SemUI.RND2.cAnd_2_15
def s_d2_cAnd_3_15 : Entry := symmEntry "ds-0246" "d2-0010" ((RNReps.q3).and (RNReps.q15)) (RNReps.q3) PLLND.SemUI.RND2.cAnd_3_15
def s_d2_cAnd_4_14 : Entry := symmEntry "ds-0247" "d2-0011" ((RNReps.q4).and (RNReps.q14)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_4_14
def s_d2_cAnd_4_15 : Entry := symmEntry "ds-0248" "d2-0012" ((RNReps.q4).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_4_15
def s_d2_cAnd_5_15 : Entry := symmEntry "ds-0249" "d2-0013" ((RNReps.q5).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_5_15
def s_d2_cAnd_6_15 : Entry := symmEntry "ds-0250" "d2-0014" ((RNReps.q6).and (RNReps.q15)) (RNReps.q2) PLLND.SemUI.RND2.cAnd_6_15
def s_d2_cAnd_7_15 : Entry := symmEntry "ds-0251" "d2-0015" ((RNReps.q7).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_7_15
def s_d2_cAnd_8_10 : Entry := symmEntry "ds-0252" "d2-0016" ((RNReps.q8).and (RNReps.q10)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_8_10
def s_d2_cAnd_8_15 : Entry := symmEntry "ds-0253" "d2-0017" ((RNReps.q8).and (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cAnd_8_15
def s_d2_cAnd_9_13 : Entry := symmEntry "ds-0254" "d2-0018" ((RNReps.q9).and (RNReps.q13)) (RNReps.q9) PLLND.SemUI.RND2.cAnd_9_13
def s_d2_cAnd_9_14 : Entry := symmEntry "ds-0255" "d2-0019" ((RNReps.q9).and (RNReps.q14)) (RNReps.q9) PLLND.SemUI.RND2.cAnd_9_14
def s_d2_cAnd_9_15 : Entry := symmEntry "ds-0256" "d2-0020" ((RNReps.q9).and (RNReps.q15)) (RNReps.q4) PLLND.SemUI.RND2.cAnd_9_15
def s_d2_cBox_14 : Entry := symmEntry "ds-0257" "d2-0021" ((RNReps.q14).somehow) (RNReps.q14) PLLND.SemUI.RND2.cBox_14
def s_d2_cImp_10_12 : Entry := symmEntry "ds-0258" "d2-0022" ((RNReps.q10).ifThen (RNReps.q12)) (RNReps.q14) PLLND.SemUI.RND2.cImp_10_12
def s_d2_cImp_10_14 : Entry := symmEntry "ds-0259" "d2-0023" ((RNReps.q10).ifThen (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cImp_10_14
def s_d2_cImp_10_15 : Entry := symmEntry "ds-0260" "d2-0024" ((RNReps.q10).ifThen (RNReps.q15)) (RNReps.q8) PLLND.SemUI.RND2.cImp_10_15
def s_d2_cImp_10_8 : Entry := symmEntry "ds-0261" "d2-0025" ((RNReps.q10).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_10_8
def s_d2_cImp_10_9 : Entry := symmEntry "ds-0262" "d2-0026" ((RNReps.q10).ifThen (RNReps.q9)) (RNReps.q14) PLLND.SemUI.RND2.cImp_10_9
def s_d2_cImp_11_12 : Entry := symmEntry "ds-0263" "d2-0027" ((RNReps.q11).ifThen (RNReps.q12)) (RNReps.q14) PLLND.SemUI.RND2.cImp_11_12
def s_d2_cImp_11_14 : Entry := symmEntry "ds-0264" "d2-0028" ((RNReps.q11).ifThen (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cImp_11_14
def s_d2_cImp_11_15 : Entry := symmEntry "ds-0265" "d2-0029" ((RNReps.q11).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_11_15
def s_d2_cImp_11_4 : Entry := symmEntry "ds-0266" "d2-0030" ((RNReps.q11).ifThen (RNReps.q4)) (RNReps.q4) PLLND.SemUI.RND2.cImp_11_4
def s_d2_cImp_11_8 : Entry := symmEntry "ds-0267" "d2-0031" ((RNReps.q11).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_11_8
def s_d2_cImp_11_9 : Entry := symmEntry "ds-0268" "d2-0032" ((RNReps.q11).ifThen (RNReps.q9)) (RNReps.q14) PLLND.SemUI.RND2.cImp_11_9
def s_d2_cImp_12_15 : Entry := symmEntry "ds-0269" "d2-0033" ((RNReps.q12).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_12_15
def s_d2_cImp_12_4 : Entry := symmEntry "ds-0270" "d2-0034" ((RNReps.q12).ifThen (RNReps.q4)) (RNReps.q15) PLLND.SemUI.RND2.cImp_12_4
def s_d2_cImp_12_8 : Entry := symmEntry "ds-0271" "d2-0035" ((RNReps.q12).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_12_8
def s_d2_cImp_13_15 : Entry := symmEntry "ds-0272" "d2-0036" ((RNReps.q13).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_13_15
def s_d2_cImp_13_8 : Entry := symmEntry "ds-0273" "d2-0037" ((RNReps.q13).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_13_8
def s_d2_cImp_14_15 : Entry := symmEntry "ds-0274" "d2-0038" ((RNReps.q14).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_14_15
def s_d2_cImp_14_4 : Entry := symmEntry "ds-0275" "d2-0039" ((RNReps.q14).ifThen (RNReps.q4)) (RNReps.q15) PLLND.SemUI.RND2.cImp_14_4
def s_d2_cImp_14_5 : Entry := symmEntry "ds-0276" "d2-0040" ((RNReps.q14).ifThen (RNReps.q5)) (RNReps.q10) PLLND.SemUI.RND2.cImp_14_5
def s_d2_cImp_14_8 : Entry := symmEntry "ds-0277" "d2-0041" ((RNReps.q14).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_14_8
def s_d2_cImp_15_0 : Entry := symmEntry "ds-0278" "d2-0042" ((RNReps.q15).ifThen (RNReps.q0)) (RNReps.q0) PLLND.SemUI.RND2.cImp_15_0
def s_d2_cImp_15_10 : Entry := symmEntry "ds-0279" "d2-0043" ((RNReps.q15).ifThen (RNReps.q10)) (RNReps.q1) PLLND.SemUI.RND2.cImp_15_10
def s_d2_cImp_15_11 : Entry := symmEntry "ds-0280" "d2-0044" ((RNReps.q15).ifThen (RNReps.q11)) (RNReps.q1) PLLND.SemUI.RND2.cImp_15_11
def s_d2_cImp_15_13 : Entry := symmEntry "ds-0281" "d2-0045" ((RNReps.q15).ifThen (RNReps.q13)) (RNReps.q1) PLLND.SemUI.RND2.cImp_15_13
def s_d2_cImp_15_2 : Entry := symmEntry "ds-0282" "d2-0046" ((RNReps.q15).ifThen (RNReps.q2)) (RNReps.q6) PLLND.SemUI.RND2.cImp_15_2
def s_d2_cImp_15_3 : Entry := symmEntry "ds-0283" "d2-0047" ((RNReps.q15).ifThen (RNReps.q3)) (RNReps.q3) PLLND.SemUI.RND2.cImp_15_3
def s_d2_cImp_15_6 : Entry := symmEntry "ds-0284" "d2-0048" ((RNReps.q15).ifThen (RNReps.q6)) (RNReps.q6) PLLND.SemUI.RND2.cImp_15_6
def s_d2_cImp_15_8 : Entry := symmEntry "ds-0285" "d2-0049" ((RNReps.q15).ifThen (RNReps.q8)) (RNReps.q1) PLLND.SemUI.RND2.cImp_15_8
def s_d2_cImp_2_15 : Entry := symmEntry "ds-0286" "d2-0050" ((RNReps.q2).ifThen (RNReps.q15)) (RNReps.q1) PLLND.SemUI.RND2.cImp_2_15
def s_d2_cImp_3_15 : Entry := symmEntry "ds-0287" "d2-0051" ((RNReps.q3).ifThen (RNReps.q15)) (RNReps.q1) PLLND.SemUI.RND2.cImp_3_15
def s_d2_cImp_4_15 : Entry := symmEntry "ds-0288" "d2-0052" ((RNReps.q4).ifThen (RNReps.q15)) (RNReps.q1) PLLND.SemUI.RND2.cImp_4_15
def s_d2_cImp_5_15 : Entry := symmEntry "ds-0289" "d2-0053" ((RNReps.q5).ifThen (RNReps.q15)) (RNReps.q8) PLLND.SemUI.RND2.cImp_5_15
def s_d2_cImp_6_15 : Entry := symmEntry "ds-0290" "d2-0054" ((RNReps.q6).ifThen (RNReps.q15)) (RNReps.q10) PLLND.SemUI.RND2.cImp_6_15
def s_d2_cImp_7_15 : Entry := symmEntry "ds-0291" "d2-0055" ((RNReps.q7).ifThen (RNReps.q15)) (RNReps.q10) PLLND.SemUI.RND2.cImp_7_15
def s_d2_cImp_8_10 : Entry := symmEntry "ds-0292" "d2-0056" ((RNReps.q8).ifThen (RNReps.q10)) (RNReps.q10) PLLND.SemUI.RND2.cImp_8_10
def s_d2_cImp_8_15 : Entry := symmEntry "ds-0293" "d2-0057" ((RNReps.q8).ifThen (RNReps.q15)) (RNReps.q10) PLLND.SemUI.RND2.cImp_8_15
def s_d2_cImp_9_15 : Entry := symmEntry "ds-0294" "d2-0058" ((RNReps.q9).ifThen (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cImp_9_15
def s_d2_cImp_9_8 : Entry := symmEntry "ds-0295" "d2-0059" ((RNReps.q9).ifThen (RNReps.q8)) (RNReps.q8) PLLND.SemUI.RND2.cImp_9_8
def s_d2_cOr_10_15 : Entry := symmEntry "ds-0296" "d2-0060" ((RNReps.q10).or (RNReps.q15)) (RNReps.q10) PLLND.SemUI.RND2.cOr_10_15
def s_d2_cOr_11_15 : Entry := symmEntry "ds-0297" "d2-0061" ((RNReps.q11).or (RNReps.q15)) (RNReps.q11) PLLND.SemUI.RND2.cOr_11_15
def s_d2_cOr_12_13 : Entry := symmEntry "ds-0298" "d2-0062" ((RNReps.q12).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_12_13
def s_d2_cOr_12_14 : Entry := symmEntry "ds-0299" "d2-0063" ((RNReps.q12).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_12_14
def s_d2_cOr_13_15 : Entry := symmEntry "ds-0300" "d2-0064" ((RNReps.q13).or (RNReps.q15)) (RNReps.q13) PLLND.SemUI.RND2.cOr_13_15
def s_d2_cOr_2_13 : Entry := symmEntry "ds-0301" "d2-0065" ((RNReps.q2).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_2_13
def s_d2_cOr_2_14 : Entry := symmEntry "ds-0302" "d2-0066" ((RNReps.q2).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_2_14
def s_d2_cOr_2_15 : Entry := symmEntry "ds-0303" "d2-0067" ((RNReps.q2).or (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cOr_2_15
def s_d2_cOr_3_13 : Entry := symmEntry "ds-0304" "d2-0068" ((RNReps.q3).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_3_13
def s_d2_cOr_3_14 : Entry := symmEntry "ds-0305" "d2-0069" ((RNReps.q3).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_3_14
def s_d2_cOr_3_15 : Entry := symmEntry "ds-0306" "d2-0070" ((RNReps.q3).or (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cOr_3_15
def s_d2_cOr_4_14 : Entry := symmEntry "ds-0307" "d2-0071" ((RNReps.q4).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_4_14
def s_d2_cOr_4_15 : Entry := symmEntry "ds-0308" "d2-0072" ((RNReps.q4).or (RNReps.q15)) (RNReps.q15) PLLND.SemUI.RND2.cOr_4_15
def s_d2_cOr_5_14 : Entry := symmEntry "ds-0309" "d2-0073" ((RNReps.q5).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_5_14
def s_d2_cOr_6_13 : Entry := symmEntry "ds-0310" "d2-0074" ((RNReps.q6).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_6_13
def s_d2_cOr_6_14 : Entry := symmEntry "ds-0311" "d2-0075" ((RNReps.q6).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_6_14
def s_d2_cOr_7_13 : Entry := symmEntry "ds-0312" "d2-0076" ((RNReps.q7).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_7_13
def s_d2_cOr_7_14 : Entry := symmEntry "ds-0313" "d2-0077" ((RNReps.q7).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_7_14
def s_d2_cOr_8_13 : Entry := symmEntry "ds-0314" "d2-0078" ((RNReps.q8).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_8_13
def s_d2_cOr_8_15 : Entry := symmEntry "ds-0315" "d2-0079" ((RNReps.q8).or (RNReps.q15)) (RNReps.q8) PLLND.SemUI.RND2.cOr_8_15
def s_d2_cOr_9_13 : Entry := symmEntry "ds-0316" "d2-0080" ((RNReps.q9).or (RNReps.q13)) (RNReps.q13) PLLND.SemUI.RND2.cOr_9_13
def s_d2_cOr_9_14 : Entry := symmEntry "ds-0317" "d2-0081" ((RNReps.q9).or (RNReps.q14)) (RNReps.q14) PLLND.SemUI.RND2.cOr_9_14

/-! ### The q15-class triangle, through `q15` itself

`w2 = q9⊃q4` IS `q15` definitionally, so its edges are identities; the
other three names of the class are linked pairwise below. -/

def t_w1_w3 : Entry := transEntry "dt-t_w1_w3" "d2-0016" "ds-0270"
  ((RNReps.q8).and (RNReps.q10)) (RNReps.q15) ((RNReps.q12).ifThen (RNReps.q4)) PLLND.SemUI.RND2.cAnd_8_10 (PLLND.SemUI.RND2.cImp_12_4).symm
def t_w1_w4 : Entry := transEntry "dt-t_w1_w4" "d2-0016" "ds-0275"
  ((RNReps.q8).and (RNReps.q10)) (RNReps.q15) ((RNReps.q14).ifThen (RNReps.q4)) PLLND.SemUI.RND2.cAnd_8_10 (PLLND.SemUI.RND2.cImp_14_4).symm
def t_w3_w4 : Entry := transEntry "dt-t_w3_w4" "d2-0034" "ds-0275"
  ((RNReps.q12).ifThen (RNReps.q4)) (RNReps.q15) ((RNReps.q14).ifThen (RNReps.q4)) PLLND.SemUI.RND2.cImp_12_4 (PLLND.SemUI.RND2.cImp_14_4).symm

def derivedEntries : List Entry :=
  [ s_d1_cAnd_10_11,
    s_d1_cAnd_10_12,
    s_d1_cAnd_11_12,
    s_d1_cAnd_2_10,
    s_d1_cAnd_2_11,
    s_d1_cAnd_2_12,
    s_d1_cAnd_2_13,
    s_d1_cAnd_2_14,
    s_d1_cAnd_2_3,
    s_d1_cAnd_2_4,
    s_d1_cAnd_2_5,
    s_d1_cAnd_2_6,
    s_d1_cAnd_2_7,
    s_d1_cAnd_2_8,
    s_d1_cAnd_2_9,
    s_d1_cAnd_3_10,
    s_d1_cAnd_3_11,
    s_d1_cAnd_3_12,
    s_d1_cAnd_3_13,
    s_d1_cAnd_3_14,
    s_d1_cAnd_3_4,
    s_d1_cAnd_3_5,
    s_d1_cAnd_3_6,
    s_d1_cAnd_3_7,
    s_d1_cAnd_3_8,
    s_d1_cAnd_3_9,
    s_d1_cAnd_4_10,
    s_d1_cAnd_4_11,
    s_d1_cAnd_4_12,
    s_d1_cAnd_4_13,
    s_d1_cAnd_4_5,
    s_d1_cAnd_4_6,
    s_d1_cAnd_4_7,
    s_d1_cAnd_4_8,
    s_d1_cAnd_4_9,
    s_d1_cAnd_5_10,
    s_d1_cAnd_5_11,
    s_d1_cAnd_5_12,
    s_d1_cAnd_5_13,
    s_d1_cAnd_5_14,
    s_d1_cAnd_5_6,
    s_d1_cAnd_5_7,
    s_d1_cAnd_5_8,
    s_d1_cAnd_5_9,
    s_d1_cAnd_6_10,
    s_d1_cAnd_6_11,
    s_d1_cAnd_6_12,
    s_d1_cAnd_6_13,
    s_d1_cAnd_6_14,
    s_d1_cAnd_6_7,
    s_d1_cAnd_6_8,
    s_d1_cAnd_6_9,
    s_d1_cAnd_7_10,
    s_d1_cAnd_7_11,
    s_d1_cAnd_7_12,
    s_d1_cAnd_7_13,
    s_d1_cAnd_7_14,
    s_d1_cAnd_7_8,
    s_d1_cAnd_7_9,
    s_d1_cAnd_8_13,
    s_d1_cAnd_8_9,
    s_d1_cAnd_9_10,
    s_d1_cAnd_9_11,
    s_d1_cAnd_9_12,
    s_d1_cBox_1,
    s_d1_cBox_10,
    s_d1_cBox_4,
    s_d1_cBox_6,
    s_d1_cBox_9,
    s_d1_cImp_10_0,
    s_d1_cImp_10_11,
    s_d1_cImp_10_2,
    s_d1_cImp_10_3,
    s_d1_cImp_10_6,
    s_d1_cImp_11_0,
    s_d1_cImp_11_10,
    s_d1_cImp_11_2,
    s_d1_cImp_11_3,
    s_d1_cImp_11_5,
    s_d1_cImp_11_6,
    s_d1_cImp_12_0,
    s_d1_cImp_12_10,
    s_d1_cImp_12_13,
    s_d1_cImp_12_14,
    s_d1_cImp_12_2,
    s_d1_cImp_12_3,
    s_d1_cImp_12_5,
    s_d1_cImp_12_6,
    s_d1_cImp_13_0,
    s_d1_cImp_13_10,
    s_d1_cImp_13_2,
    s_d1_cImp_13_3,
    s_d1_cImp_13_4,
    s_d1_cImp_13_6,
    s_d1_cImp_13_7,
    s_d1_cImp_14_0,
    s_d1_cImp_14_10,
    s_d1_cImp_14_2,
    s_d1_cImp_14_3,
    s_d1_cImp_14_6,
    s_d1_cImp_2_10,
    s_d1_cImp_2_11,
    s_d1_cImp_2_12,
    s_d1_cImp_2_13,
    s_d1_cImp_2_14,
    s_d1_cImp_2_3,
    s_d1_cImp_2_4,
    s_d1_cImp_2_5,
    s_d1_cImp_2_6,
    s_d1_cImp_2_7,
    s_d1_cImp_2_8,
    s_d1_cImp_2_9,
    s_d1_cImp_3_10,
    s_d1_cImp_3_11,
    s_d1_cImp_3_12,
    s_d1_cImp_3_13,
    s_d1_cImp_3_14,
    s_d1_cImp_3_2,
    s_d1_cImp_3_4,
    s_d1_cImp_3_5,
    s_d1_cImp_3_6,
    s_d1_cImp_3_7,
    s_d1_cImp_3_8,
    s_d1_cImp_3_9,
    s_d1_cImp_4_0,
    s_d1_cImp_4_10,
    s_d1_cImp_4_11,
    s_d1_cImp_4_12,
    s_d1_cImp_4_13,
    s_d1_cImp_4_14,
    s_d1_cImp_4_2,
    s_d1_cImp_4_3,
    s_d1_cImp_4_5,
    s_d1_cImp_4_6,
    s_d1_cImp_4_7,
    s_d1_cImp_4_8,
    s_d1_cImp_4_9,
    s_d1_cImp_5_0,
    s_d1_cImp_5_10,
    s_d1_cImp_5_11,
    s_d1_cImp_5_12,
    s_d1_cImp_5_13,
    s_d1_cImp_5_14,
    s_d1_cImp_5_2,
    s_d1_cImp_5_3,
    s_d1_cImp_5_6,
    s_d1_cImp_5_7,
    s_d1_cImp_5_8,
    s_d1_cImp_5_9,
    s_d1_cImp_6_0,
    s_d1_cImp_6_10,
    s_d1_cImp_6_11,
    s_d1_cImp_6_12,
    s_d1_cImp_6_13,
    s_d1_cImp_6_14,
    s_d1_cImp_6_3,
    s_d1_cImp_6_4,
    s_d1_cImp_6_5,
    s_d1_cImp_6_7,
    s_d1_cImp_6_8,
    s_d1_cImp_6_9,
    s_d1_cImp_7_0,
    s_d1_cImp_7_10,
    s_d1_cImp_7_11,
    s_d1_cImp_7_12,
    s_d1_cImp_7_13,
    s_d1_cImp_7_14,
    s_d1_cImp_7_2,
    s_d1_cImp_7_3,
    s_d1_cImp_7_4,
    s_d1_cImp_7_5,
    s_d1_cImp_7_6,
    s_d1_cImp_7_8,
    s_d1_cImp_7_9,
    s_d1_cImp_8_0,
    s_d1_cImp_8_13,
    s_d1_cImp_8_2,
    s_d1_cImp_8_3,
    s_d1_cImp_8_6,
    s_d1_cImp_9_0,
    s_d1_cImp_9_10,
    s_d1_cImp_9_11,
    s_d1_cImp_9_12,
    s_d1_cImp_9_13,
    s_d1_cImp_9_14,
    s_d1_cImp_9_2,
    s_d1_cImp_9_3,
    s_d1_cImp_9_5,
    s_d1_cImp_9_6,
    s_d1_cImp_9_7,
    s_d1_cOr_10_11,
    s_d1_cOr_2_10,
    s_d1_cOr_2_11,
    s_d1_cOr_2_12,
    s_d1_cOr_2_4,
    s_d1_cOr_2_5,
    s_d1_cOr_2_6,
    s_d1_cOr_2_7,
    s_d1_cOr_2_8,
    s_d1_cOr_2_9,
    s_d1_cOr_3_10,
    s_d1_cOr_3_11,
    s_d1_cOr_3_12,
    s_d1_cOr_3_4,
    s_d1_cOr_3_5,
    s_d1_cOr_3_7,
    s_d1_cOr_3_8,
    s_d1_cOr_3_9,
    s_d1_cOr_4_10,
    s_d1_cOr_4_11,
    s_d1_cOr_4_12,
    s_d1_cOr_4_13,
    s_d1_cOr_4_5,
    s_d1_cOr_4_6,
    s_d1_cOr_4_7,
    s_d1_cOr_4_8,
    s_d1_cOr_4_9,
    s_d1_cOr_5_10,
    s_d1_cOr_5_11,
    s_d1_cOr_5_12,
    s_d1_cOr_5_13,
    s_d1_cOr_5_7,
    s_d1_cOr_5_9,
    s_d1_cOr_6_11,
    s_d1_cOr_6_12,
    s_d1_cOr_6_7,
    s_d1_cOr_6_8,
    s_d1_cOr_6_9,
    s_d1_cOr_7_10,
    s_d1_cOr_7_11,
    s_d1_cOr_7_12,
    s_d1_cOr_7_8,
    s_d1_cOr_7_9,
    s_d1_cOr_9_10,
    s_d1_cOr_9_11,
    s_d1_cOr_9_12,
    s_d2_cAnd_10_14,
    s_d2_cAnd_10_15,
    s_d2_cAnd_11_14,
    s_d2_cAnd_11_15,
    s_d2_cAnd_12_13,
    s_d2_cAnd_12_14,
    s_d2_cAnd_12_15,
    s_d2_cAnd_13_15,
    s_d2_cAnd_14_15,
    s_d2_cAnd_2_15,
    s_d2_cAnd_3_15,
    s_d2_cAnd_4_14,
    s_d2_cAnd_4_15,
    s_d2_cAnd_5_15,
    s_d2_cAnd_6_15,
    s_d2_cAnd_7_15,
    s_d2_cAnd_8_10,
    s_d2_cAnd_8_15,
    s_d2_cAnd_9_13,
    s_d2_cAnd_9_14,
    s_d2_cAnd_9_15,
    s_d2_cBox_14,
    s_d2_cImp_10_12,
    s_d2_cImp_10_14,
    s_d2_cImp_10_15,
    s_d2_cImp_10_8,
    s_d2_cImp_10_9,
    s_d2_cImp_11_12,
    s_d2_cImp_11_14,
    s_d2_cImp_11_15,
    s_d2_cImp_11_4,
    s_d2_cImp_11_8,
    s_d2_cImp_11_9,
    s_d2_cImp_12_15,
    s_d2_cImp_12_4,
    s_d2_cImp_12_8,
    s_d2_cImp_13_15,
    s_d2_cImp_13_8,
    s_d2_cImp_14_15,
    s_d2_cImp_14_4,
    s_d2_cImp_14_5,
    s_d2_cImp_14_8,
    s_d2_cImp_15_0,
    s_d2_cImp_15_10,
    s_d2_cImp_15_11,
    s_d2_cImp_15_13,
    s_d2_cImp_15_2,
    s_d2_cImp_15_3,
    s_d2_cImp_15_6,
    s_d2_cImp_15_8,
    s_d2_cImp_2_15,
    s_d2_cImp_3_15,
    s_d2_cImp_4_15,
    s_d2_cImp_5_15,
    s_d2_cImp_6_15,
    s_d2_cImp_7_15,
    s_d2_cImp_8_10,
    s_d2_cImp_8_15,
    s_d2_cImp_9_15,
    s_d2_cImp_9_8,
    s_d2_cOr_10_15,
    s_d2_cOr_11_15,
    s_d2_cOr_12_13,
    s_d2_cOr_12_14,
    s_d2_cOr_13_15,
    s_d2_cOr_2_13,
    s_d2_cOr_2_14,
    s_d2_cOr_2_15,
    s_d2_cOr_3_13,
    s_d2_cOr_3_14,
    s_d2_cOr_3_15,
    s_d2_cOr_4_14,
    s_d2_cOr_4_15,
    s_d2_cOr_5_14,
    s_d2_cOr_6_13,
    s_d2_cOr_6_14,
    s_d2_cOr_7_13,
    s_d2_cOr_7_14,
    s_d2_cOr_8_13,
    s_d2_cOr_8_15,
    s_d2_cOr_9_13,
    s_d2_cOr_9_14,
    t_w1_w3,
    t_w1_w4,
    t_w3_w4 ]

set_option maxRecDepth 8192 in
theorem derivedEntries_length : derivedEntries.length = 321 := rfl

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.derivedEntries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms derivedEntries

/-- info: 'RNDB.derivedEntries_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms derivedEntries_length

end RNDB