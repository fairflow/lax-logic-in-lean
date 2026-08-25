import wip.rnDict2Hand

/-!
# The enlarged RN(◯,{}) dictionary round: 16 representatives

GENERATED FILE — do not edit by hand.  Produced by
`wip/rnDictGen.lean` (`pending2` / `cells2` / `assemble2` modes).

The 15 certified dictionary classes of `wip/rnDict.lean` enlarged by
the distinct classes among the §40 closure-failure witnesses after
pairwise separation (`wip/rnSep.lean`: w1 ≡ w2 ≡ w3, so q15 is the
class of q9 ⊃ q4 ≡ q8 ∧ q10 ≡ q12 ⊃ q4), closed under
∧/∨/⊃/◯ for ONE round with kernel-checked `Interd` certificates.
Old certified cells reference their `wip.rnDict` theorems by name;
old sorried cells and all new cells were re-resolved with the
escalated stages (exhaustive ≤4-world battery, exhaustive rooted
5-world battery, budgeted G4iLL″ search with cut-chains through all
19 representatives).  Cells that still resist are recorded as sorried
lemmas (OPEN, with candidate shortlists) or as REFUTED CELLS (new
classes beyond the 19 — the closure fails there; witness theorems in
`wip/rnDictRefute2.lean`).
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND2

open RND

/-! ## The four new representatives -/

def q15 : PLLFormula := (.ifThen q9 q4)

def repsL2 : List PLLFormula := [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15]

def rep2 : Fin 16 → PLLFormula := fun i => repsL2.getD i.val .falsePLL

/-! ## The closure tables -/

def and2T : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [0, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
   [0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3],
   [0, 4, 2, 3, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4],
   [0, 5, 2, 3, 4, 5, 2, 4, 4, 5, 5, 5, 5, 5, 5, 4],
   [0, 6, 2, 0, 2, 2, 6, 6, 6, 6, 2, 6, 6, 6, 6, 2],
   [0, 7, 2, 3, 4, 4, 6, 7, 7, 7, 4, 7, 7, 7, 7, 4],
   [0, 8, 2, 3, 4, 4, 6, 7, 8, 7, 15, 0, 0, 8, 0, 15],
   [0, 9, 2, 3, 4, 5, 6, 7, 7, 9, 5, 9, 9, 9, 9, 4],
   [0, 10, 2, 3, 4, 5, 2, 4, 15, 5, 10, 10, 5, 0, 5, 15],
   [0, 11, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 9, 0, 9, 15],
   [0, 12, 2, 3, 4, 5, 6, 7, 0, 9, 5, 9, 12, 12, 12, 4],
   [0, 13, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 12, 13, 0, 15],
   [0, 14, 2, 3, 4, 5, 6, 7, 0, 9, 5, 9, 12, 0, 14, 4],
   [0, 15, 2, 3, 4, 4, 2, 4, 15, 4, 15, 15, 4, 15, 4, 15]]
def or2T : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [2, 1, 2, 4, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [3, 1, 4, 3, 4, 5, 7, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [4, 1, 4, 4, 4, 5, 7, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [5, 1, 5, 5, 5, 5, 9, 9, 0, 9, 10, 11, 12, 13, 14, 0],
   [6, 1, 6, 7, 7, 9, 6, 7, 8, 9, 11, 11, 12, 13, 14, 0],
   [7, 1, 7, 7, 7, 9, 7, 7, 8, 9, 11, 11, 12, 13, 14, 0],
   [8, 1, 8, 8, 8, 0, 8, 8, 8, 0, 0, 0, 0, 13, 0, 8],
   [9, 1, 9, 9, 9, 9, 9, 9, 0, 9, 11, 11, 12, 13, 14, 0],
   [10, 1, 10, 10, 10, 10, 11, 11, 0, 11, 10, 11, 0, 0, 0, 10],
   [11, 1, 11, 11, 11, 11, 11, 11, 0, 11, 11, 11, 0, 0, 0, 11],
   [12, 1, 12, 12, 12, 12, 12, 12, 0, 12, 0, 0, 12, 13, 14, 0],
   [13, 1, 13, 13, 13, 13, 13, 13, 13, 13, 0, 0, 13, 13, 0, 13],
   [14, 1, 14, 14, 14, 14, 14, 14, 0, 14, 0, 0, 14, 0, 14, 0],
   [15, 1, 15, 15, 15, 0, 0, 0, 8, 0, 10, 11, 0, 13, 0, 15]]
def imp2T : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [3, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [6, 1, 6, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 6, 3, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 6, 3, 8, 1, 6, 8, 8, 1, 1, 1, 1, 1, 1, 8],
   [3, 1, 10, 3, 10, 10, 1, 1, 1, 1, 10, 1, 1, 1, 1, 10],
   [0, 1, 2, 3, 10, 10, 6, 1, 1, 1, 10, 1, 1, 1, 1, 10],
   [0, 1, 2, 3, 0, 0, 6, 0, 1, 0, 10, 0, 0, 1, 0, 10],
   [0, 1, 2, 3, 15, 10, 6, 8, 8, 1, 10, 1, 1, 1, 1, 15],
   [0, 1, 6, 3, 0, 14, 6, 0, 8, 14, 1, 1, 14, 0, 14, 8],
   [0, 1, 2, 3, 4, 5, 6, 0, 8, 14, 10, 1, 14, 0, 14, 15],
   [0, 1, 2, 3, 15, 10, 6, 0, 8, 0, 10, 0, 1, 1, 1, 15],
   [0, 1, 2, 3, 4, 0, 6, 7, 8, 0, 10, 0, 0, 1, 0, 15],
   [0, 1, 2, 3, 15, 10, 6, 0, 8, 0, 10, 0, 0, 0, 1, 15],
   [0, 1, 6, 3, 0, 0, 6, 0, 1, 0, 1, 1, 0, 1, 0, 1]]

def box2T : List Nat := [2, 1, 2, 5, 5, 5, 6, 12, 13, 12, 10, 0, 12, 13, 14, 0]

def and2Idx (i j : Fin 16) : Fin 16 :=
  ⟨((and2T.getD i.val []).getD j.val 0) % 16, Nat.mod_lt _ (by decide)⟩

def or2Idx (i j : Fin 16) : Fin 16 :=
  ⟨((or2T.getD i.val []).getD j.val 0) % 16, Nat.mod_lt _ (by decide)⟩

def imp2Idx (i j : Fin 16) : Fin 16 :=
  ⟨((imp2T.getD i.val []).getD j.val 0) % 16, Nat.mod_lt _ (by decide)⟩

def box2Idx (i : Fin 16) : Fin 16 :=
  ⟨(box2T.getD i.val 0) % 16, Nat.mod_lt _ (by decide)⟩

/-! ## Searched-cell certificates (escalated round) -/

theorem cAnd_2_15 : Interd (q2.and q15) q2 :=
  ⟨(ofG4 (.andL (A := q2) (B := q15) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))))),
   (ofG4 (.andR (.laxL (A := q0) (.head _) (.botL (.head _))) (.impR (.orR1 (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_3_15 : Interd (q3.and q15) q3 :=
  ⟨(ofG4 (.impR (.andL (A := q3) (B := q15) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _)))))),
   (ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impR (.orR2 (.impR (.orL (A := q5) (B := q6) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.laxL (A := q0) (.tail _ (.tail _ (.head _))) (.botL (.head _))) (.botL (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))⟩

theorem cAnd_4_14 : Interd (q4.and q14) q4 := hand_cAnd_4_14

theorem cAnd_4_15 : Interd (q4.and q15) q4 :=
  ⟨(ofG4 (.andL (A := q4) (B := q15) (.head _) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))),
   (ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q5) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cAnd_5_15 : Interd (q5.and q15) q4 :=
  ⟨(ofG4 (.andL (A := q5) (B := q15) (.head _) (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))),
   (ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q5) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cAnd_6_15 : Interd (q6.and q15) q2 :=
  ⟨(ofG4 (.andL (A := q6) (B := q15) (.head _) (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))),
   (ofG4 (.andR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))) (.impR (.orR1 (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))))⟩

theorem cAnd_7_15 : Interd (q7.and q15) q4 :=
  ⟨(ofG4 (.andL (A := q7) (B := q15) (.head _) (.orL (A := q3) (B := q6) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.tail _ (.head _))) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))),
   (ofG4 (.andR (.orL (A := q2) (B := q3) (.head _) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.impR (.orL (A := q5) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cAnd_8_10 : Interd (q8.and q10) q15 := hand_cAnd_8_10

theorem cAnd_8_15 : Interd (q8.and q15) q15 := hand_cAnd_8_15

theorem cAnd_9_13 : Interd (q9.and q13) q9 := hand_cAnd_9_13

theorem cAnd_9_14 : Interd (q9.and q14) q9 := hand_cAnd_9_14

theorem cAnd_9_15 : Interd (q9.and q15) q4 := hand_cAnd_9_15

theorem cAnd_10_14 : Interd (q10.and q14) q5 := hand_cAnd_10_14

theorem cAnd_10_15 : Interd (q10.and q15) q15 := hand_cAnd_10_15

theorem cAnd_11_14 : Interd (q11.and q14) q9 := hand_cAnd_11_14

theorem cAnd_11_15 : Interd (q11.and q15) q15 := hand_cAnd_11_15

theorem cAnd_12_13 : Interd (q12.and q13) q12 := hand_cAnd_12_13

theorem cAnd_12_14 : Interd (q12.and q14) q12 := hand_cAnd_12_14

theorem cAnd_12_15 : Interd (q12.and q15) q4 := hand_cAnd_12_15

theorem cAnd_13_15 : Interd (q13.and q15) q15 := hand_cAnd_13_15

theorem cAnd_14_15 : Interd (q14.and q15) q4 := hand_cAnd_14_15

theorem cOr_2_13 : Interd (q2.or q13) q13 := hand_cOr_2_13

theorem cOr_2_14 : Interd (q2.or q14) q14 := hand_cOr_2_14

theorem cOr_2_15 : Interd (q2.or q15) q15 := hand_cOr_2_15

theorem cOr_3_13 : Interd (q3.or q13) q13 := hand_cOr_3_13

theorem cOr_3_14 : Interd (q3.or q14) q14 := hand_cOr_3_14

theorem cOr_3_15 : Interd (q3.or q15) q15 := hand_cOr_3_15

theorem cOr_4_14 : Interd (q4.or q14) q14 := hand_cOr_4_14

theorem cOr_4_15 : Interd (q4.or q15) q15 := hand_cOr_4_15

theorem cOr_5_14 : Interd (q5.or q14) q14 := hand_cOr_5_14

theorem cOr_6_13 : Interd (q6.or q13) q13 := hand_cOr_6_13

theorem cOr_6_14 : Interd (q6.or q14) q14 := hand_cOr_6_14

theorem cOr_7_13 : Interd (q7.or q13) q13 := hand_cOr_7_13

theorem cOr_7_14 : Interd (q7.or q14) q14 := hand_cOr_7_14

theorem cOr_8_13 : Interd (q8.or q13) q13 := hand_cOr_8_13

theorem cOr_8_15 : Interd (q8.or q15) q8 := hand_cOr_8_15

theorem cOr_9_13 : Interd (q9.or q13) q13 := hand_cOr_9_13

theorem cOr_9_14 : Interd (q9.or q14) q14 := hand_cOr_9_14

theorem cOr_10_15 : Interd (q10.or q15) q10 :=
  ⟨(ofG4 (.impR (.orL (A := q10) (B := q15) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q2) (.head _) (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (A := q0) (.head _) (.botL (.head _)))) (.impLOr (A := q5) (B := q6) (D := q4) (.head _) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))),
   (ofG4 (.orR1 (.impR (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _)))))))⟩

theorem cOr_11_15 : Interd (q11.or q15) q11 := hand_cOr_11_15

theorem cOr_12_13 : Interd (q12.or q13) q13 := hand_cOr_12_13

theorem cOr_12_14 : Interd (q12.or q14) q14 := hand_cOr_12_14

theorem cOr_13_15 : Interd (q13.or q15) q13 := hand_cOr_13_15

theorem cImp_2_15 : Interd (q2.ifThen q15) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.orR1 (.laxL (A := q0) (.tail _ (.head _)) (.botL (.head _)))))))⟩

theorem cImp_3_15 : Interd (q3.ifThen q15) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.orR2 (.impR (.orL (A := q5) (B := q6) (.tail _ (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.laxL (A := q0) (.tail _ (.tail _ (.head _))) (.botL (.head _))) (.botL (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))))))))⟩

theorem cImp_4_15 : Interd (q4.ifThen q15) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.orL (A := q5) (B := q6) (.head _) (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.orL (A := q2) (B := q3) (.tail _ (.tail _ (.head _))) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cImp_5_15 : Interd (q5.ifThen q15) q8 := hand_cImp_5_15

theorem cImp_6_15 : Interd (q6.ifThen q15) q10 :=
  ⟨(ofG4 (.impR (.impLImp (A := q3) (B := q0) (D := q15) (.tail _ (.head _)) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.impLOr (A := q5) (B := q6) (D := q4) (.head _) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))),
   (ofG4 (.impR (.impR (.orR1 (.impLImp (A := q3) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))) (.laxL (A := q0) (.head _) (.botL (.head _))))))))⟩

theorem cImp_7_15 : Interd (q7.ifThen q15) q10 := hand_cImp_7_15

theorem cImp_8_10 : Interd (q8.ifThen q10) q10 := hand_cImp_8_10

theorem cImp_8_15 : Interd (q8.ifThen q15) q10 := hand_cImp_8_15

theorem cImp_9_8 : Interd (q9.ifThen q8) q8 := hand_cImp_9_8

theorem cImp_9_15 : Interd (q9.ifThen q15) q15 := hand_cImp_9_15

theorem cImp_10_8 : Interd (q10.ifThen q8) q8 := hand_cImp_10_8

theorem cImp_10_9 : Interd (q10.ifThen q9) q14 := hand_cImp_10_9

theorem cImp_10_12 : Interd (q10.ifThen q12) q14 := hand_cImp_10_12

theorem cImp_10_14 : Interd (q10.ifThen q14) q14 := hand_cImp_10_14

theorem cImp_10_15 : Interd (q10.ifThen q15) q8 := hand_cImp_10_15

theorem cImp_11_4 : Interd (q11.ifThen q4) q4 := hand_cImp_11_4

theorem cImp_11_8 : Interd (q11.ifThen q8) q8 := hand_cImp_11_8

theorem cImp_11_9 : Interd (q11.ifThen q9) q14 := hand_cImp_11_9

theorem cImp_11_12 : Interd (q11.ifThen q12) q14 := hand_cImp_11_12

theorem cImp_11_14 : Interd (q11.ifThen q14) q14 := hand_cImp_11_14

theorem cImp_11_15 : Interd (q11.ifThen q15) q15 := hand_cImp_11_15

theorem cImp_12_4 : Interd (q12.ifThen q4) q15 := hand_cImp_12_4

theorem cImp_12_8 : Interd (q12.ifThen q8) q8 := hand_cImp_12_8

theorem cImp_12_15 : Interd (q12.ifThen q15) q15 := hand_cImp_12_15

theorem cImp_13_8 : Interd (q13.ifThen q8) q8 := hand_cImp_13_8

theorem cImp_13_15 : Interd (q13.ifThen q15) q15 := hand_cImp_13_15

theorem cImp_14_4 : Interd (q14.ifThen q4) q15 := coll_w2_w4.symm

theorem cImp_14_5 : Interd (q14.ifThen q5) q10 := hand_cImp_14_5

theorem cImp_14_8 : Interd (q14.ifThen q8) q8 := hand_cImp_14_8

theorem cImp_14_15 : Interd (q14.ifThen q15) q15 := hand_cImp_14_15

theorem cImp_15_0 : Interd (q15.ifThen q0) q0 :=
  ⟨(ofG4 (.impLImp (A := q9) (B := q4) (D := q0) (.head _) (.impR (.orR1 (.laxR (.orL (A := q5) (B := q6) (.head _) (.impLOr (A := q2) (B := q3) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLOr (A := q2) (B := q3) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))))) (.botL (.head _)))),
   (ofG4 (.botL (.head _)))⟩

theorem cImp_15_2 : Interd (q15.ifThen q2) q6 :=
  ⟨(ofG4 (.impR (.impLImp (A := q9) (B := q4) (D := q2) (.tail _ (.head _)) (.impR (.orR1 (.laxR (.orL (A := q5) (B := q6) (.head _) (.impLOr (A := q2) (B := q3) (D := q2) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q2) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q2) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLOr (A := q2) (B := q3) (D := q2) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))),
   (ofG4 (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.head _) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))⟩

theorem cImp_15_3 : Interd (q15.ifThen q3) q3 :=
  ⟨(ofG4 (.impR (.impLImp (A := q9) (B := q4) (D := q3) (.tail _ (.head _)) (.impR (.orR1 (.laxR (.orL (A := q5) (B := q6) (.head _) (.impLOr (A := q2) (B := q3) (D := q3) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q3) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (A := q0) (B := q0) (X := q3) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.laxL (A := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.botL (.head _))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLOr (A := q2) (B := q3) (D := q3) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impLLaxLax (A := q0) (B := q3) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _)))))) (.botL (.head _))))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))),
   (ofG4 (.impR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLax (A := q3) (B := q4) (.head _) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.head _) (.tail _ (.tail _ (.head _))) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.tail _ (.tail _ (.tail _ (.head _)))) (.botL (.head _)) (.botL (.head _))))))))⟩

theorem cImp_15_6 : Interd (q15.ifThen q6) q6 :=
  ⟨(ofG4 (.impR (.impLImp (A := q9) (B := q4) (D := q6) (.tail _ (.head _)) (.impR (.orR1 (.laxR (.orL (A := q5) (B := q6) (.head _) (.impLOr (A := q2) (B := q3) (D := q6) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q6) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.impLImp (A := q2) (B := q0) (D := q6) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLOr (A := q2) (B := q3) (D := q6) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.botL (.head _)))) (.botL (.head _))))))) (.impLImp (A := q2) (B := q0) (D := q0) (.head _) (.impR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.head _))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))),
   (ofG4 (.impR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLax (A := q3) (B := q4) (.head _) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _))))) (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))⟩

theorem cImp_15_8 : Interd (q15.ifThen q8) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))))))))⟩

theorem cImp_15_10 : Interd (q15.ifThen q10) q1 :=
  ⟨topD,
   (ofG4 (.impR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))⟩

theorem cImp_15_11 : Interd (q15.ifThen q11) q1 :=
  ⟨topD,
   (ofG4 (.impR (.orR2 (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLImp (A := q3) (B := q0) (D := q4) (.tail _ (.head _)) (.impR (.impLLax (A := q3) (B := q4) (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.laxL (A := q0) (.head _) (.botL (.head _))) (.laxR (.impLImp (A := q2) (B := q0) (D := q0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))))))⟩

theorem cImp_15_13 : Interd (q15.ifThen q13) q1 :=
  ⟨topD,
   (ofG4 (.impR (.laxR (.impR (.impLOr (A := q5) (B := q6) (D := q4) (.tail _ (.head _)) (.impLLaxLax (A := q3) (B := q4) (X := q3) (.head _) (.tail _ (.tail _ (.head _))) (.laxR (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.orL (A := q2) (B := q3) (.head _) (.orR1 (.laxL (A := q0) (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (A := q0) (B := q0) (X := q0) (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))))))))))⟩

theorem cBox_14 : Interd q14.somehow q14 := hand_cBox_14

end RND2

/-! ## Closure layer DELETED (2026-08-25, Matthew's directive)

The total closure theorems and the aggregate dictionary structure
asserted that the representative table CLOSES; that claim is REFUTED
(kernel countermodels, e.g. `cBox_11_no_candidate`), so the layer
could not stand without `sorryAx` and is gone, together with every
sorried per-cell statement.  The proved per-cell theorems above are
untouched.  The reference set is the ρ-catalogue R (open-ended; 22
classes at deletion date).  History: git. -/

end SemUI
end PLLND
