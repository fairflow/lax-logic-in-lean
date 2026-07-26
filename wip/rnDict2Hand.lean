import wip.rnSepColl

/-!
# Hand-lemma layer for the enlarged dictionary round

Hand-authored `Deriv` lemmas discharging cells of the 16-class closure
round that the searcher misses (2026-07-26).  Two devices:

* `ofImpTop`: every certified `Interd (A ⊃ B) ⊤` cell of
  `wip/rnDict.lean` is an ORDER FACT `[A] ⊢ B` — this unlocks it;
* the inside-◯ case-analysis LEGO of `wip/rnSepColl.lean` (derive a
  ◯-formula from `◯q7`/`◯q3`-type hypotheses by `orElim` under
  `dSomehowElim`, closing refuted branches with `falsoElim`).
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND

/-- A certified `(A ⊃ B) ≡ ⊤` cell is the order fact `[A] ⊢ B`. -/
theorem ofImpTop {A B : PLLFormula} (h : Interd (A.ifThen B) truePLL) :
    Deriv [A] B :=
  Deriv.impElim (Deriv.cutHead topD h.2) (Deriv.iden (.head _))

/-- `[q3] ⊢ q8`: with `q3` at hand, `q4` holds by its right disjunct. -/
theorem d_q3_q8 : Deriv [q3] q8 :=
  Deriv.impIntro (Deriv.orIntro2 (Deriv.iden (.tail _ (.head _))))

/-- `[q6] ⊢ q8`: from `q5 = ◯q3` and `q6 = ¬q3`, collapse to `◯⊥`. -/
theorem d_q6_q8 : Deriv [q6] q8 := by
  refine Deriv.impIntro (Deriv.orIntro1 ?_)
  refine dSomehowElim (Deriv.iden (.head _)) ?_
  exact Deriv.falsoElim _
    (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
      (Deriv.iden (.head _)))

/-- `[q9] ⊢ q13 = ◯q8`: case analysis on `q9 = q5 ∨ q6`. -/
theorem d_q9_q13 : Deriv [q9] q13 := by
  refine Deriv.orElim (Deriv.iden (.head _)) ?c5 ?c6
  · -- q5 = ◯q3: derive q8 inside the modality
    exact dSomehowElim (Deriv.iden (.head _))
      (dSomehowIntro (d_q3_q8.toHead))
  · -- q6: q8 outright, then ◯-intro
    exact dSomehowIntro (d_q6_q8.toHead)

/-- From `◯⊥` anywhere, any ◯-formula: ex falso inside the modality. -/
theorem box_of_bb {Γ : List PLLFormula} (h : Deriv Γ q2)
    (X : PLLFormula) : Deriv Γ X.somehow :=
  dSomehowElim h (Deriv.falsoElim _ (Deriv.iden (.head _)))

/-- `[q4] ⊢ q9`: `q2`-branch by ex falso inside ◯, `q3`-branch by
◯-introduction (`q5 = ◯q3`). -/
theorem d_q4_q9 : Deriv [q4] q9 := by
  refine Deriv.orElim (Deriv.iden (.head _)) ?c2 ?c3
  · exact Deriv.orIntro1 (box_of_bb (Deriv.iden (.head _)) q3)
  · exact Deriv.orIntro1 (dSomehowIntro (Deriv.iden (.head _)))

/-- `[q4] ⊢ q14 = q10 ⊃ q5`: the hypothesis `q10` is not even
needed. -/
theorem d_q4_q14 : Deriv [q4] q14 := by
  refine Deriv.impIntro ?_
  refine Deriv.orElim (Deriv.iden (.tail _ (.head _))) ?c2 ?c3
  · exact box_of_bb (Deriv.iden (.head _)) q3
  · exact dSomehowIntro (Deriv.iden (.head _))

/-! ## Per-cell certificates (wired into the generator's `overrides`) -/

theorem hand_cAnd_9_13 : Interd (q9.and q13) q9 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) d_q9_q13⟩

theorem hand_cAnd_9_14 : Interd (q9.and q14) q9 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) (ofImpTop cImp_9_14)⟩

theorem hand_cAnd_11_14 : Interd (q11.and q14) q9 := by
  constructor
  · -- q11 = q6 ∨ q10 with q14 = q10 ⊃ q5 at hand
    refine Deriv.orElim (Deriv.andElim1 (Deriv.iden (.head _))) ?c6 ?c10
    · exact Deriv.orIntro2 (Deriv.iden (.head _))
    · exact Deriv.orIntro1
        (Deriv.impElim
          (Deriv.andElim2 (Deriv.iden (.tail _ (.head _))))
          (Deriv.iden (.head _)))
  · exact Deriv.andIntro (ofImpTop cImp_9_11) (ofImpTop cImp_9_14)

theorem hand_cAnd_12_14 : Interd (q12.and q14) q12 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) (ofImpTop cImp_12_14)⟩

theorem hand_cAnd_4_14 : Interd (q4.and q14) q4 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) d_q4_q14⟩

theorem hand_cAnd_8_10 : Interd (q8.and q10) w2 := coll_w1_w2

theorem hand_cAnd_8_15 : Interd (q8.and w2) w2 :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.andElim1 d_w2_w1) (Deriv.iden (.head _))⟩

theorem hand_cAnd_9_15 : Interd (q9.and w2) q4 :=
  ⟨Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _)))
     (Deriv.andElim1 (Deriv.iden (.head _))),
   Deriv.andIntro d_q4_q9
     (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))⟩

theorem hand_cAnd_10_15 : Interd (q10.and w2) w2 :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.andElim2 d_w2_w1) (Deriv.iden (.head _))⟩

theorem hand_cAnd_11_15 : Interd (q11.and w2) w2 :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.orIntro2 (Deriv.andElim2 d_w2_w1))
     (Deriv.iden (.head _))⟩

theorem hand_cAnd_13_15 : Interd (q13.and w2) w2 :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (dSomehowIntro (Deriv.andElim1 d_w2_w1))
     (Deriv.iden (.head _))⟩

theorem hand_cOr_2_13 : Interd (q2.or q13) q13 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (box_of_bb (Deriv.iden (.head _)) q8)
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_2_15 : Interd (q2.or w2) w2 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro (Deriv.orIntro1 (Deriv.iden (.tail _ (.head _)))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_3_14 : Interd (q3.or q14) q14 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro (dSomehowIntro (Deriv.iden (.tail _ (.head _)))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_4_15 : Interd (q4.or w2) w2 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_5_14 : Interd (q5.or q14) q14 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_6_13 : Interd (q6.or q13) q13 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (dSomehowIntro d_q6_q8.toHead)
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

end RND
end SemUI
end PLLND
