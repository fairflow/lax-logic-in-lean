import LaxLogic.PLLG4HCut
import LaxLogic.PLLTerms

/-!
# Completeness of G4iLL″, conditional on self-absorption

`SC → G4c` by plain structural induction on the height-indexed G3
derivation: the right rules and the two membership-keeping lax rules
transfer verbatim; `andL`/`orL` invert the surviving copy and contract
the strictly lighter pieces; `impL` is two cuts through the
in-context modus ponens.  Combined with `G4c.toSC` and the banked
equivalences `SC ↔ LaxND ↔ Tm`, the full chain

    G4c  =  SC  =  LaxND  =  Tm-inhabitation   (modulo `SelfAbsorb`)

pins F&M Theorem 2.8's proof-theoretic half on that one lemma.
-/

open PLLFormula

namespace PLLND

namespace G4c

private theorem push2 {x q : PLLFormula} {Γ : List PLLFormula} :
    (x :: q :: q :: Γ).Perm (q :: q :: x :: Γ) :=
  (List.Perm.swap q x _).trans ((List.Perm.swap q x Γ).cons q)

/-- **Completeness, conditional on self-absorption.** -/
theorem completeness_of_selfAbsorb (hS : SelfAbsorb) :
    ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    SCh n Γ C → G4c Γ C := by
  intro n Γ C d
  induction d with
  | init h => exact init h
  | botL h => exact botL h
  | andR _ _ ih₁ ih₂ => exact andR ih₁ ih₂
  | @andL _ Γ₀ A B _ h _ ih =>
      have hΓ := List.perm_cons_erase h
      have q : G4c (A :: B :: A :: B :: Γ₀.erase (A.and B)) _ :=
        ih.inv (.and A B)
          (((hΓ.cons B).cons A).trans (List.perm_middle (l₁ := [A, B])))
      have c₁ := contract q ((List.Perm.swap _ _ _).cons A)
      have c₂ := contract c₁ push2
      exact andL hΓ (c₂.perm (List.Perm.swap _ _ _))
  | orR1 _ ih => exact orR1 ih
  | orR2 _ ih => exact orR2 ih
  | @orL _ Γ₀ A B _ h _ _ ih₁ ih₂ =>
      have hΓ := List.perm_cons_erase h
      exact orL hΓ
        (contract (ih₁.inv (.or₁ A B)
          ((hΓ.cons A).trans (List.Perm.swap _ _ _))) (List.Perm.refl _))
        (contract (ih₂.inv (.or₂ A B)
          ((hΓ.cons B).trans (List.Perm.swap _ _ _))) (List.Perm.refl _))
  | impR _ ih => exact impR ih
  | @impL _ Γ₀ A B _ h _ _ ih₁ ih₂ =>
      have hΓ := List.perm_cons_erase h
      have q : G4c (A :: Γ₀) B :=
        (mp A B (Γ₀.erase (A.ifThen B))).perm (hΓ.symm.cons A)
      exact cut' hS (cut' hS ih₁ q) ih₂
  | laxR _ ih => exact laxR ih
  | laxL h _ ih => exact laxL h ih

/-- `G4c` and the cut-free G3 calculus agree, modulo `SelfAbsorb`. -/
theorem g4c_iff_sc (hS : SelfAbsorb) {Γ : List PLLFormula}
    {C : PLLFormula} : G4c Γ C ↔ SC Γ C := by
  constructor
  · rintro ⟨n, d⟩
    exact toSC d
  · rintro ⟨n, d⟩
    exact completeness_of_selfAbsorb hS d

/-- `G4c` captures natural-deduction provability, modulo `SelfAbsorb`. -/
theorem g4c_iff_nd (hS : SelfAbsorb) {Γ : List PLLFormula}
    {C : PLLFormula} : G4c Γ C ↔ Nonempty (LaxND Γ C) :=
  (g4c_iff_sc hS).trans cutElimination.symm

/-- **The full chain, modulo `SelfAbsorb`**: the repaired calculus
captures exactly the inhabited `Tm`-types — F&M Theorem 2.8's
proof-theoretic half, pinned on one lemma. -/
theorem g4c_iff_tm (hS : SelfAbsorb) {Γ : List PLLFormula}
    {φ : PLLFormula} : G4c Γ φ ↔ Nonempty (Tm Γ φ) :=
  (g4c_iff_nd hS).trans curry_howard.symm

end G4c

end PLLND
