import LaxLogic.PLLG4Gap

/-!
# G4iLL′: the repaired terminating-style calculus for PLL

`PLLG4Gap.lean` shows Iemhoff's G4iLL is incomplete: the sequent
`◯((◯p→r)→◯p), ◯p→r ⇒ r` needs the implication `◯p→r` **twice, on the
two sides of a box-opening**, and `L◯→` reuses the box but consumes the
implication.  This file defines the repair `G4p`, a **one-premise-token
change** to Iemhoff's Fig. 8.3: the first premise of `L◯→` *keeps* the
principal implication —

    Γ, ◯φ→ψ, χ ⇒ ◯φ      Γ, ◯χ, ψ ⇒ Δ
    ------------------------------------ L◯→′
           Γ, ◯χ, ◯φ→ψ ⇒ Δ

(cf. the `→SL` rule of van der Giessen–Iemhoff's G4iSL, whose first
premise also retains its principal).  Howe's reading (MSCS 2001, §5)
is vindicated rather than contradicted: the duplication he proved
unavoidable is now *built into the rule* — each `L◯→′` application
duplicates the implication into its boxed premise — while sequents stay
standard (no histories).  All other rules, including `R◯→`, are
unchanged from `PLLG4.lean`.

`G4p` is **not** Dershowitz–Manna terminating (the first premise trades
the succedent for `◯φ`); termination and the decision procedure are a
later, separate concern.  What this file and its successors establish
is the *proof theory*, by pure structural inductions — the plan:

1. this file: exchange, weakening, `G4 ⊆ G4p`, soundness into `SC`,
   and the gap sequent now derivable;
2. inversions (port of `PLLG4Inv.lean`);
3. generalised identity (port of `PLLG4Adm.lean`);
4. `weak_ImpLax`, the **self-absorbing** `weak_ImpLax_self` (the lemma
   whose failure for G4iLL was the root of the incompleteness — the
   kept implication is exactly what its `laxL` case needs), and the
   `◯`-strengthening `open_box`;
5. contraction, cut;
6. completeness `SC Γ C → G4p Γ C` — closing F&M Theorem 2.8's
   proof-theoretic half with a *correct* calculus.
-/

open PLLFormula

namespace PLLND

/-- **G4iLL′**: Iemhoff's G4iLL with the repaired `L◯→′`
(`impLLaxLax`, whose first premise keeps the principal implication).
All other rules as in `G4`. -/
inductive G4p : List PLLFormula → PLLFormula → Prop
  | init {Γ : List PLLFormula} {a : String}
      (h : prop a ∈ Γ) : G4p Γ (prop a)
  | botL {Γ : List PLLFormula} {C : PLLFormula}
      (h : falsePLL ∈ Γ) : G4p Γ C
  | andR {Γ : List PLLFormula} {A B : PLLFormula} :
      G4p Γ A → G4p Γ B → G4p Γ (A.and B)
  | orR1 {Γ : List PLLFormula} {A B : PLLFormula} :
      G4p Γ A → G4p Γ (A.or B)
  | orR2 {Γ : List PLLFormula} {A B : PLLFormula} :
      G4p Γ B → G4p Γ (A.or B)
  | impR {Γ : List PLLFormula} {A B : PLLFormula} :
      G4p (A :: Γ) B → G4p Γ (A.ifThen B)
  | laxR {Γ : List PLLFormula} {A : PLLFormula} :
      G4p Γ A → G4p Γ A.somehow
  | andL {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.and B :: Δ)) :
      G4p (A :: B :: Δ) C → G4p Γ C
  | orL {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.or B :: Δ)) :
      G4p (A :: Δ) C → G4p (B :: Δ) C → G4p Γ C
  | laxL {Γ Δ : List PLLFormula} {A B : PLLFormula}
      (h : Γ.Perm (A.somehow :: Δ)) :
      G4p (A :: Δ) B.somehow → G4p Γ B.somehow
  | impLProp {Γ Δ : List PLLFormula} {a : String} {B C : PLLFormula}
      (h : Γ.Perm ((prop a).ifThen B :: Δ)) (ha : prop a ∈ Δ) :
      G4p (B :: Δ) C → G4p Γ C
  | impLBot {Γ Δ : List PLLFormula} {B C : PLLFormula}
      (h : Γ.Perm (falsePLL.ifThen B :: Δ)) :
      G4p Δ C → G4p Γ C
  | impLAnd {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.and B).ifThen D :: Δ)) :
      G4p (A.ifThen (B.ifThen D) :: Δ) E → G4p Γ E
  | impLOr {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.or B).ifThen D :: Δ)) :
      G4p (A.ifThen D :: B.ifThen D :: Δ) E → G4p Γ E
  | impLImp {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) :
      G4p (B.ifThen D :: Δ) (A.ifThen B) → G4p (D :: Δ) E → G4p Γ E
  | impLLax {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: Δ)) :
      G4p Δ A → G4p (B :: Δ) C → G4p Γ C
  | impLLaxLax {Γ Δ : List PLLFormula} {A B X C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: X.somehow :: Δ)) :
      G4p (A.somehow.ifThen B :: X :: Δ) A.somehow →
      G4p (B :: X.somehow :: Δ) C → G4p Γ C

namespace G4p

/-! ### Structural admissibility -/

/-- Exchange: identical to `G4.perm`. -/
theorem perm : ∀ {Γ : List PLLFormula} {C : PLLFormula}, G4p Γ C →
    ∀ {Γ' : List PLLFormula}, Γ.Perm Γ' → G4p Γ' C := by
  intro Γ C d
  induction d with
  | init h => intro Γ' hp; exact .init (hp.subset h)
  | botL h => intro Γ' hp; exact .botL (hp.subset h)
  | andR _ _ ih₁ ih₂ => intro Γ' hp; exact .andR (ih₁ hp) (ih₂ hp)
  | orR1 _ ih => intro Γ' hp; exact .orR1 (ih hp)
  | orR2 _ ih => intro Γ' hp; exact .orR2 (ih hp)
  | impR _ ih => intro Γ' hp; exact .impR (ih (hp.cons _))
  | laxR _ ih => intro Γ' hp; exact .laxR (ih hp)
  | andL h d _ => intro Γ' hp; exact .andL (hp.symm.trans h) d
  | orL h d₁ d₂ _ _ => intro Γ' hp; exact .orL (hp.symm.trans h) d₁ d₂
  | laxL h d _ => intro Γ' hp; exact .laxL (hp.symm.trans h) d
  | impLProp h ha d _ => intro Γ' hp; exact .impLProp (hp.symm.trans h) ha d
  | impLBot h d _ => intro Γ' hp; exact .impLBot (hp.symm.trans h) d
  | impLAnd h d _ => intro Γ' hp; exact .impLAnd (hp.symm.trans h) d
  | impLOr h d _ => intro Γ' hp; exact .impLOr (hp.symm.trans h) d
  | impLImp h d₁ d₂ _ _ => intro Γ' hp; exact .impLImp (hp.symm.trans h) d₁ d₂
  | impLLax h d₁ d₂ _ _ => intro Γ' hp; exact .impLLax (hp.symm.trans h) d₁ d₂
  | impLLaxLax h d₁ d₂ _ _ =>
      intro Γ' hp; exact .impLLaxLax (hp.symm.trans h) d₁ d₂

/-- Weakening by one formula.  As for `G4`, with the one new wrinkle
that `impLLaxLax`'s first premise also absorbs `ψ` one position deeper
*past the kept implication*. -/
theorem weaken (ψ : PLLFormula) : ∀ {Γ : List PLLFormula} {C : PLLFormula},
    G4p Γ C → G4p (ψ :: Γ) C := by
  have rot : ∀ (x : PLLFormula) (l : List PLLFormula),
      (ψ :: x :: l).Perm (x :: ψ :: l) := fun x l => List.Perm.swap x ψ l
  intro Γ C d
  induction d with
  | init h => exact .init (.tail _ h)
  | botL h => exact .botL (.tail _ h)
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | impR _ ih => exact .impR (ih.perm (rot _ _))
  | laxR _ ih => exact .laxR ih
  | @andL _ Δ A B _ h _ ih =>
      exact .andL ((h.cons ψ).trans (rot _ _))
        (ih.perm ((rot A (B :: Δ)).trans ((rot B Δ).cons A)))
  | @orL _ Δ A B _ h _ _ ih₁ ih₂ =>
      exact .orL ((h.cons ψ).trans (rot _ _))
        (ih₁.perm (rot A Δ)) (ih₂.perm (rot B Δ))
  | @laxL _ Δ A _ h _ ih =>
      exact .laxL ((h.cons ψ).trans (rot _ _)) (ih.perm (rot A Δ))
  | @impLProp _ Δ a B _ h ha _ ih =>
      exact .impLProp ((h.cons ψ).trans (rot _ _)) (.tail _ ha)
        (ih.perm (rot B Δ))
  | impLBot h _ ih =>
      exact .impLBot ((h.cons ψ).trans (rot _ _)) ih
  | @impLAnd _ Δ A B D _ h _ ih =>
      exact .impLAnd ((h.cons ψ).trans (rot _ _))
        (ih.perm (rot (A.ifThen (B.ifThen D)) Δ))
  | @impLOr _ Δ A B D _ h _ ih =>
      exact .impLOr ((h.cons ψ).trans (rot _ _))
        (ih.perm ((rot (A.ifThen D) _).trans ((rot (B.ifThen D) Δ).cons _)))
  | @impLImp _ Δ A B D _ h _ _ ih₁ ih₂ =>
      exact .impLImp ((h.cons ψ).trans (rot _ _))
        (ih₁.perm (rot (B.ifThen D) Δ)) (ih₂.perm (rot D Δ))
  | @impLLax _ Δ A B _ h _ _ ih₁ ih₂ =>
      exact .impLLax ((h.cons ψ).trans (rot _ _)) ih₁ (ih₂.perm (rot B Δ))
  | @impLLaxLax _ Δ A B X _ h _ _ ih₁ ih₂ =>
      exact .impLLaxLax
        ((h.cons ψ).trans ((rot _ _).trans ((rot X.somehow Δ).cons _)))
        (ih₁.perm ((rot _ _).trans ((rot X Δ).cons _)))
        (ih₂.perm ((rot B _).trans ((rot X.somehow Δ).cons B)))

/-- Every G4iLL derivation is a G4iLL′ derivation: the repaired rule's
first premise is the old one weakened by the implication. -/
theorem ofG4 : ∀ {Γ : List PLLFormula} {C : PLLFormula}, G4 Γ C → G4p Γ C := by
  intro Γ C d
  induction d with
  | init h => exact .init h
  | botL h => exact .botL h
  | andR _ _ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orR1 _ ih => exact .orR1 ih
  | orR2 _ ih => exact .orR2 ih
  | impR _ ih => exact .impR ih
  | laxR _ ih => exact .laxR ih
  | andL h _ ih => exact .andL h ih
  | orL h _ _ ih₁ ih₂ => exact .orL h ih₁ ih₂
  | laxL h _ ih => exact .laxL h ih
  | impLProp h ha _ ih => exact .impLProp h ha ih
  | impLBot h _ ih => exact .impLBot h ih
  | impLAnd h _ ih => exact .impLAnd h ih
  | impLOr h _ ih => exact .impLOr h ih
  | impLImp h _ _ ih₁ ih₂ => exact .impLImp h ih₁ ih₂
  | impLLax h _ _ ih₁ ih₂ => exact .impLLax h ih₁ ih₂
  | impLLaxLax h _ _ ih₁ ih₂ =>
      exact .impLLaxLax h (ih₁.weaken _) ih₂

/-! ### Soundness into the cut-free G3 calculus -/

private theorem sub_cons {Δ Γ : List PLLFormula}
    (hsub : ∀ ψ ∈ Δ, ψ ∈ Γ) (A : PLLFormula) :
    ∀ ψ ∈ A :: Δ, ψ ∈ A :: Γ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact .head _
  · exact .tail _ (hsub _ hψ)

/-- **Soundness of G4iLL′** into `SC`: as for `G4.toSC`; in the
`impLLaxLax` case the first premise's extra implication lands on the
matching context formula. -/
theorem toSC : ∀ {Γ : List PLLFormula} {C : PLLFormula}, G4p Γ C → SC Γ C := by
  intro Γ C d
  induction d with
  | init h => exact SC.init h
  | botL h => exact SC.botL h
  | andR _ _ ih₁ ih₂ => exact SC.andR ih₁ ih₂
  | orR1 _ ih => exact SC.orR1 ih
  | orR2 _ ih => exact SC.orR2 ih
  | impR _ ih => exact SC.impR ih
  | laxR _ ih => exact SC.laxR ih
  | @andL Γ' Δ' A B _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.andL (h.symm.subset (.head _))
        (ih.rename (sub_cons (sub_cons hΔ B) A))
  | @orL Γ' Δ' A B _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.orL (h.symm.subset (.head _))
        (ih₁.rename (sub_cons hΔ A)) (ih₂.rename (sub_cons hΔ B))
  | @laxL Γ' Δ' A _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.laxL (h.symm.subset (.head _)) (ih.rename (sub_cons hΔ A))
  | @impLProp Γ' Δ' a B _ h ha _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.impL (h.symm.subset (.head _)) (SC.init (hΔ _ ha))
        (ih.rename (sub_cons hΔ B))
  | impLBot h _ ih =>
      exact ih.rename fun ψ hψ => h.symm.subset (.tail _ hψ)
  | @impLAnd Γ' Δ' A B D _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      have hmem := h.symm.subset (List.Mem.head _)
      have p : SC Γ' (A.ifThen (B.ifThen D)) := by
        refine SC.impR (SC.impR ?_)
        exact SC.impL (A := A.and B) (.tail _ (.tail _ hmem))
          (SC.andR (SC.iden _ (.tail _ (.head _))) (SC.iden _ (.head _)))
          (SC.iden _ (.head _))
      exact SC.cut p (ih.rename (sub_cons hΔ _))
  | @impLOr Γ' Δ' A B D _ h _ ih =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      have hmem := h.symm.subset (List.Mem.head _)
      have p₁ : SC Γ' (A.ifThen D) :=
        SC.impR (SC.impL (A := A.or B) (.tail _ hmem)
          (SC.orR1 (SC.iden _ (.head _))) (SC.iden _ (.head _)))
      have p₂ : SC Γ' (B.ifThen D) :=
        SC.impR (SC.impL (A := A.or B) (.tail _ hmem)
          (SC.orR2 (SC.iden _ (.head _))) (SC.iden _ (.head _)))
      refine SC.cut p₁ (SC.cut (p₂.rename fun ψ hψ => .tail _ hψ)
        (ih.rename ?_))
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact .tail _ (.head _)
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact .head _
      · exact .tail _ (.tail _ (hΔ _ hψ))
  | @impLImp Γ' Δ' A B D _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      have hmem := h.symm.subset (List.Mem.head _)
      have hBD : SC Γ' (B.ifThen D) :=
        SC.impR (SC.impL (A := A.ifThen B) (.tail _ hmem)
          (SC.impR (SC.iden _ (.tail _ (.head _)))) (SC.iden _ (.head _)))
      have hAB : SC Γ' (A.ifThen B) := SC.cut hBD (ih₁.rename (sub_cons hΔ _))
      exact SC.impL hmem hAB (ih₂.rename (sub_cons hΔ D))
  | @impLLax Γ' Δ' A B _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' := fun ψ hψ => h.symm.subset (.tail _ hψ)
      exact SC.impL (h.symm.subset (.head _)) (SC.laxR (ih₁.rename hΔ))
        (ih₂.rename (sub_cons hΔ B))
  | @impLLaxLax Γ' Δ' A B X _ h _ _ ih₁ ih₂ =>
      have hΔ : ∀ ψ ∈ Δ', ψ ∈ Γ' :=
        fun ψ hψ => h.symm.subset (.tail _ (.tail _ hψ))
      have hX : X.somehow ∈ Γ' := h.symm.subset (.tail _ (.head _))
      have hF : A.somehow.ifThen B ∈ Γ' := h.symm.subset (.head _)
      -- `◯A` from `◯X` by `laxL`; the opened premise may use the
      -- implication, which is present in `Γ'`
      have hOA : SC Γ' A.somehow := by
        refine SC.laxL hX (ih₁.rename ?_)
        intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact .tail _ hF
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact .head _
        · exact .tail _ (hΔ _ hψ)
      refine SC.impL hF hOA (ih₂.rename ?_)
      refine sub_cons (fun ψ hψ => ?_) B
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hX
      · exact hΔ _ hψ

end G4p

/-! ### Smoke tests -/

/-- The G4iLL gap sequent `◯((◯p→r)→◯p), ◯p→r ⇒ r` is `G4p`-derivable:
`L◯→′` duplicates the implication into the box-opening. -/
theorem G4p.gap_derivable : G4p [PLLG4Gap.Ga.somehow, PLLG4Gap.Fa] (prop "r") :=
  .impLLaxLax (List.Perm.swap _ _ _)
    (-- F′, G′ ⊢ ◯p, with the implication retained
      .impLImp (List.Perm.swap _ _ _)
        (-- r→◯p, F′ ⊢ F′ : the retained copy fires inside
          .impR
            (.impLLaxLax
              (List.perm_middle (l₁ := [(prop "p").somehow,
                (prop "r").ifThen (prop "p").somehow]))
              (.laxR (.init (.tail _ (.head _))))
              (.init (.head _))))
        (-- ◯p, F′ ⊢ ◯p
          .laxL (List.Perm.refl _) (.laxR (.init (.head _)))))
    (-- r, ◯G′, ⊢ r
      .init (.head _))

-- Old G4 derivations transfer wholesale:
example : G4p [] ((prop "A").ifThen (prop "A").somehow) :=
  G4p.ofG4 (.impR (.laxR (.init (.head _))))

-- Howe's duplication sequent, through the embedding:
example :
    G4p [((prop "B").ifThen ((prop "A").somehow.ifThen (prop "C"))).ifThen
          (prop "A").somehow,
        (prop "A").somehow.ifThen (prop "C"),
        (prop "B").somehow] (prop "C") := by
  refine G4p.ofG4 ?_
  refine .impLImp (List.Perm.refl _) ?_ ?_
  · refine .impR (.impR ?_)
    refine .impLLaxLax
      (Δ := [prop "B",
             ((prop "A").somehow.ifThen (prop "C")).ifThen (prop "A").somehow,
             (prop "B").somehow])
      (X := prop "A")
      (by decide) (.laxR (.init (.head _))) (.init (.head _))
  · exact .impLLaxLax (Δ := [(prop "B").somehow]) (X := prop "A")
      (List.Perm.swap _ _ _) (.laxR (.init (.head _))) (.init (.head _))

end PLLND
