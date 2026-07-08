import LaxLogic.PLLG4PAdm

/-!
# G4iLL′ chunk D: the weak lax-implication rule, and `◯`-spines

The engine of the contraction/cut ladder for `G4p`.  This file proves
**`weak_ImpLax`** (the lax analogue of Dyckhoff–Negri's Lemma 4.1):

    Γ ⇒ ◯D        Γ, B ⇒ E
    -------------------------
        Γ, ◯D→B ⇒ E

by structural induction on the *first* derivation, with the second as a
side hypothesis inverted along the way.  The two modal endings of the
first derivation map exactly onto the two lax implication rules — this
is the design rationale of Iemhoff's rule pair, and it survives the
repair: a `laxR` ending feeds `R◯→`, a `laxL` ending feeds `L◯→′`
(whose kept implication is obtained by weakening here).

The file also defines `◯`-**spines** (`Spine φ σ` iff `φ = ◯^k σ`) with
their `laxR`-lifts, the infrastructure for the *self-absorbing* variant
`weak_ImpLax_self` — the lemma whose G4iLL-failure caused the
incompleteness.  Design note for that next chunk: with the repaired
rule its `laxL`/`L◯→′` cases close by re-using the kept implication
verbatim, and the remaining hard case (a right rule at the spine's
non-`◯` bottom) reduces to a *smaller-weight cut* — so
`weak_ImpLax_self`, contraction and cut are proven together in a
weight-stratified induction, not freestanding.
-/

open PLLFormula

namespace PLLND

namespace G4p

/-- `Spine φ σ`: `φ = ◯^k σ` for some `k ≥ 0`. -/
inductive Spine : PLLFormula → PLLFormula → Prop
  | refl (φ : PLLFormula) : Spine φ φ
  | box {φ σ : PLLFormula} : Spine φ σ → Spine φ.somehow σ

/-- Climb a spine with `laxR`. -/
theorem Spine.lift {φ σ : PLLFormula} :
    Spine φ σ → ∀ {Γ : List PLLFormula}, G4p Γ σ → G4p Γ φ := by
  intro s
  induction s with
  | refl _ => exact fun d => d
  | box _ ih => exact fun d => .laxR (ih d)

/-- Descend one `◯` at the top of the target. -/
theorem Spine.unbox {φ σ : PLLFormula} :
    Spine φ σ.somehow → Spine φ σ := by
  intro s
  generalize hσ : σ.somehow = τ at s
  induction s with
  | refl φ => exact hσ ▸ .box (.refl σ)
  | box s ih => exact .box (ih hσ)

/-- **Weak lax-implication** (Dyckhoff–Negri Lemma 4.1, `◯`-antecedent
case): from `Γ ⇒ ◯D` and `Γ, B ⇒ E` conclude `Γ, ◯D→B ⇒ E`.  Induction
on the first derivation only. -/
theorem weak_ImpLax : ∀ {Γ : List PLLFormula} {G : PLLFormula}, G4p Γ G →
    ∀ {D : PLLFormula}, G = D.somehow →
    ∀ {B E : PLLFormula}, G4p (B :: Γ) E →
    G4p (D.somehow.ifThen B :: Γ) E := by
  intro Γ G d
  induction d with
  | init _ => intro D e; cases e
  | botL h => intro D e B E _; exact .botL (.tail _ h)
  | andR _ _ _ _ => intro D e; cases e
  | orR1 _ _ => intro D e; cases e
  | orR2 _ _ => intro D e; cases e
  | impR _ _ => intro D e; cases e
  | laxR d₁ _ =>
      intro D e B E side
      cases e
      -- rebuild with `R◯→`
      exact .impLLax (List.Perm.refl _) d₁ side
  | @laxL _ Δ A _ h d₁ _ =>
      intro D e B E side
      cases e
      -- rebuild with `L◯→′`; the kept implication arrives by weakening
      exact .impLLaxLax (h.cons _) (d₁.weaken _) (side.perm (h.cons B))
  | @andL _ Θ A' B' _ h d₁ ih =>
      intro D e B E side
      have side' : G4p (B :: A' :: B' :: Θ) E :=
        (side.andL_inv ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A', B']))
      exact .andL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih e side').perm (List.perm_middle (l₁ := [A', B'])).symm)
  | @orL _ Θ A' B' _ h d₁ d₂ ih₁ ih₂ =>
      intro D e B E side
      have side₁ : G4p (B :: A' :: Θ) E :=
        (side.orL_inv₁ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A']))
      have side₂ : G4p (B :: B' :: Θ) E :=
        (side.orL_inv₂ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B']))
      exact .orL ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih₁ e side₁).perm (List.perm_middle (l₁ := [A'])).symm)
        ((ih₂ e side₂).perm (List.perm_middle (l₁ := [B'])).symm)
  | @impLProp _ Θ a B' _ h ha d₁ ih =>
      intro D e B E side
      have side' : G4p (B :: B' :: Θ) E :=
        (side.impLProp_inv ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B']))
      exact .impLProp ((h.cons _).trans (List.Perm.swap _ _ Θ)) (.tail _ ha)
        ((ih e side').perm (List.perm_middle (l₁ := [B'])).symm)
  | @impLBot _ Θ B' _ h d₁ ih =>
      intro D e B E side
      have side' : G4p (B :: Θ) E :=
        side.impLBot_inv ((h.cons B).trans (List.Perm.swap _ B Θ))
      exact .impLBot ((h.cons _).trans (List.Perm.swap _ _ Θ)) (ih e side')
  | @impLAnd _ Θ A₁ B₁ D₁ _ h d₁ ih =>
      intro D e B E side
      have side' : G4p (B :: A₁.ifThen (B₁.ifThen D₁) :: Θ) E :=
        (side.inv (.impAnd A₁ B₁ D₁)
          ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A₁.ifThen (B₁.ifThen D₁)]))
      exact .impLAnd ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih e side').perm
          (List.perm_middle (l₁ := [A₁.ifThen (B₁.ifThen D₁)])).symm)
  | @impLOr _ Θ A₁ B₁ D₁ _ h d₁ ih =>
      intro D e B E side
      have side' : G4p (B :: A₁.ifThen D₁ :: B₁.ifThen D₁ :: Θ) E :=
        (side.inv (.impOr A₁ B₁ D₁)
          ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁]))
      exact .impLOr ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((ih e side').perm
          (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁])).symm)
  | @impLImp _ Θ A₁ B₁ D₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro D e B E side
      have side' : G4p (B :: D₁ :: Θ) E :=
        (side.impLImp_inv₂ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [D₁]))
      exact .impLImp ((h.cons _).trans (List.Perm.swap _ _ Θ))
        ((d₁.weaken _).perm (List.perm_middle (l₁ := [B₁.ifThen D₁])).symm)
        ((ih₂ e side').perm (List.perm_middle (l₁ := [D₁])).symm)
  | @impLLax _ Θ A₁ B₁ _ h d₁ d₂ ih₁ ih₂ =>
      intro D e B E side
      have side' : G4p (B :: B₁ :: Θ) E :=
        (side.impLLax_inv₂ ((h.cons B).trans (List.Perm.swap _ B Θ))).perm
          (List.perm_middle (l₁ := [B₁]))
      exact .impLLax ((h.cons _).trans (List.Perm.swap _ _ Θ))
        (d₁.weaken _)
        ((ih₂ e side').perm (List.perm_middle (l₁ := [B₁])).symm)
  | @impLLaxLax _ Θ A₁ B₁ X _ h d₁ d₂ ih₁ ih₂ =>
      intro D e B E side
      have side' : G4p (B :: B₁ :: X.somehow :: Θ) E :=
        (side.impLLax_inv₂ ((h.cons B).trans (List.Perm.swap _ B _))).perm
          (List.perm_middle (l₁ := [B₁]))
      refine .impLLaxLax
        ((h.cons _).trans (List.perm_middle
          (l₁ := [A₁.somehow.ifThen B₁, X.somehow])).symm)
        ((d₁.weaken _).perm (List.perm_middle
          (l₁ := [A₁.somehow.ifThen B₁, X])).symm)
        ((ih₂ e side').perm (List.perm_middle (l₁ := [B₁, X.somehow])).symm)

/-- Convenience form: contexts given with the implication at the head. -/
theorem weak_ImpLax' {Γ : List PLLFormula} {D B E : PLLFormula}
    (d : G4p Γ D.somehow) (side : G4p (B :: Γ) E) :
    G4p (D.somehow.ifThen B :: Γ) E :=
  weak_ImpLax d rfl side

end G4p

end PLLND
