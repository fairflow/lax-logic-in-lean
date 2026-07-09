import LaxLogic.PLLG4HCtr

/-!
# Toward cut for G4iLL″: pre-lemmas

The cut ladder (`docs/g4p-ladder.md`, revision 3) runs
`exfalso → cut_atom → K(w)`.  This file opens with the first:

* `exfalso_adm` — from `Γ ⇒ ⊥` conclude `Γ ⇒ E`.  No right rule
  concludes `⊥`, so a `⊥`-derivation is a tree of left rules over
  `botL` leaves; rebuild every rule at goal `E`, reusing the
  goal-independent auxiliary premises (`L→→`'s first premise, the two
  lax rules' box premises) verbatim.  Purely structural — no measure.
-/

open PLLFormula

namespace PLLND

namespace G4c

/-- **Ex falso, admissibly.** -/
theorem exfalso_adm : ∀ {n : Nat} {Γ : List PLLFormula} {G : PLLFormula},
    G4h n Γ G → G = falsePLL → ∀ (E : PLLFormula), G4c Γ E := by
  intro n Γ G d
  induction d with
  | init _ => intro e; cases e
  | botL h => intro _ E; exact botL h
  | andR _ _ _ _ => intro e; cases e
  | orR1 _ _ => intro e; cases e
  | orR2 _ _ => intro e; cases e
  | laxR _ _ => intro e; cases e
  | impR _ _ => intro e; cases e
  | laxL _ _ _ => intro e; cases e
  | andL h _ ih => intro e E; exact andL h (ih e E)
  | orL h _ _ ih₁ ih₂ => intro e E; exact orL h (ih₁ e E) (ih₂ e E)
  | impLProp h ha _ ih => intro e E; exact impLProp h ha (ih e E)
  | impLBot h _ ih => intro e E; exact impLBot h (ih e E)
  | impLAnd h _ ih => intro e E; exact impLAnd h (ih e E)
  | impLOr h _ ih => intro e E; exact impLOr h (ih e E)
  | impLImp h d₁ _ _ ih₂ => intro e E; exact impLImp h ⟨_, d₁⟩ (ih₂ e E)
  | impLLax h d₁ _ _ ih₂ => intro e E; exact impLLax h ⟨_, d₁⟩ (ih₂ e E)
  | impLLaxLax h hX d₁ _ _ ih₂ =>
      intro e E
      exact impLLaxLax h hX ⟨_, d₁⟩ (ih₂ e E)

/-- Ex falso at the working judgment. -/
theorem exfalso' {Γ : List PLLFormula} (d : G4c Γ falsePLL)
    (E : PLLFormula) : G4c Γ E := by
  obtain ⟨n, hd⟩ := d
  exact exfalso_adm hd rfl E

/-!
### Atomic cut

`cut_atom`: from `Γ ⇒ p` and `p, Γ ⇒ E` conclude `Γ ⇒ E`, by strong
induction on the sum of the heights.  The right derivation is
processed rule by rule — the cut copy is parametric everywhere, atoms
never being left-rule principals — with the left derivation
transported into each premise by height-preserving inversion.  Two
places need more:

* `L→→`'s first premise: the residue `B→D` is not an inversion piece,
  so the cut runs at the *enlarged* context (both `B→D` and the
  principal retained, transports by hp-weakening) and the result is
  repaired afterwards by `impR_inv`, `impLImp_dup`, and the already
  closed cut-free contraction — no measure cost, since the repairs
  make no recursive calls.
* `Lp→` whose side atom is the cut copy: the induction *switches
  sides* and analyses the left derivation — `init` supplies the
  missing membership, `botL` closes outright, and each left-rule
  ending pushes the cut into its own goal-`p` premises (transporting
  the reassembled right derivation by hp-inversion), reusing the
  goal-independent auxiliary premises verbatim.
-/

private theorem push2 {x q : PLLFormula} {Γ : List PLLFormula} :
    (x :: q :: q :: Γ).Perm (q :: q :: x :: Γ) :=
  (List.Perm.swap q x _).trans ((List.Perm.swap q x Γ).cons q)

private theorem rot3 {x y z : PLLFormula} {l : List PLLFormula} :
    (x :: y :: z :: l).Perm (z :: y :: x :: l) :=
  ((List.Perm.swap z y l).cons x).trans
    ((List.Perm.swap z x (y :: l)).trans ((List.Perm.swap y x l).cons z))

private theorem cross_split {P q : PLLFormula} {Γ' Δ Γ : List PLLFormula}
    (h : Γ'.Perm (P :: Δ)) (hp : Γ'.Perm (q :: Γ)) (hne : P ≠ q) :
    ∃ Γ₀, Δ.Perm (q :: Γ₀) ∧ Γ.Perm (P :: Γ₀) := by
  rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, _⟩ | ⟨l₁, hΔ, hm⟩
  · exact absurd e hne
  · exact ⟨l₁, hΔ, hm⟩

/-- **Atomic cut.** -/
theorem cut_atom : ∀ (k : Nat) {p : String} {m n : Nat}
    {Γ Γ' : List PLLFormula} {E : PLLFormula},
    m + n ≤ k → G4h m Γ (prop p) → G4h n Γ' E →
    Γ'.Perm (prop p :: Γ) → G4c Γ E := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro p m n Γ Γ' E hk d₁ d₂ hp
  cases d₂ with
  | init h =>
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · injection e with e'; subst e'; exact ⟨m, d₁⟩
      · exact init h'
  | botL h =>
      rcases List.mem_cons.mp (hp.subset h) with e | h'
      · cases e
      · exact botL h'
  | @andR n₀ _ A B da db =>
      exact andR (IH (m + n₀) (by omega) (Nat.le_refl _) d₁ da hp)
        (IH (m + n₀) (by omega) (Nat.le_refl _) d₁ db hp)
  | @orR1 n₀ _ A B da =>
      exact orR1 (IH (m + n₀) (by omega) (Nat.le_refl _) d₁ da hp)
  | @orR2 n₀ _ A B db =>
      exact orR2 (IH (m + n₀) (by omega) (Nat.le_refl _) d₁ db hp)
  | @laxR n₀ _ A da =>
      exact laxR (IH (m + n₀) (by omega) (Nat.le_refl _) d₁ da hp)
  | @impR n₀ _ A B da =>
      exact impR (IH (m + n₀) (by omega) (Nat.le_refl _) (d₁.weaken A) da
        ((hp.cons A).trans (List.Perm.swap _ _ _)))
  | @laxL n₀ _ A B h da =>
      have h' : A.somehow ∈ Γ := by
        rcases List.mem_cons.mp (hp.subset h) with e | h'
        · cases e
        · exact h'
      exact laxL h' (IH (m + n₀) (by omega) (Nat.le_refl _) (d₁.weaken A) da
        ((hp.cons A).trans (List.Perm.swap _ _ _)))
  | @andL n₀ _ Θ A B _ h da =>
      obtain ⟨l₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact andL hΓ (IH (m + n₀) (by omega) (Nat.le_refl _)
        (d₁.inv (.and A B) hΓ) da
        (((hΔ.cons B).cons A).trans (List.perm_middle (l₁ := [A, B]))))
  | @orL n₀ _ Θ A B _ h da db =>
      obtain ⟨l₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact orL hΓ
        (IH (m + n₀) (by omega) (Nat.le_refl _) (d₁.inv (.or₁ A B) hΓ) da
          ((hΔ.cons A).trans (List.Perm.swap _ _ _)))
        (IH (m + n₀) (by omega) (Nat.le_refl _) (d₁.inv (.or₂ A B) hΓ) db
          ((hΔ.cons B).trans (List.Perm.swap _ _ _)))
  | @impLBot n₀ _ Θ B _ h da =>
      obtain ⟨l₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact impLBot hΓ (IH (m + n₀) (by omega) (Nat.le_refl _)
        (d₁.inv (.impBot B) hΓ) da hΔ)
  | @impLAnd n₀ _ Θ A B D _ h da =>
      obtain ⟨l₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact impLAnd hΓ (IH (m + n₀) (by omega) (Nat.le_refl _)
        (d₁.inv (.impAnd A B D) hΓ) da
        ((hΔ.cons _).trans (List.Perm.swap _ _ _)))
  | @impLOr n₀ _ Θ A B D _ h da =>
      obtain ⟨l₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact impLOr hΓ (IH (m + n₀) (by omega) (Nat.le_refl _)
        (d₁.inv (.impOr A B D) hΓ) da
        (((hΔ.cons _).cons _).trans
          (List.perm_middle (l₁ := [A.ifThen D, B.ifThen D]))))
  | @impLImp n₀ _ Θ A B D _ h da db =>
      obtain ⟨l₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      -- premise 1: cut at the enlarged context, then repair
      have q₁ : G4c (B.ifThen D :: Γ) (A.ifThen B) :=
        IH (m + n₀) (by omega) (Nat.le_refl _) (d₁.weaken (B.ifThen D))
          ((da.weaken ((A.ifThen B).ifThen D)).perm
            ((((hΔ.cons _).cons _).trans rot3).trans
              ((hΓ.symm.cons _).cons _)))
          (List.Perm.refl _)
      obtain ⟨n₁, q₁'⟩ := q₁
      have q₂ : G4c (A :: B.ifThen D :: B.ifThen D ::
          A :: B.ifThen D :: l₀) B :=
        impLImp_dup (q₁'.impR_inv rfl)
          (((hΓ.cons _).cons A).trans
            (List.perm_middle (l₁ := [A, B.ifThen D])))
      have c₁ : G4c (A :: B.ifThen D :: B.ifThen D :: B.ifThen D :: l₀) B :=
        contract q₂ ((List.perm_middle (l₁ := [B.ifThen D, B.ifThen D])).cons A)
      have c₂ : G4c (B.ifThen D :: A :: B.ifThen D :: l₀) B :=
        contract c₁ push2
      have c₃ : G4c (B.ifThen D :: A :: l₀) B :=
        contract c₂ ((List.Perm.swap _ _ _).cons _)
      have q₃ : G4c (D :: l₀) E :=
        IH (m + n₀) (by omega) (Nat.le_refl _)
          (d₁.inv (.impImp A B D) hΓ) db
          ((hΔ.cons D).trans (List.Perm.swap _ _ _))
      exact impLImp hΓ (impR (c₃.perm (List.Perm.swap _ _ _))) q₃
  | @impLProp n₀ _ Θ a B _ h ha da =>
      obtain ⟨l₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      have q : G4c (B :: l₀) E :=
        IH (m + n₀) (by omega) (Nat.le_refl _)
          (d₁.inv (.impProp a B) hΓ) da
          ((hΔ.cons B).trans (List.Perm.swap _ _ _))
      rcases List.mem_cons.mp (hΔ.subset ha) with e | ha'
      · -- the side atom is the cut copy: switch sides, analyse d₁
        injection e with e'
        subst e'
        have d₂w : G4h (n₀ + 1) Γ' E := .impLProp h ha da
        cases d₁ with
        | init h₁ =>
            rcases List.mem_cons.mp (hΓ.subset h₁) with e₁ | h₁'
            · cases e₁
            · exact impLProp hΓ h₁' q
        | botL h₁ => exact botL h₁
        | @andL m₀ _ Θ₁ A₁ B₁ _ h₁ da₁ =>
            exact andL h₁ (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
              ((d₂w.inv (.and A₁ B₁)
                (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _)))).perm
                (List.perm_middle (l₁ := [A₁, B₁])))
              (List.Perm.refl _))
        | @orL m₀ _ Θ₁ A₁ B₁ _ h₁ da₁ db₁ =>
            exact orL h₁
              (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                ((d₂w.inv (.or₁ A₁ B₁)
                  (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _)))).perm
                  (List.Perm.swap _ _ _))
                (List.Perm.refl _))
              (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                ((d₂w.inv (.or₂ A₁ B₁)
                  (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _)))).perm
                  (List.Perm.swap _ _ _))
                (List.Perm.refl _))
        | @impLProp m₀ _ Θ₁ a₁ B₁ _ h₁ ha₁ da₁ =>
            exact impLProp h₁ ha₁
              (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                ((d₂w.inv (.impProp a₁ B₁)
                  (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _)))).perm
                  (List.Perm.swap _ _ _))
                (List.Perm.refl _))
        | @impLBot m₀ _ Θ₁ B₁ _ h₁ da₁ =>
            exact impLBot h₁
              (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                (d₂w.inv (.impBot B₁)
                  (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _))))
                (List.Perm.refl _))
        | @impLAnd m₀ _ Θ₁ A₁ B₁ D₁ _ h₁ da₁ =>
            exact impLAnd h₁
              (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                ((d₂w.inv (.impAnd A₁ B₁ D₁)
                  (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _)))).perm
                  (List.Perm.swap _ _ _))
                (List.Perm.refl _))
        | @impLOr m₀ _ Θ₁ A₁ B₁ D₁ _ h₁ da₁ =>
            exact impLOr h₁
              (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                ((d₂w.inv (.impOr A₁ B₁ D₁)
                  (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _)))).perm
                  (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁])))
                (List.Perm.refl _))
        | @impLImp m₀ _ Θ₁ A₁ B₁ D₁ _ h₁ da₁ db₁ =>
            exact impLImp h₁ ⟨_, da₁⟩
              (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                ((d₂w.inv (.impImp A₁ B₁ D₁)
                  (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _)))).perm
                  (List.Perm.swap _ _ _))
                (List.Perm.refl _))
        | @impLLax m₀ _ Θ₁ A₁ B₁ _ h₁ da₁ db₁ =>
            exact impLLax h₁ ⟨_, da₁⟩
              (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                ((d₂w.inv (.impLax A₁ B₁)
                  (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _)))).perm
                  (List.Perm.swap _ _ _))
                (List.Perm.refl _))
        | @impLLaxLax m₀ _ Θ₁ A₁ B₁ X₁ _ h₁ hX₁ da₁ db₁ =>
            exact impLLaxLax h₁ hX₁ ⟨_, da₁⟩
              (IH (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                ((d₂w.inv (.impLax A₁ B₁)
                  (hp.trans ((h₁.cons _).trans (List.Perm.swap _ _ _)))).perm
                  (List.Perm.swap _ _ _))
                (List.Perm.refl _))
      · exact impLProp hΓ ha' q
  | @impLLax n₀ _ Θ A B _ h da db =>
      obtain ⟨l₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      exact impLLax hΓ
        (IH (m + n₀) (by omega) (Nat.le_refl _) d₁ da hp)
        (IH (m + n₀) (by omega) (Nat.le_refl _)
          (d₁.inv (.impLax A B) hΓ) db
          ((hΔ.cons B).trans (List.Perm.swap _ _ _)))
  | @impLLaxLax n₀ _ Θ A B X _ h hX da db =>
      obtain ⟨l₀, hΔ, hΓ⟩ := cross_split h hp (by intro e; cases e)
      have hX' : X.somehow ∈ l₀ := by
        rcases List.mem_cons.mp (hΔ.subset hX) with e | h'
        · cases e
        · exact h'
      exact impLLaxLax hΓ hX'
        (IH (m + n₀) (by omega) (Nat.le_refl _) (d₁.weaken X) da
          ((hp.cons X).trans (List.Perm.swap _ _ _)))
        (IH (m + n₀) (by omega) (Nat.le_refl _)
          (d₁.inv (.impLax A B) hΓ) db
          ((hΔ.cons B).trans (List.Perm.swap _ _ _)))

/-!
### The main cut theorem, conditional on self-absorption

Design: `docs/g4p-ladder.md` (2026-07-09 afternoon).  Right-primary
case analysis on the second derivation; principal cases reduce by
strictly-lighter cuts through height-preserving *right* inversions
(`impR_inv`, and `andR_inv` below), so a secondary analysis of the
left derivation is needed in only three places: `∨`-principal (no
right inversion for `∨R`), and the two boxed-witness cases, where the
goal (or the synthetic subgoal) is boxed and the `laxL` rebuild is
therefore legitimate.  The single residual obligation is
`SelfAbsorb`.
-/

private theorem cross_split' {P q : PLLFormula} {Γ' Δ Γ : List PLLFormula}
    (h : Γ'.Perm (P :: Δ)) (hp : Γ'.Perm (q :: Γ)) :
    (P = q ∧ Δ.Perm Γ) ∨ ∃ Γ₀, Δ.Perm (q :: Γ₀) ∧ Γ.Perm (P :: Γ₀) := by
  rcases G4.perm_cons_cases (h.symm.trans hp) with ⟨e, hΔ⟩ | ⟨l₁, hΔ, hm⟩
  · exact .inl ⟨e, hΔ⟩
  · exact .inr ⟨l₁, hΔ, hm⟩

/-- Height-preserving right inversion of `∧`. -/
private theorem andR_inv : ∀ {n : Nat} {Γ : List PLLFormula} {G : PLLFormula},
    G4h n Γ G → ∀ {A B : PLLFormula}, G = A.and B →
    G4h n Γ A ∧ G4h n Γ B := by
  intro n Γ G d
  induction d with
  | init _ => intro A B e; cases e
  | botL h => intro A B e; exact ⟨.botL h, .botL h⟩
  | andR d₁ d₂ _ _ =>
      intro A B e
      injection e with e₁ e₂
      subst e₁; subst e₂
      exact ⟨d₁.succ_mono, d₂.succ_mono⟩
  | orR1 _ _ => intro A B e; cases e
  | orR2 _ _ => intro A B e; cases e
  | laxR _ _ => intro A B e; cases e
  | impR _ _ => intro A B e; cases e
  | laxL _ _ _ => intro A B e; cases e
  | andL h _ ih =>
      intro A B e
      exact ⟨.andL h (ih e).1, .andL h (ih e).2⟩
  | orL h _ _ ih₁ ih₂ =>
      intro A B e
      exact ⟨.orL h (ih₁ e).1 (ih₂ e).1, .orL h (ih₁ e).2 (ih₂ e).2⟩
  | impLProp h ha _ ih =>
      intro A B e
      exact ⟨.impLProp h ha (ih e).1, .impLProp h ha (ih e).2⟩
  | impLBot h _ ih =>
      intro A B e
      exact ⟨.impLBot h (ih e).1, .impLBot h (ih e).2⟩
  | impLAnd h _ ih =>
      intro A B e
      exact ⟨.impLAnd h (ih e).1, .impLAnd h (ih e).2⟩
  | impLOr h _ ih =>
      intro A B e
      exact ⟨.impLOr h (ih e).1, .impLOr h (ih e).2⟩
  | impLImp h d₁ _ _ ih₂ =>
      intro A B e
      exact ⟨.impLImp h d₁ (ih₂ e).1, .impLImp h d₁ (ih₂ e).2⟩
  | impLLax h d₁ _ _ ih₂ =>
      intro A B e
      exact ⟨.impLLax h d₁ (ih₂ e).1, .impLLax h d₁ (ih₂ e).2⟩
  | impLLaxLax h hX d₁ _ _ ih₂ =>
      intro A B e
      exact ⟨.impLLaxLax h hX d₁ (ih₂ e).1, .impLLaxLax h hX d₁ (ih₂ e).2⟩

/-- **Self-absorption**: an implication whose antecedent-box is
derivable *in its own presence* may fire.  Valid in every nuclear
algebra (`f∧γ ≤ jA` and `f∧jA ≤ B` give `f∧γ ≤ B∧⋀l₀ ≤ E`); the one
obligation of the conditional cut theorem below. -/
def SelfAbsorb : Prop :=
  ∀ {Γ l₀ : List PLLFormula} {A B E : PLLFormula},
    Γ.Perm (A.somehow.ifThen B :: l₀) → G4c Γ A.somehow →
    G4c (B :: l₀) E → G4c Γ E

/-- **Cut, conditional on self-absorption**, by lexicographic
induction on (cut-formula weight, height sum). -/
theorem cut_of_selfAbsorb (hS : SelfAbsorb) :
    ∀ (w : Nat) {A : PLLFormula}, A.weight ≤ w →
    ∀ (k : Nat) {m n : Nat} {Γ Γ' : List PLLFormula} {E : PLLFormula},
    m + n ≤ k → G4h m Γ A → G4h n Γ' E → Γ'.Perm (A :: Γ) →
    G4c Γ E := by
  intro w
  induction w with
  | zero =>
      intro A hA
      exact absurd hA (by have := weight_pos A; omega)
  | succ w ihw =>
    intro A hA k
    induction k using Nat.strong_induction_on with
    | _ k IHk =>
    intro m n Γ Γ' E hk d₁ d₂ hp
    cases d₂ with
    | init h =>
        rcases List.mem_cons.mp (hp.subset h) with e | h'
        · subst e; exact ⟨m, d₁⟩
        · exact init h'
    | botL h =>
        rcases List.mem_cons.mp (hp.subset h) with e | h'
        · subst e; exact exfalso_adm d₁ rfl E
        · exact botL h'
    | @andR n₀ _ A₂ B₂ da db =>
        exact andR (IHk (m + n₀) (by omega) (Nat.le_refl _) d₁ da hp)
          (IHk (m + n₀) (by omega) (Nat.le_refl _) d₁ db hp)
    | @orR1 n₀ _ A₂ B₂ da =>
        exact orR1 (IHk (m + n₀) (by omega) (Nat.le_refl _) d₁ da hp)
    | @orR2 n₀ _ A₂ B₂ db =>
        exact orR2 (IHk (m + n₀) (by omega) (Nat.le_refl _) d₁ db hp)
    | @laxR n₀ _ A₂ da =>
        exact laxR (IHk (m + n₀) (by omega) (Nat.le_refl _) d₁ da hp)
    | @impR n₀ _ A₂ B₂ da =>
        exact impR (IHk (m + n₀) (by omega) (Nat.le_refl _) (d₁.weaken A₂) da
          ((hp.cons A₂).trans (List.Perm.swap _ _ _)))
    | @laxL n₀ _ A₁ B h da =>
        rcases List.mem_cons.mp (hp.subset h) with e | h'
        · -- the box is the cut formula: left-analyse d₁ (the goal is boxed)
          subst e
          simp only [PLLFormula.weight] at hA
          have d₂w : G4h (n₀ + 1) Γ' B.somehow := .laxL h da
          have q : G4c (A₁ :: Γ) B.somehow :=
            IHk (m + n₀) (by omega) (Nat.le_refl _) (d₁.weaken A₁) da
              ((hp.cons A₁).trans (List.Perm.swap _ _ _))
          cases d₁ with
          | @laxR m₀ _ _ dL =>
              obtain ⟨nq, q'⟩ := q
              exact ihw (by omega) (m₀ + nq) (Nat.le_refl _) dL q'
                (List.Perm.refl _)
          | @laxL m₀ _ Y _ h₁ dP =>
              exact laxL h₁ (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _)
                dP ((d₂w.weaken Y).perm
                  ((hp.cons Y).trans (List.Perm.swap _ _ _)))
                (List.Perm.refl _))
          | botL h₁ => exact botL h₁
          | @andL m₀ _ Θ₁ C₁ C₂ _ h₁ da₁ =>
              exact andL h₁ (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _)
                da₁ ((d₂w.inv (.and C₁ C₂) (hp.trans ((h₁.cons _).trans
                  (List.Perm.swap _ _ _)))).perm
                  (List.perm_middle (l₁ := [C₁, C₂])))
                (List.Perm.refl _))
          | @orL m₀ _ Θ₁ C₁ C₂ _ h₁ da₁ db₁ =>
              exact orL h₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  ((d₂w.inv (.or₁ C₁ C₂) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                  ((d₂w.inv (.or₂ C₁ C₂) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLProp m₀ _ Θ₁ a₁ C₁ _ h₁ ha₁ da₁ =>
              exact impLProp h₁ ha₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  ((d₂w.inv (.impProp a₁ C₁) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLBot m₀ _ Θ₁ C₁ _ h₁ da₁ =>
              exact impLBot h₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  (d₂w.inv (.impBot C₁) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _))))
                  (List.Perm.refl _))
          | @impLAnd m₀ _ Θ₁ C₁ C₂ D₃ _ h₁ da₁ =>
              exact impLAnd h₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  ((d₂w.inv (.impAnd C₁ C₂ D₃) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLOr m₀ _ Θ₁ C₁ C₂ D₃ _ h₁ da₁ =>
              exact impLOr h₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  ((d₂w.inv (.impOr C₁ C₂ D₃) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm
                    (List.perm_middle (l₁ := [C₁.ifThen D₃, C₂.ifThen D₃])))
                  (List.Perm.refl _))
          | @impLImp m₀ _ Θ₁ C₁ C₂ D₃ _ h₁ da₁ db₁ =>
              exact impLImp h₁ ⟨_, da₁⟩
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                  ((d₂w.inv (.impImp C₁ C₂ D₃) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLLax m₀ _ Θ₁ C₁ C₂ _ h₁ da₁ db₁ =>
              exact impLLax h₁ ⟨_, da₁⟩
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                  ((d₂w.inv (.impLax C₁ C₂) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLLaxLax m₀ _ Θ₁ C₁ C₂ X₁ _ h₁ hX₁ da₁ db₁ =>
              exact impLLaxLax h₁ hX₁ ⟨_, da₁⟩
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                  ((d₂w.inv (.impLax C₁ C₂) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
        · exact laxL h' (IHk (m + n₀) (by omega) (Nat.le_refl _)
            (d₁.weaken A₁) da
            ((hp.cons A₁).trans (List.Perm.swap _ _ _)))
    | @andL n₀ _ Θ A₁ B₁ _ h da =>
        rcases cross_split' h hp with ⟨e, hΔ⟩ | ⟨l₀, hΔ, hΓ⟩
        · -- principal: right-inversion of ∧, two lighter cuts
          subst e
          simp only [PLLFormula.weight] at hA
          obtain ⟨dL₁, dL₂⟩ := andR_inv d₁ rfl
          obtain ⟨nr, r'⟩ : G4c (A₁ :: Γ) E :=
            ihw (by omega) (m + n₀) (Nat.le_refl _) (dL₂.weaken A₁) da
              (((hΔ.cons B₁).cons A₁).trans (List.Perm.swap _ _ _))
          exact ihw (by omega) (m + nr) (Nat.le_refl _) dL₁ r'
            (List.Perm.refl _)
        · exact andL hΓ (IHk (m + n₀) (by omega) (Nat.le_refl _)
            (d₁.inv (.and A₁ B₁) hΓ) da
            (((hΔ.cons B₁).cons A₁).trans (List.perm_middle (l₁ := [A₁, B₁]))))
    | @orL n₀ _ Θ A₁ B₁ _ h da db =>
        rcases cross_split' h hp with ⟨e, hΔ⟩ | ⟨l₀, hΔ, hΓ⟩
        · -- principal: no right inversion for ∨ — left-analyse d₁
          subst e
          simp only [PLLFormula.weight] at hA
          have d₂w : G4h (n₀ + 1) Γ' E := .orL h da db
          cases d₁ with
          | @orR1 m₀ _ _ _ dL =>
              exact ihw (by omega) (m₀ + n₀) (Nat.le_refl _) dL da
                (hΔ.cons A₁)
          | @orR2 m₀ _ _ _ dL =>
              exact ihw (by omega) (m₀ + n₀) (Nat.le_refl _) dL db
                (hΔ.cons B₁)
          | botL h₁ => exact botL h₁
          | @andL m₀ _ Θ₁ C₁ C₂ _ h₁ da₁ =>
              exact andL h₁ (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _)
                da₁ ((d₂w.inv (.and C₁ C₂) (hp.trans ((h₁.cons _).trans
                  (List.Perm.swap _ _ _)))).perm
                  (List.perm_middle (l₁ := [C₁, C₂])))
                (List.Perm.refl _))
          | @orL m₀ _ Θ₁ C₁ C₂ _ h₁ da₁ db₁ =>
              exact orL h₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  ((d₂w.inv (.or₁ C₁ C₂) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                  ((d₂w.inv (.or₂ C₁ C₂) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLProp m₀ _ Θ₁ a₁ C₁ _ h₁ ha₁ da₁ =>
              exact impLProp h₁ ha₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  ((d₂w.inv (.impProp a₁ C₁) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLBot m₀ _ Θ₁ C₁ _ h₁ da₁ =>
              exact impLBot h₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  (d₂w.inv (.impBot C₁) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _))))
                  (List.Perm.refl _))
          | @impLAnd m₀ _ Θ₁ C₁ C₂ D₃ _ h₁ da₁ =>
              exact impLAnd h₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  ((d₂w.inv (.impAnd C₁ C₂ D₃) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLOr m₀ _ Θ₁ C₁ C₂ D₃ _ h₁ da₁ =>
              exact impLOr h₁
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                  ((d₂w.inv (.impOr C₁ C₂ D₃) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm
                    (List.perm_middle (l₁ := [C₁.ifThen D₃, C₂.ifThen D₃])))
                  (List.Perm.refl _))
          | @impLImp m₀ _ Θ₁ C₁ C₂ D₃ _ h₁ da₁ db₁ =>
              exact impLImp h₁ ⟨_, da₁⟩
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                  ((d₂w.inv (.impImp C₁ C₂ D₃) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLLax m₀ _ Θ₁ C₁ C₂ _ h₁ da₁ db₁ =>
              exact impLLax h₁ ⟨_, da₁⟩
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                  ((d₂w.inv (.impLax C₁ C₂) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
          | @impLLaxLax m₀ _ Θ₁ C₁ C₂ X₁ _ h₁ hX₁ da₁ db₁ =>
              exact impLLaxLax h₁ hX₁ ⟨_, da₁⟩
                (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                  ((d₂w.inv (.impLax C₁ C₂) (hp.trans ((h₁.cons _).trans
                    (List.Perm.swap _ _ _)))).perm (List.Perm.swap _ _ _))
                  (List.Perm.refl _))
        · exact orL hΓ
            (IHk (m + n₀) (by omega) (Nat.le_refl _)
              (d₁.inv (.or₁ A₁ B₁) hΓ) da
              ((hΔ.cons A₁).trans (List.Perm.swap _ _ _)))
            (IHk (m + n₀) (by omega) (Nat.le_refl _)
              (d₁.inv (.or₂ A₁ B₁) hΓ) db
              ((hΔ.cons B₁).trans (List.Perm.swap _ _ _)))
    | @impLProp n₀ _ Θ a B₁ _ h ha da =>
        rcases cross_split' h hp with ⟨e, hΔ⟩ | ⟨l₀, hΔ, hΓ⟩
        · -- principal: impR-inversion, contract the present atom, cut B₁
          subst e
          simp only [PLLFormula.weight] at hA
          have ha' : prop a ∈ Γ := hΔ.subset ha
          have r : G4c Γ B₁ :=
            (contract ⟨m, d₁.impR_inv rfl⟩
              ((List.perm_cons_erase ha').cons (prop a))).perm
              (List.perm_cons_erase ha').symm
          obtain ⟨nr, r'⟩ := r
          exact ihw (by omega) (nr + n₀) (Nat.le_refl _) r' da (hΔ.cons B₁)
        · have q : G4c (B₁ :: l₀) E :=
            IHk (m + n₀) (by omega) (Nat.le_refl _)
              (d₁.inv (.impProp a B₁) hΓ) da
              ((hΔ.cons B₁).trans (List.Perm.swap _ _ _))
          rcases List.mem_cons.mp (hΔ.subset ha) with e | ha'
          · -- side atom is the cut formula: the cut is atomic — delegate
            subst e
            exact cut_atom k hk d₁ (.impLProp h ha da) hp
          · exact impLProp hΓ ha' q
    | @impLBot n₀ _ Θ B₁ _ h da =>
        rcases cross_split' h hp with ⟨e, hΔ⟩ | ⟨l₀, hΔ, hΓ⟩
        · exact ⟨n₀, da.perm hΔ⟩
        · exact impLBot hΓ (IHk (m + n₀) (by omega) (Nat.le_refl _)
            (d₁.inv (.impBot B₁) hΓ) da hΔ)
    | @impLAnd n₀ _ Θ A₁ B₁ D₁ _ h da =>
        rcases cross_split' h hp with ⟨e, hΔ⟩ | ⟨l₀, hΔ, hΓ⟩
        · -- principal: curry through the right inversion, one lighter cut
          subst e
          simp only [PLLFormula.weight] at hA
          have lK : G4h (m + 2) Γ (A₁.ifThen (B₁.ifThen D₁)) :=
            .impR (.impR (((d₁.impR_inv rfl).inv (.and A₁ B₁)
              (List.Perm.refl _)).perm (List.Perm.swap _ _ _)))
          exact ihw (by simp only [PLLFormula.weight]; omega)
            ((m + 2) + n₀) (Nat.le_refl _) lK da (hΔ.cons _)
        · exact impLAnd hΓ (IHk (m + n₀) (by omega) (Nat.le_refl _)
            (d₁.inv (.impAnd A₁ B₁ D₁) hΓ) da
            ((hΔ.cons _).trans (List.Perm.swap _ _ _)))
    | @impLOr n₀ _ Θ A₁ B₁ D₁ _ h da =>
        rcases cross_split' h hp with ⟨e, hΔ⟩ | ⟨l₀, hΔ, hΓ⟩
        · -- principal: two curried cuts through the right inversion
          subst e
          simp only [PLLFormula.weight] at hA
          have l₁ : G4h (m + 1) Γ (A₁.ifThen D₁) :=
            .impR ((d₁.impR_inv rfl).inv (.or₁ A₁ B₁) (List.Perm.refl _))
          have l₂ : G4h (m + 1) Γ (B₁.ifThen D₁) :=
            .impR ((d₁.impR_inv rfl).inv (.or₂ A₁ B₁) (List.Perm.refl _))
          obtain ⟨ni, inner⟩ : G4c (A₁.ifThen D₁ :: Γ) E :=
            ihw (by simp only [PLLFormula.weight]; omega)
              ((m + 1) + n₀) (Nat.le_refl _) (l₂.weaken _) da
              (((hΔ.cons _).cons _).trans (List.Perm.swap _ _ _))
          exact ihw (by simp only [PLLFormula.weight]; omega)
            ((m + 1) + ni) (Nat.le_refl _) l₁ inner (List.Perm.refl _)
        · exact impLOr hΓ (IHk (m + n₀) (by omega) (Nat.le_refl _)
            (d₁.inv (.impOr A₁ B₁ D₁) hΓ) da
            (((hΔ.cons _).cons _).trans
              (List.perm_middle (l₁ := [A₁.ifThen D₁, B₁.ifThen D₁]))))
    | @impLImp n₀ _ Θ A₁ B₁ D₁ _ h da db =>
        rcases cross_split' h hp with ⟨e, hΔ⟩ | ⟨l₀, hΔ, hΓ⟩
        · -- principal: the Dyckhoff–Negri four-cut chain
          subst e
          simp only [PLLFormula.weight] at hA
          have dINV : G4h m ((A₁.ifThen B₁) :: Γ) D₁ := d₁.impR_inv rfl
          obtain ⟨nb, lB⟩ : G4c (B₁ :: Γ) (A₁.ifThen B₁) :=
            impR (identity_mem (List.Mem.tail _ (List.Mem.head _)))
          obtain ⟨nk, lK⟩ : G4c Γ (B₁.ifThen D₁) :=
            impR (ihw (by simp only [PLLFormula.weight]; omega)
              (nb + m) (Nat.le_refl _) lB
              ((dINV.weaken B₁).perm (List.Perm.swap _ _ _))
              (List.Perm.refl _))
          obtain ⟨nab, lAB⟩ : G4c Γ (A₁.ifThen B₁) :=
            ihw (by simp only [PLLFormula.weight]; omega)
              (nk + n₀) (Nat.le_refl _) lK da (hΔ.cons _)
          obtain ⟨nd, lD⟩ : G4c Γ D₁ :=
            ihw (by simp only [PLLFormula.weight]; omega)
              (nab + m) (Nat.le_refl _) lAB dINV (List.Perm.refl _)
          exact ihw (by omega) (nd + n₀) (Nat.le_refl _) lD db (hΔ.cons _)
        · -- parametric: enlarged-context cut for premise 1, then repair
          have q₁ : G4c (B₁.ifThen D₁ :: Γ) (A₁.ifThen B₁) :=
            IHk (m + n₀) (by omega) (Nat.le_refl _)
              (d₁.weaken (B₁.ifThen D₁))
              ((da.weaken ((A₁.ifThen B₁).ifThen D₁)).perm
                ((((hΔ.cons _).cons _).trans rot3).trans
                  ((hΓ.symm.cons _).cons _)))
              (List.Perm.refl _)
          obtain ⟨n₁, q₁'⟩ := q₁
          have q₂ : G4c (A₁ :: B₁.ifThen D₁ :: B₁.ifThen D₁ ::
              A₁ :: B₁.ifThen D₁ :: l₀) B₁ :=
            impLImp_dup (q₁'.impR_inv rfl)
              (((hΓ.cons _).cons A₁).trans
                (List.perm_middle (l₁ := [A₁, B₁.ifThen D₁])))
          have c₁ : G4c (A₁ :: B₁.ifThen D₁ :: B₁.ifThen D₁ ::
              B₁.ifThen D₁ :: l₀) B₁ :=
            contract q₂
              ((List.perm_middle (l₁ := [B₁.ifThen D₁, B₁.ifThen D₁])).cons A₁)
          have c₂ : G4c (B₁.ifThen D₁ :: A₁ :: B₁.ifThen D₁ :: l₀) B₁ :=
            contract c₁ push2
          have c₃ : G4c (B₁.ifThen D₁ :: A₁ :: l₀) B₁ :=
            contract c₂ ((List.Perm.swap _ _ _).cons _)
          have q₃ : G4c (D₁ :: l₀) E :=
            IHk (m + n₀) (by omega) (Nat.le_refl _)
              (d₁.inv (.impImp A₁ B₁ D₁) hΓ) db
              ((hΔ.cons D₁).trans (List.Perm.swap _ _ _))
          exact impLImp hΓ (impR (c₃.perm (List.Perm.swap _ _ _))) q₃
    | @impLLax n₀ _ Θ A₁ B₁ _ h da db =>
        rcases cross_split' h hp with ⟨e, hΔ⟩ | ⟨l₀, hΔ, hΓ⟩
        · -- principal: premise 1 keeps the context — cut it directly,
          -- box the result, two lighter cuts
          subst e
          simp only [PLLFormula.weight] at hA
          obtain ⟨na, lOA⟩ : G4c Γ A₁.somehow :=
            laxR (IHk (m + n₀) (by omega) (Nat.le_refl _) d₁ da hp)
          obtain ⟨nb, lB⟩ : G4c Γ B₁ :=
            ihw (by simp only [PLLFormula.weight]; omega)
              (na + m) (Nat.le_refl _) lOA (d₁.impR_inv rfl)
              (List.Perm.refl _)
          exact ihw (by omega) (nb + n₀) (Nat.le_refl _) lB db (hΔ.cons _)
        · exact impLLax hΓ
            (IHk (m + n₀) (by omega) (Nat.le_refl _) d₁ da hp)
            (IHk (m + n₀) (by omega) (Nat.le_refl _)
              (d₁.inv (.impLax A₁ B₁) hΓ) db
              ((hΔ.cons B₁).trans (List.Perm.swap _ _ _)))
    | @impLLaxLax n₀ _ Θ A₁ B₁ X _ h hX da db =>
        rcases cross_split' h hp with ⟨e, hΔ⟩ | ⟨l₀, hΔ, hΓ⟩
        · -- principal: the box witness survives in Γ — open it, then
          -- two lighter cuts
          subst e
          simp only [PLLFormula.weight] at hA
          obtain ⟨na, lOA⟩ : G4c Γ A₁.somehow :=
            laxL (hΔ.subset hX)
              (IHk (m + n₀) (by omega) (Nat.le_refl _) (d₁.weaken X) da
                ((hp.cons X).trans (List.Perm.swap _ _ _)))
          obtain ⟨nb, lB⟩ : G4c Γ B₁ :=
            ihw (by simp only [PLLFormula.weight]; omega)
              (na + m) (Nat.le_refl _) lOA (d₁.impR_inv rfl)
              (List.Perm.refl _)
          exact ihw (by omega) (nb + n₀) (Nat.le_refl _) lB db (hΔ.cons _)
        · have qb : G4c (B₁ :: l₀) E :=
            IHk (m + n₀) (by omega) (Nat.le_refl _)
              (d₁.inv (.impLax A₁ B₁) hΓ) db
              ((hΔ.cons B₁).trans (List.Perm.swap _ _ _))
          rcases List.mem_cons.mp (hΔ.subset hX) with e | hX'
          · -- the box witness is the cut formula: build Γ ⇒ ◯A₁ by the
            -- boxed-subgoal left-analysis against the synthetic laxL
            -- packaging, then close with self-absorption
            subst e
            simp only [PLLFormula.weight] at hA
            have d₂s : G4h (n₀ + 1) Γ' A₁.somehow :=
              .laxL (h.symm.subset (.tail _ hX)) da
            have q : G4c (X :: Γ) A₁.somehow :=
              IHk (m + n₀) (by omega) (Nat.le_refl _) (d₁.weaken X) da
                ((hp.cons X).trans (List.Perm.swap _ _ _))
            have ra : G4c Γ A₁.somehow := by
              cases d₁ with
              | @laxR m₀ _ _ dL =>
                  obtain ⟨nq, q'⟩ := q
                  exact ihw (by omega) (m₀ + nq) (Nat.le_refl _) dL q'
                    (List.Perm.refl _)
              | @laxL m₀ _ Y _ h₁ dP =>
                  exact laxL h₁ (IHk (m₀ + (n₀ + 1)) (by omega)
                    (Nat.le_refl _) dP ((d₂s.weaken Y).perm
                      ((hp.cons Y).trans (List.Perm.swap _ _ _)))
                    (List.Perm.refl _))
              | botL h₁ => exact botL h₁
              | @andL m₀ _ Θ₁ C₁ C₂ _ h₁ da₁ =>
                  exact andL h₁ (IHk (m₀ + (n₀ + 1)) (by omega)
                    (Nat.le_refl _) da₁
                    ((d₂s.inv (.and C₁ C₂) (hp.trans ((h₁.cons _).trans
                      (List.Perm.swap _ _ _)))).perm
                      (List.perm_middle (l₁ := [C₁, C₂])))
                    (List.Perm.refl _))
              | @orL m₀ _ Θ₁ C₁ C₂ _ h₁ da₁ db₁ =>
                  exact orL h₁
                    (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                      ((d₂s.inv (.or₁ C₁ C₂) (hp.trans ((h₁.cons _).trans
                        (List.Perm.swap _ _ _)))).perm
                        (List.Perm.swap _ _ _))
                      (List.Perm.refl _))
                    (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                      ((d₂s.inv (.or₂ C₁ C₂) (hp.trans ((h₁.cons _).trans
                        (List.Perm.swap _ _ _)))).perm
                        (List.Perm.swap _ _ _))
                      (List.Perm.refl _))
              | @impLProp m₀ _ Θ₁ a₁ C₁ _ h₁ ha₁ da₁ =>
                  exact impLProp h₁ ha₁
                    (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                      ((d₂s.inv (.impProp a₁ C₁)
                        (hp.trans ((h₁.cons _).trans
                        (List.Perm.swap _ _ _)))).perm
                        (List.Perm.swap _ _ _))
                      (List.Perm.refl _))
              | @impLBot m₀ _ Θ₁ C₁ _ h₁ da₁ =>
                  exact impLBot h₁
                    (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                      (d₂s.inv (.impBot C₁) (hp.trans ((h₁.cons _).trans
                        (List.Perm.swap _ _ _))))
                      (List.Perm.refl _))
              | @impLAnd m₀ _ Θ₁ C₁ C₂ D₃ _ h₁ da₁ =>
                  exact impLAnd h₁
                    (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                      ((d₂s.inv (.impAnd C₁ C₂ D₃)
                        (hp.trans ((h₁.cons _).trans
                        (List.Perm.swap _ _ _)))).perm
                        (List.Perm.swap _ _ _))
                      (List.Perm.refl _))
              | @impLOr m₀ _ Θ₁ C₁ C₂ D₃ _ h₁ da₁ =>
                  exact impLOr h₁
                    (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) da₁
                      ((d₂s.inv (.impOr C₁ C₂ D₃)
                        (hp.trans ((h₁.cons _).trans
                        (List.Perm.swap _ _ _)))).perm
                        (List.perm_middle
                          (l₁ := [C₁.ifThen D₃, C₂.ifThen D₃])))
                      (List.Perm.refl _))
              | @impLImp m₀ _ Θ₁ C₁ C₂ D₃ _ h₁ da₁ db₁ =>
                  exact impLImp h₁ ⟨_, da₁⟩
                    (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                      ((d₂s.inv (.impImp C₁ C₂ D₃)
                        (hp.trans ((h₁.cons _).trans
                        (List.Perm.swap _ _ _)))).perm
                        (List.Perm.swap _ _ _))
                      (List.Perm.refl _))
              | @impLLax m₀ _ Θ₁ C₁ C₂ _ h₁ da₁ db₁ =>
                  exact impLLax h₁ ⟨_, da₁⟩
                    (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                      ((d₂s.inv (.impLax C₁ C₂)
                        (hp.trans ((h₁.cons _).trans
                        (List.Perm.swap _ _ _)))).perm
                        (List.Perm.swap _ _ _))
                      (List.Perm.refl _))
              | @impLLaxLax m₀ _ Θ₁ C₁ C₂ X₁ _ h₁ hX₁ da₁ db₁ =>
                  exact impLLaxLax h₁ hX₁ ⟨_, da₁⟩
                    (IHk (m₀ + (n₀ + 1)) (by omega) (Nat.le_refl _) db₁
                      ((d₂s.inv (.impLax C₁ C₂)
                        (hp.trans ((h₁.cons _).trans
                        (List.Perm.swap _ _ _)))).perm
                        (List.Perm.swap _ _ _))
                      (List.Perm.refl _))
            exact hS hΓ ra qb
          · exact impLLaxLax hΓ hX'
              (IHk (m + n₀) (by omega) (Nat.le_refl _) (d₁.weaken X) da
                ((hp.cons X).trans (List.Perm.swap _ _ _)))
              qb

/-- Cut at the working judgment, conditional on self-absorption. -/
theorem cut' (hS : SelfAbsorb) {Γ : List PLLFormula} {A E : PLLFormula}
    (d₁ : G4c Γ A) (d₂ : G4c (A :: Γ) E) : G4c Γ E := by
  obtain ⟨m, h₁⟩ := d₁
  obtain ⟨n, h₂⟩ := d₂
  exact cut_of_selfAbsorb hS A.weight (Nat.le_refl _) (m + n)
    (Nat.le_refl _) h₁ h₂ (List.Perm.refl _)

end G4c

end PLLND
