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

end G4c

end PLLND
