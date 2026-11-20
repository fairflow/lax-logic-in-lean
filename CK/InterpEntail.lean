/-
# Theorem 4 (ii): the implication property of `Ep` and `Ap`

Source: I. van der Giessen and I. Shillito, "Uniform interpolation with
constructive diamond", arXiv:2602.16880, §4, Theorem 4 (`thm:UIP_CK`), the
implication property.  Rocq: `theories/Sequent/G4CK/CKPropQuantifiers.v` of
github.com/ianshil/CK, section `EntailmentCorrect`: `a_rule_env_spec`,
`entail_correct`.

    Δ ⇒ Ep(Δ)            Δ, Ap(Δ ⇒ ϕ) ⇒ ϕ

The derivations are those of the Rocq proof, row by row.  Rocq distinguishes
whether `Ap(…)` is a box where it sits under `□⁻¹`; here that is the lemma
`G4CK.unboxWk`.
-/
import CK.InterpVars

namespace CK

open Form

/-- Brings the head of the right-hand list to the front of the left-hand
list (among its first four members), repeatedly. -/
syntax "ea_perm" : tactic
macro_rules
  | `(tactic| ea_perm) => `(tactic| first
      | exact List.Perm.refl _
      | (refine List.Perm.cons _ ?_; ea_perm)
      | (refine List.Perm.trans (List.Perm.swap _ _ _) ?_; refine List.Perm.cons _ ?_; ea_perm)
      | (refine List.Perm.trans (List.Perm.cons _ (List.Perm.swap _ _ _)) ?_
         refine List.Perm.trans (List.Perm.swap _ _ _) ?_; refine List.Perm.cons _ ?_; ea_perm)
      | (refine List.Perm.trans (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))) ?_
         refine List.Perm.trans (List.Perm.cons _ (List.Perm.swap _ _ _)) ?_
         refine List.Perm.trans (List.Perm.swap _ _ _) ?_; refine List.Perm.cons _ ?_; ea_perm))

theorem perm_rm {θ : Form} : ∀ {Δ : List Form}, θ ∈ Δ → Δ.Perm (θ :: rm θ Δ)
  | h :: t, hm => by
      by_cases e : θ = h
      · subst e; rw [rm, if_pos rfl]
      · have hm' : θ ∈ t := by
          rcases List.mem_cons.1 hm with rfl | h'
          · exact absurd rfl e
          · exact h'
        rw [rm, if_neg e]
        exact ((perm_rm hm').cons h).trans (List.Perm.swap _ _ _)

/-- `L, Δ ~ θ, L, rm θ Δ`. -/
theorem perm_mid {θ : Form} {Δ : List Form} (L : List Form) (hθ : θ ∈ Δ) :
    (L ++ Δ).Perm (θ :: (L ++ rm θ Δ)) :=
  ((perm_rm hθ).append_left L).trans List.perm_middle

theorem perm_mid1 {θ X : Form} {Δ : List Form} (hθ : θ ∈ Δ) :
    (X :: Δ).Perm (θ :: X :: rm θ Δ) := perm_mid [X] hθ

theorem perm_mid2 {θ X Y : Form} {Δ : List Form} (hθ : θ ∈ Δ) :
    (X :: Y :: Δ).Perm (θ :: X :: Y :: rm θ Δ) := perm_mid [X, Y] hθ

theorem unbox_rm {θ : Form} (hθ : ∀ a, θ ≠ □a) : ∀ Δ : List Form, unbox (rm θ Δ) = unbox Δ
  | [] => rfl
  | h :: t => by
      by_cases e : θ = h
      · subst e; rw [rm, if_pos rfl]
        cases θ <;> first | rfl | exact absurd rfl (hθ _)
      · rw [rm, if_neg e]
        cases h <;> first
          | exact unbox_rm hθ t
          | exact congrArg (_ :: ·) (unbox_rm hθ t)

namespace G4CK

variable {Γ L : List Form} {a b c e φ ψ : Form}

theorem top : G4CK Γ Form.top := .impR (.botL List.mem_cons_self)

theorem wk (d : G4CK Γ φ) : G4CK (ψ :: Γ) φ := d.weaken ψ
theorem wk1 (d : G4CK (a :: Γ) φ) : G4CK (a :: ψ :: Γ) φ := (d.weaken ψ).perm (by ea_perm)
theorem wk2 (d : G4CK (a :: b :: Γ) φ) : G4CK (a :: b :: ψ :: Γ) φ :=
  (d.weaken ψ).perm (by ea_perm)
theorem wk3 (d : G4CK (a :: b :: c :: Γ) φ) : G4CK (a :: b :: c :: ψ :: Γ) φ :=
  (d.weaken ψ).perm (by ea_perm)
theorem perm' (d : G4CK Γ φ) (h : L.Perm Γ) : G4CK L φ := d.perm h.symm
theorem front1 (d : G4CK (b :: a :: L) φ) : G4CK (a :: b :: L) φ := d.perm (by ea_perm)
theorem front2 (d : G4CK (c :: a :: b :: L) φ) : G4CK (a :: b :: c :: L) φ := d.perm (by ea_perm)
theorem front3 (d : G4CK (e :: a :: b :: c :: L) φ) : G4CK (a :: b :: c :: e :: L) φ :=
  d.perm (by ea_perm)

/-- Weakening under `□⁻¹`.  This replaces the Rocq case distinction
`is_box`. -/
theorem unboxWk (L : List Form) (a : Form) (d : G4CK (L ++ unbox Γ) φ) :
    G4CK (L ++ unbox (a :: Γ)) φ := by
  cases a <;> first
    | exact d
    | exact (d.weaken _).perm List.perm_middle.symm

/-- Rocq `list_conjR`. -/
theorem conjR : ∀ {l : List Form}, (∀ φ ∈ l, G4CK Γ φ) → G4CK Γ (conj l)
  | [], _ => top
  | _ :: _, h => .andR (h _ List.mem_cons_self) (conjR fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))

/-- Rocq `list_disjL`. -/
theorem disjL : ∀ {l : List Form}, (∀ φ ∈ l, G4CK (φ :: Γ) ψ) → G4CK (disj l :: Γ) ψ
  | [], _ => .botL List.mem_cons_self
  | _ :: _, h => .orL (List.Perm.refl _) (h _ List.mem_cons_self)
      (disjL fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))

end G4CK

/-- Closes `G4CK Γ φ` by the derivation `t`, whose antecedent is a
permutation of `Γ` that begins with a formula built from a recursive call;
the pointed environments of the recursive calls in `t` are found by
unification, and the bounds on the measure, left as `?_` in `t`, by
`ea_dec`. -/
macro "ea_from " t:term : tactic =>
  `(tactic| (refine' G4CK.perm' $t ?_; rotate_right; ea_perm; all_goals ea_dec))

/-- The two properties of Theorem 4 (ii) at one pointed environment. -/
def EntAt (E A : List Form → Form → Form) (Δ : List Form) (ϕ : Form) : Prop :=
  G4CK Δ (E Δ ϕ) ∧ G4CK (A Δ ϕ :: Δ) ϕ

section
variable {p : Nat} {E A : List Form → Form → Form} {Δ : List Form} {ϕ : Form}
  (H : ∀ Δ' ψ, pw Δ' ψ < pw Δ ϕ → EntAt E A Δ' ψ)
include H

theorem eRow9_ent : G4CK Δ (eRow9 E Δ ϕ) := by
  unfold eRow9
  split
  · exact .top
  · rename_i h
    exact .boxR (H _ _ (pw_unbox_lt _ h)).1

theorem eRow_ent {θ : Form} (hθ : θ ∈ Δ) : G4CK Δ (eRow p E A Δ ϕ θ) := by
  have hp := perm_rm hθ
  rcases θ with q|_|⟨δ₁,δ₂⟩|⟨δ₁,δ₂⟩|⟨(q|_|⟨δ₁,δ₂⟩|⟨δ₁,δ₂⟩|⟨δ₁,δ₂⟩|δ₁|δ₁),δ₃⟩|φ|φ <;> simp only [eRow]
  · -- (E1)
    split
    · exact .top
    · exact .idP hθ
  · -- (E0)
    exact .botL hθ
  · -- (E2)
    exact .andL hp (.front1 (H _ _ (by ea_dec)).1)
  · -- (E3)
    exact .orL hp (.orR1 (H _ _ (by ea_dec)).1) (.orR2 (H _ _ (by ea_dec)).1)
  · -- (E4), (E5)
    split
    · rename_i hq
      exact .impVarL hp (mem_rm_of_ne hq (by intro e; cases e)) (H _ _ (by ea_dec)).1
    · split
      · exact .top
      · exact .impR (.impVarL (perm_mid1 hθ) List.mem_cons_self (.wk1 (H _ _ (by ea_dec)).1))
  · exact .top
  · -- (E6)
    exact .impAndL hp (H _ _ (by ea_dec)).1
  · -- (E7)
    exact .impOrL hp (.front1 (H _ _ (by ea_dec)).1)
  · -- (E8)
    refine .impR (.impImpL (perm_mid1 hθ) (.impR ?_) ?_)
    · exact .front2 ((H _ _ (by ea_dec)).1.weakImp (H _ _ (by ea_dec)).2)
    · exact .wk1 (H _ _ (by ea_dec)).1
  · -- (E10)
    refine .impR (.impBoxL (perm_mid1 hθ) ?_ ?_)
    · exact (H _ _ (by ea_dec)).1.weakImp (H _ _ (by ea_dec)).2
    · exact .wk1 (H _ _ (by ea_dec)).1
  · -- (E13)
    refine .impR (.impDiaL (perm_mid1 hθ) List.mem_cons_self ?_ ?_)
    · exact (H _ _ (by ea_dec)).1.weakImp (H _ _ (by ea_dec)).2
    · exact .wk1 (H _ _ (by ea_dec)).1
  · -- an instance of (E9)
    exact .boxR ((H _ _ (by ea_dec)).1.perm (unbox_perm hp).symm)
  · -- (E11)
    exact .diaL hp (H _ _ (by ea_dec)).1

theorem eRow12_ent {θ₁ θ₂ : Form} (h₁ : θ₁ ∈ Δ) (h₂ : θ₂ ∈ Δ) :
    G4CK Δ (eRow12 E A Δ ϕ θ₁ θ₂) := by
  rcases θ₁ with _|_|_|_|⟨(_|_|_|_|_|_|δ₁),δ₂⟩|_|_ <;> rcases θ₂ with _|_|_|_|_|_|δ₃ <;>
    simp only [eRow12] <;> try exact .top
  -- (E12)
  have h₂' : (◇δ₃) ∈ rm ((◇δ₁) ⟶ δ₂) Δ := mem_rm_of_ne h₂ (by intro e; cases e)
  refine .impR (.impDiaL (perm_mid1 h₁) (List.mem_cons_of_mem _ h₂') ?_ ?_)
  · have d := (H (δ₃ :: unbox (rm (◇δ₃) (rm ((◇δ₁) ⟶ δ₂) Δ))) ϕ (by ea_dec)).1.weakImp
      (H _ δ₁ (by ea_dec)).2
    refine .front1 ?_
    rw [← unbox_rm (θ := ◇δ₃) (by intro a e; cases e) (rm ((◇δ₁) ⟶ δ₂) Δ)]
    exact d
  · exact .wk1 (H _ _ (by ea_dec)).1

theorem aForm_ent : G4CK (aForm p E A Δ ϕ :: Δ) ϕ := by
  cases ϕ <;> simp only [aForm]
  · -- (A9)
    split
    · exact .botL List.mem_cons_self
    · exact .idP List.mem_cons_self
  · exact .botL List.mem_cons_self
  · -- (A11)
    refine .andR (.andL (List.Perm.refl _) (.wk1 ?_)) (.andL (List.Perm.refl _) (.wk ?_)) <;>
      ea_from (H _ _ ?_).2
  · -- (A12)
    refine .orL (List.Perm.refl _) (.orR1 ?_) (.orR2 ?_) <;> ea_from (H _ _ ?_).2
  · -- (A13)
    refine .impR ?_
    ea_from (H _ _ ?_).1.weakImp (H _ _ ?_).2
  · -- (A14)
    refine .boxR ?_
    ea_from (H _ _ ?_).1.weakImp (H _ _ ?_).2
  · -- (A18)
    refine .diaL (List.Perm.refl _) ?_
    ea_from (H _ _ ?_).1.weakImp (H _ _ ?_).2

/-- Rocq `a_rule_env_spec`. -/
theorem aEnv_ent {θ : Form} (hθ : θ ∈ Δ) : G4CK (aEnv p E A Δ ϕ θ :: Δ) ϕ := by
  rcases θ with q|_|⟨δ₁,δ₂⟩|⟨δ₁,δ₂⟩|⟨(q|_|⟨δ₁,δ₂⟩|⟨δ₁,δ₂⟩|⟨δ₁,δ₂⟩|δ₁|δ₁),δ₃⟩|φ|φ <;> simp only [aEnv]
  · -- (A10), (A1)
    split
    · split
      · rename_i hpq hϕ
        subst hpq; subst hϕ
        exact .idP (List.mem_cons_of_mem _ hθ)
      · exact .botL List.mem_cons_self
    · exact .botL List.mem_cons_self
  · exact .botL List.mem_cons_self
  · -- (A2)
    refine .andL (perm_mid1 hθ) ?_
    ea_from (H _ _ ?_).2
  · -- (A3)
    refine .andL (List.Perm.refl _) (.orL (perm_mid2 hθ) (.wk2 ?_) (.wk1 ?_)) <;>
      ea_from (H _ _ ?_).1.weakImp (H _ _ ?_).2
  · -- (A4), (A5)
    split
    · rename_i hq
      refine .impVarL (perm_mid1 hθ)
        (List.mem_cons_of_mem _ (mem_rm_of_ne hq (by intro e; cases e))) ?_
      ea_from (H _ _ ?_).2
    · split
      · exact .botL List.mem_cons_self
      · refine .andL (List.Perm.refl _) (.impVarL (perm_mid2 hθ) List.mem_cons_self (.wk1 ?_))
        ea_from (H _ _ ?_).2
  · exact .botL List.mem_cons_self
  · -- (A6)
    refine .impAndL (perm_mid1 hθ) ?_
    ea_from (H _ _ ?_).2
  · -- (A7)
    refine .impOrL (perm_mid1 hθ) ?_
    ea_from (H _ _ ?_).2
  · -- (A8)
    refine .andL (List.Perm.refl _) (.impImpL (perm_mid2 hθ) (.impR (.wk3 ?_)) (.wk1 ?_))
    · ea_from (H _ _ ?_).1.weakImp (H _ _ ?_).2
    · ea_from (H _ _ ?_).2
  · -- (A15)
    refine .andL (List.Perm.refl _) (.impBoxL (perm_mid2 hθ) ?_ (.wk1 ?_))
    · refine G4CK.unboxWk [_] (A _ _) ?_
      ea_from (H _ _ ?_).1.weakImp (H _ _ ?_).2
    · ea_from (H _ _ ?_).2
  · -- (A19)
    refine .andL (List.Perm.refl _) (.impDiaL (perm_mid2 hθ) List.mem_cons_self ?_ (.wk1 ?_))
    · refine G4CK.unboxWk [_] (A _ _) ?_
      ea_from (H _ _ ?_).1.weakImp (H _ _ ?_).2
    · ea_from (H _ _ ?_).2
  · exact .botL List.mem_cons_self
  · exact .botL List.mem_cons_self

theorem aRow16_ent {θ : Form} (hθ : θ ∈ Δ) : G4CK (aRow16 E A Δ ϕ θ :: Δ) ϕ := by
  cases ϕ <;> cases θ <;> simp only [aRow16] <;> try exact .botL List.mem_cons_self
  -- (A16)
  refine .diaL (perm_mid1 hθ) ?_
  ea_from (H _ _ ?_).1.weakImp (H _ _ ?_).2

theorem aRow17_ent {θ₁ θ₂ : Form} (h₁ : θ₁ ∈ Δ) (h₂ : θ₂ ∈ Δ) :
    G4CK (aRow17 E A Δ ϕ θ₁ θ₂ :: Δ) ϕ := by
  rcases θ₁ with _|_|_|_|⟨(_|_|_|_|_|_|δ₁),δ₂⟩|_|_ <;> rcases θ₂ with _|_|_|_|_|_|δ₃ <;>
    simp only [aRow17] <;> try exact .botL List.mem_cons_self
  -- (A17)
  have h₂' : (◇δ₃) ∈ rm ((◇δ₁) ⟶ δ₂) Δ := mem_rm_of_ne h₂ (by intro e; cases e)
  refine .andL (List.Perm.refl _) (.impDiaL (perm_mid2 h₁)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h₂')) ?_ (.wk1 ?_))
  · refine G4CK.unboxWk [_, _] (A _ _) ?_
    show G4CK (δ₃ :: _ :: unbox (rm ((◇δ₁) ⟶ δ₂) Δ)) δ₁
    rw [← unbox_rm (θ := ◇δ₃) (by intro a e; cases e) (rm ((◇δ₁) ⟶ δ₂) Δ)]
    ea_from (H _ _ ?_).1.weakImp (H _ _ ?_).2
  · ea_from (H _ _ ?_).2

end

/-- **Theorem 4 (ii)**, by induction on the measure.  Rocq `entail_correct`. -/
theorem EA_entAt (p : Nat) : ∀ (n : Nat) (Δ : List Form) (ϕ : Form), pw Δ ϕ < n →
    EntAt (EA p true) (EA p false) Δ ϕ
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, Δ, ϕ, hn => by
      have H : ∀ Δ' ψ, pw Δ' ψ < pw Δ ϕ → EntAt (EA p true) (EA p false) Δ' ψ :=
        fun Δ' ψ h => EA_entAt p n Δ' ψ (by omega)
      constructor
      · rw [EA_true]
        refine G4CK.conjR fun φ hφ => ?_
        rcases List.mem_append.1 hφ with hφ | hφ
        · rcases List.mem_cons.1 hφ with rfl | hφ
          · exact eRow9_ent H
          · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hφ
            exact eRow_ent H hθ
        · obtain ⟨θ₁, h₁, hφ⟩ := List.mem_flatMap.1 hφ
          obtain ⟨θ₂, h₂, rfl⟩ := List.mem_map.1 hφ
          exact eRow12_ent H h₁ h₂
      · rw [EA_false]
        refine G4CK.disjL fun φ hφ => ?_
        rcases List.mem_append.1 hφ with hφ | hφ
        · rcases List.mem_append.1 hφ with hφ | hφ
          · rcases List.mem_cons.1 hφ with rfl | hφ
            · exact aForm_ent H
            · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hφ
              exact aEnv_ent H hθ
          · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hφ
            exact aRow16_ent H hθ
        · obtain ⟨θ₁, h₁, hφ⟩ := List.mem_flatMap.1 hφ
          obtain ⟨θ₂, h₂, rfl⟩ := List.mem_map.1 hφ
          exact aRow17_ent H h₁ h₂

/-- **Theorem 4 (ii)** for `Ep`:  `Δ ⇒ Ep(Δ)`.  Rocq `entail_correct`, first
component. -/
theorem Ep_entail (p : Nat) (Δ : List Form) : G4CK Δ (Ep p Δ) :=
  (EA_entAt p _ Δ ⊥' (Nat.lt_succ_self _)).1

/-- **Theorem 4 (ii)** for `Ap`:  `Δ, Ap(Δ ⇒ ϕ) ⇒ ϕ`.  Rocq
`entail_correct`, second component. -/
theorem Ap_entail (p : Nat) (Δ : List Form) (ϕ : Form) : G4CK (Ap p Δ ϕ :: Δ) ϕ :=
  (EA_entAt p _ Δ ϕ (Nat.lt_succ_self _)).2

#print axioms Ep_entail
#print axioms Ap_entail

end CK
