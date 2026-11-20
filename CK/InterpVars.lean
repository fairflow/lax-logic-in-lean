/-
# Theorem 4 (i): the variables of `Ep` and `Ap`

Source: I. van der Giessen and I. Shillito, "Uniform interpolation with
constructive diamond", arXiv:2602.16880, §4, Theorem 4 (`thm:UIP_CK`), the
p-freeness property.  Rocq: `theories/Sequent/G4CK/CKPropQuantifiers.v` of
github.com/ianshil/CK, section `VariablesCorrect`: `e_rule_vars`,
`e_rule_9_vars`, `e_rule_12_vars`, `a_rule_form_vars`, `a_rule_env_vars`,
`a_rule_env_form16_vars`, `a_rule_env17_vars`, `EA_vars`.

    x occurs in Ep(Δ)      gives  x ≠ p  and  x occurs in Δ
    x occurs in Ap(Δ ⇒ ϕ)  gives  x ≠ p  and  x occurs in Δ or in ϕ
-/
import CK.InterpRows

namespace CK

open Form

/-- `x` occurs in some member of `Δ`. -/
def OccL (x : Nat) (Δ : List Form) : Prop := ∃ θ, θ ∈ Δ ∧ Occurs x θ

theorem mem_of_mem_rm {θ x : Form} : ∀ {Δ : List Form}, x ∈ rm θ Δ → x ∈ Δ
  | h :: t, hx => by
      by_cases e : θ = h
      · rw [rm, if_pos e] at hx; exact List.mem_cons_of_mem _ hx
      · rw [rm, if_neg e] at hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_of_mem_rm hx')

section
variable {x : Nat} {T : Prop} {Δ : List Form}

theorem occL_cons {a : Form} {L : List Form} (h₁ : Occurs x a → T) (h₂ : OccL x L → T) :
    OccL x (a :: L) → T := by
  rintro ⟨θ, hθ, ho⟩
  rcases List.mem_cons.1 hθ with rfl | hθ'
  · exact h₁ ho
  · exact h₂ ⟨θ, hθ', ho⟩

theorem occL_nil : OccL x [] → T := fun ⟨_, h, _⟩ => nomatch h

theorem occL_rm {θ : Form} (h : OccL x Δ → T) : OccL x (rm θ Δ) → T :=
  fun ⟨θ', hθ', ho⟩ => h ⟨θ', mem_of_mem_rm hθ', ho⟩

theorem occL_unbox (h : OccL x Δ → T) : OccL x (unbox Δ) → T :=
  fun ⟨θ', hθ', ho⟩ => h ⟨□θ', box_mem_of_mem_unbox hθ', ho⟩

end

/-- `x` occurs in `φ` only if `x ≠ p` and `T`. -/
@[irreducible] def Good (x p : Nat) (T : Prop) (φ : Form) : Prop := Occurs x φ → x ≠ p ∧ T

section
variable {x p : Nat} {T : Prop} {a b : Form}
attribute [local semireducible] Good

theorem Good.elim (h : Good x p T a) (ho : Occurs x a) : x ≠ p ∧ T := h ho
theorem good_bot : Good x p T ⊥' := fun h => nomatch h
theorem good_top : Good x p T Form.top := fun h => h.elim (fun h => nomatch h) (fun h => nomatch h)
theorem good_and (h₁ : Good x p T a) (h₂ : Good x p T b) : Good x p T (a ⋏ b) := fun h => h.elim h₁ h₂
theorem good_or (h₁ : Good x p T a) (h₂ : Good x p T b) : Good x p T (a ⋎ b) := fun h => h.elim h₁ h₂
theorem good_imp (h₁ : Good x p T a) (h₂ : Good x p T b) : Good x p T (a ⟶ b) := fun h => h.elim h₁ h₂
theorem good_box (h₁ : Good x p T a) : Good x p T (□a) := h₁
theorem good_dia (h₁ : Good x p T a) : Good x p T (◇a) := h₁
theorem good_var {q : Nat} (h₁ : p ≠ q) (h₂ : Occurs x (Form.var q) → T) :
    Good x p T (Form.var q) := fun h => ⟨fun e => h₁ (e ▸ h : q = p).symm, h₂ h⟩

theorem good_conj : ∀ {l : List Form}, (∀ φ ∈ l, Good x p T φ) → Good x p T (conj l)
  | [], _ => good_top
  | _ :: _, h => good_and (h _ List.mem_cons_self)
      (good_conj fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))

theorem good_disj : ∀ {l : List Form}, (∀ φ ∈ l, Good x p T φ) → Good x p T (disj l)
  | [], _ => good_bot
  | _ :: _, h => good_or (h _ List.mem_cons_self)
      (good_disj fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))

end

/-- The two properties of Theorem 4 (i) at one pointed environment. -/
def VarsAt (x p : Nat) (E A : List Form → Form → Form) (Δ : List Form) (ϕ : Form) : Prop :=
  Good x p (OccL x Δ) (E Δ ϕ) ∧ Good x p (Occurs x ϕ ∨ OccL x Δ) (A Δ ϕ)

section
variable {x p : Nat} {T : Prop} {E A : List Form → Form → Form} {Δ : List Form} {ϕ : Form}
attribute [local semireducible] Good

theorem good_E {Δ' : List Form} {ψ : Form} (H : ∀ Δ' ψ, pw Δ' ψ < pw Δ ϕ → VarsAt x p E A Δ' ψ)
    (hb : pw Δ' ψ < pw Δ ϕ) (h : OccL x Δ' → T) : Good x p T (E Δ' ψ) :=
  fun ho => ⟨((H _ _ hb).1 ho).1, h ((H _ _ hb).1 ho).2⟩

theorem good_A {Δ' : List Form} {ψ : Form} (H : ∀ Δ' ψ, pw Δ' ψ < pw Δ ϕ → VarsAt x p E A Δ' ψ)
    (hb : pw Δ' ψ < pw Δ ϕ) (h₁ : Occurs x ψ → T) (h₂ : OccL x Δ' → T) : Good x p T (A Δ' ψ) :=
  fun ho => ⟨((H _ _ hb).2 ho).1, ((H _ _ hb).2 ho).2.elim h₁ h₂⟩

end

/-- Closes `Occurs x b`, the goal, from `ho : Occurs x a`, by unfolding
`Occurs` and at most two case distinctions. -/
macro "ea_sub" ho:ident : tactic =>
  `(tactic| first
      | exact $ho
      | (simp only [Occurs] at $ho:ident ⊢
         first
          | exact $ho
          | (simp only [$ho:ident, true_or, or_true]; done)
          | (rcases $ho:ident with ho | ho | ho <;> simp only [ho, true_or, or_true]; done)
          | (rcases $ho:ident with ho | ho <;> simp only [ho, true_or, or_true]; done)
          | (rcases $ho:ident with (ho | ho) | ho <;> simp only [ho, true_or, or_true]; done)))

/-- Closes `Occurs x a → T` for a subformula `a` of one of the members `m₁`,
`m₂` of `Δ` or of the succedent, and `OccL x Δ' → T` for the environments
of Figure 3. -/
macro "ea_occ" hT:ident hϕ:ident m₁:ident m₂:ident : tactic =>
  `(tactic| (repeat' first
      | exact $hT
      | exact occL_nil
      | refine occL_cons ?_ ?_
      | refine occL_rm ?_
      | refine occL_unbox ?_
      | (intro ho
         first
          | (refine $hϕ ?_; ea_sub ho)
          | (refine $hϕ (Or.inl ?_); ea_sub ho)
          | (refine $hT ⟨_, $m₁, ?_⟩; ea_sub ho)
          | (refine $hT ⟨_, $m₂, ?_⟩; ea_sub ho))))

/-- Decomposes a row of Figure 3 into its recursive calls. -/
macro "ea_good" H:ident hT:ident hϕ:ident m₁:ident m₂:ident : tactic =>
  `(tactic| ((repeat' first
      | exact good_bot
      | exact good_top
      | refine good_and ?_ ?_
      | refine good_or ?_ ?_
      | refine good_imp ?_ ?_
      | refine good_box ?_
      | refine good_dia ?_
      | refine good_E $H ?_ ?_
      | refine good_A $H ?_ ?_ ?_
      | refine good_var ‹_› ?_) <;>
     first
      | (show _ < _; ea_dec)
      | ea_occ $hT $hϕ $m₁ $m₂))

section
variable {x p : Nat} {T : Prop} {E A : List Form → Form → Form} {Δ : List Form} {ϕ : Form}
  (H : ∀ Δ' ψ, pw Δ' ψ < pw Δ ϕ → VarsAt x p E A Δ' ψ) (hT : OccL x Δ → T)
include H hT

/-- Rocq `e_rule_9_vars`. -/
theorem eRow9_vars : Good x p T (eRow9 E Δ ϕ) := by
  have hϕ := hT
  unfold eRow9
  split
  · exact good_top
  · rename_i h
    exact good_box (good_E H (pw_unbox_lt _ h) (occL_unbox hT))

/-- Rocq `e_rule_vars`. -/
theorem eRow_vars {θ : Form} (hθ : θ ∈ Δ) : Good x p T (eRow p E A Δ ϕ θ) := by
  have hϕ := hT
  rcases θ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> simp only [eRow]
  all_goals (try split) <;> (try split) <;> ea_good H hT hϕ hθ hθ

/-- Rocq `e_rule_12_vars`. -/
theorem eRow12_vars {θ₁ θ₂ : Form} (h₁ : θ₁ ∈ Δ) (h₂ : θ₂ ∈ Δ) :
    Good x p T (eRow12 E A Δ ϕ θ₁ θ₂) := by
  have hϕ := hT
  rcases θ₁ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> rcases θ₂ with _|_|_|_|_|_|_ <;>
    simp only [eRow12] <;> ea_good H hT hϕ h₁ h₂

variable (hϕ : Occurs x ϕ → T)
include hϕ

/-- Rocq `a_rule_form_vars`. -/
theorem aForm_vars : Good x p T (aForm p E A Δ ϕ) := by
  have hθ : True := trivial
  cases ϕ <;> simp only [aForm] <;> (try split) <;> ea_good H hT hϕ hθ hθ

/-- Rocq `a_rule_env_vars`. -/
theorem aEnv_vars {θ : Form} (hθ : θ ∈ Δ) : Good x p T (aEnv p E A Δ ϕ θ) := by
  rcases θ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> simp only [aEnv] <;>
    (try split) <;> (try split) <;> ea_good H hT hϕ hθ hθ

/-- Rocq `a_rule_env_form16_vars`. -/
theorem aRow16_vars {θ : Form} (hθ : θ ∈ Δ) : Good x p T (aRow16 E A Δ ϕ θ) := by
  cases ϕ <;> cases θ <;> simp only [aRow16] <;> ea_good H hT hϕ hθ hθ

/-- Rocq `a_rule_env17_vars`. -/
theorem aRow17_vars {θ₁ θ₂ : Form} (h₁ : θ₁ ∈ Δ) (h₂ : θ₂ ∈ Δ) :
    Good x p T (aRow17 E A Δ ϕ θ₁ θ₂) := by
  rcases θ₁ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> rcases θ₂ with _|_|_|_|_|_|_ <;>
    simp only [aRow17] <;> ea_good H hT hϕ h₁ h₂

end

/-- **Theorem 4 (i)**, by induction on the measure.  Rocq `EA_vars`. -/
theorem EA_varsAt (x p : Nat) : ∀ (n : Nat) (Δ : List Form) (ϕ : Form), pw Δ ϕ < n →
    VarsAt x p (EA p true) (EA p false) Δ ϕ
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, Δ, ϕ, hn => by
      have H : ∀ Δ' ψ, pw Δ' ψ < pw Δ ϕ → VarsAt x p (EA p true) (EA p false) Δ' ψ :=
        fun Δ' ψ h => EA_varsAt x p n Δ' ψ (by omega)
      constructor
      · rw [EA_true]
        refine good_conj fun φ hφ => ?_
        rcases List.mem_append.1 hφ with hφ | hφ
        · rcases List.mem_cons.1 hφ with rfl | hφ
          · exact eRow9_vars H id
          · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hφ
            exact eRow_vars H id hθ
        · obtain ⟨θ₁, h₁, hφ⟩ := List.mem_flatMap.1 hφ
          obtain ⟨θ₂, h₂, rfl⟩ := List.mem_map.1 hφ
          exact eRow12_vars H id h₁ h₂
      · rw [EA_false]
        refine good_disj fun φ hφ => ?_
        rcases List.mem_append.1 hφ with hφ | hφ
        · rcases List.mem_append.1 hφ with hφ | hφ
          · rcases List.mem_cons.1 hφ with rfl | hφ
            · exact aForm_vars H Or.inr Or.inl
            · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hφ
              exact aEnv_vars H Or.inr Or.inl hθ
          · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hφ
            exact aRow16_vars H Or.inr Or.inl hθ
        · obtain ⟨θ₁, h₁, hφ⟩ := List.mem_flatMap.1 hφ
          obtain ⟨θ₂, h₂, rfl⟩ := List.mem_map.1 hφ
          exact aRow17_vars H Or.inr Or.inl h₁ h₂

/-- **Theorem 4 (i)** for `Ep`: a variable of `Ep(Δ)` is not `p` and occurs
in `Δ`.  Rocq `EA_vars`, first component. -/
theorem Ep_vars {x p : Nat} {Δ : List Form} (h : Occurs x (Ep p Δ)) :
    x ≠ p ∧ ∃ θ, θ ∈ Δ ∧ Occurs x θ :=
  (EA_varsAt x p _ Δ ⊥' (Nat.lt_succ_self _)).1.elim h

/-- **Theorem 4 (i)** for `Ap`: a variable of `Ap(Δ ⇒ ϕ)` is not `p` and
occurs in `ϕ` or in `Δ`.  Rocq `EA_vars`, second component. -/
theorem Ap_vars {x p : Nat} {Δ : List Form} {ϕ : Form} (h : Occurs x (Ap p Δ ϕ)) :
    x ≠ p ∧ (Occurs x ϕ ∨ ∃ θ, θ ∈ Δ ∧ Occurs x θ) :=
  (EA_varsAt x p _ Δ ϕ (Nat.lt_succ_self _)).2.elim h

#print axioms Ep_vars
#print axioms Ap_vars

end CK
