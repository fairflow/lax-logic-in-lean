import CK.Complete

/-!
# `CK.Interp` — the uniform interpolants `Ep(Γ)` and `Ap(Γ ⇒ φ)`

**Definition 5** (`def_Ap_Ep`) and **Figure 3** of van der Giessen and
Shillito, *Uniform interpolation with constructive diamond*,
arXiv:2602.16880v2, §4.1, in the form of the Rocq development: `e_rule`,
`e_rule_9`, `e_rule_12`, `a_rule_env`, `a_rule_env_form16`, `a_rule_env17`,
`a_rule_form` and `EA` in `theories/Sequent/G4CK/CKPropQuantifiers.v`
(commit `cd09fce`).  The rows are those of Figure 3; the Lean text is
written afresh.

`EA p true Δ ϕ` is `Ep(Δ)` and `EA p false Δ ϕ` is `Ap(Δ ⇒ ϕ)`.  As in Rocq,
`E` carries a succedent `ϕ` that it only passes on: it is there for the
measure.  The list of conjuncts (disjuncts) is in Rocq's order, so that the
values agree with Rocq's syntactically (`CK/InterpTest.lean`).

**Theorem 3** (`thm:terminating`) is the termination proof of this
definition: every recursive call is at a smaller value of the measure `pw`,
Rocq's `pointed_env_order` (the succedent counted twice).
-/

namespace CK

open scoped Form

/-- `⋀ l`, with `⋀ [] = ⊤`.  Rocq `list_conj`. -/
def conj : List Form → Form
  | [] => Form.top
  | φ :: l => φ ⋏ conj l

/-- `⋁ l`, with `⋁ [] = ⊥`.  Rocq `list_disj`. -/
def disj : List Form → Form
  | [] => ⊥'
  | φ :: l => φ ⋎ disj l

/-- Remove one occurrence.  Rocq `rm`. -/
def rm (x : Form) : List Form → List Form
  | [] => []
  | h :: t => if x = h then t else h :: rm x t

/-- The measure of the pointed environment `(Δ, ϕ)`: Rocq
`pointed_env_order`, which compares `Δ • ϕ • ϕ`. -/
def pw (Δ : List Form) (ϕ : Form) : Nat := wt Δ + 2 * 5 ^ ϕ.weight

/-! ## Arithmetic of the measure -/

/-- `Σ 5^x` over a list of exponents. -/
def sp : List Nat → Nat
  | [] => 0
  | x :: xs => 5 ^ x + sp xs

theorem wt_eq_sp : ∀ L : List Form, wt L = sp (L.map Form.weight)
  | [] => rfl
  | φ :: L => congrArg (5 ^ φ.weight + ·) (wt_eq_sp L)

theorem sp_le {k : Nat} : ∀ {xs : List Nat}, (∀ x ∈ xs, x ≤ k) → sp xs ≤ xs.length * 5 ^ k
  | [], _ => Nat.zero_le _
  | x :: xs, h => by
      have h₁ : 5 ^ x ≤ 5 ^ k := Nat.pow_le_pow_right (by decide) (h x (.head _))
      have h₂ := sp_le (xs := xs) fun y hy => h y (.tail _ hy)
      show 5 ^ x + sp xs ≤ (xs.length + 1) * 5 ^ k
      rw [Nat.succ_mul]; omega

/-- At most four powers of 5 below `5^e` sum to less than `5^e`. -/
theorem sp_lt {xs : List Nat} {e : Nat} (hlen : xs.length ≤ 4) (h : ∀ x ∈ xs, x + 1 ≤ e) :
    sp xs < 5 ^ e := by
  cases xs with
  | nil => exact pow5_pos e
  | cons y ys =>
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by have := h y (.head _); omega⟩
      have h₁ := sp_le (k := k) (xs := y :: ys) fun x hx => Nat.le_of_succ_le_succ (h x hx)
      have h₂ : (y :: ys).length * 5 ^ k ≤ 4 * 5 ^ k := Nat.mul_le_mul_right _ hlen
      have h₃ : 5 ^ (k + 1) = 5 ^ k * 5 := Nat.pow_succ ..
      have h₄ := pow5_pos k
      omega

theorem wt_rm {θ : Form} : ∀ {Δ : List Form}, θ ∈ Δ → wt Δ = 5 ^ θ.weight + wt (rm θ Δ)
  | h :: t, hm => by
      by_cases e : θ = h
      · subst e; simp only [rm, if_true]; rfl
      · have hm' : θ ∈ t := by
          rcases List.mem_cons.1 hm with e' | h'
          · exact absurd e' e
          · exact h'
        have ih := wt_rm hm'
        simp only [rm, if_neg e]
        show 5 ^ h.weight + wt t = 5 ^ θ.weight + (5 ^ h.weight + wt (rm θ t))
        omega

theorem mem_rm_of_ne {θ₁ θ₂ : Form} : ∀ {Δ : List Form}, θ₂ ∈ Δ → θ₂ ≠ θ₁ → θ₂ ∈ rm θ₁ Δ
  | h :: t, hm, hne => by
      by_cases e : θ₁ = h
      · subst e
        simp only [rm, if_true]
        rcases List.mem_cons.1 hm with e' | h'
        · exact absurd e' hne
        · exact h'
      · simp only [rm, if_neg e]
        rcases List.mem_cons.1 hm with e' | h'
        · exact e' ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_rm_of_ne h' hne)

theorem wt_unbox_lt : ∀ {Δ : List Form}, Δ ≠ [] → wt (unbox Δ) < wt Δ
  | [], h => absurd rfl h
  | .box φ :: t, _ => by
      show 5 ^ φ.weight + wt (unbox t) < 5 ^ (φ.weight + 1) + wt t
      have := wt_unbox_le t
      have := pow5_lt (Nat.le_refl (φ.weight + 1))
      omega
  | .var _ :: t, _ => Nat.lt_of_le_of_lt (wt_unbox_le t) (Nat.lt_add_of_pos_left (pow5_pos _))
  | .bot :: t, _ => Nat.lt_of_le_of_lt (wt_unbox_le t) (Nat.lt_add_of_pos_left (pow5_pos _))
  | .and _ _ :: t, _ => Nat.lt_of_le_of_lt (wt_unbox_le t) (Nat.lt_add_of_pos_left (pow5_pos _))
  | .or _ _ :: t, _ => Nat.lt_of_le_of_lt (wt_unbox_le t) (Nat.lt_add_of_pos_left (pow5_pos _))
  | .imp _ _ :: t, _ => Nat.lt_of_le_of_lt (wt_unbox_le t) (Nat.lt_add_of_pos_left (pow5_pos _))
  | .dia _ :: t, _ => Nat.lt_of_le_of_lt (wt_unbox_le t) (Nat.lt_add_of_pos_left (pow5_pos _))

/-- `E9`: the call on `□⁻¹Δ`. -/
theorem pw_unbox_lt {Δ : List Form} (ϕ : Form) (h : Δ ≠ []) : pw (unbox Δ) ϕ < pw Δ ϕ :=
  Nat.add_lt_add_right (wt_unbox_lt h) _

/-- A formula `θ ∈ Δ` is replaced by lighter formulas `L`; the succedent does
not grow. -/
theorem pw_envLe {Δ U L : List Form} {θ ψ' ϕ : Form} (hθ : θ ∈ Δ)
    (hU : wt U ≤ wt (rm θ Δ)) (hlen : L.length ≤ 4)
    (hL : ∀ x ∈ L.map Form.weight, x + 1 ≤ θ.weight) (hψ : ψ'.weight ≤ ϕ.weight) :
    pw (L ++ U) ψ' < pw Δ ϕ := by
  have h₁ := wt_rm hθ
  have h₂ := wt_append L U
  have h₃ : wt L < 5 ^ θ.weight := by
    rw [wt_eq_sp]; exact sp_lt (by rw [List.length_map]; exact hlen) hL
  have h₄ : 5 ^ ψ'.weight ≤ 5 ^ ϕ.weight := Nat.pow_le_pow_right (by decide) hψ
  unfold pw; omega

/-- A formula `θ ∈ Δ` is replaced by lighter formulas `L`, and the new
succedent is lighter than `θ` too. -/
theorem pw_envNew {Δ U L : List Form} {θ ψ' ϕ : Form} (hθ : θ ∈ Δ)
    (hU : wt U ≤ wt (rm θ Δ)) (hlen : L.length ≤ 2)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: L.map Form.weight, x + 1 ≤ θ.weight) :
    pw (L ++ U) ψ' < pw Δ ϕ := by
  have h₁ := wt_rm hθ
  have h₂ := wt_append L U
  have h₃ : sp (ψ'.weight :: ψ'.weight :: L.map Form.weight) < 5 ^ θ.weight :=
    sp_lt (by simp only [List.length_cons, List.length_map]; omega) hL
  have h₄ : sp (ψ'.weight :: ψ'.weight :: L.map Form.weight)
      = 5 ^ ψ'.weight + (5 ^ ψ'.weight + wt L) := by rw [wt_eq_sp]; rfl
  unfold pw; omega

/-- The succedent `ϕ` is replaced by a lighter one and lighter formulas `L`
are added to the antecedent. -/
theorem pw_formNew {Δ U L : List Form} {ψ' ϕ : Form} (hU : wt U ≤ wt Δ) (hlen : L.length ≤ 2)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: L.map Form.weight, x + 1 ≤ ϕ.weight) :
    pw (L ++ U) ψ' < pw Δ ϕ := by
  have h₂ := wt_append L U
  have h₃ : sp (ψ'.weight :: ψ'.weight :: L.map Form.weight) < 5 ^ ϕ.weight :=
    sp_lt (by simp only [List.length_cons, List.length_map]; omega) hL
  have h₄ : sp (ψ'.weight :: ψ'.weight :: L.map Form.weight)
      = 5 ^ ψ'.weight + (5 ^ ψ'.weight + wt L) := by rw [wt_eq_sp]; rfl
  unfold pw; omega

/-- Two formulas are removed, `L` is lighter than the second; the succedent
does not grow. -/
theorem pw_env2Le {Δ U L : List Form} {θ₁ θ₂ ψ' ϕ : Form} (h₁ : θ₁ ∈ Δ)
    (h₂ : θ₂ ∈ rm θ₁ Δ) (hU : wt U ≤ wt (rm θ₂ (rm θ₁ Δ))) (hlen : L.length ≤ 4)
    (hL : ∀ x ∈ L.map Form.weight, x + 1 ≤ θ₂.weight) (hψ : ψ'.weight ≤ ϕ.weight) :
    pw (L ++ U) ψ' < pw Δ ϕ := by
  have e₁ := wt_rm h₁
  have e₂ := wt_rm h₂
  have e₃ := wt_append L U
  have h₃ : wt L < 5 ^ θ₂.weight := by
    rw [wt_eq_sp]; exact sp_lt (by rw [List.length_map]; exact hlen) hL
  have h₄ : 5 ^ ψ'.weight ≤ 5 ^ ϕ.weight := Nat.pow_le_pow_right (by decide) hψ
  have h₅ := pow5_pos θ₁.weight
  unfold pw; omega

/-- Two formulas are removed, `L` is lighter than the second and the new
succedent lighter than the first. -/
theorem pw_env2New {Δ U L : List Form} {θ₁ θ₂ ψ' ϕ : Form} (h₁ : θ₁ ∈ Δ)
    (h₂ : θ₂ ∈ rm θ₁ Δ) (hU : wt U ≤ wt (rm θ₂ (rm θ₁ Δ))) (hlen : L.length ≤ 4)
    (hL : ∀ x ∈ L.map Form.weight, x + 1 ≤ θ₂.weight) (hψ : ψ'.weight + 1 ≤ θ₁.weight) :
    pw (L ++ U) ψ' < pw Δ ϕ := by
  have e₁ := wt_rm h₁
  have e₂ := wt_rm h₂
  have e₃ := wt_append L U
  have h₃ : wt L < 5 ^ θ₂.weight := by
    rw [wt_eq_sp]; exact sp_lt (by rw [List.length_map]; exact hlen) hL
  have h₄ : 5 ^ ψ'.weight + 5 ^ ψ'.weight < 5 ^ θ₁.weight := two_pow5_lt hψ hψ
  unfold pw; omega

/-! The same lemmas with the untouched part `U` spelled out, so that the
removed formula is read off the goal. -/

theorem pw_envLe_rm {Δ L : List Form} {θ ψ' ϕ : Form} (hθ : θ ∈ Δ) (hlen : L.length ≤ 4)
    (hL : ∀ x ∈ L.map Form.weight, x + 1 ≤ θ.weight) (hψ : ψ'.weight ≤ ϕ.weight) :
    pw (L ++ rm θ Δ) ψ' < pw Δ ϕ := pw_envLe hθ (Nat.le_refl _) hlen hL hψ

theorem pw_envLe_unbox {Δ L : List Form} {θ ψ' ϕ : Form} (hθ : θ ∈ Δ) (hlen : L.length ≤ 4)
    (hL : ∀ x ∈ L.map Form.weight, x + 1 ≤ θ.weight) (hψ : ψ'.weight ≤ ϕ.weight) :
    pw (L ++ unbox (rm θ Δ)) ψ' < pw Δ ϕ := pw_envLe hθ (wt_unbox_le _) hlen hL hψ

theorem pw_envNew_rm {Δ L : List Form} {θ ψ' ϕ : Form} (hθ : θ ∈ Δ) (hlen : L.length ≤ 2)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: L.map Form.weight, x + 1 ≤ θ.weight) :
    pw (L ++ rm θ Δ) ψ' < pw Δ ϕ := pw_envNew hθ (Nat.le_refl _) hlen hL

theorem pw_envNew_unbox {Δ L : List Form} {θ ψ' ϕ : Form} (hθ : θ ∈ Δ) (hlen : L.length ≤ 2)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: L.map Form.weight, x + 1 ≤ θ.weight) :
    pw (L ++ unbox (rm θ Δ)) ψ' < pw Δ ϕ := pw_envNew hθ (wt_unbox_le _) hlen hL

theorem pw_env2Le_unbox {Δ L : List Form} {θ₁ θ₂ ψ' ϕ : Form} (h₁ : θ₁ ∈ Δ) (h₂ : θ₂ ∈ Δ)
    (hne : θ₂ ≠ θ₁) (hlen : L.length ≤ 4)
    (hL : ∀ x ∈ L.map Form.weight, x + 1 ≤ θ₂.weight) (hψ : ψ'.weight ≤ ϕ.weight) :
    pw (L ++ unbox (rm θ₂ (rm θ₁ Δ))) ψ' < pw Δ ϕ :=
  pw_env2Le h₁ (mem_rm_of_ne h₂ hne) (wt_unbox_le _) hlen hL hψ

theorem pw_env2New_unbox {Δ L : List Form} {θ₁ θ₂ ψ' ϕ : Form} (h₁ : θ₁ ∈ Δ) (h₂ : θ₂ ∈ Δ)
    (hne : θ₂ ≠ θ₁) (hlen : L.length ≤ 4)
    (hL : ∀ x ∈ L.map Form.weight, x + 1 ≤ θ₂.weight) (hψ : ψ'.weight + 1 ≤ θ₁.weight) :
    pw (L ++ unbox (rm θ₂ (rm θ₁ Δ))) ψ' < pw Δ ϕ :=
  pw_env2New h₁ (mem_rm_of_ne h₂ hne) (wt_unbox_le _) hlen hL hψ

theorem pw_formNew_unbox {Δ L : List Form} {ψ' ϕ : Form} (hlen : L.length ≤ 2)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: L.map Form.weight, x + 1 ≤ ϕ.weight) :
    pw (L ++ unbox Δ) ψ' < pw Δ ϕ := pw_formNew (wt_unbox_le _) hlen hL

theorem pw_formNew_same {Δ L : List Form} {ψ' ϕ : Form} (hlen : L.length ≤ 2)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: L.map Form.weight, x + 1 ≤ ϕ.weight) :
    pw (L ++ Δ) ψ' < pw Δ ϕ := pw_formNew (Nat.le_refl _) hlen hL

/-- Every weight is a successor; rewriting with this lets `omega` see that
weights are positive. -/
def Form.w0 (φ : Form) : Nat := φ.weight - 1

theorem Form.weight_eq (φ : Form) : φ.weight = φ.w0 + 1 := by
  have := φ.weight_pos; unfold Form.w0; omega

/-! ## The definition -/

/-- Closes a side condition "every exponent in the list is below the weight
of the principal formula". -/
local macro "wts" : tactic =>
  `(tactic| (intro x hx
             simp only [List.map, List.mem_cons, List.not_mem_nil, or_false, Form.weight] at hx ⊢
             simp only [Form.weight_eq] at hx ⊢
             omega))

/-- Closes "the new succedent is no heavier than the old one". -/
local macro "wle" : tactic =>
  `(tactic| first
      | exact Nat.le_refl _
      | exact Form.weight_pos _
      | (simp only [Form.weight]; omega))

/-- Closes the side goals of the measure lemmas. -/
local macro "side" : tactic =>
  `(tactic| first
      | assumption
      | decide
      | (simp only [List.length_cons, List.length_nil]; omega)
      | (intro x hx; cases hx; done)
      | wts
      | (intro e; cases e; done)
      | wle
      | (simp only [Form.weight]; omega))

/-- Closes one termination goal of `EA`. -/
local macro "dec" : tactic =>
  `(tactic| first
      | exact pw_unbox_lt _ (by assumption)
      | (refine pw_envLe_rm (L := [_, _]) ?_ ?_ ?_ ?_ <;> side)
      | (refine pw_envLe_rm (L := [_]) ?_ ?_ ?_ ?_ <;> side)
      | (refine pw_envLe_unbox (L := [_]) ?_ ?_ ?_ ?_ <;> side)
      | (refine pw_envLe_unbox (L := []) ?_ ?_ ?_ ?_ <;> side)
      | (refine pw_envNew_rm (L := [_, _]) ?_ ?_ ?_ <;> side)
      | (refine pw_envNew_unbox (L := []) ?_ ?_ ?_ <;> side)
      | (refine pw_env2Le_unbox (L := [_]) ?_ ?_ ?_ ?_ ?_ ?_ <;> side)
      | (refine pw_env2New_unbox (L := [_]) ?_ ?_ ?_ ?_ ?_ ?_ <;> side)
      | (refine pw_formNew_unbox (L := []) ?_ ?_ <;> side)
      | (refine pw_formNew_same (L := []) ?_ ?_ <;> side)
      | (refine pw_formNew_same (L := [_]) ?_ ?_ <;> side))

/-- **Definition 5** (`def_Ap_Ep`), Figure 3.  `EA p true Δ ϕ = Ep(Δ)` and
`EA p false Δ ϕ = Ap(Δ ⇒ ϕ)`.  Rocq `EA`.  The row names are the paper's. -/
def EA (p : Nat) : Bool → List Form → Form → Form
  | true, Δ, ϕ =>
      conj (
        -- (E9)  `□ Ep(□⁻¹Δ)` for `Δ ≠ ∅`.  Rocq `e_rule_9`.
        (if _h : Δ = [] then Form.top else □(EA p true (unbox Δ) ϕ))
        -- Rocq `e_rule`, one conjunct for each `θ ∈ Δ`.
        :: Δ.attach.map (fun θh =>
            match θh with
            -- (E0)
            | ⟨.bot, _⟩ => ⊥'
            -- (E1′), (E1″)
            | ⟨.var q, _⟩ => if p = q then Form.top else Form.var q
            -- (E2)
            | ⟨.and δ₁ δ₂, _⟩ => EA p true (δ₂ :: δ₁ :: rm (δ₁ ⋏ δ₂) Δ) ⊥'
            -- (E3)
            | ⟨.or δ₁ δ₂, _⟩ =>
                EA p true (δ₁ :: rm (δ₁ ⋎ δ₂) Δ) ϕ ⋎ EA p true (δ₂ :: rm (δ₁ ⋎ δ₂) Δ) ϕ
            -- (E5′), (E4″), (E4′)
            | ⟨.imp (.var q) δ, _⟩ =>
                if Form.var q ∈ Δ then EA p true (δ :: rm (Form.var q ⟶ δ) Δ) ϕ
                else if p = q then Form.top
                else Form.var q ⟶ EA p true (δ :: rm (Form.var q ⟶ δ) Δ) ϕ
            -- (E6)
            | ⟨.imp (.and δ₁ δ₂) δ₃, _⟩ =>
                EA p true ((δ₁ ⟶ (δ₂ ⟶ δ₃)) :: rm ((δ₁ ⋏ δ₂) ⟶ δ₃) Δ) ϕ
            -- (E7)
            | ⟨.imp (.or δ₁ δ₂) δ₃, _⟩ =>
                EA p true ((δ₂ ⟶ δ₃) :: (δ₁ ⟶ δ₃) :: rm ((δ₁ ⋎ δ₂) ⟶ δ₃) Δ) ϕ
            -- (E8′)
            | ⟨.imp (.imp δ₁ δ₂) δ₃, _⟩ =>
                (EA p true (δ₁ :: (δ₂ ⟶ δ₃) :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) ϕ
                  ⟶ EA p false (δ₁ :: (δ₂ ⟶ δ₃) :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) δ₂)
                ⟶ EA p true (δ₃ :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) ϕ
            | ⟨.imp .bot _, _⟩ => Form.top
            -- an instance of (E9)
            | ⟨.box φ, _⟩ => □(EA p true (φ :: unbox (rm (□φ) Δ)) ϕ)
            -- (E10)
            | ⟨.imp (.box δ₁) δ₂, _⟩ =>
                (□(EA p true (unbox (rm ((□δ₁) ⟶ δ₂) Δ)) ϕ
                    ⟶ EA p false (unbox (rm ((□δ₁) ⟶ δ₂) Δ)) δ₁))
                ⟶ EA p true (δ₂ :: rm ((□δ₁) ⟶ δ₂) Δ) ϕ
            -- (E11)
            | ⟨.dia φ, _⟩ => ◇(EA p true (φ :: unbox (rm (◇φ) Δ)) ϕ)
            -- (E13)
            | ⟨.imp (.dia δ₁) δ₂, _⟩ =>
                (◇(EA p true (unbox (rm ((◇δ₁) ⟶ δ₂) Δ)) ϕ
                    ⟶ EA p false (unbox (rm ((◇δ₁) ⟶ δ₂) Δ)) δ₁))
                ⟶ EA p true (δ₂ :: rm ((◇δ₁) ⟶ δ₂) Δ) ϕ)
        -- (E12)  Rocq `e_rule_12`, one conjunct for each pair `θ₁, θ₂ ∈ Δ`.
        ++ Δ.attach.flatMap (fun θh₁ => Δ.attach.map (fun θh₂ =>
            match θh₁, θh₂ with
            | ⟨.imp (.dia δ₁) δ₂, _⟩, ⟨.dia δ₃, _⟩ =>
                (□(EA p true (δ₃ :: unbox (rm (◇δ₃) (rm ((◇δ₁) ⟶ δ₂) Δ))) ϕ
                    ⟶ EA p false (δ₃ :: unbox (rm (◇δ₃) (rm ((◇δ₁) ⟶ δ₂) Δ))) δ₁))
                ⟶ EA p true (δ₂ :: rm ((◇δ₁) ⟶ δ₂) Δ) ϕ
            | _, _ => Form.top)))
  | false, Δ, ϕ =>
      disj (
        -- Rocq `a_rule_form`: the rows that read the succedent.
        (match ϕ with
          -- (A9)
          | .var q => if p = q then ⊥' else Form.var q
          -- (A11)
          | .and ϕ₁ ϕ₂ => EA p false Δ ϕ₁ ⋏ EA p false Δ ϕ₂
          -- (A12)
          | .or ϕ₁ ϕ₂ => EA p false Δ ϕ₁ ⋎ EA p false Δ ϕ₂
          -- (A13)
          | .imp ϕ₁ ϕ₂ => EA p true (ϕ₁ :: Δ) ⊥' ⟶ EA p false (ϕ₁ :: Δ) ϕ₂
          | .bot => ⊥'
          -- (A14)
          | .box δ => □(EA p true (unbox Δ) ⊥' ⟶ EA p false (unbox Δ) δ)
          -- (A18)
          | .dia δ => ◇(EA p true (unbox Δ) ⊥' ⟶ EA p false (unbox Δ) δ))
        -- Rocq `a_rule_env`, one disjunct for each `θ ∈ Δ`.
        :: Δ.attach.map (fun θh =>
            match θh with
            -- (A10), (A1″), (A1′)
            | ⟨.var q, _⟩ => if p = q then (if Form.var p = ϕ then Form.top else ⊥') else ⊥'
            -- (A2)
            | ⟨.and δ₁ δ₂, _⟩ => EA p false (δ₂ :: δ₁ :: rm (δ₁ ⋏ δ₂) Δ) ϕ
            -- (A3)
            | ⟨.or δ₁ δ₂, _⟩ =>
                (EA p true (δ₁ :: rm (δ₁ ⋎ δ₂) Δ) ϕ ⟶ EA p false (δ₁ :: rm (δ₁ ⋎ δ₂) Δ) ϕ)
                ⋏ (EA p true (δ₂ :: rm (δ₁ ⋎ δ₂) Δ) ϕ ⟶ EA p false (δ₂ :: rm (δ₁ ⋎ δ₂) Δ) ϕ)
            -- (A5′), (A4″), (A4′)
            | ⟨.imp (.var q) δ, _⟩ =>
                if Form.var q ∈ Δ then EA p false (δ :: rm (Form.var q ⟶ δ) Δ) ϕ
                else if p = q then ⊥'
                else Form.var q ⋏ EA p false (δ :: rm (Form.var q ⟶ δ) Δ) ϕ
            -- (A6)
            | ⟨.imp (.and δ₁ δ₂) δ₃, _⟩ =>
                EA p false ((δ₁ ⟶ (δ₂ ⟶ δ₃)) :: rm ((δ₁ ⋏ δ₂) ⟶ δ₃) Δ) ϕ
            -- (A7)
            | ⟨.imp (.or δ₁ δ₂) δ₃, _⟩ =>
                EA p false ((δ₂ ⟶ δ₃) :: (δ₁ ⟶ δ₃) :: rm ((δ₁ ⋎ δ₂) ⟶ δ₃) Δ) ϕ
            -- (A8′)
            | ⟨.imp (.imp δ₁ δ₂) δ₃, _⟩ =>
                (EA p true (δ₁ :: (δ₂ ⟶ δ₃) :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) ϕ
                  ⟶ EA p false (δ₁ :: (δ₂ ⟶ δ₃) :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) δ₂)
                ⋏ EA p false (δ₃ :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) ϕ
            | ⟨.bot, _⟩ => ⊥'
            | ⟨.imp .bot _, _⟩ => ⊥'
            | ⟨.box _, _⟩ => ⊥'
            -- (A15)
            | ⟨.imp (.box δ₁) δ₂, _⟩ =>
                (□(EA p true (unbox (rm ((□δ₁) ⟶ δ₂) Δ)) ϕ
                    ⟶ EA p false (unbox (rm ((□δ₁) ⟶ δ₂) Δ)) δ₁))
                ⋏ EA p false (δ₂ :: rm ((□δ₁) ⟶ δ₂) Δ) ϕ
            | ⟨.dia _, _⟩ => ⊥'
            -- (A19)
            | ⟨.imp (.dia δ₁) δ₂, _⟩ =>
                (◇(EA p true (unbox (rm ((◇δ₁) ⟶ δ₂) Δ)) ϕ
                    ⟶ EA p false (unbox (rm ((◇δ₁) ⟶ δ₂) Δ)) δ₁))
                ⋏ EA p false (δ₂ :: rm ((◇δ₁) ⟶ δ₂) Δ) ϕ)
        -- (A16)  Rocq `a_rule_env_form16`.
        ++ Δ.attach.map (fun θh =>
            match ϕ, θh with
            | .dia ψ, ⟨.dia δ, _⟩ =>
                □(EA p true (δ :: unbox (rm (◇δ) Δ)) ψ ⟶ EA p false (δ :: unbox (rm (◇δ) Δ)) ψ)
            | _, _ => ⊥')
        -- (A17)  Rocq `a_rule_env17`.
        ++ Δ.attach.flatMap (fun θh₁ => Δ.attach.map (fun θh₂ =>
            match θh₁, θh₂ with
            | ⟨.imp (.dia δ₁) δ₂, _⟩, ⟨.dia δ₃, _⟩ =>
                (□(EA p true (δ₃ :: unbox (rm (◇δ₃) (rm ((◇δ₁) ⟶ δ₂) Δ))) ϕ
                    ⟶ EA p false (δ₃ :: unbox (rm (◇δ₃) (rm ((◇δ₁) ⟶ δ₂) Δ))) δ₁))
                ⋏ EA p false (δ₂ :: rm ((◇δ₁) ⟶ δ₂) Δ) ϕ
            | _, _ => ⊥')))
termination_by _ Δ ϕ => pw Δ ϕ
decreasing_by
  all_goals dec

/-- `Ep(Δ)`.  Rocq `E`. -/
def Ep (p : Nat) (Δ : List Form) : Form := EA p true Δ ⊥'

/-- `Ap(Δ ⇒ ϕ)`.  Rocq `A`. -/
def Ap (p : Nat) (Δ : List Form) (ϕ : Form) : Form := EA p false Δ ϕ

/-- `∃p φ := Ep(φ)`.  Rocq `Ef`. -/
def Ef (p : Nat) (φ : Form) : Form := Ep p [φ]

/-- `∀p φ := Ap(⇒ φ)`.  Rocq `Af`. -/
def Af (p : Nat) (φ : Form) : Form := Ap p [] φ

end CK
