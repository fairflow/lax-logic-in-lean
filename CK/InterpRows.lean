/-
# The rows of Figure 3 as functions of the recursive calls, and the unfolding of `EA`

Source: I. van der Giessen and I. Shillito, "Uniform interpolation with
constructive diamond", arXiv:2602.16880, §4, Figure 3.  Rocq:
`theories/Sequent/G4CK/CKPropQuantifiers.v` of github.com/ianshil/CK,
`e_rule`, `e_rule_9`, `e_rule_12`, `a_rule_form`, `a_rule_env`,
`a_rule_env_form16`, `a_rule_env17`.

The Rocq rows take the recursive calls as functions defined below the current
pointed environment only; here `EA` is a total function, so the rows take
plain functions `E A : List Form → Form → Form`, and the Rocq congruence
lemmas (`…_cong_strong`) are not needed.
-/
import CK.Interp

namespace CK

open Form

variable (p : Nat) (E A : List Form → Form → Form) (Δ : List Form) (ϕ : Form)

/-- Row (E9).  Rocq `e_rule_9`. -/
def eRow9 : Form := if Δ = [] then Form.top else □(E (unbox Δ) ϕ)

/-- The rows for one antecedent formula.  Rocq `e_rule`. -/
def eRow : Form → Form
  | .bot => ⊥'
  | .var q => if p = q then Form.top else Form.var q
  | .and δ₁ δ₂ => E (δ₂ :: δ₁ :: rm (δ₁ ⋏ δ₂) Δ) ⊥'
  | .or δ₁ δ₂ => E (δ₁ :: rm (δ₁ ⋎ δ₂) Δ) ϕ ⋎ E (δ₂ :: rm (δ₁ ⋎ δ₂) Δ) ϕ
  | .imp (.var q) δ =>
      if Form.var q ∈ Δ then E (δ :: rm (Form.var q ⟶ δ) Δ) ϕ
      else if p = q then Form.top
      else Form.var q ⟶ E (δ :: rm (Form.var q ⟶ δ) Δ) ϕ
  | .imp (.and δ₁ δ₂) δ₃ => E ((δ₁ ⟶ (δ₂ ⟶ δ₃)) :: rm ((δ₁ ⋏ δ₂) ⟶ δ₃) Δ) ϕ
  | .imp (.or δ₁ δ₂) δ₃ => E ((δ₂ ⟶ δ₃) :: (δ₁ ⟶ δ₃) :: rm ((δ₁ ⋎ δ₂) ⟶ δ₃) Δ) ϕ
  | .imp (.imp δ₁ δ₂) δ₃ =>
      (E (δ₁ :: (δ₂ ⟶ δ₃) :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) ϕ
        ⟶ A (δ₁ :: (δ₂ ⟶ δ₃) :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) δ₂)
      ⟶ E (δ₃ :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) ϕ
  | .imp .bot _ => Form.top
  | .box φ => □(E (φ :: unbox (rm (□φ) Δ)) ϕ)
  | .imp (.box δ₁) δ₂ =>
      (□(E (unbox (rm ((□δ₁) ⟶ δ₂) Δ)) ϕ ⟶ A (unbox (rm ((□δ₁) ⟶ δ₂) Δ)) δ₁))
      ⟶ E (δ₂ :: rm ((□δ₁) ⟶ δ₂) Δ) ϕ
  | .dia φ => ◇(E (φ :: unbox (rm (◇φ) Δ)) ϕ)
  | .imp (.dia δ₁) δ₂ =>
      (◇(E (unbox (rm ((◇δ₁) ⟶ δ₂) Δ)) ϕ ⟶ A (unbox (rm ((◇δ₁) ⟶ δ₂) Δ)) δ₁))
      ⟶ E (δ₂ :: rm ((◇δ₁) ⟶ δ₂) Δ) ϕ

/-- Row (E12), for a pair of antecedent formulas.  Rocq `e_rule_12`. -/
def eRow12 : Form → Form → Form
  | .imp (.dia δ₁) δ₂, .dia δ₃ =>
      (□(E (δ₃ :: unbox (rm (◇δ₃) (rm ((◇δ₁) ⟶ δ₂) Δ))) ϕ
          ⟶ A (δ₃ :: unbox (rm (◇δ₃) (rm ((◇δ₁) ⟶ δ₂) Δ))) δ₁))
      ⟶ E (δ₂ :: rm ((◇δ₁) ⟶ δ₂) Δ) ϕ
  | _, _ => Form.top

/-- The rows that read the succedent.  Rocq `a_rule_form`. -/
def aForm : Form :=
  match ϕ with
  | .var q => if p = q then ⊥' else Form.var q
  | .and ϕ₁ ϕ₂ => A Δ ϕ₁ ⋏ A Δ ϕ₂
  | .or ϕ₁ ϕ₂ => A Δ ϕ₁ ⋎ A Δ ϕ₂
  | .imp ϕ₁ ϕ₂ => E (ϕ₁ :: Δ) ⊥' ⟶ A (ϕ₁ :: Δ) ϕ₂
  | .bot => ⊥'
  | .box δ => □(E (unbox Δ) ⊥' ⟶ A (unbox Δ) δ)
  | .dia δ => ◇(E (unbox Δ) ⊥' ⟶ A (unbox Δ) δ)

/-- The rows for one antecedent formula.  Rocq `a_rule_env`. -/
def aEnv : Form → Form
  | .var q => if p = q then (if Form.var p = ϕ then Form.top else ⊥') else ⊥'
  | .and δ₁ δ₂ => A (δ₂ :: δ₁ :: rm (δ₁ ⋏ δ₂) Δ) ϕ
  | .or δ₁ δ₂ =>
      (E (δ₁ :: rm (δ₁ ⋎ δ₂) Δ) ϕ ⟶ A (δ₁ :: rm (δ₁ ⋎ δ₂) Δ) ϕ)
      ⋏ (E (δ₂ :: rm (δ₁ ⋎ δ₂) Δ) ϕ ⟶ A (δ₂ :: rm (δ₁ ⋎ δ₂) Δ) ϕ)
  | .imp (.var q) δ =>
      if Form.var q ∈ Δ then A (δ :: rm (Form.var q ⟶ δ) Δ) ϕ
      else if p = q then ⊥'
      else Form.var q ⋏ A (δ :: rm (Form.var q ⟶ δ) Δ) ϕ
  | .imp (.and δ₁ δ₂) δ₃ => A ((δ₁ ⟶ (δ₂ ⟶ δ₃)) :: rm ((δ₁ ⋏ δ₂) ⟶ δ₃) Δ) ϕ
  | .imp (.or δ₁ δ₂) δ₃ => A ((δ₂ ⟶ δ₃) :: (δ₁ ⟶ δ₃) :: rm ((δ₁ ⋎ δ₂) ⟶ δ₃) Δ) ϕ
  | .imp (.imp δ₁ δ₂) δ₃ =>
      (E (δ₁ :: (δ₂ ⟶ δ₃) :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) ϕ
        ⟶ A (δ₁ :: (δ₂ ⟶ δ₃) :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) δ₂)
      ⋏ A (δ₃ :: rm ((δ₁ ⟶ δ₂) ⟶ δ₃) Δ) ϕ
  | .bot => ⊥'
  | .imp .bot _ => ⊥'
  | .box _ => ⊥'
  | .imp (.box δ₁) δ₂ =>
      (□(E (unbox (rm ((□δ₁) ⟶ δ₂) Δ)) ϕ ⟶ A (unbox (rm ((□δ₁) ⟶ δ₂) Δ)) δ₁))
      ⋏ A (δ₂ :: rm ((□δ₁) ⟶ δ₂) Δ) ϕ
  | .dia _ => ⊥'
  | .imp (.dia δ₁) δ₂ =>
      (◇(E (unbox (rm ((◇δ₁) ⟶ δ₂) Δ)) ϕ ⟶ A (unbox (rm ((◇δ₁) ⟶ δ₂) Δ)) δ₁))
      ⋏ A (δ₂ :: rm ((◇δ₁) ⟶ δ₂) Δ) ϕ

/-- Row (A16).  Rocq `a_rule_env_form16`. -/
def aRow16 (θ : Form) : Form :=
  match ϕ, θ with
  | .dia ψ, .dia δ => □(E (δ :: unbox (rm (◇δ) Δ)) ψ ⟶ A (δ :: unbox (rm (◇δ) Δ)) ψ)
  | _, _ => ⊥'

/-- Row (A17), for a pair of antecedent formulas.  Rocq `a_rule_env17`. -/
def aRow17 : Form → Form → Form
  | .imp (.dia δ₁) δ₂, .dia δ₃ =>
      (□(E (δ₃ :: unbox (rm (◇δ₃) (rm ((◇δ₁) ⟶ δ₂) Δ))) ϕ
          ⟶ A (δ₃ :: unbox (rm (◇δ₃) (rm ((◇δ₁) ⟶ δ₂) Δ))) δ₁))
      ⋏ A (δ₂ :: rm ((◇δ₁) ⟶ δ₂) Δ) ϕ
  | _, _ => ⊥'

theorem attach_map_eq {α β : Type} (l : List α) (f : α → β) (g : {x // x ∈ l} → β)
    (h : ∀ x, g x = f x.1) : l.attach.map g = l.map f := by
  rw [show g = fun x => f x.1 from funext h]
  exact List.attach_map_val

theorem attach_flatMap_eq {α β : Type} (l : List α) (f : α → List β)
    (g : {x // x ∈ l} → List β) (h : ∀ x, g x = f x.1) : l.attach.flatMap g = l.flatMap f := by
  rw [List.flatMap_def, List.flatMap_def, attach_map_eq l f g h]

/-- The unfolding of `Ep`. -/
theorem EA_true : EA p true Δ ϕ =
    conj (eRow9 (EA p true) Δ ϕ
      :: Δ.map (eRow p (EA p true) (EA p false) Δ ϕ)
      ++ Δ.flatMap (fun θ₁ => Δ.map (eRow12 (EA p true) (EA p false) Δ ϕ θ₁))) := by
  rw [EA]
  refine congrArg conj (congr (congrArg HAppend.hAppend (congr (congrArg List.cons ?_) ?_)) ?_)
  · unfold eRow9
    by_cases h : Δ = []
    · rw [dif_pos h, if_pos h]
    · rw [dif_neg h, if_neg h]
  · apply attach_map_eq
    rintro ⟨θ, hθ⟩
    rcases θ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> rfl
  · apply attach_flatMap_eq
    rintro ⟨θ₁, h₁⟩
    apply attach_map_eq
    rintro ⟨θ₂, h₂⟩
    rcases θ₁ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> rcases θ₂ with _|_|_|_|_|_|_ <;> rfl

/-- The unfolding of `Ap`. -/
theorem EA_false : EA p false Δ ϕ =
    disj (aForm p (EA p true) (EA p false) Δ ϕ
      :: Δ.map (aEnv p (EA p true) (EA p false) Δ ϕ)
      ++ Δ.map (aRow16 (EA p true) (EA p false) Δ ϕ)
      ++ Δ.flatMap (fun θ₁ => Δ.map (aRow17 (EA p true) (EA p false) Δ ϕ θ₁))) := by
  cases ϕ <;>
  · rw [EA]
    refine congrArg disj (congr (congrArg HAppend.hAppend (congr (congrArg HAppend.hAppend
      (congr (congrArg List.cons ?_) ?_)) ?_)) ?_)
    · rfl
    · apply attach_map_eq
      rintro ⟨θ, hθ⟩
      rcases θ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> rfl
    · apply attach_map_eq
      rintro ⟨θ, hθ⟩
      cases θ <;> rfl
    · apply attach_flatMap_eq
      rintro ⟨θ₁, h₁⟩
      apply attach_map_eq
      rintro ⟨θ₂, h₂⟩
      rcases θ₁ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> rcases θ₂ with _|_|_|_|_|_|_ <;> rfl

#print axioms EA_true
#print axioms EA_false

end CK
