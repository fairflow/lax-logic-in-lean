import CK.Syntax

/-!
# `CK.G4CK` — the sequent calculus G4CK

Figure 2 of van der Giessen and Shillito, *Uniform interpolation with
constructive diamond*, arXiv:2602.16880v2, §3; Rocq `Provable` in
`theories/Sequent/G4CK/CKSequents.v` (commit `cd09fce`).  One constructor
per rule of the figure, in the figure's order; sixteen, as in Rocq.

## Encoding (divergence D1, representation only)

The paper's antecedents are finite multisets and Rocq uses `stdpp`'s
`gmultiset`.  Here an antecedent is a `List`, and each left rule carries a
field `h : Γ.Perm (principal :: Δ)`, the convention of
`LaxLogic/PLL/G4/G4.lean`.  So every index of every conclusion is a variable
or a constructor applied to variables, and `□⁻¹` (`unbox`) occurs in
premises only.  Two rules, `(p→L)` and `(◇→L)`, have a second formula that
the rule leaves in place (`p`, `◇γ`); it is a membership side condition, as in
`G4h.impLProp` of `LaxLogic/PLL/G4/G4H.lean` (divergence D4).

Provability is a `Prop` (divergence D2): Rocq's `Provable` lives in `Type`.
-/

namespace CK

open scoped Form

/-- **G4CK** (Figure 2).  `G4CK Γ φ` is `⊢_{G4CK} Γ ⇒ φ`. -/
inductive G4CK : List Form → Form → Prop
  /-- `(⊥L)`  `Γ,⊥ ⇒ φ`.  Rocq `ExFalso`. -/
  | botL {Γ : List Form} {φ : Form}
      (h : ⊥' ∈ Γ) : G4CK Γ φ
  /-- `(IdP)`  `Γ,p ⇒ p`.  Rocq `Atom`. -/
  | idP {Γ : List Form} {p : Nat}
      (h : Form.var p ∈ Γ) : G4CK Γ (.var p)
  /-- `(∧L)`  `Γ,φ,ψ ⇒ χ  /  Γ,φ∧ψ ⇒ χ`.  Rocq `AndL`. -/
  | andL {Γ Δ : List Form} {φ ψ χ : Form}
      (h : Γ.Perm ((φ ⋏ ψ) :: Δ)) :
      G4CK (φ :: ψ :: Δ) χ → G4CK Γ χ
  /-- `(∧R)`  `Γ ⇒ φ   Γ ⇒ ψ  /  Γ ⇒ φ∧ψ`.  Rocq `AndR`. -/
  | andR {Γ : List Form} {φ ψ : Form} :
      G4CK Γ φ → G4CK Γ ψ → G4CK Γ (φ ⋏ ψ)
  /-- `(∨L)`  `Γ,φ ⇒ χ   Γ,ψ ⇒ χ  /  Γ,φ∨ψ ⇒ χ`.  Rocq `OrL`. -/
  | orL {Γ Δ : List Form} {φ ψ χ : Form}
      (h : Γ.Perm ((φ ⋎ ψ) :: Δ)) :
      G4CK (φ :: Δ) χ → G4CK (ψ :: Δ) χ → G4CK Γ χ
  /-- `(∨R₁)`  `Γ ⇒ φ₁  /  Γ ⇒ φ₁∨φ₂`.  Rocq `OrR1`. -/
  | orR1 {Γ : List Form} {φ ψ : Form} :
      G4CK Γ φ → G4CK Γ (φ ⋎ ψ)
  /-- `(∨R₂)`  `Γ ⇒ φ₂  /  Γ ⇒ φ₁∨φ₂`.  Rocq `OrR2`. -/
  | orR2 {Γ : List Form} {φ ψ : Form} :
      G4CK Γ ψ → G4CK Γ (φ ⋎ ψ)
  /-- `(→R)`  `Γ,φ ⇒ ψ  /  Γ ⇒ φ→ψ`.  Rocq `ImpR`. -/
  | impR {Γ : List Form} {φ ψ : Form} :
      G4CK (φ :: Γ) ψ → G4CK Γ (φ ⟶ ψ)
  /-- `(∧→L)`  `Γ,φ→(ψ→χ) ⇒ δ  /  Γ,(φ∧ψ)→χ ⇒ δ`.  Rocq `ImpLAnd`. -/
  | impAndL {Γ Δ : List Form} {φ ψ χ δ : Form}
      (h : Γ.Perm (((φ ⋏ ψ) ⟶ χ) :: Δ)) :
      G4CK ((φ ⟶ (ψ ⟶ χ)) :: Δ) δ → G4CK Γ δ
  /-- `(∨→L)`  `Γ,φ→χ,ψ→χ ⇒ δ  /  Γ,(φ∨ψ)→χ ⇒ δ`.  Rocq `ImpLOr`. -/
  | impOrL {Γ Δ : List Form} {φ ψ χ δ : Form}
      (h : Γ.Perm (((φ ⋎ ψ) ⟶ χ) :: Δ)) :
      G4CK ((φ ⟶ χ) :: (ψ ⟶ χ) :: Δ) δ → G4CK Γ δ
  /-- `(p→L)`  `Γ,p,φ ⇒ χ  /  Γ,p,p→φ ⇒ χ`.  Rocq `ImpLVar`.
  The atom `p` occurs in the conclusion and in the premise alike, so it is
  recorded as a side condition `p ∈ Δ` and only `p→φ` is exposed
  (divergence D4). -/
  | impVarL {Γ Δ : List Form} {p : Nat} {φ χ : Form}
      (h : Γ.Perm ((Form.var p ⟶ φ) :: Δ)) (hp : Form.var p ∈ Δ) :
      G4CK (φ :: Δ) χ → G4CK Γ χ
  /-- `(→→L)`  `Γ,ψ→χ ⇒ φ→ψ   Γ,χ ⇒ δ  /  Γ,(φ→ψ)→χ ⇒ δ`.
  Rocq `ImpLImp`. -/
  | impImpL {Γ Δ : List Form} {φ ψ χ δ : Form}
      (h : Γ.Perm (((φ ⟶ ψ) ⟶ χ) :: Δ)) :
      G4CK ((ψ ⟶ χ) :: Δ) (φ ⟶ ψ) → G4CK (χ :: Δ) δ → G4CK Γ δ
  /-- `(□R)`  `□⁻¹Γ ⇒ φ  /  Γ ⇒ □φ`.  Rocq `BoxR`. -/
  | boxR {Γ : List Form} {φ : Form} :
      G4CK (unbox Γ) φ → G4CK Γ (□φ)
  /-- `(□→L)`  `□⁻¹Γ ⇒ φ   Γ,ψ ⇒ δ  /  Γ,□φ→ψ ⇒ δ`.  Rocq `ImpBox`.
  The principal formula is not a box, so `□⁻¹(Γ,□φ→ψ) = □⁻¹Γ`. -/
  | impBoxL {Γ Δ : List Form} {φ ψ δ : Form}
      (h : Γ.Perm (((□φ) ⟶ ψ) :: Δ)) :
      G4CK (unbox Δ) φ → G4CK (ψ :: Δ) δ → G4CK Γ δ
  /-- `(◇→L)`  `□⁻¹Γ,γ ⇒ φ   Γ,◇γ,ψ ⇒ δ  /  Γ,◇γ,◇φ→ψ ⇒ δ`.
  Rocq `ImpDiam`.  As for `(p→L)`, `◇γ` occurs in the conclusion and in the
  second premise alike and is recorded as `◇γ ∈ Δ` (divergence D4); it is not
  a box, so `□⁻¹(Γ,◇γ) = □⁻¹Γ` and the first premise is `γ, □⁻¹Δ ⇒ φ`. -/
  | impDiaL {Γ Δ : List Form} {γ φ ψ δ : Form}
      (h : Γ.Perm (((◇φ) ⟶ ψ) :: Δ)) (hγ : (◇γ) ∈ Δ) :
      G4CK (γ :: unbox Δ) φ → G4CK (ψ :: Δ) δ → G4CK Γ δ
  /-- `(◇L)`  `□⁻¹Γ,φ ⇒ ψ  /  Γ,◇φ ⇒ ◇ψ`.  Rocq `DiamL`. -/
  | diaL {Γ Δ : List Form} {φ ψ : Form}
      (h : Γ.Perm ((◇φ) :: Δ)) :
      G4CK (φ :: unbox Δ) ψ → G4CK Γ (◇ψ)

end CK
