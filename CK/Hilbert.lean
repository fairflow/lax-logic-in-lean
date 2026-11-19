import CK.Syntax

/-!
# `CK.Hilbert` — the generalised Hilbert calculus CKH

Figure 1 of van der Giessen and Shillito, arXiv:2602.16880v2, §2, which the
paper takes from de Groot, Shillito and Clouston (LICS 2025); Rocq
`IAxioms`, `MAxioms`, `extCKH_prv` and `CKH_prv` in `theories/GHC/CKH.v`
(commit `cd09fce`).

A consecution is `Γ ⊢ φ` with `Γ` a **set** of formulas, here a predicate
`Form → Prop`, as Rocq's `Ensembles`.  `(Nec)` has the empty set in its
premise.
-/

namespace CK

open scoped Form

/-- The axioms `A₁`–`A₉`, `K□`, `K◇` of Figure 1.  Rocq `IAxioms` and
`MAxioms` (there with an equation `F = …`; here the instance is the index,
which is a constructor form). -/
inductive Axiom : Form → Prop
  /-- `A₁`  `φ → (ψ → φ)`. -/
  | a1 (φ ψ : Form) : Axiom (φ ⟶ (ψ ⟶ φ))
  /-- `A₂`  `(φ → (ψ → χ)) → (φ → ψ) → (φ → χ)`. -/
  | a2 (φ ψ χ : Form) : Axiom ((φ ⟶ (ψ ⟶ χ)) ⟶ ((φ ⟶ ψ) ⟶ (φ ⟶ χ)))
  /-- `A₃`  `φ → (φ ∨ ψ)`. -/
  | a3 (φ ψ : Form) : Axiom (φ ⟶ (φ ⋎ ψ))
  /-- `A₄`  `ψ → (φ ∨ ψ)`. -/
  | a4 (φ ψ : Form) : Axiom (ψ ⟶ (φ ⋎ ψ))
  /-- `A₅`  `(φ → χ) → (ψ → χ) → ((φ ∨ ψ) → χ)`. -/
  | a5 (φ ψ χ : Form) : Axiom ((φ ⟶ χ) ⟶ ((ψ ⟶ χ) ⟶ ((φ ⋎ ψ) ⟶ χ)))
  /-- `A₆`  `(φ ∧ ψ) → φ`. -/
  | a6 (φ ψ : Form) : Axiom ((φ ⋏ ψ) ⟶ φ)
  /-- `A₇`  `(φ ∧ ψ) → ψ`. -/
  | a7 (φ ψ : Form) : Axiom ((φ ⋏ ψ) ⟶ ψ)
  /-- `A₈`  `(φ → ψ) → (φ → χ) → (φ → (ψ ∧ χ))`. -/
  | a8 (φ ψ χ : Form) : Axiom ((φ ⟶ ψ) ⟶ ((φ ⟶ χ) ⟶ (φ ⟶ (ψ ⋏ χ))))
  /-- `A₉`  `⊥ → φ`. -/
  | a9 (φ : Form) : Axiom (⊥' ⟶ φ)
  /-- `K□`  `□(φ → ψ) → (□φ → □ψ)`. -/
  | kBox (φ ψ : Form) : Axiom ((□(φ ⟶ ψ)) ⟶ ((□φ) ⟶ □ψ))
  /-- `K◇`  `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kDia (φ ψ : Form) : Axiom ((□(φ ⟶ ψ)) ⟶ ((◇φ) ⟶ ◇ψ))

/-- **CKH** (Figure 1).  `CKH Γ φ` is `Γ ⊢_{CKH} φ`.  Rocq `CKH_prv`. -/
inductive CKH : (Form → Prop) → Form → Prop
  /-- `(Ax)`  `φ` is an instance of an axiom. -/
  | ax {Γ : Form → Prop} {φ : Form} (h : Axiom φ) : CKH Γ φ
  /-- `(El)`  `φ ∈ Γ`. -/
  | el {Γ : Form → Prop} {φ : Form} (h : Γ φ) : CKH Γ φ
  /-- `(Nec)`  `∅ ⊢ φ  /  Γ ⊢ □φ`. -/
  | nec {Γ : Form → Prop} {φ : Form} : CKH (fun _ => False) φ → CKH Γ (□φ)
  /-- `(MP)`  `Γ ⊢ φ   Γ ⊢ φ → ψ  /  Γ ⊢ ψ`. -/
  | mp {Γ : Form → Prop} {φ ψ : Form} : CKH Γ φ → CKH Γ (φ ⟶ ψ) → CKH Γ ψ

end CK
