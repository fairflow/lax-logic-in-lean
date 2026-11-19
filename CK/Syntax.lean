/-!
# `CK.Syntax` — formulas, weight, `□⁻¹Γ`

Transcribed from

* I. van der Giessen and I. Shillito, *Uniform interpolation with
  constructive diamond*, arXiv:2602.16880v2 (27 May 2026), §2;
* its Rocq development, `github.com/ianshil/CK`, branch
  `uniform_interpolation`, commit `cd09fce`:
  `theories/Syntax/im_syntax.v` (`form`), `theories/Sequent/syntax_facts.v`
  (`weight`), `theories/Sequent/Environments.v` (`open_boxes`).

Nothing here is new; the Lean text is written afresh, not copied.

This file imports nothing.
-/

namespace CK

/-- The language `𝓛` of §2 (Rocq `form`):
`φ ::= p | ⊥ | φ ∧ φ | φ ∨ φ | φ → φ | □φ | ◇φ`.
`¬φ := φ → ⊥` and `⊤ := ¬⊥` are abbreviations, as in the paper. -/
inductive Form where
  /-- A propositional variable `p ∈ Prop`. -/
  | var (p : Nat)
  /-- `⊥`. -/
  | bot
  /-- `φ ∧ ψ`. -/
  | and (φ ψ : Form)
  /-- `φ ∨ ψ`. -/
  | or (φ ψ : Form)
  /-- `φ → ψ`. -/
  | imp (φ ψ : Form)
  /-- `□φ`. -/
  | box (φ : Form)
  /-- `◇φ`. -/
  | dia (φ : Form)
  deriving DecidableEq, Repr

namespace Form

@[inherit_doc] scoped notation "⊥'" => Form.bot
@[inherit_doc] scoped infixr:35 " ⋏ " => Form.and
@[inherit_doc] scoped infixr:30 " ⋎ " => Form.or
@[inherit_doc] scoped infixr:25 " ⟶ " => Form.imp
@[inherit_doc] scoped prefix:75 "□" => Form.box
@[inherit_doc] scoped prefix:75 "◇" => Form.dia

/-- `¬φ := φ → ⊥` (§2). -/
def neg (φ : Form) : Form := φ ⟶ ⊥'

/-- `⊤ := ¬⊥` (§2). -/
def top : Form := neg ⊥'

/-- **Definition 1** (`def:weight`; Rocq `weight`):
`w(⊥) = w(p) = 1`, `w(ψ ∨ χ) = w(ψ → χ) = w(ψ) + w(χ) + 1`,
`w(ψ ∧ χ) = w(ψ) + w(χ) + 2`, `w(□ψ) = w(◇ψ) = w(ψ) + 1`. -/
def weight : Form → Nat
  | var _ => 1
  | bot => 1
  | and φ ψ => weight φ + weight ψ + 2
  | or φ ψ => weight φ + weight ψ + 1
  | imp φ ψ => weight φ + weight ψ + 1
  | box φ => weight φ + 1
  | dia φ => weight φ + 1

/-- The variables of a formula (the paper's `Vars(φ)`). -/
def Occurs (p : Nat) : Form → Prop
  | var q => q = p
  | bot => False
  | and φ ψ => Occurs p φ ∨ Occurs p ψ
  | or φ ψ => Occurs p φ ∨ Occurs p ψ
  | imp φ ψ => Occurs p φ ∨ Occurs p ψ
  | box φ => Occurs p φ
  | dia φ => Occurs p φ

end Form

/-- `□⁻¹Γ := {φ | □φ ∈ Γ}` (§2), with multiplicity; Rocq `open_boxes`,
in its list form `l_open_boxes`. -/
def unbox : List Form → List Form
  | [] => []
  | .box φ :: Γ => φ :: unbox Γ
  | _ :: Γ => unbox Γ

end CK
