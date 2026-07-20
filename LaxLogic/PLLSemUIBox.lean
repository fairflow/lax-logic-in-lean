import LaxLogic.PLLSemUI

/-!
# The box-commutation law: `∀p.◯φ = ◯(∀p.φ)`, `∃p.◯φ = ◯(∃p.φ)`

The one-◯ two-variable sweep found every ◯-headed row obeying

    ∀p.◯φ = ◯(∀p.φ)          ∃p.◯φ = ◯(∃p.φ)

(retrodicting the old values `∀p.◯p = ◯⊥ = ◯(∀p.p)` and
`∀p.◯(◯p⊃p) = ◯⊥ = ◯(∀p.(◯p⊃p))`).  This file proves the law at the
spec level:

    semAll_box : IsSemAll p φ ψ → BoxRowAmalgAll p φ ψ →
                 IsSemAll p ◯φ ◯ψ
    semEx_box  : IsSemEx p φ ψ → BoxRowAmalgEx p φ ψ →
                 IsSemEx p ◯φ ◯ψ

Each law has a FREE half, proved here unconditionally inside the
theorems: the ∀-side forward direction (a ◯ψ-world's variants force
◯φ: transfer ◯ψ across the bisimulation, then each ψ-witness forces φ
by its own spec at the identity variant) and the ∃-side backward
direction (a variant forcing ◯φ pulls back: i-forth the future,
take the witness, m-back it, and the pulled-back witness forces ψ by
the ∃-spec).  The other half of each is the ∀∃-AMALGAMATION and is
isolated as a residue with the quantifier machinery already
discharged — a pure model-surgery statement:

* `BoxRowAmalgAll p φ ψ`: a constraint row refuting ψ POINTWISE
  amalgamates into a single p-variant refuting ◯φ at (the image of)
  the row's base;
* `BoxRowAmalgEx p φ ψ`: pointwise ψ-witnesses in every future row
  amalgamate into a single p-variant forcing ◯φ.

These residues are exactly where the canonical-model descriptions
(the Θ-promises) must enter; the sweep certifies their consequences
throughout the one-◯ two-variable fragment to weight 6.  With the
law, the ◯-clause of the definability induction reduces to the
residues, leaving ⊃ and ∨ as the genuinely quantificational
connectives — the same division of labour as in IPC.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-- **∀-side residue (the amalgamation)**: a row refuting ψ pointwise
amalgamates into one p-variant refuting ◯φ at the row's base. -/
def BoxRowAmalgAll (p : String) (φ ψ : PLLFormula) : Prop :=
  ∀ (C : ConstraintModel) (x : C.W),
    (∀ y, C.Rm x y → ¬ C.force y ψ) →
    ∃ (N : ConstraintModel) (B : PBisim p C N) (x' : N.W),
      B.Z x x' ∧ ¬ N.force x' φ.somehow

/-- **∃-side residue (the amalgamation)**: pointwise ψ-witnesses in
every future row amalgamate into one p-variant forcing ◯φ. -/
def BoxRowAmalgEx (p : String) (φ ψ : PLLFormula) : Prop :=
  ∀ (C : ConstraintModel) (w : C.W),
    (∀ x, C.Ri w x → ∃ y, C.Rm x y ∧ C.force y ψ) →
    ∃ (N : ConstraintModel) (B : PBisim p C N) (w' : N.W),
      B.Z w w' ∧ N.force w' φ.somehow

/-- **Box-commutation, ∀-side**: if ψ is the semantic ∀p-value of φ
and the ∀-amalgamation residue holds, then ◯ψ is the semantic
∀p-value of ◯φ.  The forward half is unconditional. -/
theorem semAll_box {p : String} {φ ψ : PLLFormula}
    (h : IsSemAll p φ ψ) (hAm : BoxRowAmalgAll p φ ψ) :
    IsSemAll p φ.somehow ψ.somehow := by
  obtain ⟨hpf, hspec⟩ := h
  have hAψ : ∀ a ∈ ψ.atoms, a ≠ p := fun a ha he => hpf (he ▸ ha)
  refine ⟨hpf, ?_⟩
  intro C w
  constructor
  · intro hw v hv N B v' hZ
    have hbox : N.force v' ψ.somehow :=
      (force_iff_of_bisim B
        (show ∀ a ∈ ψ.somehow.atoms, a ≠ p from hAψ) hZ).mp
        (C.force_hered hv hw)
    intro x' hx'
    obtain ⟨y', hy', hψ'⟩ := hbox x' hx'
    exact ⟨y', hy',
      (hspec N y').mp hψ' y' (N.refl_i y') N (ABisim.id _ N) y' rfl⟩
  · intro h' x hwx
    by_contra hno
    have hrow : ∀ y, C.Rm x y → ¬ C.force y ψ :=
      fun y hy hψ => hno ⟨y, hy, hψ⟩
    obtain ⟨N, B, x', hZ, hnbox⟩ := hAm C x hrow
    exact hnbox (h' x hwx N B x' hZ)

/-- **Box-commutation, ∃-side**: if ψ is the semantic ∃p-value of φ
and the ∃-amalgamation residue holds, then ◯ψ is the semantic
∃p-value of ◯φ.  The backward half is unconditional. -/
theorem semEx_box {p : String} {φ ψ : PLLFormula}
    (h : IsSemEx p φ ψ) (hAm : BoxRowAmalgEx p φ ψ) :
    IsSemEx p φ.somehow ψ.somehow := by
  obtain ⟨hpf, hspec⟩ := h
  refine ⟨hpf, ?_⟩
  intro C w
  constructor
  · intro hw
    exact hAm C w hw
  · rintro ⟨N, B, w', hZ, hbox⟩
    intro x hx
    obtain ⟨x', hx', hZx⟩ := B.iforth hZ hx
    obtain ⟨y', hy', hφ'⟩ := hbox x' hx'
    obtain ⟨y, hy, hZy⟩ := B.mback hZx hy'
    exact ⟨y, hy, (hspec C y).mpr ⟨N, B, y', hZy, hφ'⟩⟩

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.semAll_box' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semAll_box

/-- info: 'PLLND.SemUI.semEx_box' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms semEx_box

end SemUI
end PLLND
