import LaxLogic.PLL.SemUI.SemUI

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

/-! ## First wave at the residues: the promise mechanism discharges the
decoration-refutable class

The levelled model IS the canonical Θ-descriptions in model clothing
(its own docstring: the p-worlds are constraint-reachable but never on
the constraint cone of level 0).  Level-0 row-rigidity says: a row all
of whose promises are withheld.  That discharges `BoxRowAmalgAll p φ ⊥`
for every φ refuted at level 0 over a non-fallible base
(`Lob0Refutes`), which covers the decoration-refutable ⊥-valued rows —
and the law then GENERATES values:

    ∀p.◯(p ∨ ¬p) = ◯⊥      (semAll_box_em — NEW)
    ∀p.◯(¬¬p ⊃ p) = ◯⊥     (semAll_box_nn — NEW)
    ∀p.◯p = ◯⊥             (semAll_box_p' — re-derived, consistency)

Dually `boxRowAmalgEx_prop` (decorate p everywhere) gives
`∃p.◯p = ◯⊤` (`semEx_box_p`).  NOT covered: φ = ◯p ⊃ p (its level-0
refutation fails — level-0 rows may lack ◯p entirely, so `◯p ⊃ p`
holds vacuously); `semAll_box_lob` reached that row through the
level-1 argument, and the general residues remain OPEN — the full
canonical-model graft is the second wave. -/

/-- φ is refuted at level 0 of the Löb variant over every non-fallible
base world — the "all promises withheld" refutation class. -/
def Lob0Refutes (p : String) (φ : PLLFormula) : Prop :=
  ∀ (C : ConstraintModel) (z : C.W), z ∉ C.F →
    ¬ (lobVariant C p).force (z, 0) φ

/-- **The ∀-residue for the value ⊥, discharged on the
`Lob0Refutes` class**: level 0 of the Löb variant is
constraint-rigid, so a fallibility-free row there has every promise
withheld — no member forces φ, and ◯φ fails at the base. -/
theorem boxRowAmalgAll_lob0 {p : String} {φ : PLLFormula}
    (h : Lob0Refutes p φ) : BoxRowAmalgAll p φ .falsePLL := by
  intro C x hrow
  refine ⟨lobVariant C p, lobVariant_pbisim C p, (x, 0), rfl, ?_⟩
  intro hbox
  obtain ⟨d, hd, hφ⟩ := hbox (x, 0) ((lobVariant C p).refl_i (x, 0))
  obtain ⟨z, j⟩ := d
  have hj : j = 0 := by
    rcases hd.2 with h0 | ⟨h1, -⟩
    · exact h0.symm
    · exact absurd h1 (by omega)
  subst hj
  exact h C z (fun hF => hrow z hd.1 hF) hφ

/-- `p` itself is level-0 refuted. -/
theorem lob0_prop (p : String) : Lob0Refutes p (.prop p) := by
  intro C z hz hp
  have hp' : (z, 0) ∈ (if p = p then
      {a : (lobModel C).W | 2 ≤ a.2 ∨ a.1 ∈ C.F} else (lobModel C).V p) := hp
  rw [if_pos rfl] at hp'
  rcases hp' with h2 | hF
  · omega
  · exact hz hF

/-- `p ∨ ¬p` is level-0 refuted: level 0 is undecorated, and level 2
above it forces p non-fallibly. -/
theorem lob0_em (p : String) :
    Lob0Refutes p
      ((PLLFormula.prop p).or ((PLLFormula.prop p).ifThen .falsePLL)) := by
  intro C z hz h
  rcases h with hp | hnp
  · have hp' : (z, 0) ∈ (if p = p then
        {a : (lobModel C).W | 2 ≤ a.2 ∨ a.1 ∈ C.F} else (lobModel C).V p) := hp
    rw [if_pos rfl] at hp'
    rcases hp' with h2 | hF
    · omega
    · exact hz hF
  · have h02 : (lobVariant C p).Ri (z, 0) (z, 2) := ⟨C.refl_i z, by omega⟩
    have hp2 : (lobVariant C p).force (z, 2) (.prop p) := by
      show (z, 2) ∈ (if p = p then
        {a : (lobModel C).W | 2 ≤ a.2 ∨ a.1 ∈ C.F} else (lobModel C).V p)
      rw [if_pos rfl]
      exact Or.inl (by omega)
    exact hz (hnp (z, 2) h02 hp2)

/-- `¬¬p ⊃ p` is level-0 refuted: every level forces ¬¬p (a p-world
sits at level ≥ 2 above everything), level 0 stays undecorated. -/
theorem lob0_nn (p : String) :
    Lob0Refutes p
      ((((PLLFormula.prop p).ifThen .falsePLL).ifThen .falsePLL).ifThen
        (.prop p)) := by
  intro C z hz hM
  have hnn : (lobVariant C p).force (z, 0)
      (((PLLFormula.prop p).ifThen .falsePLL).ifThen .falsePLL) := by
    rintro ⟨y, k⟩ hyk hnp
    have hup : (lobVariant C p).Ri (y, k) (y, max k 2) :=
      ⟨C.refl_i y, Nat.le_max_left k 2⟩
    have hpm : (lobVariant C p).force (y, max k 2) (.prop p) := by
      show (y, max k 2) ∈ (if p = p then
        {a : (lobModel C).W | 2 ≤ a.2 ∨ a.1 ∈ C.F} else (lobModel C).V p)
      rw [if_pos rfl]
      exact Or.inl (Nat.le_max_right k 2)
    exact hnp (y, max k 2) hup hpm
  have hp := hM (z, 0) ((lobVariant C p).refl_i (z, 0)) hnn
  have hp' : (z, 0) ∈ (if p = p then
      {a : (lobModel C).W | 2 ≤ a.2 ∨ a.1 ∈ C.F} else (lobModel C).V p) := hp
  rw [if_pos rfl] at hp'
  rcases hp' with h2 | hF
  · omega
  · exact hz hF

/-- **`∀p.◯(p ∨ ¬p) = ◯⊥`** — the first law-generated value. -/
theorem semAll_box_em (p : String) :
    IsSemAll p
      (((PLLFormula.prop p).or ((PLLFormula.prop p).ifThen
        .falsePLL)).somehow)
      PLLFormula.falsePLL.somehow :=
  semAll_box (semAll_em_p p) (boxRowAmalgAll_lob0 (lob0_em p))

/-- **`∀p.◯(¬¬p ⊃ p) = ◯⊥`**. -/
theorem semAll_box_nn (p : String) :
    IsSemAll p
      ((((((PLLFormula.prop p).ifThen .falsePLL).ifThen .falsePLL)).ifThen
        (.prop p)).somehow)
      PLLFormula.falsePLL.somehow :=
  semAll_box (semAll_nnp_imp_p p) (boxRowAmalgAll_lob0 (lob0_nn p))

/-- Consistency check: the law re-derives `∀p.◯p = ◯⊥`
(`semAll_box_p` proved it directly). -/
theorem semAll_box_p' (p : String) :
    IsSemAll p (PLLFormula.prop p).somehow PLLFormula.falsePLL.somehow :=
  semAll_box (semAll_prop_self p) (boxRowAmalgAll_lob0 (lob0_prop p))

/-- The ∃-residue for the atom: decorate p everywhere. -/
theorem boxRowAmalgEx_prop (p : String) :
    BoxRowAmalgEx p (.prop p) truePLL := by
  intro C w _
  refine ⟨redecorate C p Set.univ (fun _ _ => trivial) (fun _ => trivial),
    redecorate_pbisim C p Set.univ (fun _ _ => trivial) (fun _ => trivial),
    w, rfl, ?_⟩
  intro x hx
  refine ⟨x, C.refl_m x, ?_⟩
  show x ∈ (if p = p then Set.univ else C.V p)
  rw [if_pos rfl]
  trivial

/-- **`∃p.◯p = ◯⊤`** — the law on the ∃-side (`semEx_box_p` in the
theory file proved the value ⊤ directly; ◯⊤ ⊣⊢ ⊤, consistency by
`semEx_unique`). -/
theorem semEx_box_p' (p : String) :
    IsSemEx p (PLLFormula.prop p).somehow truePLL.somehow :=
  semEx_box (semEx_prop_self p) (boxRowAmalgEx_prop p)

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.semAll_box' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semAll_box

/-- info: 'PLLND.SemUI.semEx_box' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms semEx_box

/--
info: 'PLLND.SemUI.semAll_box_em' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semAll_box_em

/--
info: 'PLLND.SemUI.semEx_box_p'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semEx_box_p'

end SemUI
end PLLND
