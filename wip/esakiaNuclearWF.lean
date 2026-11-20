import Mathlib.Order.Nucleus
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.UpperLower.Principal
import Mathlib.Order.WellFounded
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic
import Meta.Audit

/-!
# Nuclei on the down-sets of a well-founded poset

Between the finite layer of the nuclear Esakia duality
(`wip/esakiaNuclearFin.lean`: on a finite Heyting algebra every nucleus is
`j_S`, F4 and F6) and the general case (`wip/esakiaNuclearGen.lean`: nuclei
correspond to the nuclear closed subsets of the prime spectrum, G2).  No
topology and no logic: order theory over Mathlib's `Nucleus` and `LowerSet`.

For a partial order `P`, the down-sets `LowerSet P` are a frame, and for
`Z ⊆ P`

    jZ Z D = {p | ∀ q ≤ p, q ∈ Z → q ∈ D}

is a nucleus on it (the `◯`-clause of a subframe model with `S = Z`, the
down-sets being the propositions).

* `nucleus_eq_jZ`: if `<` is well-founded on `P`, every nucleus `j` is
  `jZ (kept j)`, with `kept j = {p | p ∉ j (Iio p)}`.
* `nucleusIso`: so `Nucleus (LowerSet P) ≃o (Set P)ᵒᵈ`.
* `nucleus_complemented`: so the frame of nuclei is complemented (Boolean).
* `dense_ne_jZ`: well-foundedness cannot be dropped.  On the descending chain
  `ℕᵒᵈ` the nucleus sending every nonempty down-set to `⊤` is `jZ Z` for no
  `Z` (the cell R5 of `wip/esakiaNuclearGen.lean`, for Mathlib's types).

Pins: `[propext, Classical.choice, Quot.sound]`; choice enters through
Mathlib's `Nucleus` and `LowerSet` (their order and lattice instances).
-/

namespace EsakiaNuclear.WF

open Set

section General

variable {P : Type*} [PartialOrder P]

/-- The nucleus of a set `Z` of points: `p ∈ jZ Z D` iff every point of `Z`
below `p` is in `D`. -/
def jZ (Z : Set P) : Nucleus (LowerSet P) where
  toFun D := ⟨{p | ∀ q, q ≤ p → q ∈ Z → q ∈ D}, fun _ _ hba ha q hq hz => ha q (hq.trans hba) hz⟩
  map_inf' D E := by
    ext p
    constructor
    · intro h
      exact ⟨fun q hq hz => (h q hq hz).1, fun q hq hz => (h q hq hz).2⟩
    · rintro ⟨h1, h2⟩ q hq hz
      exact ⟨h1 q hq hz, h2 q hq hz⟩
  idempotent' D := by
    intro p hp q hq hz
    exact hp q hq hz q le_rfl hz
  le_apply' D := by
    intro p hp q hq _
    exact D.lower hq hp

theorem mem_jZ {Z : Set P} {D : LowerSet P} {p : P} :
    p ∈ jZ Z D ↔ ∀ q, q ≤ p → q ∈ Z → q ∈ D := Iff.rfl

/-- The points kept by a nucleus. -/
def kept (j : Nucleus (LowerSet P)) : Set P := {p | p ∉ j (LowerSet.Iio p)}

theorem kept_jZ (Z : Set P) : kept (jZ Z) = Z := by
  ext p
  simp only [kept, mem_setOf_eq, mem_jZ, LowerSet.mem_Iio_iff]
  constructor
  · intro h
    by_contra hp
    exact h fun q hq hz => lt_of_le_of_ne hq (fun e => hp (e ▸ hz))
  · intro hp h
    exact lt_irrefl p (h p le_rfl hp)

theorem jZ_antitone {Z Z' : Set P} (h : Z' ⊆ Z) : jZ Z ≤ jZ Z' := by
  intro D p hp q hq hz
  exact hp q hq (h hz)

theorem kept_antitone {j j' : Nucleus (LowerSet P)} (h : j ≤ j') : kept j' ⊆ kept j := by
  intro p hp hj
  exact hp (h (LowerSet.Iio p) hj)

/-- A point kept by `j` that lies in `j D` lies in `D`. -/
theorem mem_of_kept (j : Nucleus (LowerSet P)) {D : LowerSet P} {q : P}
    (hz : q ∈ kept j) (hq : q ∈ j D) : q ∈ D := by
  by_contra hD
  apply hz
  have h1 : q ∈ j (D ⊓ LowerSet.Iic q) := by
    rw [Nucleus.map_inf]
    exact ⟨hq, Nucleus.le_apply (x := LowerSet.Iic q) (show q ∈ LowerSet.Iic q from le_rfl)⟩
  have h2 : D ⊓ LowerSet.Iic q ≤ LowerSet.Iio q := by
    rintro r ⟨hr, hrq⟩
    exact lt_of_le_of_ne hrq (fun e => hD (e ▸ hr))
  exact j.monotone h2 h1

variable [WellFoundedLT P]

/-- **Every nucleus on the down-sets is the nucleus of its kept points.** -/
theorem nucleus_eq_jZ (j : Nucleus (LowerSet P)) : j = jZ (kept j) := by
  apply le_antisymm
  · intro D p hp q hq hz
    exact mem_of_kept j hz (((j D).lower hq) hp)
  · intro D p
    induction p using WellFoundedLT.induction with
    | ind p ih =>
      intro hp
      have hlow : LowerSet.Iio p ≤ j D := by
        intro q hq
        exact ih q hq fun r hr hz => hp r (hr.trans (le_of_lt hq)) hz
      by_cases hz : p ∈ kept j
      · exact (Nucleus.le_apply (n := j) (x := D)) (hp p le_rfl hz)
      · have h1 : p ∈ j (LowerSet.Iio p) := by
          simpa [kept] using hz
        have h2 : j (LowerSet.Iio p) ≤ j (j D) := j.monotone hlow
        have h3 : j (j D) = j D := Nucleus.idempotent (n := j) D
        exact h3 ▸ h2 h1

/-- **The nuclei on the down-sets of a well-founded poset are the subsets,
with the order reversed.** -/
def nucleusIso : Nucleus (LowerSet P) ≃o (Set P)ᵒᵈ where
  toFun j := OrderDual.toDual (kept j)
  invFun Z := jZ (OrderDual.ofDual Z)
  left_inv j := (nucleus_eq_jZ j).symm
  right_inv Z := by
    show OrderDual.toDual (kept (jZ (OrderDual.ofDual Z))) = Z
    rw [kept_jZ]; rfl
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      have h' : kept b ⊆ kept a := h
      rw [nucleus_eq_jZ a, nucleus_eq_jZ b]
      exact jZ_antitone h'
    · intro h
      exact kept_antitone h

/-- **The frame of nuclei is complemented**, hence a Boolean algebra. -/
theorem nucleus_complemented : ComplementedLattice (Nucleus (LowerSet P)) :=
  (nucleusIso (P := P)).symm.complementedLattice

end General

/-! ## Well-foundedness is needed: a descending chain

`ℕᵒᵈ` is an infinite descending chain.  Its down-sets are `⊥` and the tails.
The nucleus sending every nonempty down-set to `⊤` (double negation on this
frame) is `jZ Z` for no `Z`.  This is the cell R5 (`EsakiaNuclear.Bridge.r5`,
`wip/esakiaNuclearGenProofs.lean`: on `ω` with `Rᵢ = Rₘ = ≤`, no `S ⊆ ω`
gives `j_C` as `j_S`), restated for Mathlib's `Nucleus` and `LowerSet`. -/

/-- The nucleus on the down-sets of `ℕᵒᵈ` that sends every nonempty down-set
to `⊤`. -/
def dense : Nucleus (LowerSet ℕᵒᵈ) where
  toFun D := ⟨{_p | (D : Set ℕᵒᵈ).Nonempty}, fun _ _ _ h => h⟩
  map_inf' D E := by
    ext p
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨⟨q, hq.1⟩, ⟨q, hq.2⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      rcases le_total a b with h | h
      · exact ⟨a, ha, E.lower h hb⟩
      · exact ⟨b, D.lower h ha, hb⟩
  idempotent' D := by
    rintro p ⟨q, hq⟩
    exact hq
  le_apply' D := fun p hp => ⟨p, hp⟩

theorem mem_dense {D : LowerSet ℕᵒᵈ} {p : ℕᵒᵈ} : p ∈ dense D ↔ (D : Set ℕᵒᵈ).Nonempty :=
  Iff.rfl

/-- **Without well-foundedness the theorem fails**: on the down-sets of the
descending chain `ℕᵒᵈ`, the nucleus `dense` is `jZ Z` for no `Z`. -/
theorem dense_ne_jZ (Z : Set ℕᵒᵈ) : dense ≠ jZ Z := by
  intro h
  by_cases hZ : Z.Nonempty
  · obtain ⟨p, hp⟩ := hZ
    have h1 : p ∈ dense (LowerSet.Iio p) := by
      refine mem_dense.mpr ⟨OrderDual.toDual (OrderDual.ofDual p + 1), ?_⟩
      show OrderDual.toDual (OrderDual.ofDual p + 1) < p
      exact OrderDual.ofDual_lt_ofDual.mp (Nat.lt_succ_self _)
    rw [h] at h1
    exact lt_irrefl p (mem_jZ.mp h1 p le_rfl hp)
  · have h1 : (OrderDual.toDual 0 : ℕᵒᵈ) ∈ jZ Z ⊥ := fun q _ hq => absurd ⟨q, hq⟩ hZ
    rw [← h] at h1
    obtain ⟨q, hq⟩ := mem_dense.mp h1
    exact hq

end EsakiaNuclear.WF

#axioms_within EsakiaNuclear.WF.nucleus_eq_jZ [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.WF.nucleusIso [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.WF.nucleus_complemented [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.WF.dense_ne_jZ [propext, Classical.choice, Quot.sound]
