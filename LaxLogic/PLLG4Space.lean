import LaxLogic.PLLG4

/-!
# Termination A: the finite formula space

Backward `G4iLL″` search cannot terminate by a decreasing rule measure
(the lax rules retain, the Dyckhoff rules consume, and an erased
implication can re-enter as a piece of a split conjunction).  It
terminates by **finiteness of the reachable space**: every formula
appearing in any premise of any rule has weight bounded by the
conclusion's formulas and atoms among theirs — retained material
trivially, opened boxes and premise goals as subformulas, and the
Dyckhoff pieces because the curried transforms *strictly decrease*
weight (the `∧ = +2` convention's purpose).

This file: the atom set of a formula, the space predicate
`InSpace W as φ` (weight ≤ `W`, atoms ⊆ `as`, decidable), a concrete
`Finset` enumeration `enum as W` with `InSpace.mem_enum` embedding the
space into it (one direction is all the pigeonhole needs), and the
component/piece stability lemmas the sequent-level argument will
consume.
-/

namespace PLLFormula

/-- The atoms occurring in a formula. -/
def atoms : PLLFormula → Finset String
  | prop a => {a}
  | falsePLL => ∅
  | and A B => A.atoms ∪ B.atoms
  | or A B => A.atoms ∪ B.atoms
  | ifThen A B => A.atoms ∪ B.atoms
  | somehow A => A.atoms

@[simp] theorem atoms_prop {a : String} : (prop a).atoms = {a} := rfl
@[simp] theorem atoms_false : (falsePLL).atoms = ∅ := rfl
@[simp] theorem atoms_and {A B : PLLFormula} :
    (A.and B).atoms = A.atoms ∪ B.atoms := rfl
@[simp] theorem atoms_or {A B : PLLFormula} :
    (A.or B).atoms = A.atoms ∪ B.atoms := rfl
@[simp] theorem atoms_ifThen {A B : PLLFormula} :
    (A.ifThen B).atoms = A.atoms ∪ B.atoms := rfl
@[simp] theorem atoms_somehow {A : PLLFormula} :
    (A.somehow).atoms = A.atoms := rfl

/-- The weight-bounded space over a finite atom alphabet. -/
def InSpace (W : Nat) (as : Finset String) (φ : PLLFormula) : Prop :=
  φ.weight ≤ W ∧ φ.atoms ⊆ as

instance (W : Nat) (as : Finset String) (φ : PLLFormula) :
    Decidable (InSpace W as φ) := by
  unfold InSpace; infer_instance

namespace InSpace

variable {W : Nat} {as : Finset String} {A B D : PLLFormula}

/-! ### Subformula components stay in the space -/

theorem and_left (h : InSpace W as (A.and B)) : InSpace W as A :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (by rw [atoms_and]; exact Finset.mem_union_left _ hx)⟩

theorem and_right (h : InSpace W as (A.and B)) : InSpace W as B :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (by rw [atoms_and]; exact Finset.mem_union_right _ hx)⟩

theorem or_left (h : InSpace W as (A.or B)) : InSpace W as A :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (by rw [atoms_or]; exact Finset.mem_union_left _ hx)⟩

theorem or_right (h : InSpace W as (A.or B)) : InSpace W as B :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (by rw [atoms_or]; exact Finset.mem_union_right _ hx)⟩

theorem imp_left (h : InSpace W as (A.ifThen B)) : InSpace W as A :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (by rw [atoms_ifThen]; exact Finset.mem_union_left _ hx)⟩

theorem imp_right (h : InSpace W as (A.ifThen B)) : InSpace W as B :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (by rw [atoms_ifThen]; exact Finset.mem_union_right _ hx)⟩

theorem box (h : InSpace W as A.somehow) : InSpace W as A :=
  ⟨by have h1 := h.1; simp only [weight] at h1; omega,
   fun x hx => h.2 (by rw [atoms_somehow]; exact hx)⟩

/-! ### The Dyckhoff pieces stay in the space (weights strictly drop) -/

theorem impAnd_piece (h : InSpace W as ((A.and B).ifThen D)) :
    InSpace W as (A.ifThen (B.ifThen D)) := by
  obtain ⟨hw, ha⟩ := h
  simp only [weight] at hw
  refine ⟨by simp only [weight]; omega, fun x hx => ha ?_⟩
  rw [atoms_ifThen, atoms_and]
  rw [atoms_ifThen, atoms_ifThen] at hx
  simp only [Finset.mem_union] at hx ⊢
  tauto

theorem impOr_piece₁ (h : InSpace W as ((A.or B).ifThen D)) :
    InSpace W as (A.ifThen D) := by
  obtain ⟨hw, ha⟩ := h
  simp only [weight] at hw
  have := weight_pos B
  refine ⟨by simp only [weight]; omega, fun x hx => ha ?_⟩
  rw [atoms_ifThen, atoms_or]
  rw [atoms_ifThen] at hx
  simp only [Finset.mem_union] at hx ⊢
  tauto

theorem impOr_piece₂ (h : InSpace W as ((A.or B).ifThen D)) :
    InSpace W as (B.ifThen D) := by
  obtain ⟨hw, ha⟩ := h
  simp only [weight] at hw
  have := weight_pos A
  refine ⟨by simp only [weight]; omega, fun x hx => ha ?_⟩
  rw [atoms_ifThen, atoms_or]
  rw [atoms_ifThen] at hx
  simp only [Finset.mem_union] at hx ⊢
  tauto

theorem impImp_piece (h : InSpace W as ((A.ifThen B).ifThen D)) :
    InSpace W as (B.ifThen D) := by
  obtain ⟨hw, ha⟩ := h
  simp only [weight] at hw
  have := weight_pos A
  refine ⟨by simp only [weight]; omega, fun x hx => ha ?_⟩
  rw [atoms_ifThen] at hx ⊢
  rw [atoms_ifThen]
  simp only [Finset.mem_union] at hx ⊢
  tauto

end InSpace

/-! ### A concrete finite enumeration containing the space -/

/-- All formulas built in at most `W` weight over alphabet `as` land in
this finite set (`InSpace.mem_enum`); the converse is not needed. -/
def enum (as : Finset String) : Nat → Finset PLLFormula
  | 0 => ∅
  | W + 1 =>
      (as.image prop ∪ {falsePLL}
      ∪ ((enum as W ×ˢ enum as W).image fun p => p.1.and p.2)
      ∪ ((enum as W ×ˢ enum as W).image fun p => p.1.or p.2)
      ∪ ((enum as W ×ˢ enum as W).image fun p => p.1.ifThen p.2)
      ∪ ((enum as W).image somehow)).filter (fun φ => φ.weight ≤ W + 1)

theorem InSpace.mem_enum : ∀ (W : Nat) {as : Finset String} {φ : PLLFormula},
    InSpace W as φ → φ ∈ enum as W := by
  intro W
  induction W with
  | zero =>
      intro as φ h
      exact absurd h.1 (by have := weight_pos φ; omega)
  | succ W ih =>
      intro as φ h
      obtain ⟨hw, ha⟩ := h
      simp only [enum]
      refine Finset.mem_filter.mpr ⟨?_, hw⟩
      cases φ with
      | prop a =>
          have haa : a ∈ as := ha (by rw [atoms_prop]; exact Finset.mem_singleton_self a)
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, haa, rfl⟩)))))
      | falsePLL =>
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton_self _)))))
      | and A B =>
          simp only [weight] at hw
          have hA := ih (as := as) (φ := A)
            ⟨by omega, fun x hx => ha (by rw [atoms_and]; exact Finset.mem_union_left _ hx)⟩
          have hB := ih (as := as) (φ := B)
            ⟨by omega, fun x hx => ha (by rw [atoms_and]; exact Finset.mem_union_right _ hx)⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, rfl⟩))))
      | or A B =>
          simp only [weight] at hw
          have hA := ih (as := as) (φ := A)
            ⟨by omega, fun x hx => ha (by rw [atoms_or]; exact Finset.mem_union_left _ hx)⟩
          have hB := ih (as := as) (φ := B)
            ⟨by omega, fun x hx => ha (by rw [atoms_or]; exact Finset.mem_union_right _ hx)⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, rfl⟩)))
      | ifThen A B =>
          simp only [weight] at hw
          have hA := ih (as := as) (φ := A)
            ⟨by omega, fun x hx => ha (by rw [atoms_ifThen]; exact Finset.mem_union_left _ hx)⟩
          have hB := ih (as := as) (φ := B)
            ⟨by omega, fun x hx => ha (by rw [atoms_ifThen]; exact Finset.mem_union_right _ hx)⟩
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, rfl⟩))
      | somehow A =>
          simp only [weight] at hw
          have hA := ih (as := as) (φ := A)
            ⟨by omega, fun x hx => ha (by rw [atoms_somehow]; exact hx)⟩
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨A, hA, rfl⟩)

end PLLFormula
