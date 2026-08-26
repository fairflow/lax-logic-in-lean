/-
# The bridge lemma, and the bottom diamond as a cube instance

`CoversVF` (`RNDB/Order.lean`) is the fragment's own cover relation
stated on FORMULAS: `Lt a b` with no variable-free interposer.  Mathlib's
`⋖` on the quotient `RNClass` (`LaxLogic/ClosedFragmentLattice.lean`) is
the same relation stated on CLASSES.  The bridge is the alignment of the
two spellings — `VarFree ↔ atomFree`, `Le ↔ Deriv` (`le_iff_nonempty`),
`< ↔ Lt` — after which the two kernel-proved covers `⊥ ⋖ ◯⊥`, `⊥ ⋖ ¬◯⊥`
transfer to the quotient, and the cube-embedding theorem
(`CubeEmbedding.cube_le_iff`) fires on `U = {[◯⊥], [¬◯⊥]}`:

    THE BOTTOM DIAMOND  {⊥, ◯⊥, ¬◯⊥, ◯⊥ ∨ ¬◯⊥} ≅ 2²

is the first full instance — forced by MEMBERSHIP of the two covers
alone; exactness of `U(⊥)` is not needed for the embedding.
-/
import RNDB.Order
import LaxLogic.ClosedFragmentLattice
import Certified.RhoRefutations

open PLLND PLLND.SemUI PLLND.LaxInfinite PLLFormula

namespace RNDB

open RhoOrder

/-! ## The spelling bridges -/

/-- `VarFree` (the `Prop`, `PLLNoFall.lean`) is `atomFree` (the `Bool`,
`PLLLaxInfinite.lean`). -/
theorem varFree_iff_atomFree : ∀ φ, NoFall.VarFree φ ↔ atomFree φ = true
  | .prop _ => by simp [NoFall.VarFree, atomFree]
  | .falsePLL => by simp [NoFall.VarFree, atomFree]
  | .and φ ψ => by
      simp [NoFall.VarFree, atomFree, varFree_iff_atomFree φ, varFree_iff_atomFree ψ]
  | .or φ ψ => by
      simp [NoFall.VarFree, atomFree, varFree_iff_atomFree φ, varFree_iff_atomFree ψ]
  | .ifThen φ ψ => by
      simp [NoFall.VarFree, atomFree, varFree_iff_atomFree φ, varFree_iff_atomFree ψ]
  | .somehow φ => by simp [NoFall.VarFree, atomFree, varFree_iff_atomFree φ]

/-- A closed formula's class. -/
def mkC (φ : PLLFormula) (h : atomFree φ = true) : RNClass :=
  Quotient.mk closedSetoid (Closed.mk φ h)

/-- The quotient order is `Deriv`, through `le_iff_nonempty`. -/
theorem mkC_le_iff {a b : PLLFormula} {ha : atomFree a = true}
    {hb : atomFree b = true} : mkC a ha ≤ mkC b hb ↔ Deriv [a] b :=
  le_iff_nonempty

/-- The quotient strict order is `Lt`. -/
theorem mkC_lt_iff {a b : PLLFormula} {ha : atomFree a = true}
    {hb : atomFree b = true} : mkC a ha < mkC b hb ↔ Lt a b := by
  rw [lt_iff_le_not_ge, mkC_le_iff, mkC_le_iff]
  exact Iff.rfl

/-- **The bridge lemma**: a `CoversVF` cover on formulas is a Mathlib
`⋖` cover on classes.  The interposer quantifier matches because every
class of the quotient is represented by an `atomFree` formula, and
`atomFree` is `VarFree`. -/
theorem covBy_of_coversVF {a b : PLLFormula} (ha : atomFree a = true)
    (hb : atomFree b = true) (h : CoversVF a b) : mkC a ha ⋖ mkC b hb := by
  refine ⟨(mkC_lt_iff).mpr h.1, fun c hac hcb => ?_⟩
  induction c using Quotient.ind with
  | _ z =>
    exact h.2 z.1 ((varFree_iff_atomFree z.1).mpr z.2)
      ⟨(mkC_lt_iff (ha := ha) (hb := z.2)).mp hac,
       (mkC_lt_iff (ha := z.2) (hb := hb)).mp hcb⟩

/-! ## The two covers, on classes -/

/-- The class of `◯⊥` (= ρ2). -/
def obotC : RNClass := mkC oBot rfl

/-- The class of `¬◯⊥` (= ρ3). -/
def nbotC : RNClass := mkC nBot rfl

theorem bot_covBy_obotC : (⊥ : RNClass) ⋖ obotC :=
  covBy_of_coversVF rfl rfl bot_coversVF_obot

theorem bot_covBy_nbotC : (⊥ : RNClass) ⋖ nbotC :=
  covBy_of_coversVF rfl rfl bot_coversVF_nbot

/-- The two covers are distinct classes (`[◯⊥] ⊬ ¬◯⊥`, from the
certificate corpus: `RhoCerts.rho_2_nle_3` with `ρ2 = ◯⊥`, `ρ3 = ¬◯⊥`
syntactically). -/
theorem obotC_ne_nbotC : obotC ≠ nbotC := by
  intro h
  have heq : LaxEquiv oBot nBot := Quotient.exact h
  have h23 : rhoF 2 = oBot ∧ rhoF 3 = nBot := by decide +kernel
  exact (h23.1 ▸ h23.2 ▸ RhoCerts.rho_2_nle_3)
    (le_iff_nonempty.mp heq.1)

/-! ## The bottom diamond -/

/-- `U(⊥)`'s two certified members, as a `Finset`. -/
def bottomU : Finset RNClass :=
  ⟨obotC ::ₘ {nbotC}, by
    simp [Multiset.nodup_cons, Multiset.mem_singleton, obotC_ne_nbotC]⟩

theorem mem_bottomU {y : RNClass} : y ∈ bottomU ↔ y = obotC ∨ y = nbotC := by
  simp [bottomU, Finset.mem_mk, Multiset.mem_singleton]

theorem bottomU_covers : ∀ y ∈ bottomU, (⊥ : RNClass) ⋖ y := by
  intro y hy
  rcases mem_bottomU.mp hy with rfl | rfl
  · exact bot_covBy_obotC
  · exact bot_covBy_nbotC

/-- **The bottom diamond**: the four joins `⊥ ∨ ⋁S`, `S ⊆ {[◯⊥], [¬◯⊥]}`,
form a Boolean square in RN(◯,{}) — the first full instance of the cube
embedding, from cover MEMBERSHIP alone. -/
theorem bottom_diamond {S T : Finset RNClass} (hS : S ⊆ bottomU)
    (hT : T ⊆ bottomU) :
    CubeEmbedding.cube ⊥ S ≤ CubeEmbedding.cube ⊥ T ↔ S ⊆ T :=
  PLLND.rn_cube_le_iff bottomU_covers hS hT

theorem bottom_diamond_inj {S T : Finset RNClass} (hS : S ⊆ bottomU)
    (hT : T ⊆ bottomU)
    (h : CubeEmbedding.cube ⊥ S = CubeEmbedding.cube ⊥ T) : S = T :=
  PLLND.rn_cube_inj bottomU_covers hS hT h

/-- The diamond's top corner is ρ4's class, `◯⊥ ∨ ¬◯⊥`, on the nose. -/
theorem cube_bottomU_eq_rho4 :
    CubeEmbedding.cube ⊥ bottomU = mkC (rhoF 4) (by decide +kernel) := by
  show (⊥ ⊔ (obotC ⊔ (nbotC ⊔ ⊥)) : RNClass) = _
  rw [sup_bot_eq, bot_sup_eq]
  rfl

end RNDB

/-! ## Pins -/

/-- info: 'RNDB.covBy_of_coversVF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RNDB.covBy_of_coversVF

/-- info: 'RNDB.bottom_diamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RNDB.bottom_diamond

/-- info: 'RNDB.cube_bottomU_eq_rho4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RNDB.cube_bottomU_eq_rho4
