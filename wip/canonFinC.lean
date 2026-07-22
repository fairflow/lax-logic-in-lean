import LaxLogic.PLLFinComp

/-!
# `canonFinC` — the confluent finite canonical model (PCLL)  [WIP]

Branch `ui-confluence`.  The finite analogue of `PLLConfluentComplete`'s
`canonU`/`obInv`: worlds `{T : FTheory // MaxIn cl T}` as in `canonFin`,
but `Rₘ` is the `obInv` relation with the `◯◯ → ◯` collapse kept LOCAL
(Matthew's steer): we propagate the COLLAPSED box `boxOf χ` (= `χ` if `χ`
is already `◯ψ`, else `◯χ`).  Because `boxOf` always returns a `◯` and is
idempotent on `◯`s, transitivity closes with no `◯◯` ever entering `cl` —
so `cl` stays a finite subformula-closed set.
-/

open PLLFormula

namespace PLLND
namespace FinComp

open SetDeriv

variable {cl : Finset PLLFormula}

/-- The collapsed box: `◯χ` normalised by `◯◯ = ◯`.  Always a `◯`, and
idempotent (`boxOf (boxOf χ) = boxOf χ`). -/
def boxOf : PLLFormula → PLLFormula
  | .somehow ψ => .somehow ψ
  | φ => φ.somehow

@[simp] theorem boxOf_somehow (ψ : PLLFormula) :
    boxOf (.somehow ψ) = .somehow ψ := rfl

theorem boxOf_idem (χ : PLLFormula) : boxOf (boxOf χ) = boxOf χ := by
  cases χ <;> rfl

/-- The ◯-unit at the canonical level: `χ ∈ val` and `◯χ ∈ cl` give
`◯χ ∈ val`, by `laxIntro` and deductive closure. -/
theorem boxUnit {T : {T : FTheory // MaxIn cl T}} {χ : PLLFormula}
    (hbox : χ.somehow ∈ cl) (hχ : χ ∈ T.1.val) : χ.somehow ∈ T.1.val :=
  T.2.ded_closed hbox
    (setDeriv_coe_iff.mpr ⟨.laxIntro (.iden (Finset.mem_toList.mpr hχ))⟩)

/-- Confluent `Rₘ` (finite `obInv`, `◯◯`-collapsed): `val ⊆ val`, and
every collapsed box `boxOf χ ∈ cl` whose `χ` is validated at `U` is
validated at `T`. -/
def RmC (cl : Finset PLLFormula) (T U : {T : FTheory // MaxIn cl T}) : Prop :=
  T.1.val ⊆ U.1.val ∧
    ∀ χ : PLLFormula, boxOf χ ∈ cl → χ ∈ U.1.val → boxOf χ ∈ T.1.val

theorem RmC_refl (T : {T : FTheory // MaxIn cl T}) : RmC cl T T := by
  refine ⟨subset_rfl, fun χ hbox hχ => ?_⟩
  cases χ with
  | somehow ψ => exact hχ
  | prop a => exact boxUnit hbox hχ
  | falsePLL => exact boxUnit hbox hχ
  | and a b => exact boxUnit hbox hχ
  | or a b => exact boxUnit hbox hχ
  | ifThen a b => exact boxUnit hbox hχ

theorem RmC_trans {T U V : {T : FTheory // MaxIn cl T}}
    (h : RmC cl T U) (h' : RmC cl U V) : RmC cl T V := by
  refine ⟨h.1.trans h'.1, fun χ hbox hχ => ?_⟩
  have hU : boxOf χ ∈ U.1.val := h'.2 χ hbox hχ
  have hbb : boxOf (boxOf χ) = boxOf χ := boxOf_idem χ
  have hT : boxOf (boxOf χ) ∈ T.1.val :=
    h.2 (boxOf χ) (by rw [hbb]; exact hbox) hU
  rwa [hbb] at hT

/-- **The confluent finite canonical model.**  As `canonFin`, but with
`Rₘ` the collapsed `obInv` relation `RmC`. -/
def canonFinC (cl : Finset PLLFormula) : ConstraintModel where
  W := {T : FTheory // MaxIn cl T}
  Ri T T' := T.1.val ⊆ T'.1.val
  Rm := RmC cl
  F := {T | PLLFormula.falsePLL ∈ T.1.val}
  V a := {T | PLLFormula.prop a ∉ cl ∨ PLLFormula.prop a ∈ T.1.val}
  refl_i _ := subset_rfl
  trans_i h h' := h.trans h'
  refl_m := RmC_refl
  trans_m := RmC_trans
  sub_mi h := h.1
  hered_F h hw := h hw
  hered_V h hw := hw.imp_right (fun h' => h h')
  full_F {a} {T} hw := by
    by_cases hcl : PLLFormula.prop a ∈ cl
    · exact .inr (T.2.ded_closed hcl (falso _ (of_mem (Finset.mem_coe.mpr hw))))
    · exact .inl hcl

-- audit: the confluent Rm + model are sorry-free
#print axioms RmC_trans
#print axioms canonFinC

end FinComp
end PLLND
