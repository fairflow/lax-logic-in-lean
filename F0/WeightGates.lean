import F0.Weight
import LaxLogic.RN.Rho
import LaxLogic.PLL.Search.Exec

/-!
# Gates for the formula weights (`F0/Weight.lean`)

2026-10-22.  The values Matthew fixed, checked by the kernel (`decide`), and
the agreement of `F0.size` with `PLLND.fsize`
(`LaxLogic/PLL/Search/Exec.lean`), proved here so that `F0/Weight.lean`
keeps its light import closure.
-/

open PLLFormula RNReps

namespace F0

/-- `F0.size` is the node count `PLLND.fsize`. -/
theorem size_eq_fsize : ∀ φ : PLLFormula, size φ = PLLND.fsize φ
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by
      show size A + size B + 1 = PLLND.fsize A + PLLND.fsize B + 1
      rw [size_eq_fsize A, size_eq_fsize B]
  | .or A B => by
      show size A + size B + 1 = PLLND.fsize A + PLLND.fsize B + 1
      rw [size_eq_fsize A, size_eq_fsize B]
  | .ifThen A B => by
      show size A + size B + 1 = PLLND.fsize A + PLLND.fsize B + 1
      rw [size_eq_fsize A, size_eq_fsize B]
  | .somehow A => by
      show size A + 1 = PLLND.fsize A + 1
      rw [size_eq_fsize A]

namespace Gates

/-- ρ14 `= ◯¬◯⊥ ∨ ¬¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥` weighs `(2, 20, 8)`. -/
theorem weight_rho14 : weight (RhoOrder.rhoF 14) = (2, 20, 8) := by decide

/-- `◯(¬◯⊥ ∨ ¬¬◯⊥) ↠ ◯⊥ ∨ ¬◯⊥` weighs `(2, 20, 15)`. -/
theorem weight_alt14 : weight (q12.ifThen q4) = (2, 20, 15) := by decide

/-- ρ14 is chosen over the alternative, as incumbent ... -/
theorem pick_rho14 : pickRep (RhoOrder.rhoF 14) [q12.ifThen q4] = RhoOrder.rhoF 14 := by
  decide

/-- ... and as a member, against the alternative as incumbent. -/
theorem pick_rho14' : pickRep (q12.ifThen q4) [RhoOrder.rhoF 14] = RhoOrder.rhoF 14 := by
  decide

/-- `⊤` has size 3. -/
theorem size_top : size (ifThen falsePLL falsePLL) = 3 := by decide

/-- `◯◯⊥` comes after `¬¬◯⊥`: ◯-depth is compared first ... -/
theorem depth_first : weightLt q6 (somehow q2) ∧ ¬ weightLt (somehow q2) q6 := by decide

/-- ... although `◯◯⊥` is the smaller formula. -/
theorem depth_first_control : size (somehow q2) < size q6 := by decide

/-- A tie with the incumbent keeps the incumbent: `◯⊥ ∨ ¬◯⊥` against
`¬◯⊥ ∨ ◯⊥`, of equal weight. -/
theorem tie_keeps_incumbent :
    weight (q3.or q2) = weight q4 ∧ pickRep q4 [q3.or q2] = q4 := by decide

/-- Remaining ties go to the syntactic order, whatever the order of the
members: `¬◯⊥ ∨ ◯⊥` before `◯⊥ ∨ ¬◯⊥` (`↠` ranks below `◯`). -/
theorem tie_syntactic :
    pickRep q7 [q4, q3.or q2] = q3.or q2 ∧ pickRep q7 [q3.or q2, q4] = q3.or q2 := by
  decide

end Gates
end F0

#axioms_within F0.size_eq_fsize [propext, Quot.sound]
#axioms_within F0.Gates.weight_rho14 [propext, Quot.sound]
#axioms_within F0.Gates.weight_alt14 [propext, Quot.sound]
#axioms_within F0.Gates.pick_rho14 [propext, Quot.sound]
#axioms_within F0.Gates.pick_rho14' [propext, Quot.sound]
#axioms_within F0.Gates.size_top [propext, Quot.sound]
#axioms_within F0.Gates.depth_first [propext, Quot.sound]
#axioms_within F0.Gates.depth_first_control [propext, Quot.sound]
#axioms_within F0.Gates.tie_keeps_incumbent [propext, Quot.sound]
#axioms_within F0.Gates.tie_syntactic [propext, Quot.sound]
