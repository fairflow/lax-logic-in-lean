import F0.Names
import LaxLogic.PLL.Semantics.LaxInfinite
import LaxLogic.RN.Rho

/-!
# Gates for the family names (`F0/Names.lean`)

2026-10-22.  Checked by the kernel (`decide`):

* the first RN elements, written out; `t 1`, `t 2`, `t 3` are literally
  ρ2, ρ3, ρ4;
* the staircase of `LaxLogic/PLL/Semantics/LaxInfinite.lean`,
  `subOb (sLad k)` (the "rung k" of the infinitude proof), is `t (2k+1)`
  for `k ≤ 3`, so it needs no family of its own;
* the naming rule: the preferred membership wins whatever the order of
  the list, and a class with no membership is unnamed.
-/

open PLLFormula

namespace F0.NamesGates

theorem t_zero : F0.t 0 = falsePLL := rfl
theorem t_one : F0.t 1 = F0.ob := by decide
theorem t_two : F0.t 2 = ifThen F0.ob falsePLL := by decide
theorem t_three : F0.t 3 = or F0.ob (ifThen F0.ob falsePLL) := by decide
theorem t_four : F0.t 4 = ifThen (or F0.ob (ifThen F0.ob falsePLL)) F0.ob := by decide

theorem t_rho : F0.t 1 = RhoOrder.rhoF 2 ∧ F0.t 2 = RhoOrder.rhoF 3 ∧ F0.t 3 = RhoOrder.rhoF 4 := by
  decide

theorem staircase_0 : PLLND.LaxInfinite.subOb (PLLND.LaxInfinite.sLad 0) = F0.t 1 := by decide
theorem staircase_1 : PLLND.LaxInfinite.subOb (PLLND.LaxInfinite.sLad 1) = F0.t 3 := by decide
theorem staircase_2 : PLLND.LaxInfinite.subOb (PLLND.LaxInfinite.sLad 2) = F0.t 5 := by decide
theorem staircase_3 : PLLND.LaxInfinite.subOb (PLLND.LaxInfinite.sLad 3) = F0.t 7 := by decide

theorem name_pref :
    F0.nameOf [(.c, 2), (.t, 7), (.g, 1)] = some (.t, 7) ∧
    F0.nameOf [(.t, 7), (.t, 5), (.c, 1)] = some (.t, 5) ∧
    F0.nameOf [(.w, 1), (.top, 0)] = some (.top, 0) := by decide

theorem name_none : F0.nameOf [] = none := rfl

theorem domain_head : F0.Fam.domain.take 4 = [(.bot, 0), (.top, 0), (.t, 0), (.t, 1)] := by decide

/-! ## The rows of `Fam.definition`, as theorems -/

theorem bot_def : F0.Fam.term .bot 0 = falsePLL := rfl
theorem top_def : F0.Fam.term .top 0 = ifThen falsePLL falsePLL := rfl
theorem t_base : F0.t 0 = falsePLL ∧ F0.t 1 = somehow falsePLL ∧
    F0.t 2 = ifThen (somehow falsePLL) falsePLL := by decide
/-- The RN recursion of the `t` row, on the whole search domain (`t n`, `n ≤ 12`). -/
theorem t_rec : (List.range 5).all (fun k =>
    F0.t (2 * k + 3) == (F0.t (2 * k + 1)).or (F0.t (2 * k + 2)) &&
    F0.t (2 * k + 4) == ((F0.t (2 * k + 1)).or (F0.t (2 * k + 2))).ifThen (F0.t (2 * k + 1))) = true := by
  decide
theorem c_def (k : Nat) : F0.c k = (F0.t (2 * k + 1)).somehow := rfl
theorem g_def (k : Nat) : F0.g k = (F0.c k).ifThen (F0.t (2 * k + 1)) := rfl
theorem s_def (k : Nat) : F0.s k = (F0.c k).or (F0.t (2 * k + 2)) := rfl
theorem r_def (k : Nat) : F0.r k = (F0.t (2 * k + 4)).ifThen (F0.c k) := rfl
theorem w_def (k : Nat) : F0.w k = (F0.g k).and (F0.t (2 * k + 4)) := rfl
/-- `Fam.term` is the family's constant. -/
theorem term_t : F0.Fam.term .t = F0.t := rfl
theorem term_c : F0.Fam.term .c = F0.c := rfl
theorem term_g : F0.Fam.term .g = F0.g := rfl
theorem term_s : F0.Fam.term .s = F0.s := rfl
theorem term_r : F0.Fam.term .r = F0.r := rfl
theorem term_w : F0.Fam.term .w = F0.w := rfl

end F0.NamesGates

-- The displayed labels (a `String` computation, checked by evaluation).
#guard F0.Fam.label .t 7 == "t7" && F0.Fam.label .c 2 == "c2" && F0.Fam.label .bot 0 == "⊥"
#guard F0.Fam.all.map F0.Fam.leanName ==
  ["PLLFormula.falsePLL", "PLLFormula.truePLL", "F0.t", "F0.c", "F0.g", "F0.s", "F0.r", "F0.w"]

#axioms_within F0.NamesGates.t_four [propext, Quot.sound]
#axioms_within F0.NamesGates.t_rho [propext, Quot.sound]
#axioms_within F0.NamesGates.staircase_0 [propext, Quot.sound]
#axioms_within F0.NamesGates.staircase_1 [propext, Quot.sound]
#axioms_within F0.NamesGates.staircase_2 [propext, Quot.sound]
#axioms_within F0.NamesGates.staircase_3 [propext, Quot.sound]
#axioms_within F0.NamesGates.name_pref [propext, Quot.sound]
#axioms_within F0.NamesGates.domain_head [propext, Quot.sound]
#axioms_within F0.NamesGates.t_base [propext, Quot.sound]
#axioms_within F0.NamesGates.t_rec [propext, Quot.sound]
#axioms_within F0.NamesGates.c_def [propext, Quot.sound]
#axioms_within F0.NamesGates.w_def [propext, Quot.sound]
#axioms_within F0.NamesGates.term_t [propext, Quot.sound]
