/-
# `minModV` round-1 smoke test — the Peirce cell, driven end to end

    GP = (◯p ⊃ q) ⊃ q      (PLL-underivable; the W4 design pass's own
                             completeness-gap witness for the W3 calculus)

`Kripke.point` (one infallible reflexive world, empty valuation) refutes
`GP`, `Λ*` there is `{◯p ⊃ q}` — implication only, so `hloc` holds — and
the recursion exercises EVERY round-1 branch:

* `(n+1), .imp` with `e = a` (the antecedent is forced at the root);
* `(n+1), .atom` with `impPart Λ* ≠ []` → `regPrimeV_join` whose `Υ`
  contains the MODAL antecedent `◯p`;
* the join `ih` demands `I(◯p)` → the `0, .circ` case, whose float has
  no candidate (one world) → `CircSupplyV` fires — discharged here by
  the generalised `Ax^I◯` at the empty valuation, exactly the
  maximal-world route of frj-w4 §11.

Consistency control: the paper calculus already derives this cell
(`provable_circ_peirce`); here the REPAIRED calculus re-derives it
through the extended completeness recursion.
-/
import wip.minmodv
import wip.minmodv_assembly
import FRJ.Fallible

namespace FRJ.MinModVTest

open FRJ Form

def p : Form := .atom "p"
def q : Form := .atom "q"

/-- `(◯p ⊃ q) ⊃ q`. -/
def GP : Form := .imp (.imp (.circ p) q) q

/-- The root of `point` refutes `GP`: `◯p` is unforced (no world forces
`p`), so the antecedent holds vacuously, while `q` fails. -/
theorem not_valid_GP : ¬ Kripke.point.valid GP := by
  intro h
  exact h () trivial (fun b _ hOp => by
    obtain ⟨c, -, hc⟩ := hOp () trivial
    exact hc)

/-- `Λ*` is world-wise `◯`-free on `point`. -/
theorem hloc_GP : ∀ b : Kripke.point.W,
    circPart (lamStar Kripke.point b GP) = [] := by
  intro b
  cases b
  decide

/-- The sole-candidate supply, discharged by `Ax^I◯` at the empty
valuation: the only `◯`-shaped right subformula is `◯p`, and
`classForce [] p = false`. -/
def hsup_GP : CircSupplyV Kripke.point GP := fun a Z hZ _ _ => by
  cases a
  have hZp : Z = p := by
    simp only [GP, p, q, sfR, sfPos, sfNeg] at hZ
    simp_all [p]
  subst hZp
  exact { stab := []
          th := vacZoneA GP []
          der := .axIC p [] (fun _ h => absurd h List.not_mem_nil)
            (by decide) (by decide) (CtxEq.refl _)
          sub := fun _ h => absurd h List.not_mem_nil
          cov := by decide }

/-- **The repaired calculus derives the Peirce cell THROUGH the extended
completeness recursion** — the round-1 delta driven end to end. -/
theorem provableV_circ_peirce_viaMinModV : ProvableV GP :=
  completenessV_of_supply Kripke.point hloc_GP point_infallible hsup_GP
    not_valid_GP

/-- info: 'FRJ.MinModVTest.provableV_circ_peirce_viaMinModV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_circ_peirce_viaMinModV

/-! ## Round 2: the same cell with the supply DISCHARGED

`point` is discrete, hence cone-grounded, so `circSupplyV_of_coneGrounded`
replaces the hand-built supply above (which stays as documentation of the
`Ax^I◯` discharge the derived route performs at the corner). -/

theorem point_coneGrounded : Kripke.point.ConeGrounded :=
  fun _ _ _ hu => Kripke.point.le_antisymm trivial hu

/-- **The Peirce cell through the recursion with NO hand-built supply.** -/
theorem provableV_circ_peirce_discharged : ProvableV GP :=
  completenessV_of_coneGrounded Kripke.point hloc_GP point_infallible
    point_coneGrounded not_valid_GP

/-- info: 'FRJ.MinModVTest.provableV_circ_peirce_discharged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_circ_peirce_discharged

/-- The Peirce cell through the ASSEMBLED recursion — no supply. -/
theorem provableV_circ_peirce_assembled : ProvableV GP :=
  completenessV Kripke.point hloc_GP point_infallible not_valid_GP

/-- info: 'FRJ.MinModVTest.provableV_circ_peirce_assembled' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_circ_peirce_assembled

end FRJ.MinModVTest
