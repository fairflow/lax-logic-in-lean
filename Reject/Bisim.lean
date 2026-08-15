/-
BISIMULATION for PLL constraint models — REUSED, not reinvented.

The notion completeness needs already exists in this tree:
`PLLND.SemUI.ABisim` (`LaxLogic/PLLSemUI.lean`), built for the SEMANTIC
ROUTE TO UNIFORM INTERPOLATION, where a p-variant is a world related
by a bisimulation protecting every atom but `p`.  Its zig-zag is
already the one `◯` forces — `iforth`/`iback` to move the outer
universal of the `∀∃` clause, `mforth`/`mback` to move the inner
existential — and `force_iff_of_bisim` is already proved.

T2 needs the case where NO atom is forgotten, so this file is a thin
adapter: `Bisim M N := SemUI.ABisim (fun _ => True) M N`, with the alphabet
side condition discharged once.  Nothing is duplicated; if the UI
route later strengthens `ABisim`, `Reject` inherits it.

(The UI campaign itself is PARKED — docs/disproof-handoff.md scope
rule — but its machinery is not, and this is the second time it has
paid for itself.)
-/
import Reject.Height
import LaxLogic.PLLSemUI

namespace Reject

open PLLND PLLND.SemUI

/-- **A full bisimulation**: `ABisim` with every atom protected. -/
abbrev Bisim (M N : ConstraintModel) : Type := SemUI.ABisim (fun _ => True) M N

/-- **Bisimilar worlds force the same formulas** — the alphabet side
condition of `force_iff_of_bisim` discharged, once. -/
theorem Bisim.force {M N : ConstraintModel} (B : Bisim M N) (φ : PLLFormula)
    {x : M.W} {y : N.W} (h : B.Z x y) : M.force x φ ↔ N.force y φ :=
  SemUI.force_iff_of_bisim B (fun _ _ => trivial) h

/-- An isomorphism is a bisimulation, so `Iso.force` is the special
case where the relation is the graph of a bijection. -/
def Iso.toBisim {M N : ConstraintModel} (e : Iso M N) : Bisim M N where
  Z x y := e.toFun x = y
  atoms := by rintro x y rfl a _; exact e.val
  fall := by rintro x y rfl; exact e.fal
  iforth := by rintro x y rfl v h; exact ⟨e.toFun v, e.ri.mp h, rfl⟩
  iback := by
    rintro x y rfl v' h
    refine ⟨e.invFun v', e.ri.mpr ?_, e.right_inv v'⟩
    rw [e.right_inv]; exact h
  mforth := by rintro x y rfl u h; exact ⟨e.toFun u, e.rm.mp h, rfl⟩
  mback := by
    rintro x y rfl u' h
    refine ⟨e.invFun u', e.rm.mpr ?_, e.right_inv u'⟩
    rw [e.right_inv]; exact h

/-! ## Pins -/

/--
info: 'Reject.Bisim.force' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Bisim.force

end Reject
