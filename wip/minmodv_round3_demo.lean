/-
# The flight shape served by the STRICT-(J2) calculus — round 3's vacuity witness

    G3 = (◯w ⊃ q) ⊃ ◯w

History (2026-08-27): calculus round 3 relaxed the barren (J2) to
`RefAt` and cited this cell as its live demo.  The conservativity
screening (Matthew's option B) then found the demo's own (J2) was
VACUOUS — the join below has an empty stable implication zone — so the
retention that serves the flight shape is the KEPT CHAIN, which is
round-2 (V1) machinery with full `RefAt` power.  Round 3 was reverted
the same day: no witnessed instance of necessity exists, and this file
now certifies the round-2 derivation of the same cell by the SAME tree.

What the tree shows: the goal violates the seen-recursion's guard
(`◯w` inside a left-implication antecedent, `G3_unguarded`), the
single-world countermodel makes `w`'s corner fire with `◯w` in flight,
and the `Λ*`-member `M = ◯w ⊃ q` is retained in the very `w`-row that
serves `◯w` — by the kept chain through

    RefAt (◯w)  =  circ → ups (w ∈ Υ)

(`M_kept`), a retention the PAPER's `Θ^⊃/Υ` zone can never perform
(`M_not_ups_kept`).  Four nodes: `Ax^I w`, the `⋈^At` with the kept
adoption, `◯∈`, `⊃∈`.
-/
import wip.minmodv_seen
import FRJ.WitnessKit
import FRJ.Fallible

set_option maxRecDepth 4000

namespace FRJ.Round3Demo

open FRJ Form

def wf : Form := .atom "w"
def qf : Form := .atom "q"
def Ow : Form := .circ wf
/-- The in-flight member: `◯w ⊃ q`. -/
def M : Form := .imp Ow qf
def G3 : Form := .imp M Ow

/-- `G3` violates the seen-recursion's guard: its left implication `M`
carries a `◯` in antecedent position — the guarded theorem does not
apply, and this file serves the cell anyway. -/
theorem G3_unguarded : guardB G3 = false := by decide

/-- Consistency control: `G3` is refuted on the one-world infallible
model, so it is no PLL theorem and the refutation calculus SHOULD
derive it. -/
theorem G3_not_valid : ¬ Kripke.point.valid G3 := by
  change ¬ Kripke.point.force Kripke.point.root G3
  decide

/-! ## The four-node witness -/

def Θw : List Form := FRJ.rm (gAt G3) wf ++ gImp G3 ++ gCirc G3

def R1 : FRJVi G3 [] Θw wf :=
  .axI wf (by decide) (by decide) (CtxEq.refl _)

def stab1 : Fin 1 → List Form := fun _ => []
def th1 : Fin 1 → List Form := fun _ => Θw
def rhs1 : Fin 1 → Form := fun _ => wf

def keptw : List Form :=
  keptOf (upsilon rhs1) (joinCtxAtVBase stab1 th1 wf) (thPool th1)

/-- **THE KEPT CHAIN (V1), LIVE**: the greedy kept chain adopts the
in-flight member `M = ◯w ⊃ q` — its antecedent `◯w` is `RefAt`-refuted
through the `circ`-clause over `w ∈ Υ`.  Round-2 machinery; (J2) below
is vacuous. -/
theorem M_kept : M ∈ keptw := by decide

/-- The certified contrast: the PAPER second zone (`Θ^⊃/Υ`) does NOT
contain `M` — its antecedent `◯w` is no premise right formula; the V1
kept chain is what carries it. -/
theorem M_not_ups_kept : M ∉ restrict (thPool th1) (upsilon rhs1) := by
  decide

def Rw : FRJVr G3 .barren
    (joinCtxAtVBase stab1 th1 wf ++ keptw) wf :=
  .joinAt (fun _ => R1) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

def ROw : FRJVr G3 .barren
    (joinCtxAtVBase stab1 th1 wf ++ keptw) Ow :=
  .circIn Rw (Or.inl rfl) (by decide)

def goal : FRJVr G3 .barren
    (joinCtxAtVBase stab1 th1 wf ++ keptw) G3 :=
  .impIn ROw (.base (by decide)) (by decide)

/-- **The flight-shaped cell, derived in the STRICT-(J2) calculus** —
the kept chain alone performs the retention the paper zone cannot. -/
theorem provableV_selfref : ProvableV G3 := ⟨.barren, _, ⟨goal⟩⟩

/-- info: 'FRJ.Round3Demo.provableV_selfref' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_selfref

end FRJ.Round3Demo
