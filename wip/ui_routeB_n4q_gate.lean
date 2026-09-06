/-
Route (B), node **N4**, WP9: **the gates, watched failing.**

Rule: never ship a gate you have not watched fail.  Two defects are injected
here and the check goes red on each, kernel-checked as a `= false`:

1. **Drop the goal term `3 ^ wNeg goal` from `ν`.**  `docs/n4-loopcheck.md`
   §4 lists it because the `∀p` goal inversion at an implication goal
   `Q ⊃ N` moves `invertPos Q` INTO the station: without the goal term that
   edge strictly RAISES the measure, and the `∀p` aggregate's goal moves
   are not strict either.  Cell (i) refutes the truncated measure.

2. **Drop the guard-deficiency component `κ`.**  Then the measure is `ν`
   alone (times nothing), and the guard edge — the whole point of the loop
   check — raises it: at cell (i) the row `A(done ⇒ ↑(a∨b))` from the `∃p`
   station adds `3 ^ wPos (a∨b)` to a measure that was `sum3 done`.

Neither defect is subtle enough to survive a designed cell, which is the
point of stage 0: both were run before the descent proof was scoped.
-/
import wip.ui_routeB_n4q_meas
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Gate 1 · `ν` without the goal weight -/

/-- The truncated weight component: `goalW` dropped. -/
def nuBad1 (s : QState) : Nat := 2 * sum3 s.1 + sum3 s.2.1

/-- The measure built on it. -/
def qMuBad1 (s : QState) : Nat := kap s * bigW s + nuBad1 s

def descBad1 (n : Nat) (s : QState) : Bool :=
  (reachQ n [s]).all (fun t => (edgesQ t).all (fun u => decide (qMuBad1 u < qMuBad1 t)))

/-- **RED**: dropping `3 ^ wNeg goal` breaks the descent already at the
◯-free cell (i). -/
theorem gate_nu_goal_term : descBad1 2 (stA cell1 goal1) = false := by decide +kernel

/-! # Gate 2 · no guard-deficiency component -/

/-- The measure without `κ`: `ν` alone. -/
def qMuBad2 (s : QState) : Nat := nu s

def descBad2 (n : Nat) (s : QState) : Bool :=
  (reachQ n [s]).all (fun t => (edgesQ t).all (fun u => decide (qMuBad2 u < qMuBad2 t)))

/-- **RED**: without `κ` the guard edge raises the measure — the failure the
loop check exists to repair. -/
theorem gate_kappa : descBad2 2 (stE cell1) = false := by decide +kernel

/-- And in `∀p` mode. -/
theorem gate_kappa_A : descBad2 2 (stA cell1 goal1) = false := by decide +kernel

/-! # The positive control at the same depth and the same cell

The two gates are not vacuous: the committed measure passes exactly where
the two defects fail. -/

theorem gate_control : descOK 2 (stA cell1 goal1) = true ∧ descOK 2 (stE cell1) = true := by
  constructor <;> decide +kernel

end LJFO

/-! ## Pins -/

#axioms_within LJFO.gate_nu_goal_term [propext, Quot.sound]
#axioms_within LJFO.gate_kappa [propext]
#axioms_within LJFO.gate_kappa_A [propext]
#axioms_within LJFO.gate_control [propext, Quot.sound]
