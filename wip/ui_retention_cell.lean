/-
The cell that exercises the retention rows of `interpF`, and the cycle
of the termination note in `LJF/OFuelMin.lean` (2026-09-04).

Everything below is a kernel-checked fact about one two-member station,
so the configuration the note reasons about is not hypothetical:

* the station is saturated, so both aggregates are the row lists of
  `LJF/OFuelMin.lean`;
* it holds a parked `◯`-implication, whose `∃p` row carries the RETAINED
  guard `A_f(done ⇒ ↑↓◯c)` — at `done`, not at the residual `[Y]`;
* it holds a parked `q`-implication, whose `∀p` attack row carries the
  conjunct `↑c`, which is what routes the `∀p` traversal back into the
  `∃p` traversal at the SAME station.

Those two rows are the two cross-edges of the cycle

    UEntry@done (↑c) → UStab@done c → TStab@done
      → UEntry@done (↑↓◯c) → UStab@done (↓◯c) → URF@done (↓◯c)
      → UEntry@done (◯c) → UEntry@done (↑c)

whose existence is what forbids a lexicographic (station-and-goal weight,
derivation size) founding of the minimality family once the retention
discharge is taken as a recursive call.
-/
import LJF.OFuelMin

namespace LJFO
namespace RetentionCell

/-- The eigenvariable. -/
def pv : String := "p"

/-- The `p`-free atom the `∃p` side is asked for at the cross-edge. -/
def cv : String := "c"

/-- The `p`-free atom both parked implications conclude. -/
def av : String := "a"

/-- The parked `◯`-implication: its `∃p` row carries the retained guard. -/
def X : Neg := .imp (.down (.circ (.atom cv))) (.up (.atom av))

/-- The parked `q`-implication: its `∀p` attack row carries `↑c`. -/
def Y : Neg := .imp (.atom cv) (.up (.atom av))

/-- The station. -/
def done : List Neg := [X, Y]

/-- Neither atom is present, so neither parked implication fires: the
station is saturated and both aggregates are row lists. -/
theorem done_saturated : Saturated done := by rfl

/-- `c` is absent, so the `∀p` aggregate at goal `↑c` is the disjunction
of `atomHead` and the attack rows, not `⊤`. -/
theorem cv_absent : atomMem cv done = false := by decide

theorem X_split : (X, [Y]) ∈ splits done := by decide

theorem Y_split : (Y, [X]) ∈ splits done := by decide

/-- **The retention row.**  In the `∃p` aggregate at fuel `f+1`, the row
of `X` guards its fire by the `∀p` interpolant of `↑↓◯c` at the FULL
station `done` — the residual `[Y]` appears only in the fire's body and
in the paired `∃p` of the residual. -/
theorem cimpRow (f : Nat) :
    nAnd
      (.imp (.down (interpF pv f [] done
              (some (.up (.down (.circ (.atom cv)))))))
           (interpF pv f [Neg.up (.atom av)] [Y] none))
      (interpF pv f [] [Y] none) ∈ eConjRowsF pv f done :=
  cimpConjMemF X_split

/-- **The cross-edge row.**  In the `∀p` aggregate at goal `↑c` and fuel
`f+1`, the attack row of `Y` has `↑c` as its first conjunct: supplying it
is a call of the `∃p` traversal at the SAME station `done`. -/
theorem qimpRow (f : Nat) :
    pGuard pv cv nBot
      (nAnd (.up (.atom cv))
        (interpF pv f [Neg.up (.atom av)] [X] (some (.up (.atom cv))))) ∈
      truStationRowsF pv f done (.atom cv) :=
  rowMem Y_split

/-- The two rows sit in the aggregates themselves, not only in the row
lists. -/
theorem eAggregate (f : Nat) :
    interpF pv (f + 1) [] done none = nAndAll (eConjRowsF pv f done) :=
  interpFE_eq done_saturated

theorem aAggregate (f : Nat) :
    interpF pv (f + 1) [] done (some (.up (.atom cv))) =
      nOrAll (atomHead pv cv ++ truStationRowsF pv f done (.atom cv)) :=
  interpFA_atom_eq done_saturated (by simp [cv_absent])

end RetentionCell
end LJFO

#axioms_within LJFO.RetentionCell.done_saturated [propext]
#axioms_within LJFO.RetentionCell.cv_absent [propext]
#axioms_within LJFO.RetentionCell.cimpRow [propext, Quot.sound]
#axioms_within LJFO.RetentionCell.qimpRow [propext, Quot.sound]
#axioms_within LJFO.RetentionCell.eAggregate [propext]
#axioms_within LJFO.RetentionCell.aAggregate [propext]
