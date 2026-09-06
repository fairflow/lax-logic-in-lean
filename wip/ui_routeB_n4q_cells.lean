/-
Route (B), node **N4**, WP8, stage 1: the DESIGNED cells for the loop-checked
recursion `interpQ` (`wip/ui_routeB_n4q.lean`), and the refutation of the
blueprint's PER-STATION loop check `interpQ0`.

Rule 9 of `CLAUDE.md`: no enumeration.  The cells are the six ◯-free cells of
`docs/n4-circfree-cases.md` — on which the literal chain of `interpP` is
REFUTED (five of them) — and five modal cells chosen from the shapes the
recursion can loop through, plus the running cell S1 of
`docs/ui-ljfo-clause-table.md` §4.12.

Each verdict is a KERNEL-CHECKED equation `interpQ p f … = interpQ p W …` at
the fuels above the measured threshold `W` — evidence of literal constancy at
those fuels, not the ∀-quantified statement, which is `QStabLit` and is proved
from a bound, not from a decide.
-/
import wip.ui_routeB_n4q
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 0 · Positive and negative controls against `interpP`

Where no parked compound implication is ever reached, the loop check never
fires and `interpQ` IS `interpP`; where one is, they differ.  Both halves are
kernel-checked, so the change is located exactly. -/

/-- A station with only an atom and a `q`-implication (cell (v)). -/
theorem q_eq_p_cell5 : ∀ f ∈ [0,1,2,3,4,5],
    interpQ "p" f [] cell5 (some goal5) [] = interpP "p" f [] cell5 (some goal5) := by
  decide +kernel

theorem q_eq_p_cell5E : ∀ f ∈ [0,1,2,3,4,5],
    interpQ "p" f [] cell5 none [] = interpP "p" f [] cell5 none := by
  decide +kernel

/-- A station carrying only a parked box. -/
def qBox : List Neg := [.circ (.atom "a")]

theorem q_eq_p_box : ∀ f ∈ [0,1,2,3,4,5],
    interpQ "p" f [] qBox (some (.circ (.atom "b"))) []
      = interpP "p" f [] qBox (some (.circ (.atom "b"))) := by
  decide +kernel

/-- A station carrying only a `q`-implication with a boxed body. -/
def qCimpAtom : List Neg := [.imp (.atom "c") (.circ (.atom "g"))]

theorem q_eq_p_qimpBox : ∀ f ∈ [0,1,2,3,4],
    interpQ "p" f [] qCimpAtom (some (.up (.atom "e"))) []
      = interpP "p" f [] qCimpAtom (some (.up (.atom "e"))) := by
  decide +kernel

/-- **The negative control**: at cell (i) the two DIFFER from fuel 2 on — the
self-attack row is exactly what the loop check removes. -/
theorem q_ne_p_cell1 : ∀ f ∈ [2,3,4],
    interpQ "p" f [] cell1 (some goal1) [] ≠ interpP "p" f [] cell1 (some goal1) := by
  decide +kernel

/-! # Part 1 · The six ◯-free cells

`interpP`'s chains at these cells are strictly `sizeNeg`-ascending
(`not_aStabEq1`…`not_aStabEq6d`).  `interpQ`'s are literally constant from the
fuel recorded here. -/

/-- (i) `[(a ∨ b) ⊃ ↑c] ⇒ ↑(a ∨ b)` — the self-attack.  Constant from 2. -/
theorem q1_A : ∀ f ∈ [3,4,5,6],
    interpQ "p" f [] cell1 (some goal1) [] = interpQ "p" 2 [] cell1 (some goal1) [] := by
  decide +kernel

/-- (i) the ∃p chain.  Constant from 3. -/
theorem q1_E : ∀ f ∈ [4,5,6,7],
    interpQ "p" f [] cell1 none [] = interpQ "p" 3 [] cell1 none [] := by
  decide +kernel

/-- (ii) the 2-cycle `[(a∨b) ⊃ ↑c, (c∨d) ⊃ ↑a] ⇒ ↑(a∨b)`.  Constant from 4. -/
theorem q2_A : ∀ f ∈ [5,6,7],
    interpQ "p" f [] cell2 (some goal2ab) []
      = interpQ "p" 4 [] cell2 (some goal2ab) [] := by
  decide +kernel

/-- (ii) at the other goal of the cycle. -/
theorem q2_Acd : ∀ f ∈ [5,6,7],
    interpQ "p" f [] cell2 (some goal2cd) []
      = interpQ "p" 4 [] cell2 (some goal2cd) [] := by
  decide +kernel

/-- (iii) the Dyckhoff shape `[↓(a ⊃ ↑b) ⊃ ↑c] ⇒ ↑↓(a ⊃ ↑b)`.  Constant from 8
— the LATEST of the ◯-free cells, and the one that refutes the per-station
policy (Part 3). -/
theorem q3_A : ∀ f ∈ [9,10,11],
    interpQ "p" f [] cell3 (some goal3) [] = interpQ "p" 8 [] cell3 (some goal3) [] := by
  decide +kernel

/-- (iii) the ∃p chain.  Constant from 9. -/
theorem q3_E : ∀ f ∈ [10,11,12],
    interpQ "p" f [] cell3 none [] = interpQ "p" 9 [] cell3 none [] := by
  decide +kernel

/-- (iv) the shift shape `[↓↑a ⊃ ↑b] ⇒ ↑↓↑a`.  Constant from 2. -/
theorem q4_A : ∀ f ∈ [3,4,5,6],
    interpQ "p" f [] cell4 (some goal4) [] = interpQ "p" 2 [] cell4 (some goal4) [] := by
  decide +kernel

/-- (v) the unsaturated control `[p ⊃ ↑c, ↑p] ⇒ ↑c`.  Constant from 3, as for
`interpP` (`aStabEq5`). -/
theorem q5_A : ∀ f ∈ [4,5,6,7],
    interpQ "p" f [] cell5 (some goal5) [] = interpQ "p" 3 [] cell5 (some goal5) [] := by
  decide +kernel

/-- (vi) nested guards `[(a∨b) ⊃ ↑c, ↓↑c ⊃ ↑d] ⇒ ↑d`.  Constant from 5. -/
theorem q6_A : ∀ f ∈ [6,7,8],
    interpQ "p" f [] cell6 (some goal6d) []
      = interpQ "p" 5 [] cell6 (some goal6d) [] := by
  decide +kernel

/-- (vi) at the inner goal.  Constant from 4. -/
theorem q6_Aab : ∀ f ∈ [5,6,7],
    interpQ "p" f [] cell6 (some goal6ab) []
      = interpQ "p" 4 [] cell6 (some goal6ab) [] := by
  decide +kernel

/-! # Part 2 · The modal cells

The direction the ◯-free transport of `n4_circFree_uncond` cannot reach.  Five
designed shapes and the running cell S1. -/

/-- (m1) a parked box under a lax goal: `[◯a] ⇒ ◯b`. -/
def m1 : List Neg := [.circ (.atom "a")]
/-- (m2) a ◯-implication with a self-referential guard: `[↓◯a ⊃ ↑b]`. -/
def m2 : List Neg := [.imp (.down (.circ (.atom "a"))) (.up (.atom "b"))]
/-- (m3) a box whose opening re-creates a parked implication. -/
def m3 : List Neg := [.circ (.down (.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))))]
/-- (m4) a ◯-implication whose fire re-creates a box: `[↓◯a ⊃ ◯b]`. -/
def m4 : List Neg := [.imp (.down (.circ (.atom "a"))) (.circ (.atom "b"))]
/-- (m5) a box and a ◯-implication on the same antecedent. -/
def m5 : List Neg := [.circ (.atom "a"), .imp (.down (.circ (.atom "a"))) (.up (.atom "b"))]

/-- (m1) constant from 4. -/
theorem qm1_A : ∀ f ∈ [5,6,7],
    interpQ "p" f [] m1 (some (.circ (.atom "b"))) []
      = interpQ "p" 4 [] m1 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- (m2) at the ◯-implication's own guard goal `↑↓◯a`.  Constant from 3. -/
theorem qm2_A : ∀ f ∈ [4,5,6],
    interpQ "p" f [] m2 (some (.up (.down (.circ (.atom "a"))))) []
      = interpQ "p" 3 [] m2 (some (.up (.down (.circ (.atom "a"))))) [] := by
  decide +kernel

/-- (m2) at the ◯-goal underneath it.  Constant from 5. -/
theorem qm2_Ac : ∀ f ∈ [6,7,8],
    interpQ "p" f [] m2 (some (.circ (.atom "a"))) []
      = interpQ "p" 5 [] m2 (some (.circ (.atom "a"))) [] := by
  decide +kernel

/-- (m3) the box that re-creates a parked implication.  Constant from 7. -/
theorem qm3_A : ∀ f ∈ [8,9,10],
    interpQ "p" f [] m3 (some (.circ (.atom "c"))) []
      = interpQ "p" 7 [] m3 (some (.circ (.atom "c"))) [] := by
  decide +kernel

/-- (m4) the fire that re-creates a box.  Constant from 6. -/
theorem qm4_A : ∀ f ∈ [7,8,9],
    interpQ "p" f [] m4 (some (.circ (.atom "b"))) []
      = interpQ "p" 6 [] m4 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- (m5) box and ◯-implication together.  Constant from 7. -/
theorem qm5_A : ∀ f ∈ [8,9],
    interpQ "p" f [] m5 (some (.circ (.atom "b"))) []
      = interpQ "p" 7 [] m5 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- **S1**, the running cell `[↓◯(↓(d ⊃ ↑a)) ⊃ ↑e, c ⊃ ◯g]`, at the shift
goal.  Constant from 13 — the deepest threshold measured. -/
theorem qS1_A : ∀ f ∈ [14,15],
    interpQ "p" f [] s1Station (some (.up (.atom "e"))) []
      = interpQ "p" 13 [] s1Station (some (.up (.atom "e"))) [] := by
  decide +kernel

/-- **S1** at the ◯-goal.  Constant from 14. -/
theorem qS1_Ac : ∀ f ∈ [15,16],
    interpQ "p" f [] s1Station (some (.circ (.atom "g"))) []
      = interpQ "p" 14 [] s1Station (some (.circ (.atom "g"))) [] := by
  decide +kernel

/-- **S1**, the ∃p chain.  Constant from 13. -/
theorem qS1_E : ∀ f ∈ [14,15],
    interpQ "p" f [] s1Station none [] = interpQ "p" 13 [] s1Station none [] := by
  decide +kernel

/-! # Part 3 · The per-station policy is REFUTED

The blueprint's WP3 loop elimination resets `seen` at every station change,
"because the antecedents of a station are finitely many".  Cell (iii) refutes
it, and the cell is ◯-FREE, so the failure is not modal:

    A(cell3 ⇒ ↑↓(a ⊃ ↑b))  --goal inversion-->  A(cell3 ⇒ a ⊃ ↑b)
      --implication branch, station grows by ↑a, seen RESET-->
        E([↑a] ++ cell3)  --Dyckhoff guard-->  A(… ⇒ ↑↓(a ⊃ ↑b))  at the
        bigger station,

so the guard loop survives with the station growing by one `↑a` each time
round.  The chain is not constant at any of the fuels below; each inequality
is kernel-checked.  (This is not a `∀ f` refutation — that would need the
ascent lemma — but it settles the design question the policy was chosen for:
`interpQ0` has no fixpoint below fuel 12 where `interpQ` has one at 8.) -/

theorem q0_3_not_const : ∀ f ∈ [8,9,10,11],
    interpQ0 "p" f [] cell3 (some goal3) []
      ≠ interpQ0 "p" (f + 1) [] cell3 (some goal3) [] := by
  decide +kernel

/-- The same station, the same fuels, under the global policy: constant. -/
theorem q_3_const_there : ∀ f ∈ [8,9,10,11],
    interpQ "p" f [] cell3 (some goal3) []
      = interpQ "p" (f + 1) [] cell3 (some goal3) [] := by
  decide +kernel

end LJFO

/-! ## Pins -/

#axioms_within LJFO.q_eq_p_cell5 [propext]
#axioms_within LJFO.q_eq_p_cell5E [propext]
#axioms_within LJFO.q_eq_p_box [propext]
#axioms_within LJFO.q_eq_p_qimpBox [propext]
#axioms_within LJFO.q_ne_p_cell1 [propext]
#axioms_within LJFO.q1_A [propext]
#axioms_within LJFO.q1_E [propext]
#axioms_within LJFO.q2_A [propext]
#axioms_within LJFO.q2_Acd [propext]
#axioms_within LJFO.q3_A [propext]
#axioms_within LJFO.q3_E [propext]
#axioms_within LJFO.q4_A [propext]
#axioms_within LJFO.q5_A [propext]
#axioms_within LJFO.q6_A [propext]
#axioms_within LJFO.q6_Aab [propext]
#axioms_within LJFO.qm1_A [propext]
#axioms_within LJFO.qm2_A [propext]
#axioms_within LJFO.qm2_Ac [propext]
#axioms_within LJFO.qm3_A [propext]
#axioms_within LJFO.qm4_A [propext]
#axioms_within LJFO.qm5_A [propext]
#axioms_within LJFO.qS1_A [propext]
#axioms_within LJFO.qS1_Ac [propext]
#axioms_within LJFO.qS1_E [propext]
#axioms_within LJFO.q0_3_not_const [propext]
#axioms_within LJFO.q_3_const_there [propext]
