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


/-! # Part 0b · Calibration: the transcription is faithful

`interpQ` is a 400-line re-transcription of `interpP`, so the controls above
are not enough: they exercise the atom rows, the `q`-implication rows with
their fire, the box rows, the atom goal and the ◯ goal, and nothing else.
These check the REMAINING clauses, all on the station

    cStation = [c ⊃ ↑e, ◯a]

which carries no parked compound implication, so the loop check never fires
and any difference would be a transcription error and nothing else.  Every one
is `decide +kernel`. -/

/-- A station with a `q`-implication and a box: no compound implication, so
`interpQ` must agree with `interpP` at every goal and every todo. -/
def cStation : List Neg := [.imp (.atom "c") (.up (.atom "e")), .circ (.atom "a")]

/-- The four `↑`-goal shapes and the two structural goals. -/
theorem cal_goals : ∀ f ∈ [0,1,2,3,4],
    (interpQ "p" f [] cStation (some (.up (.or (.atom "a") (.atom "b")))) []
       = interpP "p" f [] cStation (some (.up (.or (.atom "a") (.atom "b"))))) ∧
    (interpQ "p" f [] cStation (some (.up (.down (.up (.atom "a"))))) []
       = interpP "p" f [] cStation (some (.up (.down (.up (.atom "a")))))) ∧
    (interpQ "p" f [] cStation (some (.up .fls)) []
       = interpP "p" f [] cStation (some (.up .fls))) ∧
    (interpQ "p" f [] cStation (some (.and (.up (.atom "a")) (.up (.atom "b")))) []
       = interpP "p" f [] cStation (some (.and (.up (.atom "a")) (.up (.atom "b"))))) ∧
    (interpQ "p" f [] cStation (some (.imp (.atom "d") (.up (.atom "b")))) []
       = interpP "p" f [] cStation (some (.imp (.atom "d") (.up (.atom "b"))))) ∧
    (interpQ "p" f [] cStation (some (.imp (.or (.atom "d") (.atom "b")) (.up (.atom "e")))) []
       = interpP "p" f [] cStation (some (.imp (.or (.atom "d") (.atom "b")) (.up (.atom "e"))))) := by
  decide +kernel

/-- The seven ◯-goal shapes: the lax prefix, clause by clause. -/
theorem cal_circGoals : ∀ f ∈ [0,1,2,3],
    (interpQ "p" f [] cStation (some (.circ (.atom "g"))) []
       = interpP "p" f [] cStation (some (.circ (.atom "g")))) ∧
    (interpQ "p" f [] cStation (some (.circ .fls)) []
       = interpP "p" f [] cStation (some (.circ .fls))) ∧
    (interpQ "p" f [] cStation (some (.circ (.or (.atom "g") (.atom "h")))) []
       = interpP "p" f [] cStation (some (.circ (.or (.atom "g") (.atom "h"))))) ∧
    (interpQ "p" f [] cStation (some (.circ (.down (.up (.atom "g"))))) []
       = interpP "p" f [] cStation (some (.circ (.down (.up (.atom "g")))))) ∧
    (interpQ "p" f [] cStation (some (.circ (.down (.circ (.atom "g"))))) []
       = interpP "p" f [] cStation (some (.circ (.down (.circ (.atom "g")))))) ∧
    (interpQ "p" f [] cStation
        (some (.circ (.down (.and (.up (.atom "g")) (.up (.atom "h")))))) []
       = interpP "p" f [] cStation
        (some (.circ (.down (.and (.up (.atom "g")) (.up (.atom "h")))))) ) ∧
    (interpQ "p" f [] cStation
        (some (.circ (.down (.imp (.atom "g") (.up (.atom "h")))))) []
       = interpP "p" f [] cStation
        (some (.circ (.down (.imp (.atom "g") (.up (.atom "h")))))) ) := by
  decide +kernel

/-- The processing clauses: a disjunctive hypothesis in both modes, `↑⊥` in
both modes, a conjunction, a shifted negative, an inert `⊥ ⊃ N`, and each of
the three shapes `interpP` newly parks. -/
theorem cal_processing : ∀ f ∈ [0,1,2,3,4],
    (interpQ "p" f [.up (.or (.atom "d") (.atom "b"))] cStation none []
       = interpP "p" f [.up (.or (.atom "d") (.atom "b"))] cStation none) ∧
    (interpQ "p" f [.up (.or (.atom "d") (.atom "b"))] cStation (some (.up (.atom "e"))) []
       = interpP "p" f [.up (.or (.atom "d") (.atom "b"))] cStation (some (.up (.atom "e")))) ∧
    (interpQ "p" f [.up .fls] cStation none []
       = interpP "p" f [.up .fls] cStation none) ∧
    (interpQ "p" f [.up .fls] cStation (some (.up (.atom "e"))) []
       = interpP "p" f [.up .fls] cStation (some (.up (.atom "e")))) ∧
    (interpQ "p" f [.and (.up (.atom "d")) (.circ (.atom "b"))] cStation none []
       = interpP "p" f [.and (.up (.atom "d")) (.circ (.atom "b"))] cStation none) ∧
    (interpQ "p" f [.up (.down (.circ (.atom "d")))] cStation none []
       = interpP "p" f [.up (.down (.circ (.atom "d")))] cStation none) ∧
    (interpQ "p" f [.imp .fls (.up (.atom "e"))] cStation none []
       = interpP "p" f [.imp .fls (.up (.atom "e"))] cStation none) := by
  decide +kernel

/-- The five compound-implication rows, in the ONE case where the check cannot
fire: fuel 1, where the guard call is the fuel-0 default in both recursions.
Each of `oimp`, `simp`, `aimp`, `dyk`, `cimp` is exercised. -/
theorem cal_parkedRows_fuel1 :
    (interpQ "p" 1 [] cell1 none [] = interpP "p" 1 [] cell1 none) ∧
    (interpQ "p" 1 [] cell4 none [] = interpP "p" 1 [] cell4 none) ∧
    (interpQ "p" 1 [] cell3 none [] = interpP "p" 1 [] cell3 none) ∧
    (interpQ "p" 1 [] [.imp (.down (.and (.up (.atom "a")) (.up (.atom "b"))))
                            (.up (.atom "c"))] none []
       = interpP "p" 1 [] [.imp (.down (.and (.up (.atom "a")) (.up (.atom "b"))))
                            (.up (.atom "c"))] none) ∧
    (interpQ "p" 1 [] [.imp (.down (.circ (.atom "a"))) (.up (.atom "b"))] none []
       = interpP "p" 1 [] [.imp (.down (.circ (.atom "a"))) (.up (.atom "b"))] none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! # Part 1 · The six ◯-free cells

`interpP`'s chains at these cells are strictly `sizeNeg`-ascending
(`not_aStabEq1`…`not_aStabEq6d`).  `interpQ`'s are literally constant from the
fuel recorded here. -/

/-- (i) `[(a ∨ b) ⊃ ↑c] ⇒ ↑(a ∨ b)` — the self-attack.  Constant from 4. -/
theorem q1_A : ∀ f ∈ [5,6,7],
    interpQ "p" f [] cell1 (some goal1) [] = interpQ "p" 4 [] cell1 (some goal1) [] := by
  decide +kernel

/-- (i) the ∃p chain.  Constant from 3. -/
theorem q1_E : ∀ f ∈ [4,5,6],
    interpQ "p" f [] cell1 none [] = interpQ "p" 3 [] cell1 none [] := by
  decide +kernel

/-- (ii) the 2-cycle `[(a∨b) ⊃ ↑c, (c∨d) ⊃ ↑a] ⇒ ↑(a∨b)`.  Constant from 6. -/
theorem q2_A : ∀ f ∈ [7,8],
    interpQ "p" f [] cell2 (some goal2ab) []
      = interpQ "p" 6 [] cell2 (some goal2ab) [] := by
  decide +kernel

/-- (ii) at the other goal of the cycle. -/
theorem q2_Acd : ∀ f ∈ [7,8],
    interpQ "p" f [] cell2 (some goal2cd) []
      = interpQ "p" 6 [] cell2 (some goal2cd) [] := by
  decide +kernel

/-- (iii) the Dyckhoff shape `[↓(a ⊃ ↑b) ⊃ ↑c] ⇒ ↑↓(a ⊃ ↑b)`.  Constant from 12
— the LATEST of the ◯-free cells, and the one that refutes the per-station
policy (Part 3). -/
theorem q3_A : ∀ f ∈ [13,14],
    interpQ "p" f [] cell3 (some goal3) [] = interpQ "p" 12 [] cell3 (some goal3) [] := by
  decide +kernel

/-- (iii) the ∃p chain.  Constant from 9. -/
theorem q3_E : ∀ f ∈ [10,11,12],
    interpQ "p" f [] cell3 none [] = interpQ "p" 9 [] cell3 none [] := by
  decide +kernel

/-- (iv) the shift shape `[↓↑a ⊃ ↑b] ⇒ ↑↓↑a`.  Constant from 4. -/
theorem q4_A : ∀ f ∈ [5,6,7],
    interpQ "p" f [] cell4 (some goal4) [] = interpQ "p" 4 [] cell4 (some goal4) [] := by
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
theorem q6_Aab : ∀ f ∈ [7,8],
    interpQ "p" f [] cell6 (some goal6ab) []
      = interpQ "p" 6 [] cell6 (some goal6ab) [] := by
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

/-- (m2) at the ◯-implication's own guard goal `↑↓◯a`.  Constant from 6. -/
theorem qm2_A : ∀ f ∈ [7,8],
    interpQ "p" f [] m2 (some (.up (.down (.circ (.atom "a"))))) []
      = interpQ "p" 6 [] m2 (some (.up (.down (.circ (.atom "a"))))) [] := by
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
goal.  Constant from 12 — the deepest threshold measured, with S1 at the ◯-goal. -/
theorem qS1_A : ∀ f ∈ [13,14],
    interpQ "p" f [] s1Station (some (.up (.atom "e"))) []
      = interpQ "p" 12 [] s1Station (some (.up (.atom "e"))) [] := by
  decide +kernel

/-- **S1** at the ◯-goal.  Constant from 13. -/
theorem qS1_Ac : ∀ f ∈ [14,15],
    interpQ "p" f [] s1Station (some (.circ (.atom "g"))) []
      = interpQ "p" 13 [] s1Station (some (.circ (.atom "g"))) [] := by
  decide +kernel

/-- **S1**, the ∃p chain.  Constant from 12. -/
theorem qS1_E : ∀ f ∈ [13,14],
    interpQ "p" f [] s1Station none [] = interpQ "p" 12 [] s1Station none [] := by
  decide +kernel


/-! # Part 2b · Harder modal shapes

The refutation candidate of the package is a chain of stations that keeps
reopening boxes — the Ghilardi–Zawadowski shape.  (m1)–(m5) do not reach it:
they each have one box or one ◯-implication.  These six do, and none of them
refutes the design.

  (m6)  a ◯-implication whose BOXED ANTECEDENT carries another ◯-implication
  (m7)  opening a box PRODUCES a ◯-implication whose guard reopens
  (m8)  firing RE-CREATES the same ◯-implication under a box
  (m9)  box opening creates a parked implication whose BODY is a box
  (m10) the S1 variant whose FIRE re-creates the guard's antecedent — the
        deepest threshold in the package, 16
  (m11) two nested boxes -/

/-- The inner ◯-implication `↓◯a ⊃ ↑b`. -/
def qInner : Neg := .imp (.down (.circ (.atom "a"))) (.up (.atom "b"))
/-- `↓(d ⊃ ↑a)`, S1's boxed antecedent body. -/
def qDA : Pos := .down (.imp (.atom "d") (.up (.atom "a")))

def m6 : List Neg := [.imp (.down (.circ (.down qInner))) (.up (.atom "c"))]
def m7 : List Neg := [.circ (.down qInner), .circ (.atom "a")]
def m8 : List Neg := [.imp (.down (.circ (.atom "a"))) (.circ (.down qInner))]
def m9 : List Neg :=
  [.circ (.down (.imp (.or (.atom "a") (.atom "b")) (.circ (.atom "c"))))]
def m10 : List Neg :=
  [.imp (.down (.circ qDA)) (.circ (.atom "g")), .imp (.atom "c") (.circ qDA)]
def m11 : List Neg :=
  [.circ (.down (.circ (.down (.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))))))]

/-- (m6) nested guards through a box.  Constant from 10. -/
theorem qm6_A : ∀ f ∈ [11,12],
    interpQ "p" f [] m6 (some (.up (.atom "c"))) []
      = interpQ "p" 10 [] m6 (some (.up (.atom "c"))) [] := by
  decide +kernel

/-- (m6) the ∃p chain.  Constant from 10. -/
theorem qm6_E : ∀ f ∈ [11,12],
    interpQ "p" f [] m6 none [] = interpQ "p" 10 [] m6 none [] := by
  decide +kernel

/-- (m7) opening a box produces a ◯-implication whose guard reopens.
Constant from 10. -/
theorem qm7_A : ∀ f ∈ [11,12],
    interpQ "p" f [] m7 (some (.circ (.atom "b"))) []
      = interpQ "p" 10 [] m7 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- (m8) firing re-creates the same ◯-implication under a box.
Constant from 10. -/
theorem qm8_A : ∀ f ∈ [11,12],
    interpQ "p" f [] m8 (some (.circ (.atom "b"))) []
      = interpQ "p" 10 [] m8 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- (m9) a parked implication with a boxed body, made by opening a box.
Constant from 9. -/
theorem qm9_A : ∀ f ∈ [10,11,12],
    interpQ "p" f [] m9 (some (.circ (.atom "d"))) []
      = interpQ "p" 9 [] m9 (some (.circ (.atom "d"))) [] := by
  decide +kernel

/-- (m11) two nested boxes.  Constant from 10. -/
theorem qm11_A : ∀ f ∈ [11,12],
    interpQ "p" f [] m11 (some (.circ (.atom "d"))) []
      = interpQ "p" 10 [] m11 (some (.circ (.atom "d"))) [] := by
  decide +kernel

/-- **(m10)**, the deepest cell in the package: the S1 variant whose fire
re-creates the guard's antecedent.  Constant from 16 — and its ∃p chain has a
FALSE fixpoint at 12/13 before it climbs again, which is why every certificate
here checks two or three fuels above the threshold and never one. -/
theorem qm10_A : ∀ f ∈ [17,18],
    interpQ "p" f [] m10 (some (.circ (.atom "g"))) []
      = interpQ "p" 16 [] m10 (some (.circ (.atom "g"))) [] := by
  decide +kernel

/-- (m10) the ∃p chain.  Constant from 15. -/
theorem qm10_E : ∀ f ∈ [16,17],
    interpQ "p" f [] m10 none [] = interpQ "p" 15 [] m10 none [] := by
  decide +kernel

/-- (m10) the false fixpoint, kernel-checked: the ∃p chain repeats at fuel 12
and then moves again at 14.  A single repeated level is NOT stabilisation. -/
theorem qm10_false_fixpoint :
    interpQ "p" 12 [] m10 none [] = interpQ "p" 13 [] m10 none [] ∧
    interpQ "p" 13 [] m10 none [] ≠ interpQ "p" 14 [] m10 none [] := by
  constructor <;> decide +kernel

/-! # Part 3 · The per-station policy is REFUTED

The blueprint's WP3 loop elimination resets `seen` at every station change,
"because the antecedents of a station are finitely many".  Cell (iii) refutes
it, and the cell is ◯-FREE, so the failure is not modal:

    A(cell3 ⇒ ↑↓(a ⊃ ↑b))  --goal inversion-->  A(cell3 ⇒ a ⊃ ↑b)
      --implication branch, station grows by ↑a, seen RESET-->
        E([↑a] ++ cell3)  --Dyckhoff guard-->  A(… ⇒ ↑↓(a ⊃ ↑b))  at the
        bigger station,

so the guard loop survives with the station growing by one `↑a` each time
round.  The chain is not constant at any of the fuels below, where the global
policy already is; each inequality is kernel-checked.  (This is not a `∀ f` refutation — that would need the
ascent lemma — but it settles the design question the policy was chosen for:
`interpQ0` has no repeated level through fuel 16 where `interpQ` has one at
12.) -/

theorem q0_3_not_const : ∀ f ∈ [12,13,14,15],
    interpQ0 "p" f [] cell3 (some goal3) []
      ≠ interpQ0 "p" (f + 1) [] cell3 (some goal3) [] := by
  decide +kernel

/-- The same station, the same fuels, under the global policy: constant. -/
theorem q_3_const_there : ∀ f ∈ [12,13,14,15],
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
#axioms_within LJFO.cal_goals [propext]
#axioms_within LJFO.cal_circGoals [propext]
#axioms_within LJFO.cal_processing [propext]
#axioms_within LJFO.cal_parkedRows_fuel1 [propext]
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
#axioms_within LJFO.qm6_A [propext]
#axioms_within LJFO.qm6_E [propext]
#axioms_within LJFO.qm7_A [propext]
#axioms_within LJFO.qm8_A [propext]
#axioms_within LJFO.qm9_A [propext]
#axioms_within LJFO.qm11_A [propext]
#axioms_within LJFO.qm10_A [propext]
#axioms_within LJFO.qm10_E [propext]
#axioms_within LJFO.qm10_false_fixpoint [propext]
#axioms_within LJFO.q0_3_not_const [propext]
#axioms_within LJFO.q_3_const_there [propext]
