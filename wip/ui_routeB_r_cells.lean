/-
Route (B), node **N4**, WP12, Stage 0 / **R1**: the DESIGNED cells for the
pair-recording recursion `interpR` (`wip/ui_routeB_r_def.lean`).

Rule 9 of `CLAUDE.md`: no enumeration.  The cells are the eighteen of
`wip/ui_routeB_n4q_cells.lean` — the six ◯-free cells of
`docs/n4-circfree-cases.md`, five designed modal cells, the six
Ghilardi–Zawadowski shapes and the running cell S1 — together with the two
cells the `PQEquiv` campaign designed, (vii) (`docs/pqequiv-cases.md` §4)
and (ix) (`docs/pqhard-cases.md`, `_probe/stage0d.lean`).

Each verdict is a KERNEL-CHECKED equation `interpR p f … = interpR p T …`
at the three fuels `T+1, T+2, T+3` above the measured threshold `T` —
evidence of literal constancy at those fuels, not the ∀-quantified
statement, which is `RBound` and is proved from a measure, not from a
`decide`.  THREE fuels and never one: the measured first-repeat column of
`docs/n4-pair-design.md` §2 shows false fixpoints at nine of the thirty-one
chains, one of them (cell (m6)) twenty-nine fuels below its threshold.
-/
import wip.ui_routeB_r_def
import wip.ui_routeB_n4q_cells
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 0 · Calibration: the transcription is faithful

`interpR` is a re-transcription of `interpG`, so the cells are not enough:
they exercise the parked rows and little else.  These locate the change
exactly.  Where the loop check cannot fire the two must AGREE, clause for
clause; where the pair test is coarser than the antecedent test they must
DIFFER, and the fuel at which they first differ is recorded. -/

/-- Every goal shape and every processing clause, on the station
`cStation = [c ⊃ ↑e, ◯a]`, which carries no compound implication: the check
never fires, so `interpR` must be `interpQ` here, and any difference would
be a transcription error and nothing else. -/
theorem r_eq_q_cal : ∀ f ∈ [0,1,2,3,4],
    (interpR "p" f [] cStation (some (.up (.atom "e"))) []
       = interpQ "p" f [] cStation (some (.up (.atom "e"))) []) ∧
    (interpR "p" f [] cStation (some (.up (.or (.atom "a") (.atom "b")))) []
       = interpQ "p" f [] cStation (some (.up (.or (.atom "a") (.atom "b")))) []) ∧
    (interpR "p" f [] cStation (some (.up (.down (.up (.atom "a"))))) []
       = interpQ "p" f [] cStation (some (.up (.down (.up (.atom "a"))))) []) ∧
    (interpR "p" f [] cStation (some (.up .fls)) []
       = interpQ "p" f [] cStation (some (.up .fls)) []) ∧
    (interpR "p" f [] cStation (some (.and (.up (.atom "a")) (.up (.atom "b")))) []
       = interpQ "p" f [] cStation (some (.and (.up (.atom "a")) (.up (.atom "b")))) []) ∧
    (interpR "p" f [] cStation (some (.imp (.atom "d") (.up (.atom "b")))) []
       = interpQ "p" f [] cStation (some (.imp (.atom "d") (.up (.atom "b")))) []) ∧
    (interpR "p" f [] cStation
        (some (.imp (.or (.atom "d") (.atom "b")) (.up (.atom "e")))) []
       = interpQ "p" f [] cStation
        (some (.imp (.or (.atom "d") (.atom "b")) (.up (.atom "e")))) []) := by
  decide +kernel

/-- The seven ◯-goal shapes: the lax prefix, clause by clause. -/
theorem r_eq_q_calCirc : ∀ f ∈ [0,1,2,3],
    (interpR "p" f [] cStation (some (.circ (.atom "g"))) []
       = interpQ "p" f [] cStation (some (.circ (.atom "g"))) []) ∧
    (interpR "p" f [] cStation (some (.circ .fls)) []
       = interpQ "p" f [] cStation (some (.circ .fls)) []) ∧
    (interpR "p" f [] cStation (some (.circ (.or (.atom "g") (.atom "h")))) []
       = interpQ "p" f [] cStation (some (.circ (.or (.atom "g") (.atom "h")))) []) ∧
    (interpR "p" f [] cStation (some (.circ (.down (.up (.atom "g"))))) []
       = interpQ "p" f [] cStation (some (.circ (.down (.up (.atom "g"))))) []) ∧
    (interpR "p" f [] cStation (some (.circ (.down (.circ (.atom "g"))))) []
       = interpQ "p" f [] cStation (some (.circ (.down (.circ (.atom "g"))))) []) ∧
    (interpR "p" f [] cStation
        (some (.circ (.down (.and (.up (.atom "g")) (.up (.atom "h")))))) []
       = interpQ "p" f [] cStation
        (some (.circ (.down (.and (.up (.atom "g")) (.up (.atom "h")))))) []) ∧
    (interpR "p" f [] cStation
        (some (.circ (.down (.imp (.atom "g") (.up (.atom "h")))))) []
       = interpQ "p" f [] cStation
        (some (.circ (.down (.imp (.atom "g") (.up (.atom "h")))))) []) := by
  decide +kernel

/-- The processing clauses: a disjunctive hypothesis in both modes, `↑⊥` in
both modes, a conjunction, a shifted negative, an inert `⊥ ⊃ N`. -/
theorem r_eq_q_calProc : ∀ f ∈ [0,1,2,3,4],
    (interpR "p" f [.up (.or (.atom "d") (.atom "b"))] cStation none []
       = interpQ "p" f [.up (.or (.atom "d") (.atom "b"))] cStation none []) ∧
    (interpR "p" f [.up (.or (.atom "d") (.atom "b"))] cStation (some (.up (.atom "e"))) []
       = interpQ "p" f [.up (.or (.atom "d") (.atom "b"))] cStation (some (.up (.atom "e"))) []) ∧
    (interpR "p" f [.up .fls] cStation none []
       = interpQ "p" f [.up .fls] cStation none []) ∧
    (interpR "p" f [.up .fls] cStation (some (.up (.atom "e"))) []
       = interpQ "p" f [.up .fls] cStation (some (.up (.atom "e"))) []) ∧
    (interpR "p" f [.and (.up (.atom "d")) (.circ (.atom "b"))] cStation none []
       = interpQ "p" f [.and (.up (.atom "d")) (.circ (.atom "b"))] cStation none []) ∧
    (interpR "p" f [.up (.down (.circ (.atom "d")))] cStation none []
       = interpQ "p" f [.up (.down (.circ (.atom "d")))] cStation none []) ∧
    (interpR "p" f [.imp .fls (.up (.atom "e"))] cStation none []
       = interpQ "p" f [.imp .fls (.up (.atom "e"))] cStation none []) := by
  decide +kernel

/-- The five compound-implication rows at fuel 1, where the guard call is the
fuel-0 default in both recursions: each of `oimp`, `simp`, `aimp`, `dyk`,
`cimp` exercised. -/
theorem r_eq_q_rows_fuel1 :
    (interpR "p" 1 [] cell1 none [] = interpQ "p" 1 [] cell1 none []) ∧
    (interpR "p" 1 [] cell4 none [] = interpQ "p" 1 [] cell4 none []) ∧
    (interpR "p" 1 [] cell3 none [] = interpQ "p" 1 [] cell3 none []) ∧
    (interpR "p" 1 [] [.imp (.down (.and (.up (.atom "a")) (.up (.atom "b"))))
                            (.up (.atom "c"))] none []
       = interpQ "p" 1 [] [.imp (.down (.and (.up (.atom "a")) (.up (.atom "b"))))
                            (.up (.atom "c"))] none []) ∧
    (interpR "p" 1 [] [.imp (.down (.circ (.atom "a"))) (.up (.atom "b"))] none []
       = interpQ "p" 1 [] [.imp (.down (.circ (.atom "a"))) (.up (.atom "b"))] none []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Cell (i) has ONE compound antecedent and its station never changes, so
the antecedent test and the pair test coincide there at every fuel: the two
recursions agree. -/
theorem r_eq_q_cell1 : ∀ f ∈ [0,1,2,3,4,5,6,7,8],
    (interpR "p" f [] cell1 (some goal1) [] = interpQ "p" f [] cell1 (some goal1) []) ∧
    (interpR "p" f [] cell1 none [] = interpQ "p" f [] cell1 none []) := by
  decide +kernel

/-- **The negative controls.**  Where the station GROWS, the pair test does not
cut what the antecedent test cuts, and the two recursions differ from the fuel
recorded here: cell (iii) from 5, cell (vi) from 4, (m10) from 4. -/
theorem r_ne_q_cell3 : ∀ f ∈ [5,6,7,8],
    interpR "p" f [] cell3 (some goal3) [] ≠ interpQ "p" f [] cell3 (some goal3) [] := by
  decide +kernel

theorem r_ne_q_cell6 : ∀ f ∈ [4,5,6],
    interpR "p" f [] cell6 (some goal6d) [] ≠ interpQ "p" f [] cell6 (some goal6d) [] := by
  decide +kernel

theorem r_ne_q_m10 : ∀ f ∈ [4,5,6],
    interpR "p" f [] m10 (some (.circ (.atom "g"))) []
      ≠ interpQ "p" f [] m10 (some (.circ (.atom "g"))) [] := by
  decide +kernel

/-! # Part 1 · R1 on the ◯-free cells (rule 8: these first)

The station of cell (iii) grows by one `↑a` per round as a LIST — which is
what refutes the blueprint's per-station reset (`docs/n4-loopcheck.md` §2) —
and stabilises after one round as a SET.  It is the decisive cell for the
pair design, and it bottoms out at 13. -/

/-- (i) `[(a ∨ b) ⊃ ↑c] ⇒ ↑(a ∨ b)`, the self-attack.  Constant from 4. -/
theorem r1_A : ∀ f ∈ [5,6,7],
    interpR "p" f [] cell1 (some goal1) [] = interpR "p" 4 [] cell1 (some goal1) [] := by
  decide +kernel

/-- (i) the ∃p chain.  Constant from 3. -/
theorem r1_E : ∀ f ∈ [4,5,6],
    interpR "p" f [] cell1 none [] = interpR "p" 3 [] cell1 none [] := by
  decide +kernel

/-- (ii) the 2-cycle `[(a∨b) ⊃ ↑c, (c∨d) ⊃ ↑a] ⇒ ↑(a∨b)`.  Constant from 8. -/
theorem r2_A : ∀ f ∈ [9,10,11],
    interpR "p" f [] cell2 (some goal2ab) []
      = interpR "p" 8 [] cell2 (some goal2ab) [] := by
  decide +kernel

/-- (ii) at the other goal of the cycle.  Constant from 8. -/
theorem r2_Acd : ∀ f ∈ [9,10,11],
    interpR "p" f [] cell2 (some goal2cd) []
      = interpR "p" 8 [] cell2 (some goal2cd) [] := by
  decide +kernel

/-- **(iii)** the Dyckhoff shape `[↓(a ⊃ ↑b) ⊃ ↑c] ⇒ ↑↓(a ⊃ ↑b)` — the cell
that refutes the LIST-based per-station reset.  Read as a SET the station
stabilises after one round and the chain bottoms out: constant from 13. -/
theorem r3_A : ∀ f ∈ [14,15,16],
    interpR "p" f [] cell3 (some goal3) [] = interpR "p" 13 [] cell3 (some goal3) [] := by
  decide +kernel

/-- (iii) the ∃p chain.  Constant from 13 — and it has a FALSE FIXPOINT at 9. -/
theorem r3_E : ∀ f ∈ [14,15,16],
    interpR "p" f [] cell3 none [] = interpR "p" 13 [] cell3 none [] := by
  decide +kernel

/-- (iii) the false fixpoint, kernel-checked: the ∃p chain repeats at 9 and
moves again. -/
theorem r3_E_false_fixpoint :
    interpR "p" 9 [] cell3 none [] = interpR "p" 10 [] cell3 none [] ∧
    interpR "p" 10 [] cell3 none [] ≠ interpR "p" 11 [] cell3 none [] := by
  constructor <;> decide +kernel

/-- (iv) the shift shape `[↓↑a ⊃ ↑b] ⇒ ↑↓↑a`.  Constant from 4. -/
theorem r4_A : ∀ f ∈ [5,6,7],
    interpR "p" f [] cell4 (some goal4) [] = interpR "p" 4 [] cell4 (some goal4) [] := by
  decide +kernel

/-- (v) the unsaturated control `[p ⊃ ↑c, ↑p] ⇒ ↑c`.  Constant from 3. -/
theorem r5_A : ∀ f ∈ [4,5,6],
    interpR "p" f [] cell5 (some goal5) [] = interpR "p" 3 [] cell5 (some goal5) [] := by
  decide +kernel

/-- (vi) nested guards `[(a∨b) ⊃ ↑c, ↓↑c ⊃ ↑d] ⇒ ↑d`.  Constant from 7. -/
theorem r6_A : ∀ f ∈ [8,9,10],
    interpR "p" f [] cell6 (some goal6d) []
      = interpR "p" 7 [] cell6 (some goal6d) [] := by
  decide +kernel

/-- (vi) at the inner goal.  Constant from 8. -/
theorem r6_Aab : ∀ f ∈ [9,10,11],
    interpR "p" f [] cell6 (some goal6ab) []
      = interpR "p" 8 [] cell6 (some goal6ab) [] := by
  decide +kernel

/-! ## The two cells the `PQEquiv` campaign designed -/

/-- cell (vii) (`docs/pqequiv-cases.md` §4): a Dyckhoff-parked implication
whose inner antecedent is DISJUNCTIVE. -/
def q7 : Pos := .down (.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c")))
def cell7 : List Neg := [.imp q7 (.up (.atom "g"))]
def goal7 : Neg := .up q7

/-- cell (ix) (`docs/pqhard-cases.md`, `_probe/stage0d.lean`): the station
whose residue state carries a non-trivial self-attack content `b`. -/
def qa9 : Pos := .or (.atom "a") (.atom "b")
def cell9 : List Neg := [.imp qa9 (.up (.atom "c")), .imp (.atom "c") (.up (.atom "a"))]
def goal9 : Neg := .up (.atom "a")

/-- (vii) constant from 17. -/
theorem r7_A : ∀ f ∈ [18,19,20],
    interpR "p" f [] cell7 (some goal7) [] = interpR "p" 17 [] cell7 (some goal7) [] := by
  decide +kernel

/-- (vii) the ∃p chain.  Constant from 17, with a false fixpoint at 13. -/
theorem r7_E : ∀ f ∈ [18,19,20],
    interpR "p" f [] cell7 none [] = interpR "p" 17 [] cell7 none [] := by
  decide +kernel

/-- (ix) constant from 7. -/
theorem r9_A : ∀ f ∈ [8,9,10],
    interpR "p" f [] cell9 (some goal9) [] = interpR "p" 7 [] cell9 (some goal9) [] := by
  decide +kernel

/-- (ix) the ∃p chain.  Constant from 7. -/
theorem r9_E : ∀ f ∈ [8,9,10],
    interpR "p" f [] cell9 none [] = interpR "p" 7 [] cell9 none [] := by
  decide +kernel

/-! # Part 2 · R1 on the modal cells

The five designed shapes (m1)–(m5), the six Ghilardi–Zawadowski shapes
(m6)–(m11) and the running cell S1. -/

/-- (m1) constant from 4. -/
theorem rm1_A : ∀ f ∈ [5,6,7],
    interpR "p" f [] m1 (some (.circ (.atom "b"))) []
      = interpR "p" 4 [] m1 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- (m2) at the ◯-implication's own guard goal `↑↓◯a`.  Constant from 6. -/
theorem rm2_A : ∀ f ∈ [7,8,9],
    interpR "p" f [] m2 (some (.up (.down (.circ (.atom "a"))))) []
      = interpR "p" 6 [] m2 (some (.up (.down (.circ (.atom "a"))))) [] := by
  decide +kernel

/-- (m2) at the ◯-goal underneath it.  Constant from 5. -/
theorem rm2_Ac : ∀ f ∈ [6,7,8],
    interpR "p" f [] m2 (some (.circ (.atom "a"))) []
      = interpR "p" 5 [] m2 (some (.circ (.atom "a"))) [] := by
  decide +kernel

/-- (m3) the box that re-creates a parked implication.  Constant from 7,
with a false fixpoint at 2. -/
theorem rm3_A : ∀ f ∈ [8,9,10],
    interpR "p" f [] m3 (some (.circ (.atom "c"))) []
      = interpR "p" 7 [] m3 (some (.circ (.atom "c"))) [] := by
  decide +kernel

/-- (m4) the fire that re-creates a box.  Constant from 6. -/
theorem rm4_A : ∀ f ∈ [7,8,9],
    interpR "p" f [] m4 (some (.circ (.atom "b"))) []
      = interpR "p" 6 [] m4 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- (m5) box and ◯-implication together.  Constant from 9. -/
theorem rm5_A : ∀ f ∈ [10,11,12],
    interpR "p" f [] m5 (some (.circ (.atom "b"))) []
      = interpR "p" 9 [] m5 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- **(m6)** nested guards through a box.  Constant from 34 — twenty-four
fuels later than under `interpQ`, and with a FALSE FIXPOINT at 5. -/
theorem rm6_A : ∀ f ∈ [35,36,37],
    interpR "p" f [] m6 (some (.up (.atom "c"))) []
      = interpR "p" 34 [] m6 (some (.up (.atom "c"))) [] := by
  decide +kernel

/-- (m6) the ∃p chain.  Constant from 34. -/
theorem rm6_E : ∀ f ∈ [35,36,37],
    interpR "p" f [] m6 none [] = interpR "p" 34 [] m6 none [] := by
  decide +kernel

/-- (m6)'s false fixpoint, kernel-checked: the ∀p chain repeats at fuel 5
and moves again at 7 — twenty-nine fuels below the threshold.  This is why
every certificate here checks three fuels above its threshold. -/
theorem rm6_false_fixpoint :
    interpR "p" 5 [] m6 (some (.up (.atom "c"))) []
      = interpR "p" 6 [] m6 (some (.up (.atom "c"))) [] ∧
    interpR "p" 6 [] m6 (some (.up (.atom "c"))) []
      ≠ interpR "p" 7 [] m6 (some (.up (.atom "c"))) [] := by
  constructor <;> decide +kernel

/-- (m7) opening a box produces a ◯-implication whose guard reopens.
Constant from 12. -/
theorem rm7_A : ∀ f ∈ [13,14,15],
    interpR "p" f [] m7 (some (.circ (.atom "b"))) []
      = interpR "p" 12 [] m7 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- (m8) firing re-creates the same ◯-implication under a box.  Constant
from 10. -/
theorem rm8_A : ∀ f ∈ [11,12,13],
    interpR "p" f [] m8 (some (.circ (.atom "b"))) []
      = interpR "p" 10 [] m8 (some (.circ (.atom "b"))) [] := by
  decide +kernel

/-- (m9) a parked implication with a boxed body, made by opening a box.
Constant from 9. -/
theorem rm9_A : ∀ f ∈ [10,11,12],
    interpR "p" f [] m9 (some (.circ (.atom "d"))) []
      = interpR "p" 9 [] m9 (some (.circ (.atom "d"))) [] := by
  decide +kernel

/-- (m11) two nested boxes.  Constant from 10. -/
theorem rm11_A : ∀ f ∈ [11,12,13],
    interpR "p" f [] m11 (some (.circ (.atom "d"))) []
      = interpR "p" 10 [] m11 (some (.circ (.atom "d"))) [] := by
  decide +kernel

/-- **(m10)**, the deepest cell in the package: the S1 variant whose fire
re-creates the guard's antecedent.  Constant from 34. -/
theorem rm10_A : ∀ f ∈ [35,36,37],
    interpR "p" f [] m10 (some (.circ (.atom "g"))) []
      = interpR "p" 34 [] m10 (some (.circ (.atom "g"))) [] := by
  decide +kernel

/-- (m10) the ∃p chain.  Constant from 33, with a false fixpoint at 30. -/
theorem rm10_E : ∀ f ∈ [34,35,36],
    interpR "p" f [] m10 none [] = interpR "p" 33 [] m10 none [] := by
  decide +kernel

/-- **S1**, the running cell `[↓◯(↓(d ⊃ ↑a)) ⊃ ↑e, c ⊃ ◯g]`, at the shift
goal.  Constant from 30. -/
theorem rS1_A : ∀ f ∈ [31,32,33],
    interpR "p" f [] s1Station (some (.up (.atom "e"))) []
      = interpR "p" 30 [] s1Station (some (.up (.atom "e"))) [] := by
  decide +kernel

/-- **S1** at the ◯-goal.  Constant from 31. -/
theorem rS1_Ac : ∀ f ∈ [32,33,34],
    interpR "p" f [] s1Station (some (.circ (.atom "g"))) []
      = interpR "p" 31 [] s1Station (some (.circ (.atom "g"))) [] := by
  decide +kernel

/-- **S1**, the ∃p chain.  Constant from 30. -/
theorem rS1_E : ∀ f ∈ [31,32,33],
    interpR "p" f [] s1Station none [] = interpR "p" 30 [] s1Station none [] := by
  decide +kernel

/-! # Part 3 · The gate, watched failing

The claim these certificates make is that the chain is constant AT AND ABOVE
the recorded threshold.  A threshold one below the measured one is a claim of
the same shape that is FALSE, and the kernel says so.  Both gates are
kernel-checked `= false` propositions; each would be a `decide +kernel`
success if the recorded threshold were wrong by one. -/

/-- Gate: at cell (iii) the level below the threshold is NOT the threshold's. -/
theorem gate_cell3_below :
    decide (interpR "p" 12 [] cell3 (some goal3) []
              = interpR "p" 13 [] cell3 (some goal3) []) = false := by
  decide +kernel

/-- Gate: the same at (m10), where the threshold is 34. -/
theorem gate_m10_below :
    decide (interpR "p" 33 [] m10 (some (.circ (.atom "g"))) []
              = interpR "p" 34 [] m10 (some (.circ (.atom "g"))) []) = false := by
  decide +kernel

end LJFO

/-! ## Pins -/

#axioms_within LJFO.r_eq_q_cal [propext]
#axioms_within LJFO.r_eq_q_calCirc [propext]
#axioms_within LJFO.r_eq_q_calProc [propext]
#axioms_within LJFO.r_eq_q_rows_fuel1 [propext]
#axioms_within LJFO.r_eq_q_cell1 [propext]
#axioms_within LJFO.r_ne_q_cell3 [propext]
#axioms_within LJFO.r_ne_q_cell6 [propext]
#axioms_within LJFO.r_ne_q_m10 [propext]
#axioms_within LJFO.r1_A [propext]
#axioms_within LJFO.r1_E [propext]
#axioms_within LJFO.r2_A [propext]
#axioms_within LJFO.r2_Acd [propext]
#axioms_within LJFO.r3_A [propext]
#axioms_within LJFO.r3_E [propext]
#axioms_within LJFO.r3_E_false_fixpoint [propext]
#axioms_within LJFO.r4_A [propext]
#axioms_within LJFO.r5_A [propext]
#axioms_within LJFO.r6_A [propext]
#axioms_within LJFO.r6_Aab [propext]
#axioms_within LJFO.r7_A [propext]
#axioms_within LJFO.r7_E [propext]
#axioms_within LJFO.r9_A [propext]
#axioms_within LJFO.r9_E [propext]
#axioms_within LJFO.rm1_A [propext]
#axioms_within LJFO.rm2_A [propext]
#axioms_within LJFO.rm2_Ac [propext]
#axioms_within LJFO.rm3_A [propext]
#axioms_within LJFO.rm4_A [propext]
#axioms_within LJFO.rm5_A [propext]
#axioms_within LJFO.rm6_A [propext]
#axioms_within LJFO.rm6_E [propext]
#axioms_within LJFO.rm6_false_fixpoint [propext]
#axioms_within LJFO.rm7_A [propext]
#axioms_within LJFO.rm8_A [propext]
#axioms_within LJFO.rm9_A [propext]
#axioms_within LJFO.rm11_A [propext]
#axioms_within LJFO.rm10_A [propext]
#axioms_within LJFO.rm10_E [propext]
#axioms_within LJFO.rS1_A [propext]
#axioms_within LJFO.rS1_Ac [propext]
#axioms_within LJFO.rS1_E [propext]
#axioms_within LJFO.gate_cell3_below [propext]
#axioms_within LJFO.gate_m10_below [propext]
