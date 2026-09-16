/-
Route (B), node **N4**, WP12b, **stage 0 of stage 1**: the cell-dependent
content of the measure, decided in the kernel on the designed cells, and the
two gates watched failing.

`rMu = κ₂ · W + ν` (`wip/ui_routeB_r_meas.lean`).  `κ₂` is not
kernel-computable at a cell — the candidate enumeration is exponential in the
closure — and its two lemmas (`kap2_le`, `kap2_lt`) are cell-INDEPENDENT
combinatorics, discharged by proof.  What is cell-dependent is the rest of the
edge table of `docs/n4-bound.md` §3, and that is decided here:

    edgeOKR s t  :=  clStR t ⊆ clStR s  ∧
                     (seen carried  →  ν t < ν s)  ∧
                     (seen extended →  ν t < ν s + W s)

along every edge out of every state reachable within `n` steps of the cell
(`descROK`), against an edge list whose ADEQUACY is itself decided
(`adeqROK`: masking the level below to `edgesR s` changes nothing at `s`, so
`edgesR s` covers every state `stepR` consults there).

**The two gates, each a kernel-checked `= false`:**

* `gate_r_nu_goal_term` — drop `3 ^ wNeg goal` from `ν` and the check goes red
  at the ◯-free cell (i).  The term pays for `invertPos Q` entering the
  station at a `∀p` implication goal, and for every goal move at a fixed
  station.
* `gate_r_kappa` — treat a GUARD edge as an ordinary one (demand `ν t < ν s`
  there too) and the check goes red at the same cell: the guard edge RAISES
  `ν`, which is the failure `κ₂` exists to repair and the reason the measure
  is a product and not a sum.
* `gate_r_control` — the committed test passes at the same cell and the same
  depth, so neither gate is vacuous.

Rule 9: designed cells, no enumeration.  Rule 8: the ◯-free cells first.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_bound
import wip.ui_routeB_r_cells
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The decidable edge test -/

/-- The closure does not grow along the edge. -/
def clSubR (t s : RState) : Bool := subNeg (clStR t) (clStR s)

/-- **The committed edge test.** -/
def edgeOKR (s t : RState) : Bool :=
  clSubR t s &&
    (if decide (t.2.2.2 = s.2.2.2) then decide (nuR t < nuR s)
     else decide (nuR t < nuR s + bigWR s))

/-- The bounded reachable set of a state, along `edgesR`. -/
def reachR : Nat → List RState → List RState
  | 0, front => front
  | n + 1, front => front ++ reachR n (front.flatMap edgesR)

/-- **The stage-0 predicate**: the edge test holds along every edge out of
every state reachable within `n` steps. -/
def descROK (n : Nat) (s : RState) : Bool :=
  (reachR n [s]).all (fun t => (edgesR t).all (fun u => edgeOKR t u))

/-- A level masked to a state list: `⊤` off the list. -/
def maskAtR (E : List RState) (F : ApproxR) : ApproxR :=
  fun todo done g seen => if (todo, done, g, seen) ∈ E then F todo done g seen else nTop

/-- **Adequacy of the mirror.** -/
def adeqROK (p : String) (f : Nat) (s : RState) : Bool :=
  decide (atStR (stepR id p (interpR p f)) s
        = atStR (stepR id p (maskAtR (edgesR s) (interpR p f))) s)

/-- The state of a cell in `∀p` mode. -/
def stAR (done : List Neg) (G : Neg) : RState := ([], done, some G, [])
/-- The state of a cell in `∃p` mode. -/
def stER (done : List Neg) : RState := ([], done, none, [])

/-! # Part 2 · The ◯-free cells (rule 8: the fragment first) -/

/-- (i)–(vi): the mirror is adequate at the cell's own state. -/
theorem adeq_r_circFree :
    adeqROK "p" 3 (stAR cell1 goal1) = true ∧
    adeqROK "p" 3 (stER cell1) = true ∧
    adeqROK "p" 3 (stAR cell2 goal2ab) = true ∧
    adeqROK "p" 3 (stAR cell3 goal3) = true ∧
    adeqROK "p" 3 (stER cell3) = true ∧
    adeqROK "p" 3 (stAR cell4 goal4) = true ∧
    adeqROK "p" 3 (stAR cell5 goal5) = true ∧
    adeqROK "p" 3 (stAR cell6 goal6d) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- (i)–(vi), and the two cells the `PQEquiv` campaign designed: the edge test
holds along every edge of the reachable set. -/
theorem desc_r_circFree :
    descROK 3 (stAR cell1 goal1) = true ∧
    descROK 3 (stER cell1) = true ∧
    descROK 3 (stAR cell2 goal2ab) = true ∧
    descROK 3 (stAR cell2 goal2cd) = true ∧
    descROK 3 (stAR cell3 goal3) = true ∧
    descROK 3 (stER cell3) = true ∧
    descROK 3 (stAR cell4 goal4) = true ∧
    descROK 3 (stAR cell5 goal5) = true ∧
    descROK 3 (stAR cell6 goal6d) = true ∧
    descROK 3 (stAR cell6 goal6ab) = true ∧
    descROK 3 (stAR cell7 goal7) = true ∧
    descROK 3 (stAR cell9 goal9) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! # Part 3 · The modal cells -/

/-- (m1), (m6), (m10): the mirror is adequate. -/
theorem adeq_r_modal :
    adeqROK "p" 3 (stAR m1 (.circ (.atom "b"))) = true ∧
    adeqROK "p" 3 (stAR m6 (.up (.atom "c"))) = true ∧
    adeqROK "p" 3 (stER m6) = true ∧
    adeqROK "p" 3 (stAR m10 (.circ (.atom "g"))) = true ∧
    adeqROK "p" 3 (stER m10) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- (m1), (m6), (m10): the edge test holds along every edge. -/
theorem desc_r_modal :
    descROK 2 (stAR m1 (.circ (.atom "b"))) = true ∧
    descROK 2 (stAR m6 (.up (.atom "c"))) = true ∧
    descROK 2 (stER m6) = true ∧
    descROK 2 (stAR m10 (.circ (.atom "g"))) = true ∧
    descROK 2 (stER m10) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! # Part 4 · The gates, watched failing -/

/-- `ν` without the goal term. -/
def nuNGR (s : RState) : Nat := 2 * sum3 s.1 + sum3 s.2.1

/-- The edge test with the goal term dropped from `ν`. -/
def edgeNGOKR (s t : RState) : Bool :=
  clSubR t s &&
    (if decide (t.2.2.2 = s.2.2.2) then decide (nuNGR t < nuNGR s)
     else decide (nuNGR t < nuNGR s + bigWR s))

def descNGOK (n : Nat) (s : RState) : Bool :=
  (reachR n [s]).all (fun t => (edgesR t).all (fun u => edgeNGOKR t u))

/-- The edge test with the guard edge treated as an ordinary one. -/
def edgeNKOKR (s t : RState) : Bool := clSubR t s && decide (nuR t < nuR s)

def descNKOK (n : Nat) (s : RState) : Bool :=
  (reachR n [s]).all (fun t => (edgesR t).all (fun u => edgeNKOKR t u))

/-- **GATE, watched failing**: drop the goal term from `ν` and the check goes
red at the ◯-free cell (i), in both modes. -/
theorem gate_r_nu_goal_term :
    descNGOK 3 (stAR cell1 goal1) = false ∧
    descNGOK 3 (stER cell1) = false := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **GATE, watched failing**: treat the guard edge as ordinary — no `κ₂` to
pay for it — and the check goes red at the same cell.  The guard edge RAISES
`ν`; that is what the first component of the measure is for. -/
theorem gate_r_kappa :
    descNKOK 3 (stAR cell1 goal1) = false ∧
    descNKOK 3 (stER cell1) = false := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **CONTROL**: the committed test passes at the same cell and the same
depth, so neither gate is vacuous. -/
theorem gate_r_control :
    descROK 3 (stAR cell1 goal1) = true ∧
    descROK 3 (stER cell1) = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

end LJFO

/-! ## Pins -/

#axioms_within LJFO.adeq_r_circFree [propext]
#axioms_within LJFO.desc_r_circFree [propext, Quot.sound]
#axioms_within LJFO.adeq_r_modal [propext]
#axioms_within LJFO.desc_r_modal [propext, Quot.sound]
#axioms_within LJFO.gate_r_nu_goal_term [propext, Quot.sound]
#axioms_within LJFO.gate_r_kappa [propext, Quot.sound]
#axioms_within LJFO.gate_r_control [propext, Quot.sound]
