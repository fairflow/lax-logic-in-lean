/-
LJF◯ — the ◯-goal row family, named (simplification round 2, batch 1).

The seven ◯-goal equation lemmas of `LJFO.lean` (forced change #2's
goal-inversion family, box-wrapped per forced change #3) share one
station map verbatim; only the goal parameter and the prefix family
vary by shape.  This module names the family once — `laxRows` =
`laxPrefix ++ circStationRows` — and proves the single unified
equation

    interp p [] done (some (.circ Q)) = ◯(↓(nOrAll (laxRows p done Q)))

by `cases Q` from the existing seven lemmas.  Additive: nothing in the
tail is edited; consumers migrate to `laxRows` in batch 2 (where the
seven-way clause groups of the U-family collapse to single clauses).

The reviewer's §5 recommendation ("name the attack map"), landed at
last; `docs/ljf-simplification-pass.md` §2.6 identified the same
refactor for the intuitionistic round.
-/
import LaxLogic.LJFO

namespace LJFO

set_option linter.unusedVariables false in
/-- The station rows of every ◯-goal aggregate: one row per split of
the saturated station, the goal threaded through the continuations —
identical across all seven goal shapes.  (The inner match binds the
`attach` membership witness exactly as the seven originals do, so the
unified equation closes definitionally.) -/
def circStationRows (p : String) (done : List Neg) (G : Pos) : List Neg :=
  (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
    match X, hXr with
    | .imp (.atom a) N, hXr =>
        pGuard p a nBot
          (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ G))))
    | .imp (.down (.imp Q' N')) N, hXr =>
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.circ G)))
    | .imp (.down (.circ Q')) N, hXr =>
        nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
             (interp p [N] rest (some (.circ G)))
    | .circ R, hXr =>
        .imp (.down (interp p [.up R] rest none))
             (interp p [.up R] rest (some (.circ G)))
    | _, _ => nBot)

/-- The lax goal-inversion prefix (forced change #2's family), by goal
shape. -/
def laxPrefix (p : String) (done : List Neg) : Pos → List Neg
  | .atom q => [interp p [] done (some (.up (.atom q)))]
  | .fls => [interp p [] done (some (.up .fls))]
  | .or P₁ P₂ => [interp p [] done (some (.circ P₁)),
                  interp p [] done (some (.circ P₂)),
                  interp p [] done (some (.up (.or P₁ P₂)))]
  | .down (.up P') => [interp p [] done (some (.circ P'))]
  | .down (.circ P') => [interp p [] done (some (.circ P'))]
  | .down (.and M₁ M₂) => [interp p [] done (some (.up (.down (.and M₁ M₂))))]
  | .down (.imp Q₀ N₀) => [interp p [] done (some (.up (.down (.imp Q₀ N₀))))]

/-- The ◯-goal row family: goal-inversion prefix, then the station
rows. -/
def laxRows (p : String) (done : List Neg) (Q : Pos) : List Neg :=
  laxPrefix p done Q ++ circStationRows p done Q

/-- **The unified ◯-goal equation**: every ◯-goal aggregate is the
box-wrapped disjunction of its `laxRows`.  One statement replacing
seven at every future use site. -/
theorem interp_circ_laxRows {p : String} {done : List Neg}
    (hsat : Saturated done) :
    ∀ Q : Pos, interp p [] done (some (.circ Q)) =
      .circ (.down (nOrAll (laxRows p done Q)))
  | .atom q => interpA_circAtom_eq hsat
  | .fls => interpA_circFls_eq hsat
  | .or P₁ P₂ => interpA_circOr_eq hsat P₁ P₂
  | .down (.up P') => interpA_circDownUp_eq hsat P'
  | .down (.circ P') => interpA_circDownCirc_eq hsat P'
  | .down (.and M₁ M₂) => interpA_circDownAnd_eq hsat M₁ M₂
  | .down (.imp Q₀ N₀) => interpA_circDownImp_eq hsat Q₀ N₀

end LJFO
