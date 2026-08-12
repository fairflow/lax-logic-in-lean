/-
LJF◯ — the station maps and the ◯-goal row family, named (simplification
round 2).

Every aggregate of `interp` at a saturated station is a list of rows, one
per split of the station, optionally behind a goal-inversion prefix.  The
tail used to spell that list out in full at every statement about it: five
times in the `∃p` projections and `interpE_eq`, seven times in the ◯-goal
equations (forced change #2's goal-inversion family, box-wrapped per forced
change #3), which differ only in the goal parameter and the prefix.

This module names each map once, against the frozen core alone:

* `eConjRows p done` — the `∃p` conjunct rows (goal `none`);
* `circStationRows p done G` — the ◯-goal station rows, identical across
  all seven goal shapes;
* `laxPrefix p done Q` — the goal-inversion prefix, by shape;
* `laxRows := laxPrefix ++ circStationRows`;

and proves the two equations the tail consumes — `interpE_eq` (batch 2) and

    interp p [] done (some (◯Q)) = ◯(↓(nOrAll (laxRows p done Q)))

(`interp_circ_laxRows`, batch 1) — plus the row-membership combinators
`rowMem`/`rowMemR`, which replace the
`List.mem_append_right _ (List.mem_map_of_mem (List.mem_attach _ ⟨_, _⟩))`
blob that the traversals used to re-prove inline at every call site.

Batch 1 put `laxRows` here on top of `LaxLogic.LJFO`; batch 2 reverses the
dependency — the proofs need only `interp` in `LaxLogic.LJFOCore` (which
stays FROZEN), so this module sits between the core and the tail, and
`LaxLogic.LJFO` imports it.  The seven per-shape equation lemmas
`interpA_circ*_eq` that batch 1 chained through are superseded by the
unified equation and preserved in
`Archive/ljfo-simp-round2-superseded.lean`.

The reviewer's §5 recommendation ("name the attack map"), landed at last;
`docs/ljf-simplification-pass.md` §2.6 identified the same refactor for the
intuitionistic round.
-/
import LaxLogic.LJFOCore

namespace LJFO

/-! ## Saturation

Named here rather than in the tail: the station equations below are exactly
the statements that need it, and it is the only tail definition they use. -/

/-- Saturation: no parked implication can fire. -/
def Saturated (done : List Neg) : Prop :=
  findFire done (splits done) = none

/-! ## Row membership

Every row list is a `(splits done).attach.map`, optionally behind a
goal-inversion prefix; every membership obligation the traversals discharge
is one of these two shapes, with the row function fixed by the goal. -/

/-- A split's row belongs to the station map. -/
theorem rowMem {done : List Neg}
    {f : {x : Neg × List Neg // x ∈ splits done} → Neg}
    {X : Neg} {rest : List Neg} (hsp : (X, rest) ∈ splits done) :
    f ⟨(X, rest), hsp⟩ ∈ (splits done).attach.map f :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(X, rest), hsp⟩)

/-- A split's row belongs to a station map behind a goal-inversion prefix. -/
theorem rowMemR {done : List Neg} {pre : List Neg}
    {f : {x : Neg × List Neg // x ∈ splits done} → Neg}
    {X : Neg} {rest : List Neg} (hsp : (X, rest) ∈ splits done) :
    f ⟨(X, rest), hsp⟩ ∈ pre ++ (splits done).attach.map f :=
  List.mem_append_right _ (rowMem hsp)

/-! ## The `∃p` station map -/

set_option linter.unusedVariables false in
/-- The conjunct rows of the `∃p` aggregate at a saturated station: one row
per split, each member's residual interpolated at the `none` goal.  Spelled
out verbatim in `interpE_eq` and in all five `*ConjMem` projections before
round 2. -/
def eConjRows (p : String) (done : List Neg) : List Neg :=
  (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
    match X with
    | .up (.atom a) => pGuard p a nTop (.up (.atom a))
    | .imp (.atom a) N =>
        pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
    | .imp (.down (.imp Q' N')) N =>
        nAnd
          (.imp (.down (interp p [.imp (.down N') N] rest
                         (some (.imp Q' N'))))
               (interp p [N] rest none))
          (interp p [.imp (.down N') N] rest none)
    | .circ Q =>
        .circ (.down (interp p [.up Q] rest none))
    | .imp (.down (.circ Q')) N =>
        nAnd
          (.imp (.down (interp p [] rest (some (.up (.down (.circ Q'))))))
               (interp p [N] rest none))
          (interp p [] rest none)
    | _ => nTop)

/-- The saturated `∃p` aggregate, as an equation. -/
theorem interpE_eq {p : String} {done : List Neg} (hsat : Saturated done) :
    interp p [] done none = nAndAll (eConjRows p done) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-! ### The `∃p` conjunct projections

One `rowMem` each; before round 2 every one of these repeated the whole
station map in its statement. -/

/-- The `∃p` conjunct of a `q`-implication member, and its membership in the
interpolant's conjunction list. -/
theorem qimpConjMem {p : String} {done : List Neg} {a : String} {N : Neg}
    {rest : List Neg} (hXr : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    pGuard p a nTop (.imp (.atom a) (interp p [N] rest none)) ∈
      eConjRows p done :=
  rowMem hXr

/-- Likewise for a surviving atom. -/
theorem atomConjMem {p : String} {done : List Neg} {a : String}
    {rest : List Neg} (hXr : (Neg.up (.atom a), rest) ∈ splits done) :
    pGuard p a nTop (.up (.atom a)) ∈ eConjRows p done :=
  rowMem hXr

/-- And for a Dyckhoff member. -/
theorem dykConjMem {p : String} {done : List Neg} {Q' : Pos} {N' N : Neg}
    {rest : List Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
           (interp p [N] rest none))
      (interp p [.imp (.down N') N] rest none) ∈ eConjRows p done :=
  rowMem hXr

/-- And for a parked box. -/
theorem boxConjMem {p : String} {done : List Neg} {Q : Pos}
    {rest : List Neg} (hXr : (Neg.circ Q, rest) ∈ splits done) :
    Neg.circ (.down (interp p [.up Q] rest none)) ∈ eConjRows p done :=
  rowMem hXr

/-- And for a `◯`-implication member. -/
theorem cimpConjMem {p : String} {done : List Neg} {Q' : Pos} {N : Neg}
    {rest : List Neg}
    (hXr : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interp p [] rest (some (.up (.down (.circ Q'))))))
           (interp p [N] rest none))
      (interp p [] rest none) ∈ eConjRows p done :=
  rowMem hXr

/-! ## The `tru`-goal station map

The `∀p` aggregates at a SHIFTED goal `↑G` share one station map — the
◯-goal map of `circStationRows` minus its `circL` row, which is lax-only
(only a lax sequent may focus left on a box) — and differ only in the goal
parameter and the goal-inversion prefix.  Four of the equations below
spelled that map out verbatim before round 3, exactly as the seven ◯-goal
equations did before round 2. -/

set_option linter.unusedVariables false in
/-- The station rows of every `↑`-goal aggregate: one row per split of the
saturated station, the goal threaded through the continuations.  Identical
across all four shifted goal shapes. -/
def truStationRows (p : String) (done : List Neg) (G : Pos) : List Neg :=
  (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
    match X, hXr with
    | .imp (.atom a) N, hXr =>
        pGuard p a nBot
          (nAnd (.up (.atom a)) (interp p [N] rest (some (.up G))))
    | .imp (.down (.imp Q' N')) N, hXr =>
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up G)))
    | .imp (.down (.circ Q')) N, hXr =>
        nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
             (interp p [N] rest (some (.up G)))
    | _, _ => nBot)

/-! ### The `∀p` aggregates as equations, at each goal shape

Stated outside any mutual block so the elaborator reuses `interp`'s own
compiled matchers. -/

theorem interpA_atom_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : ¬ atomMem q done = true) :
    interp p [] done (some (.up (.atom q))) =
      nOrAll (atomHead p q ++ truStationRows p done (.atom q)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp only [hq, if_false, Bool.false_eq_true]; rfl

theorem interpA_atomT_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : atomMem q done = true) :
    interp p [] done (some (.up (.atom q))) = nTop := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp [hq]

theorem interpA_fls_eq {p : String} {done : List Neg}
    (hsat : Saturated done) :
    interp p [] done (some (.up .fls)) =
      nOrAll (truStationRows p done .fls) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_or_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P₁ P₂ : Pos) :
    interp p [] done (some (.up (.or P₁ P₂))) =
      nOrAll ([interp p [] done (some (.up P₁)),
               interp p [] done (some (.up P₂))] ++
              truStationRows p done (.or P₁ P₂)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_down_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M : Neg) :
    interp p [] done (some (.up (.down M))) =
      nOrAll ([interp p [] done (some M)] ++ truStationRows p done (.down M)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_imp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (Q : Pos) (N : Neg) :
    interp p [] done (some (.imp Q N)) =
      nAndAll ((invertPos Q).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interp p b done none))
            (interp p b done (some N)))) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_and_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M N : Neg) :
    interp p [] done (some (.and M N)) =
      nAnd (interp p [] done (some M)) (interp p [] done (some N)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-! ## The ◯-goal row family -/

set_option linter.unusedVariables false in
/-- The station rows of every ◯-goal aggregate: one row per split of the
saturated station, the goal threaded through the continuations — identical
across all seven goal shapes.  (The inner match binds the `attach`
membership witness exactly as `interp` does, so the unified equation closes
definitionally.) -/
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
box-wrapped disjunction of its `laxRows`.  One statement replacing the seven
`interpA_circ*_eq` lemmas at every use site; the goal dispatch of `interp`
matches on the positive under the `◯`, so the shape analysis survives as the
`cases` closing the second branch. -/
theorem interp_circ_laxRows {p : String} {done : List Neg}
    (hsat : Saturated done) (Q : Pos) :
    interp p [] done (some (.circ Q)) =
      .circ (.down (nOrAll (laxRows p done Q))) := by
  match Q with
  | .atom _ | .fls | .or _ _ | .down (.up _) | .down (.circ _)
  | .down (.and _ _) | .down (.imp _ _) =>
    conv => lhs; rw [interp]
    split
    all_goals rename_i heq
    · rw [hsat] at heq; cases heq
    · rfl

/-- The row list of a ◯-goal aggregate is `laxRows`: the identification the
lax arms of the traversals open with, once instead of seven times. -/
theorem laxRows_of_eq {p : String} {done : List Neg} {L : List Neg}
    (hsat : Saturated done) (Q : Pos)
    (hV : interp p [] done (some (.circ Q)) = .circ (.down (nOrAll L))) :
    L = laxRows p done Q :=
  nOrAll_inj (Pos.down.inj (Neg.circ.inj
    (hV.symm.trans (interp_circ_laxRows hsat Q))))

/-! ### The four station rows of a ◯-goal aggregate

The membership side conditions of `UStab`/`ULF`/`UInvG`/`UpElim`, one
`rowMemR` each, discharged once here rather than by an inline
`List.mem_append_right _ (List.mem_map_of_mem (List.mem_attach _ ⟨_, _⟩))`
at each of the seven former per-shape call sites. -/

/-- The fired-`q`-implication row. -/
theorem laxRows_qimpMem {p : String} {done : List Neg} {Q : Pos}
    {c : String} {Nc : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.atom c) Nc, rest) ∈ splits done) :
    pGuard p c nBot (nAnd (.up (.atom c))
      (interp p [Nc] rest (some (.circ Q)))) ∈ laxRows p done Q :=
  rowMemR hsp

/-- The Dyckhoff row. -/
theorem laxRows_dykMem {p : String} {done : List Neg} {Q : Pos}
    {Q' : Pos} {N' N : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
         (interp p [N] rest (some (.circ Q))) ∈ laxRows p done Q :=
  rowMemR hsp

/-- The `◯`-implication row. -/
theorem laxRows_cimpMem {p : String} {done : List Neg} {Q : Pos}
    {Q' : Pos} {N : Neg} {rest : List Neg}
    (hsp : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
         (interp p [N] rest (some (.circ Q))) ∈ laxRows p done Q :=
  rowMemR hsp

/-- The opened-box row — the lax-only one (`circL`). -/
theorem laxRows_boxMem {p : String} {done : List Neg} {Q : Pos}
    {R : Pos} {rest : List Neg}
    (hsp : (Neg.circ R, rest) ∈ splits done) :
    Neg.imp (.down (interp p [.up R] rest none))
      (interp p [.up R] rest (some (.circ Q))) ∈ laxRows p done Q :=
  rowMemR hsp

end LJFO
