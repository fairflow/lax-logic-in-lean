/- # Archive: LJF◯ simplification round 2 — superseded proofs (2026-08-12)

This file is NOT built (Archive/ is outside the Lake package roots). It
preserves, verbatim, the top-level artefacts deleted from LaxLogic/LJFO.lean
by simplification round 2, batch 2. The pre-round-2 state is commit 797f301
(batch 1 close); the pre-simplification LJF◯ state is 0dc8f13.

Why each block was superseded (docs/ljfo-plan.md, "Round 2 design pin"):

* `interpA_circAtom_eq`, `interpA_circFls_eq`, `interpA_circOr_eq`,
  `interpA_circDownUp_eq`, `interpA_circDownCirc_eq`,
  `interpA_circDownAnd_eq`, `interpA_circDownImp_eq` — the seven per-shape
  ◯-goal aggregate equations. Each spelled out the SAME station map
  verbatim, differing only in the goal parameter and the goal-inversion
  prefix. Superseded by the single

      interp_circ_laxRows (hsat) (Q) :
        interp p [] done (some (◯Q)) = ◯(↓(nOrAll (laxRows p done Q)))

  in LaxLogic/LJFORows.lean, where `laxRows = laxPrefix ++ circStationRows`
  names the prefix family and the station map. The shape analysis these
  seven lemmas performed by their statements survives inside that one
  proof, as the `cases Q` closing the non-fire branch: `interp`'s goal
  dispatch matches on the positive UNDER the `◯`, so the seven cases are
  irreducible — what round 2 removed is their SEVENFOLD RESTATEMENT, not
  the case split.
* `interpCircShape` — the Σ'-packaged shape-generic seam introduced so that
  callers with an abstract positive could cross the box wrapper. It had no
  call sites; `interp_circ_laxRows` is that seam with the row list named
  instead of existentially quantified.

Not archived, because their statements are unchanged up to the naming of
the map (same names, same types, `rfl`-interconvertible): `interpE_eq` and
the five `*ConjMem` projections, whose common station map is now
`eConjRows` in LaxLogic/LJFORows.lean, and whose proofs are now the shared
`rowMem` combinator. `Saturated` moved unchanged to the same module.
-/

namespace LJFO

variable {p : String}

theorem interpA_circAtom_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} :
    interp p [] done (some (.circ (.atom q))) = .circ (.down (nOrAll ([interp p [] done (some (.up (.atom q)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
                       (interp p [N] rest (some (.circ (.atom q))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.atom q))))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circFls_eq {p : String} {done : List Neg}
    (hsat : Saturated done) :
    interp p [] done (some (.circ .fls)) = .circ (.down (nOrAll ([interp p [] done (some (.up .fls))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ .fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ .fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
                       (interp p [N] rest (some (.circ .fls)))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ .fls)))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circOr_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P₁ P₂ : Pos) :
    interp p [] done (some (.circ (.or P₁ P₂))) = .circ (.down (nOrAll ([interp p [] done (some (.circ P₁)),
                     interp p [] done (some (.circ P₂)),
                     interp p [] done (some (.up (.or P₁ P₂)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
                       (interp p [N] rest (some (.circ (.or P₁ P₂))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.or P₁ P₂))))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownUp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P' : Pos) :
    interp p [] done (some (.circ (.down (.up P')))) = .circ (.down (nOrAll ([interp p [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.up P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.up P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
                       (interp p [N] rest (some (.circ (.down (.up P')))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.up P')))))
              | _, _ => nBot)))) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownCirc_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P' : Pos) :
    interp p [] done (some (.circ (.down (.circ P')))) = .circ (.down (nOrAll ([interp p [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.circ P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.circ P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
                       (interp p [N] rest (some (.circ (.down (.circ P')))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.circ P')))))
              | _, _ => nBot)))) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownAnd_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M₁ M₂ : Neg) :
    interp p [] done (some (.circ (.down (.and M₁ M₂)))) = .circ (.down (nOrAll ([interp p [] done (some (.up (.down (.and M₁ M₂))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.and M₁ M₂))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
                       (interp p [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.and M₁ M₂)))))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownImp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (Q₀ : Pos) (N₀ : Neg) :
    interp p [] done (some (.circ (.down (.imp Q₀ N₀)))) = .circ (.down (nOrAll ([interp p [] done (some (.up (.down (.imp Q₀ N₀))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.up (.down (.circ Q')))))
                       (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-- Every ◯-goal aggregate is box-wrapped: the row list, with its
equation.  One case per goal shape, so callers with an abstract positive
can still cross the wrapper. -/
def interpCircShape {p : String} {done : List Neg} (hsat : Saturated done) :
    ∀ (P₀ : Pos), Σ' L, interp p [] done (some (.circ P₀)) = .circ (.down (nOrAll L))
  | .atom _ => ⟨_, interpA_circAtom_eq hsat⟩
  | .fls => ⟨_, interpA_circFls_eq hsat⟩
  | .or P₁ P₂ => ⟨_, interpA_circOr_eq hsat P₁ P₂⟩
  | .down (.up P') => ⟨_, interpA_circDownUp_eq hsat P'⟩
  | .down (.circ P') => ⟨_, interpA_circDownCirc_eq hsat P'⟩
  | .down (.and M₁ M₂) => ⟨_, interpA_circDownAnd_eq hsat M₁ M₂⟩
  | .down (.imp Q₀ N₀) => ⟨_, interpA_circDownImp_eq hsat Q₀ N₀⟩

end LJFO
