/-
LJF◯ — the fuel-founded retention interpolant (route (B) layer 4a).

`interpF` mirrors `interp` clause for clause, founded on structural fuel
instead of the weight measure — which makes the RETENTION guard
admissible: the modal-implication rows carry `A(done ⇒ ↑↓◯Q′)` at the
FULL station (the (b)-form, evaluator-certified), the `L◯→″` retention
discipline that dissolves the crossed-station obstruction.  Sound
defaults at fuel 0 (`⊤` in ∃p mode, `⊥` in ∀p mode): every fuel level is
sound; sufficiency is only needed for minimality.  Purely additive; the
weight-founded development is untouched.
-/
import LaxLogic.LJFOCore

namespace LJFO

def interpF (p : String) : (fuel : Nat) → (todo done : List Neg) →
    (goal : Option Neg) → Neg
  | 0, _, _, none => nTop
  | 0, _, _, some _ => nBot
  -- ── processing phase: consume the head of `todo` ──
  -- park an atom
  | f+1, .up (.atom a) :: todo, done, g =>
      interpF p f todo (.up (.atom a) :: done) g
  -- absurd hypothesis: `∨` over no branches is `⊥`, `∧` over none is `⊤`
  | f+1, .up .fls :: _, _, none => nBot
  | f+1, .up .fls :: _, _, some _ => nTop
  -- context split: `∨` of branch results in `∃p` mode, `∧` in `∀p` mode
  -- [sum3 b < 3^(w P∨Q), both branches]
  | f+1, .up (.or P Q) :: todo, done, none =>
      nOrAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ => interpF p f (b ++ todo) done none))
  -- context split in ∀p mode: each branch conjunct guarded by the branch's
  -- ∃p, for the same reason as the implication goal — minimality would
  -- otherwise demand deriving one branch's ∀p from another branch's ∃p.
  | f+1, .up (.or P Q) :: todo, done, some G =>
      nAndAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interpF p f (b ++ todo) done none))
            (interpF p f (b ++ todo) done (some G))))
  -- a shifted negative moves into the context  [w M < w ↑↓M = w M + 1]
  | f+1, .up (.down M) :: todo, done, g =>
      interpF p f (M :: todo) done g
  -- a conjunction splits  [3^wM + 3^wN < 3^(wM+wN+3)]
  | f+1, .and M N :: todo, done, g =>
      interpF p f (M :: N :: todo) done g
  -- `⊥ ⊃ N` is inert: drop it
  | f+1, .imp .fls _ :: todo, done, g =>
      interpF p f todo done g
  -- `a ⊃ N` parks until its atom arrives
  | f+1, .imp (.atom a) N :: todo, done, g =>
      interpF p f todo (.imp (.atom a) N :: done) g
  -- `(Q₁∨Q₂) ⊃ N` splits  [3^(wQ₁+wN+1) + 3^(wQ₂+wN+1) < 3^(wQ₁+wQ₂+1+wN+1)]
  | f+1, .imp (.or Q₁ Q₂) N :: todo, done, g =>
      interpF p f (.imp Q₁ N :: .imp Q₂ N :: todo) done g
  -- `↓↑P' ⊃ N` strips the double shift  [w drops by 1]
  | f+1, .imp (.down (.up P')) N :: todo, done, g =>
      interpF p f (.imp P' N :: todo) done g
  -- currying: `↓(M₁∧M₂) ⊃ N  ↝  ↓M₁ ⊃ (↓M₂ ⊃ N)`  [w: +5 vs +4 — the
  -- inequality that forces `∧` to cost 3]
  | f+1, .imp (.down (.and M₁ M₂)) N :: todo, done, g =>
      interpF p f (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done g
  -- the Dyckhoff implication parks
  | f+1, .imp (.down (.imp Q' N')) N :: todo, done, g =>
      interpF p f todo (.imp (.down (.imp Q' N')) N :: done) g
  -- a box parks: not left-invertible, opened only under a lax goal
  | f+1, .circ Q :: todo, done, g =>
      interpF p f todo (.circ Q :: done) g
  -- the ◯-implication parks: the modal Dyckhoff shape
  | f+1, .imp (.down (.circ Q')) N :: todo, done, g =>
      interpF p f todo (.imp (.down (.circ Q')) N :: done) g
  -- ── aggregate phase: `todo` exhausted ──
  | f+1, [], done, g =>
    match hf : findFire done (splits done) with
    -- a parked `a ⊃ N` whose atom has arrived fires  [3^wN < 3^(wN+2)]
    | some (_, N, rest) => interpF p f [N] rest g
    | none =>
      match g with
      -- ∃p mode: conjunction over the saturated context
      | none =>
          nAndAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
            match X with
            -- a surviving atom is its own p-free content
            | .up (.atom a) => pGuard p a nTop (.up (.atom a))
            -- `a ⊃ N`, atom absent: guard the recursion by the atom
            | .imp (.atom a) N =>
                pGuard p a nTop (.imp (.atom a) (interpF p f [N] rest none))
            -- the Dyckhoff implication: what it yields, guarded by what
            -- the goal interpolant of its antecedent demands — PAIRED with
            -- the ∃p of the residual station, which the minimality
            -- dispatch projects (third clause the (ii) induction forced;
            -- sound because done ⊢ res via resSim)
            | .imp (.down (.imp Q' N')) N =>
                nAnd
                  (.imp (.down (interpF p f [.imp (.down N') N] rest
                                 (some (.imp Q' N'))))
                       (interpF p f [N] rest none))
                  (interpF p f [.imp (.down N') N] rest none)
            -- a parked box: everything the opened station yields, boxed
            -- [2·3^wQ + Σrest < 3^(wQ+1) + Σrest]
            | .circ Q =>
                .circ (.down (interpF p f [.up Q] rest none))
            -- the ◯-implication: the modal Dyckhoff pair — the fire guarded
            -- by the ∀p of (rest ⇒ ◯Q′), PAIRED with the ∃p of rest (the
            -- E-res component, forced as in the intuitionistic case).  No
            -- residual and no witness-box family: modal descent (plan
            -- §3-results (e)) handles self-uses inside the antecedent.
            | .imp (.down (.circ Q')) N =>
                nAnd
                  (.imp (.down (interpF p f [] done (some (.up (.down (.circ Q'))))))
                       (interpF p f [N] rest none))
                  (interpF p f [] rest none)
            -- unreachable shapes park nothing
            | _ => nTop))
      -- ∀p mode: by the goal
      | some G =>
        match G with
        -- goal inversion  [2·sum3 b + 3^wN < 3^(wQ+wN+1)]
        -- ∀p at an implication goal: each branch conjunct is GUARDED by the
        -- branch's ∃p — without the guard, minimality fails (it would demand
        -- E(Γ) ⊢ E(Γ+b), which is false); with it, soundness still closes
        -- because eSound supplies the guard.  This is the clause the (ii)
        -- induction forces.
        | .imp Q N =>
            nAndAll ((invertPos Q).attach.map
              (fun ⟨b, hb⟩ =>
                .imp (.down (interpF p f b done none))
                  (interpF p f b done (some N))))
        | .and M N =>
            nAnd (interpF p f [] done (some M)) (interpF p f [] done (some N))
        -- context attacks: ways the saturated context can advance any goal;
        -- inlined per goal shape so each aggregate case is self-contained
        | .up (.atom q) =>
            if atomMem q done then nTop
            else nOrAll (atomHead p q ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.up (Pos.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.up (Pos.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.up (Pos.atom q))))
              | _, _ => nBot))
        | .up .fls =>
            nOrAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.up Pos.fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.up Pos.fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.up Pos.fls)))
              | _, _ => nBot))
        | .up (.or P₁ P₂) =>
            nOrAll ([interpF p f [] done (some (.up P₁)),
                     interpF p f [] done (some (.up P₂))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.up (Pos.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.up (Pos.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.up (Pos.or P₁ P₂))))
              | _, _ => nBot))
        | .up (.down M) =>
            nOrAll ([interpF p f [] done (some M)] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.up (Pos.down M)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.up (Pos.down M))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.up (Pos.down M))))
              | _, _ => nBot))
        | .circ (.atom q) =>
            .circ (.down (nOrAll ([interpF p f [] done (some (.up (.atom q)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.circ (.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.circ (.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.circ (.atom q))))
              | .circ R, hXr =>
                  .imp (.down (interpF p f [.up R] rest none))
                       (interpF p f [.up R] rest (some (.circ (.atom q))))
              | _, _ => nBot))))
        | .circ .fls =>
            .circ (.down (nOrAll ([interpF p f [] done (some (.up .fls))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.circ .fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.circ .fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.circ .fls)))
              | .circ R, hXr =>
                  .imp (.down (interpF p f [.up R] rest none))
                       (interpF p f [.up R] rest (some (.circ .fls)))
              | _, _ => nBot))))
        | .circ (.or P₁ P₂) =>
            .circ (.down (nOrAll ([interpF p f [] done (some (.circ P₁)),
                     interpF p f [] done (some (.circ P₂)),
                     interpF p f [] done (some (.up (.or P₁ P₂)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.circ (.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.circ (.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.circ (.or P₁ P₂))))
              | .circ R, hXr =>
                  .imp (.down (interpF p f [.up R] rest none))
                       (interpF p f [.up R] rest (some (.circ (.or P₁ P₂))))
              | _, _ => nBot))))
        | .circ (.down (.up P')) =>
            .circ (.down (nOrAll ([interpF p f [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.circ (.down (.up P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.circ (.down (.up P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.circ (.down (.up P')))))
              | .circ R, hXr =>
                  .imp (.down (interpF p f [.up R] rest none))
                       (interpF p f [.up R] rest (some (.circ (.down (.up P')))))
              | _, _ => nBot))))
        | .circ (.down (.circ P')) =>
            .circ (.down (nOrAll ([interpF p f [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.circ (.down (.circ P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.circ (.down (.circ P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.circ (.down (.circ P')))))
              | .circ R, hXr =>
                  .imp (.down (interpF p f [.up R] rest none))
                       (interpF p f [.up R] rest (some (.circ (.down (.circ P')))))
              | _, _ => nBot))))
        | .circ (.down (.and M₁ M₂)) =>
            .circ (.down (nOrAll ([interpF p f [] done (some (.up (.down (.and M₁ M₂))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.circ (.down (.and M₁ M₂))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .circ R, hXr =>
                  .imp (.down (interpF p f [.up R] rest none))
                       (interpF p f [.up R] rest (some (.circ (.down (.and M₁ M₂)))))
              | _, _ => nBot))))
        | .circ (.down (.imp Q₀ N₀)) =>
            .circ (.down (nOrAll ([interpF p f [] done (some (.up (.down (.imp Q₀ N₀))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpF p f [N] rest (some (.circ (.down (.imp Q₀ N₀))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpF p f [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interpF p f [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpF p f [] done (some (.up (.down (.circ Q')))))
                       (interpF p f [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .circ R, hXr =>
                  .imp (.down (interpF p f [.up R] rest none))
                       (interpF p f [.up R] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | _, _ => nBot))))
end LJFO
