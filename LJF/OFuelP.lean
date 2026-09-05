/-
LJF◯ — the PARKING retention interpolant `interpP` (route (B), node N0e).

`interpP` is `interpF` (`LJF/OFuel.lean`) with three definitional changes
and no others.  The principle they express:

    **no rewriting of hypotheses** — every non-atomic implication PARKS,
    and fires through the retained `∀p` of its antecedent at the FULL
    station.

(a) The three PROCESSING clauses of `interpF` that RESHAPE a parked
    implication's antecedent

        (Q₁∨Q₂) ⊃ N  ↦  Q₁ ⊃ N, Q₂ ⊃ N
        ↓↑P′ ⊃ N     ↦  P′ ⊃ N
        ↓(M₁∧M₂) ⊃ N ↦  ↓M₁ ⊃ ↓M₂ ⊃ N

    are replaced by PARKING clauses: the head moves from `todo` to
    `done` unchanged.  `LJF/OFuelHeight.lean` §7.2 is the reason — the
    derivation transformers of those three clauses (`invImpOr`,
    `invStrip`, `invCurry`) RAISE the derivation height while the station
    weight drops, which is exactly what a (height, weight) founding
    cannot absorb.

(b) Each of the three newly parked shapes gets its rows, of the same form
    as the ◯-implication rows of `interpF`, with the antecedent's own
    goal `↑Q` in place of `↑↓◯Q′`:

        ∃p aggregate   A(done ⇒ ↑Q) ⊃ E(N :: rest)  ∧  E(rest)
        ∀p attack row  A(done ⇒ ↑Q)                 ∧  A(N :: rest ⇒ goal)

(c) The Dyckhoff rows `↓(Q′ ⊃ N′) ⊃ N` carry their guard at the FULL
    station too, and — since 2026-09-05 — at the ANTECEDENT'S OWN GOAL:
    `A(done ⇒ ↑↓(Q′ ⊃ N′))` in place of `interpF`'s
    `A(↓N′ ⊃ N :: rest ⇒ Q′ ⊃ N′)`.  Retention at the full station is
    what removes `dykCommute` (`LJF/OFuelHeight.lean` §7.3, §9), whose
    height rise is unbounded; the goal `↑↓(Q′ ⊃ N′)` — rather than the
    body `Q′ ⊃ N′` — is what makes the row an instance of (b) at
    `Q := ↓(Q′ ⊃ N′)`, so that the antecedent dispatch is the SAME
    obligation as for the other four parked shapes.  Guarding by the
    body was the one row of `interpP` violating `interpP`'s own
    principle, and it forced a separate, unreachable obligation
    (`DykAntP`); see `docs/ui-ljfo-clause-table.md` §4.15.  The E-side
    residual component `E(↓N′ ⊃ N :: rest)` is unchanged.

Fuel-0 defaults are unchanged (`⊤` in ∃p mode, `⊥` in ∀p mode), so every
fuel level is still sound by construction.  The parked-shape predicate is
extended here (`ParkedNP`, `ParkedCtxP`); `LJF/O.lean`'s `ParkedN` and
`LJF/OCore.lean` are untouched, and so is `interpF` itself — this module
is purely additive.

Generated from `LJF/OFuel.lean` by a mechanical clause-by-clause
transformation; the diff is exactly (a), (b), (c).
-/
import LJF.O
import LJF.OFuel
import Meta.Audit

namespace LJFO

/-! ## The extended parked shapes

`LJF/O.lean`'s `ParkedN` has five constructors; `interpP` parks three more
shapes, so the recursion reaches saturated stations of eight shapes.  A
separate predicate rather than an edit of `ParkedN`: `LJF/O.lean` is
frozen, and the weight-founded development must keep the old invariant. -/

/-- The eight shapes `interpP`'s parking can produce.  The first five are
`LJF/O.lean`'s `ParkedN`; the last three are the shapes `interpF`
reshapes and `interpP` parks. -/
inductive ParkedNP : Neg → Prop
  | atom (a : String) : ParkedNP (.up (.atom a))
  | qimp (a : String) (N : Neg) : ParkedNP (.imp (.atom a) N)
  | dyk (Q' : Pos) (N' N : Neg) : ParkedNP (.imp (.down (.imp Q' N')) N)
  | box (Q : Pos) : ParkedNP (.circ Q)
  | cimp (Q' : Pos) (N : Neg) : ParkedNP (.imp (.down (.circ Q')) N)
  | oimp (Q₁ Q₂ : Pos) (N : Neg) : ParkedNP (.imp (.or Q₁ Q₂) N)
  | simp (P' : Pos) (N : Neg) : ParkedNP (.imp (.down (.up P')) N)
  | aimp (M₁ M₂ N : Neg) : ParkedNP (.imp (.down (.and M₁ M₂)) N)

/-- Every member is a parked shape. -/
def ParkedCtxP (done : List Neg) : Prop := ∀ X ∈ done, ParkedNP X

theorem ParkedCtxP.nil : ParkedCtxP [] := fun _ h => absurd h List.not_mem_nil

theorem ParkedCtxP.cons {X : Neg} {done : List Neg}
    (hX : ParkedNP X) (h : ParkedCtxP done) : ParkedCtxP (X :: done) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hX
  · exact h Z hZ

theorem ParkedCtxP.sub {done rest : List Neg}
    (hs : Sub rest done) (h : ParkedCtxP done) : ParkedCtxP rest :=
  fun Z hZ => h Z (hs Z hZ)

/-- The old invariant implies the new one: `interpP` parks strictly more. -/
theorem ParkedNP.of_parkedN {X : Neg} (h : ParkedN X) : ParkedNP X := by
  cases h with
  | atom a => exact .atom a
  | qimp a N => exact .qimp a N
  | dyk Q' N' N => exact .dyk Q' N' N
  | box Q => exact .box Q
  | cimp Q' N => exact .cimp Q' N

theorem ParkedCtxP.of_parkedCtx {done : List Neg} (h : ParkedCtx done) :
    ParkedCtxP done := fun X hX => ParkedNP.of_parkedN (h X hX)

/-! ## The interpolant -/

set_option linter.unusedVariables false in
def interpP (p : String) : (fuel : Nat) → (todo done : List Neg) →
    (goal : Option Neg) → Neg
  | 0, _, _, none => nTop
  | 0, _, _, some _ => nBot
  -- ── processing phase: consume the head of `todo` ──
  -- park an atom
  | f+1, .up (.atom a) :: todo, done, g =>
      interpP p f todo (.up (.atom a) :: done) g
  -- absurd hypothesis: `∨` over no branches is `⊥`, `∧` over none is `⊤`
  | f+1, .up .fls :: _, _, none => nBot
  | f+1, .up .fls :: _, _, some _ => nTop
  -- context split: `∨` of branch results in `∃p` mode, `∧` in `∀p` mode
  -- [sum3 b < 3^(w P∨Q), both branches]
  | f+1, .up (.or P Q) :: todo, done, none =>
      nOrAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ => interpP p f (b ++ todo) done none))
  -- context split in ∀p mode: each branch conjunct guarded by the branch's
  -- ∃p, for the same reason as the implication goal — minimality would
  -- otherwise demand deriving one branch's ∀p from another branch's ∃p.
  | f+1, .up (.or P Q) :: todo, done, some G =>
      nAndAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interpP p f (b ++ todo) done none))
            (interpP p f (b ++ todo) done (some G))))
  -- a shifted negative moves into the context  [w M < w ↑↓M = w M + 1]
  | f+1, .up (.down M) :: todo, done, g =>
      interpP p f (M :: todo) done g
  -- a conjunction splits  [3^wM + 3^wN < 3^(wM+wN+3)]
  | f+1, .and M N :: todo, done, g =>
      interpP p f (M :: N :: todo) done g
  -- `⊥ ⊃ N` is inert: drop it
  | f+1, .imp .fls _ :: todo, done, g =>
      interpP p f todo done g
  -- `a ⊃ N` parks until its atom arrives
  | f+1, .imp (.atom a) N :: todo, done, g =>
      interpP p f todo (.imp (.atom a) N :: done) g
  -- `(Q₁∨Q₂) ⊃ N` PARKS: `interpF` splits it into `Q₁ ⊃ N, Q₂ ⊃ N`
  | f+1, .imp (.or Q₁ Q₂) N :: todo, done, g =>
      interpP p f todo (.imp (.or Q₁ Q₂) N :: done) g
  -- `↓↑P′ ⊃ N` PARKS: `interpF` strips the double shift to `P′ ⊃ N`
  | f+1, .imp (.down (.up P')) N :: todo, done, g =>
      interpP p f todo (.imp (.down (.up P')) N :: done) g
  -- `↓(M₁∧M₂) ⊃ N` PARKS: `interpF` curries it to `↓M₁ ⊃ ↓M₂ ⊃ N`
  | f+1, .imp (.down (.and M₁ M₂)) N :: todo, done, g =>
      interpP p f todo (.imp (.down (.and M₁ M₂)) N :: done) g
  -- the Dyckhoff implication parks
  | f+1, .imp (.down (.imp Q' N')) N :: todo, done, g =>
      interpP p f todo (.imp (.down (.imp Q' N')) N :: done) g
  -- a box parks: not left-invertible, opened only under a lax goal
  | f+1, .circ Q :: todo, done, g =>
      interpP p f todo (.circ Q :: done) g
  -- the ◯-implication parks: the modal Dyckhoff shape
  | f+1, .imp (.down (.circ Q')) N :: todo, done, g =>
      interpP p f todo (.imp (.down (.circ Q')) N :: done) g
  -- ── aggregate phase: `todo` exhausted ──
  | f+1, [], done, g =>
    match hf : findFire done (splits done) with
    -- a parked `a ⊃ N` whose atom has arrived fires  [3^wN < 3^(wN+2)]
    | some (_, N, rest) => interpP p f [N] rest g
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
                pGuard p a nTop (.imp (.atom a) (interpP p f [N] rest none))
            -- the Dyckhoff implication: what it yields, guarded by the
            -- ∀p of its ANTECEDENT'S OWN GOAL `↑↓(Q′ ⊃ N′)` at the full
            -- station — the same row form as the ◯-implication below,
            -- at `Q := ↓(Q′ ⊃ N′)` — PAIRED with the ∃p of the residual
            -- station, which the minimality dispatch projects (third
            -- clause the (ii) induction forced; sound because
            -- done ⊢ res via resSim)
            | .imp (.down (.imp Q' N')) N =>
                nAnd
                  (.imp (.down (interpP p f [] done (some (.up (.down (.imp Q' N'))))))
                       (interpP p f [N] rest none))
                  (interpP p f [.imp (.down N') N] rest none)
            -- a parked box: everything the opened station yields, boxed
            -- [2·3^wQ + Σrest < 3^(wQ+1) + Σrest]
            | .circ Q =>
                .circ (.down (interpP p f [.up Q] rest none))
            -- the ◯-implication: the modal Dyckhoff pair — the fire guarded
            -- by the ∀p of (rest ⇒ ◯Q′), PAIRED with the ∃p of rest (the
            -- E-res component, forced as in the intuitionistic case).  No
            -- residual and no witness-box family: modal descent (plan
            -- §3-results (e)) handles self-uses inside the antecedent.
            | .imp (.down (.circ Q')) N =>
                nAnd
                  (.imp (.down (interpP p f [] done (some (.up (.down (.circ Q'))))))
                       (interpP p f [N] rest none))
                  (interpP p f [] rest none)
            -- the three newly parked shapes: the SAME row form as the
            -- ◯-implication above, with the antecedent's own goal
            -- (`↑Q` for the parked `Q ⊃ N`) in place of `↑↓◯Q′`
            | .imp (.or Qa Qb) N =>
                nAnd
                  (.imp (.down (interpP p f [] done (some (.up (.or Qa Qb)))))
                       (interpP p f [N] rest none))
                  (interpP p f [] rest none)
            | .imp (.down (.up Pa)) N =>
                nAnd
                  (.imp (.down (interpP p f [] done (some (.up (.down (.up Pa))))))
                       (interpP p f [N] rest none))
                  (interpP p f [] rest none)
            | .imp (.down (.and Ma Mb)) N =>
                nAnd
                  (.imp (.down (interpP p f [] done (some (.up (.down (.and Ma Mb))))))
                       (interpP p f [N] rest none))
                  (interpP p f [] rest none)
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
                .imp (.down (interpP p f b done none))
                  (interpP p f b done (some N))))
        | .and M N =>
            nAnd (interpP p f [] done (some M)) (interpP p f [] done (some N))
        -- context attacks: ways the saturated context can advance any goal;
        -- inlined per goal shape so each aggregate case is self-contained
        | .up (.atom q) =>
            if atomMem q done then nTop
            else nOrAll (atomHead p q ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.up (Pos.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.up (Pos.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.up (Pos.atom q))))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.up (Pos.atom q))))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.up (Pos.atom q))))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.up (Pos.atom q))))
              | _, _ => nBot))
        | .up .fls =>
            nOrAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.up Pos.fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.up Pos.fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.up Pos.fls)))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.up Pos.fls)))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.up Pos.fls)))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.up Pos.fls)))
              | _, _ => nBot))
        | .up (.or P₁ P₂) =>
            nOrAll ([interpP p f [] done (some (.up P₁)),
                     interpP p f [] done (some (.up P₂))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.up (Pos.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.up (Pos.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.up (Pos.or P₁ P₂))))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.up (Pos.or P₁ P₂))))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.up (Pos.or P₁ P₂))))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.up (Pos.or P₁ P₂))))
              | _, _ => nBot))
        | .up (.down M) =>
            nOrAll ([interpP p f [] done (some M)] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.up (Pos.down M)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.up (Pos.down M))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.up (Pos.down M))))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.up (Pos.down M))))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.up (Pos.down M))))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.up (Pos.down M))))
              | _, _ => nBot))
        | .circ (.atom q) =>
            .circ (.down (nOrAll ([interpP p f [] done (some (.up (.atom q)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.circ (.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.circ (.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.circ (.atom q))))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.circ (.atom q))))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.circ (.atom q))))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.circ (.atom q))))
              | .circ R, hXr =>
                  .imp (.down (interpP p f [.up R] rest none))
                       (interpP p f [.up R] rest (some (.circ (.atom q))))
              | _, _ => nBot))))
        | .circ .fls =>
            .circ (.down (nOrAll ([interpP p f [] done (some (.up .fls))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.circ .fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.circ .fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.circ .fls)))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.circ .fls)))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.circ .fls)))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.circ .fls)))
              | .circ R, hXr =>
                  .imp (.down (interpP p f [.up R] rest none))
                       (interpP p f [.up R] rest (some (.circ .fls)))
              | _, _ => nBot))))
        | .circ (.or P₁ P₂) =>
            .circ (.down (nOrAll ([interpP p f [] done (some (.circ P₁)),
                     interpP p f [] done (some (.circ P₂)),
                     interpP p f [] done (some (.up (.or P₁ P₂)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.circ (.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.circ (.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.circ (.or P₁ P₂))))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.circ (.or P₁ P₂))))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.circ (.or P₁ P₂))))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.circ (.or P₁ P₂))))
              | .circ R, hXr =>
                  .imp (.down (interpP p f [.up R] rest none))
                       (interpP p f [.up R] rest (some (.circ (.or P₁ P₂))))
              | _, _ => nBot))))
        | .circ (.down (.up P')) =>
            .circ (.down (nOrAll ([interpP p f [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.circ (.down (.up P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.circ (.down (.up P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.circ (.down (.up P')))))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.circ (.down (.up P')))))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.circ (.down (.up P')))))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.circ (.down (.up P')))))
              | .circ R, hXr =>
                  .imp (.down (interpP p f [.up R] rest none))
                       (interpP p f [.up R] rest (some (.circ (.down (.up P')))))
              | _, _ => nBot))))
        | .circ (.down (.circ P')) =>
            .circ (.down (nOrAll ([interpP p f [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.circ (.down (.circ P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.circ (.down (.circ P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.circ (.down (.circ P')))))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.circ (.down (.circ P')))))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.circ (.down (.circ P')))))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.circ (.down (.circ P')))))
              | .circ R, hXr =>
                  .imp (.down (interpP p f [.up R] rest none))
                       (interpP p f [.up R] rest (some (.circ (.down (.circ P')))))
              | _, _ => nBot))))
        | .circ (.down (.and M₁ M₂)) =>
            .circ (.down (nOrAll ([interpP p f [] done (some (.up (.down (.and M₁ M₂))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.circ (.down (.and M₁ M₂))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .circ R, hXr =>
                  .imp (.down (interpP p f [.up R] rest none))
                       (interpP p f [.up R] rest (some (.circ (.down (.and M₁ M₂)))))
              | _, _ => nBot))))
        | .circ (.down (.imp Q₀ N₀)) =>
            .circ (.down (nOrAll ([interpP p f [] done (some (.up (.down (.imp Q₀ N₀))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interpP p f [N] rest (some (.circ (.down (.imp Q₀ N₀))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.imp Q' N')))))
                       (interpP p f [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
                       (interpP p f [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .imp (.or Qa Qb) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
                       (interpP p f [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .imp (.down (.up Pa)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
                       (interpP p f [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .imp (.down (.and Ma Mb)) N, hXr =>
                  nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
                       (interpP p f [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .circ R, hXr =>
                  .imp (.down (interpP p f [.up R] rest none))
                       (interpP p f [.up R] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | _, _ => nBot))))

end LJFO

/-! ### Sanity check, and its negative control

On a station carrying NONE of the three reshaped shapes — and none
reachable from its bodies — `interpP` and `interpF` are the SAME formula.
The station is the running cell S1 of `docs/ui-ljfo-clause-table.md`
§4.12,

    S1 = [ ↓◯(↓(d ⊃ ↑a)) ⊃ ↑e,  c ⊃ ◯g ]

a ◯-implication and a `q`-implication, whose bodies are a shift and a
box.  Kernel-checked by `decide` (not `#eval`, not `native_decide`), so
these are theorems.

The negative control is the other half: on a station carrying each of the
three changed shapes the two definitions DIFFER, so the agreement above
is not vacuous. -/

namespace LJFO

/-- The S1 station: `↓◯(↓(d ⊃ ↑a)) ⊃ ↑e` and `c ⊃ ◯g`. -/
def s1Station : List Neg :=
  [ .imp (.down (.circ (.down (.imp (.atom "d") (.up (.atom "a")))))) (.up (.atom "e"))
  , .imp (.atom "c") (.circ (.atom "g")) ]

set_option maxHeartbeats 4000000 in
/-- `∃p` agrees at every fuel through 8. -/
theorem interpP_eq_interpF_s1E : ∀ f ∈ [0,1,2,3,4,5,6,7,8],
    interpP "p" f [] s1Station none = interpF "p" f [] s1Station none := by
  decide

set_option maxHeartbeats 4000000 in
/-- `∀p` at a shifted goal agrees at every fuel through 8. -/
theorem interpP_eq_interpF_s1A : ∀ f ∈ [0,1,2,3,4,5,6,7,8],
    interpP "p" f [] s1Station (some (.up (.atom "e")))
      = interpF "p" f [] s1Station (some (.up (.atom "e"))) := by
  decide

set_option maxHeartbeats 4000000 in
/-- `∀p` at a ◯-goal agrees at every fuel through 7. -/
theorem interpP_eq_interpF_s1Circ : ∀ f ∈ [0,1,2,3,4,5,6,7],
    interpP "p" f [] s1Station (some (.circ (.atom "g")))
      = interpF "p" f [] s1Station (some (.circ (.atom "g"))) := by
  decide

/-! The negative control, one station per changed clause. -/

/-- Carries `↓↑c ⊃ ↑e`. -/
def sStripStation : List Neg :=
  [ .imp (.down (.up (.atom "c"))) (.up (.atom "e")) ]

/-- Carries `(c ∨ d) ⊃ ↑e`. -/
def sOrStation : List Neg :=
  [ .imp (.or (.atom "c") (.atom "d")) (.up (.atom "e")) ]

/-- Carries `↓(↑c ∧ ↑d) ⊃ ↑e`. -/
def sAndStation : List Neg :=
  [ .imp (.down (.and (.up (.atom "c")) (.up (.atom "d")))) (.up (.atom "e")) ]

set_option maxHeartbeats 4000000 in
theorem interpP_ne_interpF_strip : ∀ f ∈ [2,3,4,5],
    interpP "p" f [] sStripStation none ≠ interpF "p" f [] sStripStation none := by
  decide

set_option maxHeartbeats 4000000 in
theorem interpP_ne_interpF_or : ∀ f ∈ [2,3,4,5],
    interpP "p" f [] sOrStation none ≠ interpF "p" f [] sOrStation none := by
  decide

set_option maxHeartbeats 4000000 in
theorem interpP_ne_interpF_curry : ∀ f ∈ [2,3,4,5],
    interpP "p" f [] sAndStation none ≠ interpF "p" f [] sAndStation none := by
  decide

end LJFO

/-! ### Axiom audit -/

#axioms_within LJFO.ParkedNP.of_parkedN [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.ParkedCtxP.cons [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.interpP_eq_interpF_s1E [propext]
#axioms_within LJFO.interpP_eq_interpF_s1A [propext]
#axioms_within LJFO.interpP_eq_interpF_s1Circ [propext]
#axioms_within LJFO.interpP_ne_interpF_strip [propext]
#axioms_within LJFO.interpP_ne_interpF_or [propext]
#axioms_within LJFO.interpP_ne_interpF_curry [propext]
