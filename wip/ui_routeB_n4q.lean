/-
Route (B), node **N4**, WP8: the LOOP-CHECKED recursion.

`wip/ui_routeB_n4_lit.lean` refutes the LITERAL form of N1 at every
saturated parked station carrying a compound implication: the ∀p attack
row of a parked `Q ⊃ N ∈ done` at the goal `↑Q` re-enters the same call
one fuel down, so the chain is strictly `sizeNeg`-ascending.  Up to
interderivability the chain does stabilise on ◯-free stations
(`n4_circFree_uncond`), and the reason is that the looping disjunct adds
no consequence.

This module builds `interpP` (`LJF/OFuelP.lean`) again with ONE
definitional change: a list `seen : List Pos` of the antecedents whose own
goal has already been attacked, with

* the ∀p attack row of a parked compound implication `Q′ ⊃ N` replaced by
  `⊥` — the unit of the aggregate's `nOrAll` — when `Q′ ∈ seen`;
* the ∃p row's guarded conjunct replaced by `⊤` — the unit of the
  aggregate's `nAndAll` — on the same test, the residual component kept;
* a guard call that IS emitted made at `Q′ :: seen`.

Recording at the GUARD CALL SITE, and not at the aggregate, is what makes
`seen` monotone along every edge of the recursion — it is extended only at
a guard call, and only with an antecedent not already in it — which is
what the measure of `wip/ui_routeB_n4q_thm.lean` §1 needs.  Recording the
goal's positive at the aggregate instead gives smaller interpolants and
earlier thresholds, but `seen` then drops at the ∃p companion of a
disjunctive hypothesis in ∀p mode, and the measure does not close there;
`docs/n4-loopcheck.md` §4 records the comparison.

Dropping a disjunct of a ∀p aggregate makes it STRONGER and dropping a
conjunct of an ∃p aggregate makes it WEAKER, so both soundness statements
(`done ⊢ E`, `A, done ⊢ G`) are preserved by the change in the easy
direction; minimality is the direction at risk and is not claimed here.

**Two policies, and the reason both are built.**  The blueprint's WP3
loop elimination is a PER-STATION check: `seen` grows within a station and
is reset whenever the station changes, "because the antecedents of a
station are finitely many".  That policy is REFUTED here (§ cell (iii)):
the ∀p goal-inversion at an implication goal `Q ⊃ N` moves `invertPos Q`
into the station and starts the goal again, so a station can grow without
bound while `seen` is reset each time round, and the guard loop survives.
The failure is ◯-FREE: it is cell (iii) of `docs/n4-circfree-cases.md`.
The policy that does terminate carries `seen` across station changes as
well.  The two are the two instances of ONE recursion, parameterised by
the reset map `rst : List Pos → List Pos`:

    interpQ0 = interpG (fun _ => [])   -- per-station: REFUTED (cell (iii))
    interpQ  = interpG id              -- global

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_n4_cells
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The loop check -/

/-- Has this antecedent's own goal already been attacked? -/
def seenMem : List Pos → Pos → Bool
  | [], _ => false
  | R :: s, Q => if R = Q then true else seenMem s Q

theorem seenMem_cons_self (s : List Pos) (Q : Pos) : seenMem (Q :: s) Q = true := by
  simp [seenMem]

/-- One approximant level: the previous fuel level, as a function. -/
abbrev ApproxQ : Type := List Neg → List Neg → Option Neg → List Pos → Neg

/-- The ∃p row of a parked compound implication `Qa ⊃ N`, loop-checked: the
guarded conjunct becomes `⊤` when `Qa` is already in `seen`, and the guard
call that is emitted records `Qa`.  `res` is the extra todo of the
Dyckhoff row (`[↓N′ ⊃ N]`), `[]` for the other four. -/
def parkRowE (rst : List Pos → List Pos) (prev : ApproxQ)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest res : List Neg)
    (seen : List Pos) : Neg :=
  nAnd (if seenMem seen Qa then nTop
        else .imp (.down (prev [] done (some (.up Qa)) (Qa :: seen)))
                  (prev [N] rest none (rst seen)))
       (prev res rest none (rst seen))

/-- The ∀p attack row of a parked compound implication `Qa ⊃ N` at the goal
`goal`, loop-checked: `⊥` when `Qa`'s own goal is already in `seen`, and the
guard call that is emitted records `Qa`. -/
def parkRowA (rst : List Pos → List Pos) (prev : ApproxQ)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest : List Neg) (goal : Neg)
    (seen : List Pos) : Neg :=
  if seenMem seen Qa then nBot
  else nAnd (prev [] done (some (.up Qa)) (Qa :: seen))
            (prev [N] rest (some goal) (rst seen))

/-! # Part 2 · The row maps -/

/-- The ∃p station map, loop-checked (`eConjRowsP`). -/
def eRowsQ (rst : List Pos → List Pos) (p : String) (prev : ApproxQ)
    (done : List Neg) (seen : List Pos) : List Neg :=
  (splits done).map (fun (Xr : Neg × List Neg) =>
    match Xr with
    | (.up (.atom a), _) => pGuard p a nTop (.up (.atom a))
    | (.imp (.atom a) N, rest) =>
        pGuard p a nTop (.imp (.atom a) (prev [N] rest none (rst seen)))
    | (.imp (.down (.imp Q' N')) N, rest) =>
        parkRowE rst prev done (.down (.imp Q' N')) N rest [.imp (.down N') N] seen
    | (.circ Q, rest) => .circ (.down (prev [.up Q] rest none (rst seen)))
    | (.imp (.down (.circ Q')) N, rest) =>
        parkRowE rst prev done (.down (.circ Q')) N rest [] seen
    | (.imp (.or Qa Qb) N, rest) => parkRowE rst prev done (.or Qa Qb) N rest [] seen
    | (.imp (.down (.up Pa)) N, rest) =>
        parkRowE rst prev done (.down (.up Pa)) N rest [] seen
    | (.imp (.down (.and Ma Mb)) N, rest) =>
        parkRowE rst prev done (.down (.and Ma Mb)) N rest [] seen
    | _ => nTop)

/-- The ∀p station map, loop-checked (`truStationRowsP` when `box = false`,
`circStationRowsP` when `box = true`; the two differ only in the box row,
which `interpP` emits under a ◯-goal and nowhere else). -/
def aRowsQ (rst : List Pos → List Pos) (p : String) (prev : ApproxQ)
    (done : List Neg) (goal : Neg) (box : Bool) (seen : List Pos) : List Neg :=
  (splits done).map (fun (Xr : Neg × List Neg) =>
    match Xr with
    | (.imp (.atom a) N, rest) =>
        pGuard p a nBot
          (nAnd (.up (.atom a)) (prev [N] rest (some goal) (rst seen)))
    | (.imp (.down (.imp Q' N')) N, rest) =>
        parkRowA rst prev done (.down (.imp Q' N')) N rest goal seen
    | (.imp (.down (.circ Q')) N, rest) =>
        parkRowA rst prev done (.down (.circ Q')) N rest goal seen
    | (.imp (.or Qa Qb) N, rest) => parkRowA rst prev done (.or Qa Qb) N rest goal seen
    | (.imp (.down (.up Pa)) N, rest) =>
        parkRowA rst prev done (.down (.up Pa)) N rest goal seen
    | (.imp (.down (.and Ma Mb)) N, rest) =>
        parkRowA rst prev done (.down (.and Ma Mb)) N rest goal seen
    | (.circ R, rest) =>
        if box then
          .imp (.down (prev [.up R] rest none (rst seen)))
               (prev [.up R] rest (some goal) (rst seen))
        else nBot
    | _ => nBot)

/-- The lax goal-inversion prefix, loop-checked (`laxPrefixP`); every call is
at the same station and the same `seen`. -/
def laxPrefixQ (prev : ApproxQ) (done : List Neg) (seen : List Pos) :
    Pos → List Neg
  | .atom q => [prev [] done (some (.up (.atom q))) seen]
  | .fls => [prev [] done (some (.up .fls)) seen]
  | .or P₁ P₂ => [prev [] done (some (.circ P₁)) seen,
                  prev [] done (some (.circ P₂)) seen,
                  prev [] done (some (.up (.or P₁ P₂))) seen]
  | .down (.up P') => [prev [] done (some (.circ P')) seen]
  | .down (.circ P') => [prev [] done (some (.circ P')) seen]
  | .down (.and M₁ M₂) => [prev [] done (some (.up (.down (.and M₁ M₂)))) seen]
  | .down (.imp Q₀ N₀) => [prev [] done (some (.up (.down (.imp Q₀ N₀)))) seen]

/-! # Part 3 · The aggregate and the step -/

/-- The aggregate phase at a saturated station, loop-checked. -/
def aggQ (rst : List Pos → List Pos) (p : String) (prev : ApproxQ)
    (done : List Neg) (g : Option Neg) (seen : List Pos) : Neg :=
  match g with
  | none => nAndAll (eRowsQ rst p prev done seen)
  | some (.imp Q N) =>
      nAndAll ((invertPos Q).map (fun b =>
        .imp (.down (prev b done none seen)) (prev b done (some N) seen)))
  | some (.and M N) =>
      nAnd (prev [] done (some M) seen) (prev [] done (some N) seen)
  | some (.up (.atom q)) =>
      if atomMem q done then nTop
      else nOrAll (atomHead p q ++
        aRowsQ rst p prev done (.up (.atom q)) false seen)
  | some (.up .fls) =>
      nOrAll (aRowsQ rst p prev done (.up .fls) false seen)
  | some (.up (.or P₁ P₂)) =>
      nOrAll ([prev [] done (some (.up P₁)) seen,
               prev [] done (some (.up P₂)) seen] ++
        aRowsQ rst p prev done (.up (.or P₁ P₂)) false seen)
  | some (.up (.down M)) =>
      nOrAll ([prev [] done (some M) seen] ++
        aRowsQ rst p prev done (.up (.down M)) false seen)
  | some (.circ Q) =>
      .circ (.down (nOrAll (laxPrefixQ prev done seen Q ++
        aRowsQ rst p prev done (.circ Q) true seen)))

/-- One fuel level of the loop-checked recursion, given the level below.
Clause for clause `interpP`'s `f+1` case. -/
def stepQ (rst : List Pos → List Pos) (p : String) (prev : ApproxQ) :
    List Neg → List Neg → Option Neg → List Pos → Neg
  | .up (.atom a) :: todo, done, g, s => prev todo (.up (.atom a) :: done) g (rst s)
  | .up .fls :: _, _, none, _ => nBot
  | .up .fls :: _, _, some _, _ => nTop
  | .up (.or P Q) :: todo, done, none, s =>
      nOrAll ((invertPos (.or P Q)).map (fun b => prev (b ++ todo) done none (rst s)))
  | .up (.or P Q) :: todo, done, some G, s =>
      nAndAll ((invertPos (.or P Q)).map (fun b =>
        .imp (.down (prev (b ++ todo) done none (rst s)))
          (prev (b ++ todo) done (some G) (rst s))))
  | .up (.down M) :: todo, done, g, s => prev (M :: todo) done g (rst s)
  | .and M N :: todo, done, g, s => prev (M :: N :: todo) done g (rst s)
  | .imp .fls _ :: todo, done, g, s => prev todo done g (rst s)
  | .imp (.atom a) N :: todo, done, g, s => prev todo (.imp (.atom a) N :: done) g (rst s)
  | .imp (.or Q₁ Q₂) N :: todo, done, g, s =>
      prev todo (.imp (.or Q₁ Q₂) N :: done) g (rst s)
  | .imp (.down (.up P')) N :: todo, done, g, s =>
      prev todo (.imp (.down (.up P')) N :: done) g (rst s)
  | .imp (.down (.and M₁ M₂)) N :: todo, done, g, s =>
      prev todo (.imp (.down (.and M₁ M₂)) N :: done) g (rst s)
  | .imp (.down (.imp Q' N')) N :: todo, done, g, s =>
      prev todo (.imp (.down (.imp Q' N')) N :: done) g (rst s)
  | .circ Q :: todo, done, g, s => prev todo (.circ Q :: done) g (rst s)
  | .imp (.down (.circ Q')) N :: todo, done, g, s =>
      prev todo (.imp (.down (.circ Q')) N :: done) g (rst s)
  | [], done, g, seen =>
      match findFire done (splits done) with
      | some (_, N, rest) => prev [N] rest g (rst seen)
      | none => aggQ rst p prev done g seen

/-- **The loop-checked interpolant, with a reset policy.** -/
def interpG (rst : List Pos → List Pos) (p : String) :
    Nat → List Neg → List Neg → Option Neg → List Pos → Neg
  | 0 => fun _ _ g _ => match g with | none => nTop | some _ => nBot
  | f + 1 => stepQ rst p (interpG rst p f)

/-- The blueprint's PER-STATION loop check: `seen` is reset on every station
change.  REFUTED below at cell (iii). -/
abbrev interpQ0 : String → Nat → List Neg → List Neg → Option Neg → List Pos → Neg :=
  interpG (fun _ => [])

/-- **The loop-checked interpolant**: `seen` is carried across station
changes as well, so it is monotone along every edge of the recursion. -/
abbrev interpQ : String → Nat → List Neg → List Neg → Option Neg → List Pos → Neg :=
  interpG id

/-- The fuel-0 defaults, as equations. -/
theorem interpG_zero_none (rst : List Pos → List Pos) (p : String)
    (todo done : List Neg) (seen : List Pos) :
    interpG rst p 0 todo done none seen = nTop := rfl

theorem interpG_zero_some (rst : List Pos → List Pos) (p : String)
    (todo done : List Neg) (G : Neg) (seen : List Pos) :
    interpG rst p 0 todo done (some G) seen = nBot := rfl

/-- The step equation. -/
theorem interpG_succ (rst : List Pos → List Pos) (p : String) (f : Nat) :
    interpG rst p (f + 1) = stepQ rst p (interpG rst p f) := rfl

/-! # Part 4 · `p`-freeness

`wip/ui_routeB_n3.lean`'s `interpP_pfree` for `interpP`, re-proved for
`interpG`.  The step form pays here: the induction is on the fuel and the
step is one lemma, so the sixteen aggregate clauses are discharged once,
against an arbitrary `prev`, rather than through `fun_induction`. -/

theorem pfree_parkRowE {p : String} {rst : List Pos → List Pos} {prev : ApproxQ}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (Qa : Pos) (N : Neg) (rest res : List Neg)
    (seen : List Pos) : PFreeN p (parkRowE rst prev done Qa N rest res seen) := by
  unfold parkRowE
  refine pfree_nAnd ?_ (hp _ _ _ _)
  split
  · exact pfree_nTop
  · exact ⟨hp _ _ _ _, hp _ _ _ _⟩

theorem pfree_parkRowA {p : String} {rst : List Pos → List Pos} {prev : ApproxQ}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (Qa : Pos) (N : Neg) (rest : List Neg) (goal : Neg)
    (seen : List Pos) : PFreeN p (parkRowA rst prev done Qa N rest goal seen) := by
  unfold parkRowA
  split
  · exact pfree_nBot
  · exact pfree_nAnd (hp _ _ _ _) (hp _ _ _ _)

theorem pfree_eRowsQ {p : String} {rst : List Pos → List Pos} {prev : ApproxQ}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (seen : List Pos) :
    ∀ x ∈ eRowsQ rst p prev done seen, PFreeN p x := by
  intro x hx
  simp only [eRowsQ, List.mem_map] at hx
  obtain ⟨⟨X, rest⟩, _, rfl⟩ := hx
  match X with
  | .up (.atom a) => exact pfree_pGuard pfree_nTop (fun h => h)
  | .imp (.atom a) N =>
      exact pfree_pGuard pfree_nTop (fun h => ⟨h, hp _ _ _ _⟩)
  | .imp (.down (.imp _ _)) _ => exact pfree_parkRowE hp _ _ _ _ _ _
  | .circ _ => exact hp _ _ _ _
  | .imp (.down (.circ _)) _ => exact pfree_parkRowE hp _ _ _ _ _ _
  | .imp (.or _ _) _ => exact pfree_parkRowE hp _ _ _ _ _ _
  | .imp (.down (.up _)) _ => exact pfree_parkRowE hp _ _ _ _ _ _
  | .imp (.down (.and _ _)) _ => exact pfree_parkRowE hp _ _ _ _ _ _
  | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _ | .and _ _ =>
      exact pfree_nTop

theorem pfree_aRowsQ {p : String} {rst : List Pos → List Pos} {prev : ApproxQ}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (goal : Neg) (box : Bool) (seen : List Pos) :
    ∀ x ∈ aRowsQ rst p prev done goal box seen, PFreeN p x := by
  intro x hx
  simp only [aRowsQ, List.mem_map] at hx
  obtain ⟨⟨X, rest⟩, _, rfl⟩ := hx
  match X with
  | .imp (.atom a) N =>
      exact pfree_pGuard pfree_nBot (fun h => ⟨h, hp _ _ _ _⟩)
  | .imp (.down (.imp _ _)) _ => exact pfree_parkRowA hp _ _ _ _ _ _
  | .imp (.down (.circ _)) _ => exact pfree_parkRowA hp _ _ _ _ _ _
  | .imp (.or _ _) _ => exact pfree_parkRowA hp _ _ _ _ _ _
  | .imp (.down (.up _)) _ => exact pfree_parkRowA hp _ _ _ _ _ _
  | .imp (.down (.and _ _)) _ => exact pfree_parkRowA hp _ _ _ _ _ _
  | .circ _ =>
      dsimp only
      split
      · exact ⟨hp _ _ _ _, hp _ _ _ _⟩
      · exact pfree_nBot
  | .up (.atom _) | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _
  | .and _ _ => exact pfree_nBot

theorem pfree_laxPrefixQ {p : String} {prev : ApproxQ}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (seen : List Pos) (Q : Pos) :
    ∀ x ∈ laxPrefixQ prev done seen Q, PFreeN p x := by
  match Q with
  | .atom _ | .fls | .or _ _ | .down (.up _) | .down (.circ _)
  | .down (.and _ _) | .down (.imp _ _) =>
    intro x hx
    simp only [laxPrefixQ, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact hp _ _ _ _

theorem pfree_aggQ {p : String} {rst : List Pos → List Pos} {prev : ApproxQ}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (g : Option Neg) (seen : List Pos) :
    PFreeN p (aggQ rst p prev done g seen) := by
  match g with
  | none => exact pfree_nAndAll (pfree_eRowsQ hp _ _)
  | some (.imp Q N) =>
      refine pfree_nAndAll ?_
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx
      exact ⟨hp _ _ _ _, hp _ _ _ _⟩
  | some (.and _ _) => exact pfree_nAnd (hp _ _ _ _) (hp _ _ _ _)
  | some (.up (.atom q)) =>
      show PFreeN p (if atomMem q done then _ else _)
      split
      · exact pfree_nTop
      · refine pfree_nOrAll ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact pfree_atomHead x hx
        · exact pfree_aRowsQ hp _ _ _ _ x hx
  | some (.up .fls) => exact pfree_nOrAll (pfree_aRowsQ hp _ _ _ _)
  | some (.up (.or _ _)) =>
      refine pfree_nOrAll ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hp _ _ _ _
        · rcases List.mem_singleton.mp hx with rfl; exact hp _ _ _ _
      · exact pfree_aRowsQ hp _ _ _ _ x hx
  | some (.up (.down _)) =>
      refine pfree_nOrAll ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_singleton.mp hx with rfl; exact hp _ _ _ _
      · exact pfree_aRowsQ hp _ _ _ _ x hx
  | some (.circ _) =>
      show PFreeN p (Neg.circ (.down (nOrAll _)))
      refine pfree_nOrAll ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact pfree_laxPrefixQ hp _ _ _ x hx
      · exact pfree_aRowsQ hp _ _ _ _ x hx

theorem pfree_stepQ {p : String} {rst : List Pos → List Pos} {prev : ApproxQ}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen)) :
    ∀ todo done g seen, PFreeN p (stepQ rst p prev todo done g seen) := by
  intro todo done g seen
  match todo, g with
  | [], g =>
      show PFreeN p (match findFire done (splits done) with
        | some (_, N, rest) => prev [N] rest g (rst seen)
        | none => aggQ rst p prev done g seen)
      split
      · exact hp _ _ _ _
      · exact pfree_aggQ hp _ _ _
  | .up (.atom _) :: _, _ => exact hp _ _ _ _
  | .up .fls :: _, none => exact pfree_nBot
  | .up .fls :: _, some _ => exact pfree_nTop
  | .up (.or _ _) :: _, none =>
      refine pfree_nOrAll ?_
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx
      exact hp _ _ _ _
  | .up (.or _ _) :: _, some _ =>
      refine pfree_nAndAll ?_
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx
      exact ⟨hp _ _ _ _, hp _ _ _ _⟩
  | .up (.down _) :: _, _ => exact hp _ _ _ _
  | .and _ _ :: _, _ => exact hp _ _ _ _
  | .imp .fls _ :: _, _ => exact hp _ _ _ _
  | .imp (.atom _) _ :: _, _ => exact hp _ _ _ _
  | .imp (.or _ _) _ :: _, _ => exact hp _ _ _ _
  | .imp (.down (.up _)) _ :: _, _ => exact hp _ _ _ _
  | .imp (.down (.and _ _)) _ :: _, _ => exact hp _ _ _ _
  | .imp (.down (.imp _ _)) _ :: _, _ => exact hp _ _ _ _
  | .circ _ :: _, _ => exact hp _ _ _ _
  | .imp (.down (.circ _)) _ :: _, _ => exact hp _ _ _ _

/-- **The loop-checked interpolant never mentions `p`, at any fuel, under any
reset policy.** -/
theorem interpG_pfree (rst : List Pos → List Pos) (p : String) :
    ∀ (f : Nat) (todo done : List Neg) (g : Option Neg) (seen : List Pos),
      PFreeN p (interpG rst p f todo done g seen) := by
  intro f
  induction f with
  | zero =>
      intro todo done g seen
      match g with
      | none => exact pfree_nTop
      | some _ => exact pfree_nBot
  | succ f ih => exact pfree_stepQ (fun t d g s => ih t d g s)

theorem interpQ_pfree (p : String) (f : Nat) (todo done : List Neg)
    (g : Option Neg) (seen : List Pos) : PFreeN p (interpQ p f todo done g seen) :=
  interpG_pfree id p f todo done g seen

end LJFO
