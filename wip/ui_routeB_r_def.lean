/-
Route (B), node **N4**, WP12: the recursion `interpR`, which cuts only
GENUINE loops.

`wip/ui_routeB_n4q.lean` builds `interpQ`, which records the ANTECEDENT
`Qa` alone at a guard call and cuts every later re-attack of `Qa ⊃ N`,
whatever station it happens at.  `docs/ui-ljfo-clause-table.md` §4.28
shows why that is too coarse for a derivation-level cofinality argument:
a re-attack at a STRICTLY LARGER station is not answered by a
sub-derivation of the guard sequent, so the escape it would need sits at
the wrong station, and absorbing it needs per-fuel minimality.

`interpR` records the PAIR `(Qa, done)` — the antecedent together with the
station AS A SET — and cuts a re-attack only when a pair `(Qa, T)` with
`T` set-equal to the current station is already recorded.  This is the
blueprint's PER-STATION policy, which `docs/n4-loopcheck.md` §2 refutes
with the station read as a LIST (cell (iii)'s station grows by one `↑a`
per round), read instead as a SET, where cell (iii)'s station stabilises
after one round.

Everything else is `interpG` verbatim: the cut is `⊥` in the ∀p aggregate
and `⊤` in the ∃p aggregate (the SYMMETRIC check; the asymmetric first
draft of §4.25 loops), the guard call is made at the extended `seen`, and
`seen` is carried along every edge, so it is monotone.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_n4q
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The station read as a set, and the pair check -/

/-- Membership of a negative in a station, as a `Bool`. -/
def negMem : List Neg → Neg → Bool
  | [], _ => false
  | X :: s, Y => if X = Y then true else negMem s Y

/-- `T` is contained in `S` as a set. -/
def subNeg : List Neg → List Neg → Bool
  | [], _ => true
  | X :: T, S => negMem S X && subNeg T S

/-- `T` and `S` have the same members. -/
def sameSet (T S : List Neg) : Bool := subNeg T S && subNeg S T

/-- The record carried by `interpR`: the pairs (antecedent, station) at
whose guard the recursion has already been called. -/
abbrev SeenR : Type := List (Pos × List Neg)

/-- **The genuine-loop test.**  Has `Qa`'s own goal already been attacked at
a station with the same members as `done`? -/
def seenMemR : SeenR → Pos → List Neg → Bool
  | [], _, _ => false
  | (Q, T) :: s, Qa, done =>
      if Q = Qa then (if sameSet T done then true else seenMemR s Qa done)
      else seenMemR s Qa done

theorem seenMemR_cons_self (s : SeenR) (Q : Pos) (done : List Neg) :
    seenMemR ((Q, done) :: s) Q done = true := by
  have h : sameSet done done = true := by
    have hsub : ∀ (T S : List Neg), (∀ X ∈ T, negMem S X = true) → subNeg T S = true := by
      intro T
      induction T with
      | nil => intro _ _; rfl
      | cons X T ih =>
          intro S h
          simp only [subNeg, Bool.and_eq_true]
          exact ⟨h X (by simp), ih S (fun Y hY => h Y (by simp [hY]))⟩
    have hmem : ∀ (S : List Neg) (X : Neg), X ∈ S → negMem S X = true := by
      intro S
      induction S with
      | nil => intro X hX; cases hX
      | cons Y S ih =>
          intro X hX
          simp only [negMem]
          by_cases hYX : Y = X
          · simp [hYX]
          · simp only [hYX, if_false]
            rcases List.mem_cons.mp hX with rfl | hX'
            · exact absurd rfl hYX
            · exact ih X hX'
    simp only [sameSet, Bool.and_eq_true]
    exact ⟨hsub done done (fun X hX => hmem done X hX), hsub done done (fun X hX => hmem done X hX)⟩
  simp [seenMemR, h]

/-! # Part 2 · The rows

One approximant level, and the two clauses that carry the cut.  The only
difference from `wip/ui_routeB_n4q.lean` is the test `seenMemR seen Qa done`
in place of `seenMem seen Qa`, and the recorded item `(Qa, done)` in place
of `Qa`. -/

/-- One approximant level: the previous fuel level, as a function. -/
abbrev ApproxR : Type := List Neg → List Neg → Option Neg → SeenR → Neg

/-- The ∃p row of a parked compound implication `Qa ⊃ N`, loop-checked on the
PAIR: the guarded conjunct becomes `⊤` when `(Qa, done)` is already recorded
up to set-equality of the station, and the guard call that is emitted records
`(Qa, done)`.  `res` is the extra todo of the Dyckhoff row (`[↓N′ ⊃ N]`),
`[]` for the other four. -/
def parkRowER (rst : SeenR → SeenR) (prev : ApproxR)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest res : List Neg)
    (seen : SeenR) : Neg :=
  nAnd (if seenMemR seen Qa done then nTop
        else .imp (.down (prev [] done (some (.up Qa)) ((Qa, done) :: seen)))
                  (prev [N] rest none (rst seen)))
       (prev res rest none (rst seen))

/-- The ∀p attack row of a parked compound implication `Qa ⊃ N` at the goal
`goal`, loop-checked on the PAIR. -/
def parkRowAR (rst : SeenR → SeenR) (prev : ApproxR)
    (done : List Neg) (Qa : Pos) (N : Neg) (rest : List Neg) (goal : Neg)
    (seen : SeenR) : Neg :=
  if seenMemR seen Qa done then nBot
  else nAnd (prev [] done (some (.up Qa)) ((Qa, done) :: seen))
            (prev [N] rest (some goal) (rst seen))

/-! # Part 3 · The row maps -/

/-- The ∃p station map (`eRowsQ`). -/
def eRowsR (rst : SeenR → SeenR) (p : String) (prev : ApproxR)
    (done : List Neg) (seen : SeenR) : List Neg :=
  (splits done).map (fun (Xr : Neg × List Neg) =>
    match Xr with
    | (.up (.atom a), _) => pGuard p a nTop (.up (.atom a))
    | (.imp (.atom a) N, rest) =>
        pGuard p a nTop (.imp (.atom a) (prev [N] rest none (rst seen)))
    | (.imp (.down (.imp Q' N')) N, rest) =>
        parkRowER rst prev done (.down (.imp Q' N')) N rest [.imp (.down N') N] seen
    | (.circ Q, rest) => .circ (.down (prev [.up Q] rest none (rst seen)))
    | (.imp (.down (.circ Q')) N, rest) =>
        parkRowER rst prev done (.down (.circ Q')) N rest [] seen
    | (.imp (.or Qa Qb) N, rest) => parkRowER rst prev done (.or Qa Qb) N rest [] seen
    | (.imp (.down (.up Pa)) N, rest) =>
        parkRowER rst prev done (.down (.up Pa)) N rest [] seen
    | (.imp (.down (.and Ma Mb)) N, rest) =>
        parkRowER rst prev done (.down (.and Ma Mb)) N rest [] seen
    | _ => nTop)

/-- The ∀p station map (`aRowsQ`). -/
def aRowsR (rst : SeenR → SeenR) (p : String) (prev : ApproxR)
    (done : List Neg) (goal : Neg) (box : Bool) (seen : SeenR) : List Neg :=
  (splits done).map (fun (Xr : Neg × List Neg) =>
    match Xr with
    | (.imp (.atom a) N, rest) =>
        pGuard p a nBot
          (nAnd (.up (.atom a)) (prev [N] rest (some goal) (rst seen)))
    | (.imp (.down (.imp Q' N')) N, rest) =>
        parkRowAR rst prev done (.down (.imp Q' N')) N rest goal seen
    | (.imp (.down (.circ Q')) N, rest) =>
        parkRowAR rst prev done (.down (.circ Q')) N rest goal seen
    | (.imp (.or Qa Qb) N, rest) => parkRowAR rst prev done (.or Qa Qb) N rest goal seen
    | (.imp (.down (.up Pa)) N, rest) =>
        parkRowAR rst prev done (.down (.up Pa)) N rest goal seen
    | (.imp (.down (.and Ma Mb)) N, rest) =>
        parkRowAR rst prev done (.down (.and Ma Mb)) N rest goal seen
    | (.circ R, rest) =>
        if box then
          .imp (.down (prev [.up R] rest none (rst seen)))
               (prev [.up R] rest (some goal) (rst seen))
        else nBot
    | _ => nBot)

/-- The lax goal-inversion prefix (`laxPrefixQ`). -/
def laxPrefixR (prev : ApproxR) (done : List Neg) (seen : SeenR) :
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

/-! # Part 4 · The aggregate and the step -/

/-- The aggregate phase at a saturated station (`aggQ`). -/
def aggR (rst : SeenR → SeenR) (p : String) (prev : ApproxR)
    (done : List Neg) (g : Option Neg) (seen : SeenR) : Neg :=
  match g with
  | none => nAndAll (eRowsR rst p prev done seen)
  | some (.imp Q N) =>
      nAndAll ((invertPos Q).map (fun b =>
        .imp (.down (prev b done none seen)) (prev b done (some N) seen)))
  | some (.and M N) =>
      nAnd (prev [] done (some M) seen) (prev [] done (some N) seen)
  | some (.up (.atom q)) =>
      if atomMem q done then nTop
      else nOrAll (atomHead p q ++
        aRowsR rst p prev done (.up (.atom q)) false seen)
  | some (.up .fls) =>
      nOrAll (aRowsR rst p prev done (.up .fls) false seen)
  | some (.up (.or P₁ P₂)) =>
      nOrAll ([prev [] done (some (.up P₁)) seen,
               prev [] done (some (.up P₂)) seen] ++
        aRowsR rst p prev done (.up (.or P₁ P₂)) false seen)
  | some (.up (.down M)) =>
      nOrAll ([prev [] done (some M) seen] ++
        aRowsR rst p prev done (.up (.down M)) false seen)
  | some (.circ Q) =>
      .circ (.down (nOrAll (laxPrefixR prev done seen Q ++
        aRowsR rst p prev done (.circ Q) true seen)))

/-- One fuel level of the pair-recording recursion (`stepQ`). -/
def stepR (rst : SeenR → SeenR) (p : String) (prev : ApproxR) :
    List Neg → List Neg → Option Neg → SeenR → Neg
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
      | none => aggR rst p prev done g seen

/-- **The pair-recording loop-checked interpolant, with a reset policy.** -/
def interpGR (rst : SeenR → SeenR) (p : String) :
    Nat → List Neg → List Neg → Option Neg → SeenR → Neg
  | 0 => fun _ _ g _ => match g with | none => nTop | some _ => nBot
  | f + 1 => stepR rst p (interpGR rst p f)

/-- **`interpR`**: the pair-recording recursion with `seen` carried along
every edge. -/
abbrev interpR : String → Nat → List Neg → List Neg → Option Neg → SeenR → Neg :=
  interpGR id

/-- The fuel-0 defaults, as equations. -/
theorem interpGR_zero_none (rst : SeenR → SeenR) (p : String)
    (todo done : List Neg) (seen : SeenR) :
    interpGR rst p 0 todo done none seen = nTop := rfl

theorem interpGR_zero_some (rst : SeenR → SeenR) (p : String)
    (todo done : List Neg) (G : Neg) (seen : SeenR) :
    interpGR rst p 0 todo done (some G) seen = nBot := rfl

/-- The step equation. -/
theorem interpGR_succ (rst : SeenR → SeenR) (p : String) (f : Nat) :
    interpGR rst p (f + 1) = stepR rst p (interpGR rst p f) := rfl

/-! # Part 5 · `p`-freeness

`interpG_pfree` re-proved for `interpGR`; the proofs are the same, the
recursion being the same up to the recorded item. -/

theorem pfree_parkRowER {p : String} {rst : SeenR → SeenR} {prev : ApproxR}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (Qa : Pos) (N : Neg) (rest res : List Neg)
    (seen : SeenR) : PFreeN p (parkRowER rst prev done Qa N rest res seen) := by
  unfold parkRowER
  refine pfree_nAnd ?_ (hp _ _ _ _)
  split
  · exact pfree_nTop
  · exact ⟨hp _ _ _ _, hp _ _ _ _⟩

theorem pfree_parkRowAR {p : String} {rst : SeenR → SeenR} {prev : ApproxR}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (Qa : Pos) (N : Neg) (rest : List Neg) (goal : Neg)
    (seen : SeenR) : PFreeN p (parkRowAR rst prev done Qa N rest goal seen) := by
  unfold parkRowAR
  split
  · exact pfree_nBot
  · exact pfree_nAnd (hp _ _ _ _) (hp _ _ _ _)

theorem pfree_eRowsR {p : String} {rst : SeenR → SeenR} {prev : ApproxR}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (seen : SeenR) :
    ∀ x ∈ eRowsR rst p prev done seen, PFreeN p x := by
  intro x hx
  simp only [eRowsR, List.mem_map] at hx
  obtain ⟨⟨X, rest⟩, _, rfl⟩ := hx
  match X with
  | .up (.atom a) => exact pfree_pGuard pfree_nTop (fun h => h)
  | .imp (.atom a) N =>
      exact pfree_pGuard pfree_nTop (fun h => ⟨h, hp _ _ _ _⟩)
  | .imp (.down (.imp _ _)) _ => exact pfree_parkRowER hp _ _ _ _ _ _
  | .circ _ => exact hp _ _ _ _
  | .imp (.down (.circ _)) _ => exact pfree_parkRowER hp _ _ _ _ _ _
  | .imp (.or _ _) _ => exact pfree_parkRowER hp _ _ _ _ _ _
  | .imp (.down (.up _)) _ => exact pfree_parkRowER hp _ _ _ _ _ _
  | .imp (.down (.and _ _)) _ => exact pfree_parkRowER hp _ _ _ _ _ _
  | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _ | .and _ _ =>
      exact pfree_nTop

theorem pfree_aRowsR {p : String} {rst : SeenR → SeenR} {prev : ApproxR}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (goal : Neg) (box : Bool) (seen : SeenR) :
    ∀ x ∈ aRowsR rst p prev done goal box seen, PFreeN p x := by
  intro x hx
  simp only [aRowsR, List.mem_map] at hx
  obtain ⟨⟨X, rest⟩, _, rfl⟩ := hx
  match X with
  | .imp (.atom a) N =>
      exact pfree_pGuard pfree_nBot (fun h => ⟨h, hp _ _ _ _⟩)
  | .imp (.down (.imp _ _)) _ => exact pfree_parkRowAR hp _ _ _ _ _ _
  | .imp (.down (.circ _)) _ => exact pfree_parkRowAR hp _ _ _ _ _ _
  | .imp (.or _ _) _ => exact pfree_parkRowAR hp _ _ _ _ _ _
  | .imp (.down (.up _)) _ => exact pfree_parkRowAR hp _ _ _ _ _ _
  | .imp (.down (.and _ _)) _ => exact pfree_parkRowAR hp _ _ _ _ _ _
  | .circ _ =>
      dsimp only
      split
      · exact ⟨hp _ _ _ _, hp _ _ _ _⟩
      · exact pfree_nBot
  | .up (.atom _) | .up .fls | .up (.or _ _) | .up (.down _) | .imp .fls _
  | .and _ _ => exact pfree_nBot

theorem pfree_laxPrefixR {p : String} {prev : ApproxR}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (seen : SeenR) (Q : Pos) :
    ∀ x ∈ laxPrefixR prev done seen Q, PFreeN p x := by
  match Q with
  | .atom _ | .fls | .or _ _ | .down (.up _) | .down (.circ _)
  | .down (.and _ _) | .down (.imp _ _) =>
    intro x hx
    simp only [laxPrefixR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact hp _ _ _ _

theorem pfree_aggR {p : String} {rst : SeenR → SeenR} {prev : ApproxR}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen))
    (done : List Neg) (g : Option Neg) (seen : SeenR) :
    PFreeN p (aggR rst p prev done g seen) := by
  match g with
  | none => exact pfree_nAndAll (pfree_eRowsR hp _ _)
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
        · exact pfree_aRowsR hp _ _ _ _ x hx
  | some (.up .fls) => exact pfree_nOrAll (pfree_aRowsR hp _ _ _ _)
  | some (.up (.or _ _)) =>
      refine pfree_nOrAll ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hp _ _ _ _
        · rcases List.mem_singleton.mp hx with rfl; exact hp _ _ _ _
      · exact pfree_aRowsR hp _ _ _ _ x hx
  | some (.up (.down _)) =>
      refine pfree_nOrAll ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_singleton.mp hx with rfl; exact hp _ _ _ _
      · exact pfree_aRowsR hp _ _ _ _ x hx
  | some (.circ _) =>
      show PFreeN p (Neg.circ (.down (nOrAll _)))
      refine pfree_nOrAll ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact pfree_laxPrefixR hp _ _ _ x hx
      · exact pfree_aRowsR hp _ _ _ _ x hx

theorem pfree_stepR {p : String} {rst : SeenR → SeenR} {prev : ApproxR}
    (hp : ∀ todo done g seen, PFreeN p (prev todo done g seen)) :
    ∀ todo done g seen, PFreeN p (stepR rst p prev todo done g seen) := by
  intro todo done g seen
  match todo, g with
  | [], g =>
      show PFreeN p (match findFire done (splits done) with
        | some (_, N, rest) => prev [N] rest g (rst seen)
        | none => aggR rst p prev done g seen)
      split
      · exact hp _ _ _ _
      · exact pfree_aggR hp _ _ _
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

/-- **The pair-recording interpolant never mentions `p`.** -/
theorem interpGR_pfree (rst : SeenR → SeenR) (p : String) :
    ∀ (f : Nat) (todo done : List Neg) (g : Option Neg) (seen : SeenR),
      PFreeN p (interpGR rst p f todo done g seen) := by
  intro f
  induction f with
  | zero =>
      intro todo done g seen
      match g with
      | none => exact pfree_nTop
      | some _ => exact pfree_nBot
  | succ f ih => exact pfree_stepR (fun t d g s => ih t d g s)

theorem interpR_pfree (p : String) (f : Nat) (todo done : List Neg)
    (g : Option Neg) (seen : SeenR) : PFreeN p (interpR p f todo done g seen) :=
  interpGR_pfree id p f todo done g seen

end LJFO

/-! ## Pins -/

#axioms_within LJFO.seenMemR_cons_self [propext, Quot.sound]
#axioms_within LJFO.interpGR_zero_none [propext]
#axioms_within LJFO.interpGR_zero_some [propext]
#axioms_within LJFO.interpGR_succ [propext]
#axioms_within LJFO.pfree_parkRowER [propext, Quot.sound]
#axioms_within LJFO.pfree_parkRowAR [propext, Quot.sound]
#axioms_within LJFO.pfree_eRowsR [propext, Quot.sound]
#axioms_within LJFO.pfree_aRowsR [propext, Quot.sound]
#axioms_within LJFO.pfree_laxPrefixR [propext, Quot.sound]
#axioms_within LJFO.pfree_aggR [propext, Quot.sound]
#axioms_within LJFO.pfree_stepR [propext, Quot.sound]
#axioms_within LJFO.interpGR_pfree [propext, Quot.sound]
#axioms_within LJFO.interpR_pfree [propext, Quot.sound]
