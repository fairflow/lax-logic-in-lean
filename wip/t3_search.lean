/-
T3 — THE SEARCHER: forward saturation over constructions, with sharing.

T2 says the class `solo`/`join` generates is complete, so a search that
ranges over it is searching the right space.  T2 §G also says the
extracted MODEL is exponential, so the search must SHARE: two
constructions that behave the same as premises are interchangeable,
and only one need be kept.  That is the DAG, and this is it.

**The state a join consumes from a premise.**  By
`Reject.join_force_box_iff` a join needs, from each component `c`, four
things over the goal's subformula closure `cl`:

  root(c)  formulas forced at c's root      (the ⊃/∧/∨ clauses)
  univ(c)  formulas forced at EVERY world   (⊃ quantifies over the cone)
  some(c)  formulas forced at SOME world    (what a modal cone realises)
  box(c)   A such that every world of c has an Rₘ-successor forcing A
                                            (the ◯-positive obligation)

Two premises with the same 4-tuple are interchangeable, so the store is
keyed by it.  That is the sharing the tree cannot express.

**Scope, stated.**  Cone choices are restricted to WHOLE components
(which are `Rₘ`-upward closed, so every choice is legal).  The searcher
is therefore SOUND but not known complete: cones selecting part of a
component are not explored.  Every hit is a kernel-checkable
certificate (`Reject.certifies`), so unsoundness is impossible; only
coverage is at risk, and it is reported, never assumed.

**Covering goals.**  Matthew's point: one saturation over a goal whose
subformula closure contains many catalogue representatives settles
many questions at once, because EVERY WORLD of EVERY stored model
certifies an underivability (`Reject.not_laxND_of_check_any`).  The
harvest is free; the choice of goal is what makes it productive.
-/
import Reject.Cert

open PLLND PLLND.FinCM

namespace T3Search

abbrev F := PLLFormula

def vd (b : Bool) : String := if b then "pass" else "FAIL"

/-! ## The closure -/

def subs : F → List F
  | .prop a => [.prop a]
  | .falsePLL => [.falsePLL]
  | .and φ ψ => (.and φ ψ) :: (subs φ ++ subs ψ)
  | .or φ ψ => (.or φ ψ) :: (subs φ ++ subs ψ)
  | .ifThen φ ψ => (.ifThen φ ψ) :: (subs φ ++ subs ψ)
  | .somehow φ => (.somehow φ) :: subs φ

def closureOf (gs : List F) : List F :=
  (gs.flatMap subs ++ [(PLLFormula.falsePLL : F)]).eraseDups

def atomsOf (cl : List F) : List String :=
  (cl.filterMap fun φ => match φ with | .prop a => some a | _ => none).eraseDups

/-! ## Assembly: the join, as data -/

def offAt (Ms : List FinCM) (i : Nat) : Nat := 1 + ((Ms.take i).map (·.n)).sum
def totW (Ms : List FinCM) : Nat := 1 + (Ms.map (·.n)).sum

/-- A fresh root below the disjoint union, with the modal cone taken to
be the union of the components listed in `cone` (whole components are
`Rₘ`-upward closed, so this is always legal). -/
def assemble (Ms : List FinCM) (cone : List Nat) (atoms : List String) : FinCM :=
  { n := totW Ms
    ri := ((List.range (totW Ms)).filter (fun w => w != 0)).map (fun w => (0, w))
          ++ Ms.zipIdx.flatMap (fun p =>
               p.1.ri.map fun e => (offAt Ms p.2 + e.1, offAt Ms p.2 + e.2))
    rm := (cone.flatMap fun i =>
             match Ms[i]? with
             | some M => (List.range M.n).map fun u => (0, offAt Ms i + u)
             | none => [])
          ++ Ms.zipIdx.flatMap (fun p =>
               p.1.rm.map fun e => (offAt Ms p.2 + e.1, offAt Ms p.2 + e.2))
    fall := Ms.zipIdx.flatMap (fun p => p.1.fall.map (offAt Ms p.2 + ·))
    val := atoms.map (fun a => (0, a))
           ++ Ms.zipIdx.flatMap (fun p =>
                p.1.val.map fun e => (offAt Ms p.2 + e.1, e.2)) }

/-- One `solo` world. -/
def soloOf (atoms : List String) (fal : Bool) : FinCM :=
  ⟨1, [], [], if fal then [0] else [], atoms.map fun a => (0, a)⟩

/-! ## The shared state -/

structure St where
  root : List Bool
  univ : List Bool
  some_ : List Bool
  box : List Bool
  deriving BEq, Repr

def stateOf (cl : List F) (M : FinCM) : St :=
  let ws := List.range M.n
  { root := cl.map fun φ => M.forceB 0 φ
    univ := cl.map fun φ => ws.all fun w => M.forceB w φ
    some_ := cl.map fun φ => ws.any fun w => M.forceB w φ
    box := cl.map fun φ => ws.all fun w => ws.any fun u => M.rmB w u && M.forceB u φ }

structure Node where
  st : St
  wit : FinCM

/-! ## Saturation -/

def subsetsUpTo (k : Nat) (l : List Nat) : List (List Nat) :=
  match k with
  | 0 => [[]]
  | k + 1 =>
      let smaller := subsetsUpTo k l
      (smaller ++ l.flatMap fun x => smaller.map fun s => x :: s).eraseDups

/-- One saturation round: every join of at most `arity` stored nodes,
with every whole-component cone choice and every root-atom choice.
Nodes whose state is already present are DISCARDED — that is the
sharing. -/
def round (cl : List F) (arity : Nat) (atomChoices : List (List String))
    (store : List Node) (cap : Nat) : List Node := Id.run do
  let idxs := List.range store.length
  let combos := (subsetsUpTo arity idxs).filter (fun s => s.length ≥ 1)
  let mut out := store
  for combo in combos do
    if out.length ≥ cap then break
    let Ms := combo.filterMap fun i => (store[i]?).map (·.wit)
    for cone in subsetsUpTo Ms.length (List.range Ms.length) do
      for at_ in atomChoices do
        if out.length < cap then
          let M := assemble Ms cone at_
          if M.wellB && Reject.BuiltB M then
            let s := stateOf cl M
            if !(out.any fun nd => nd.st == s) then
              out := out ++ [⟨s, M⟩]
  return out

def saturate (cl : List F) (arity rounds cap : Nat) : List Node := Id.run do
  let ats := (atomsOf cl)
  let atomChoices := (subsetsUpTo ats.length (List.range ats.length)).map fun s =>
    s.filterMap fun i => ats[i]?
  let seeds : List FinCM :=
    (atomChoices.flatMap fun a => [soloOf a false, soloOf a true])
  let mut store : List Node := []
  for M in seeds do
    if M.wellB && Reject.BuiltB M then
      let s := stateOf cl M
      if !(store.any fun nd => nd.st == s) then store := store ++ [⟨s, M⟩]
  for _ in List.range rounds do
    let before := store.length
    store := round cl arity atomChoices store cap
    if store.length == before then break
  return store

/-! ## The harvest -/

/-- Every world of every stored model certifies an underivability. -/
def refutesAt (store : List Node) (Γ : List F) (C : F) : Option (Nat × Nat) :=
  store.zipIdx.findSome? fun p =>
    ((List.range p.1.wit.n).find? fun w => checkB p.1.wit w Γ C).map fun w => (p.2, w)

/-! ## The corpus -/

def bot : F := .falsePLL
def top : F := .ifThen bot bot
def oBot : F := .somehow bot
def nOBot : F := .ifThen oBot bot
def nnOBot : F := .ifThen nOBot bot
def q4 : F := .or nOBot oBot
def q5 : F := .somehow nOBot
def q6 : F := nnOBot
def q7 : F := .or nnOBot nOBot
def q9 : F := .or nnOBot q5
def q10 : F := .ifThen nnOBot oBot
def q11 : F := .or q10 nnOBot
def q8 : F := .ifThen q5 q4
def q14 : F := .ifThen q10 q5
def pv : F := .prop "p"
def qv : F := .prop "q"

/-- The catalogue representatives that fit the closed fragment. -/
def reps : List (String × F) :=
  [("⊥", bot), ("⊤", top), ("◯⊥", oBot), ("¬◯⊥", nOBot), ("ρ4", q4),
   ("ρ5=¬¬◯⊥", q6), ("ρ6", q7), ("ρ7=◯¬◯⊥", q5), ("ρ8", q10), ("ρ9", q9),
   ("ρ10", q11), ("ρ11=g1", q8), ("ρ12=r1", q14)]

/-- **The covering goal**: one formula whose subformula closure holds
every representative, so ONE saturation serves the whole harvest. -/
def coveringGoal : F := reps.foldl (fun acc p => .and acc p.2) top

def derivableCorpus : List (String × List F × F) :=
  [("G4iLL blocker",
    [.somehow (.ifThen (.ifThen (.somehow pv) (.prop "r")) (.somehow pv)),
     .ifThen (.somehow pv) (.prop "r")], .prop "r"),
   ("laxIntro", [pv], .somehow pv),
   ("◯◯p ⊢ ◯p", [.somehow (.somehow pv)], .somehow pv),
   ("⊢ ¬◯⊥ ⊃ ¬◯⊥", [], .ifThen nOBot nOBot),
   ("◯⊥ ⊢ ◯⊥", [oBot], oBot),
   ("⊢ ⊤", [], top)]

/-! ## Driver -/

/-- One saturation, calibrated, checked adversarially, then harvested. -/
def runGoal (label : String) (goal : F) (arity rounds cap : Nat)
    (known : List (String × List F × F))
    (harvest : List (String × F)) : IO Nat := do
  let cl := closureOf [goal]
  IO.println s!"== {label} =="
  IO.println s!"   closure {cl.length} formulas; atoms {atomsOf cl}"
  (← IO.getStdout).flush
  let store := saturate cl arity rounds cap
  IO.println s!"   saturation: {store.length} DISTINCT states; witnesses min {(store.map (·.wit.n)).foldl min 999} max {(store.map (·.wit.n)).foldl max 0} total {(store.map (·.wit.n)).sum} worlds"
  (← IO.getStdout).flush
  let mut hits := 0
  for (nm, Γ, C) in known do
    match refutesAt store Γ C with
    | some (i, w) =>
        hits := hits + 1
        IO.println s!"   CAL pass  {nm} — node {i}, world {w}"
    | none =>
        IO.println s!"   CAL FLAG  {nm} — not settled at this budget"
  IO.println s!"   CAL {hits}/{known.length}"
  let mut bad := 0
  for (nm, Γ, C) in derivableCorpus do
    match refutesAt store Γ C with
    | some (i, w) =>
        bad := bad + 1
        IO.println s!"   ADV FAIL (UNSOUND) {nm} — node {i}, world {w}"
    | none => pure ()
  IO.println s!"   ADV {vd (bad == 0)} ({derivableCorpus.length} derivable sequents, none certified)"
  let mut sep := 0
  let mut cells := 0
  for (n1, f1) in harvest do
    for (n2, f2) in harvest do
      if n1 != n2 then
        cells := cells + 1
        if (refutesAt store [f1] f2).isSome then sep := sep + 1
  IO.println s!"   HARVEST {sep}/{cells} ordered pairs separated ({sep} facts from {store.length} nodes, {(store.map (·.wit.n)).sum} worlds)"
  (← IO.getStdout).flush
  return sep

def pq : List (String × F) :=
  [("⊤", top), ("p", pv), ("q", qv), ("◯p", .somehow pv),
   ("p∨q", .or pv qv), ("p⊃q", .ifThen pv qv),
   ("(p⊃q)∨(q⊃p)", .or (.ifThen pv qv) (.ifThen qv pv)),
   ("◯(p∨q)", .somehow (.or pv qv)),
   ("◯p∨◯q", .or (.somehow pv) (.somehow qv))]

/-- The p,q covering goal — the same principle applied to a fragment
that HAS atoms. -/
def coveringGoalPQ : F := pq.foldl (fun acc p => .and acc p.2) top

def main : IO Unit := do
  IO.println "T3 SEARCHER — forward saturation over constructions, with sharing"
  IO.println "COVERAGE = CLOSURE: a saturation settles exactly what its"
  IO.println "covering goal's subformula closure reaches.  Two goals, to show it."
  IO.println ""
  let closedKnown : List (String × List F × F) :=
    [("⊬ ¬◯⊥", [], nOBot), ("⊬ ρ4 = ¬◯⊥ ∨ ◯⊥", [], q4),
     ("⊬ ρ6 = ¬¬◯⊥ ∨ ¬◯⊥", [], q7), ("⊬ ρ11 = g1", [], q8),
     ("⊬ ρ12 = r1", [], q14)]
  let s1 ← runGoal "GOAL 1 — the closed fragment (13 catalogue representatives)"
    coveringGoal 2 4 400 closedKnown reps
  IO.println ""
  let pqKnown : List (String × List F × F) :=
    [("⊬ ◯p", [], .somehow pv), ("⊬ ◯p ⊃ p", [], .ifThen (.somehow pv) pv),
     ("⊬ (p⊃q)∨(q⊃p)", [], .or (.ifThen pv qv) (.ifThen qv pv)),
     ("⊬ p ∨ ¬p", [], .or pv (.ifThen pv bot)),
     ("⊬ ◯(p∨q) ⊃ (◯p∨◯q)  [PCLL-only]", [],
       .ifThen (.somehow (.or pv qv)) (.or (.somehow pv) (.somehow qv)))]
  let s2 ← runGoal "GOAL 2 — a p,q covering goal (the SAME method, atoms present)"
    coveringGoalPQ 2 3 400 pqKnown pq
  IO.println ""
  IO.println s!"TOTAL harvested separations: {s1 + s2}"
  IO.println "T3-SEARCH-DONE"

end T3Search

def main : IO Unit := T3Search.main
