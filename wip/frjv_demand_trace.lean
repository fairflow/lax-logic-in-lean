/-
# Demand tracer for the V-visit (2026-08-26, FRJV completeness campaign)

Simulates the demand graph of the (revised, visitG-shaped) completeness
construction on a concrete countermodel: FREE root, tagged tier entered
only under `◯`, pledges only at tagged prime/∨ demands at circ-carrying
worlds.  V-routing throughout: the ∨-join disjunct conditions are RefAt,
so their row demands are the RefAt-descent LEAVES; `axIC` serves
`I(◯Z)` at any world whose `Λ*` is classically satisfiable with `Z`
refuted (not corner-only).  Event kinds:

* `PLEDGE a C` — a tagged prime/∨ demand at circ-carrying `a`; checked
  against the Lemma A′ witness question;
* `CORNER a Z` — a CircSupply corner where `axIC` also fails;
* `FLOAT e B` — a tagged `⊃`-float into a non-anchor world.

Choice policy: ALL minimal candidates are traced (a safe
over-approximation of the construction's freedom).  Each demand carries
its provenance; `log` prints the demand graph.

## Findings (2026-08-26 run)

V-routing collapses the demand graph: frame 9900 (both cells) and
(20,13) trace CLEAN — no pledge, corner, or float events at all.  The
residual bad path, on sepM (all three cells) and (20,12):

    I(◯⊥)@1:  Λ*₁ = {ρ12, δ} with cl(δ) = false blocks axIC;
    not a corner; minRef escalates to tagged ⊥@2 = the dead pledge.

The kernel witness (FRJ/WitnessV.lean, R2/R4) serves this same demand
with an axIC row INSIDE the join: legitimate because the join needs
only pairwise hJ1 (the sibling stab {ν} is classically true), NOT the
visit's blanket Λ*-coverage invariant (IrrWit.cov/MRWit.cov).  The
visit OVER-DEMANDS; the completeness construction must run on WEAKENED
wit invariants reverse-engineered from the witness pattern (axIC rows
in joins + classically-true stab discipline + impNotIn floats).
-/
import FRJ.Search.Pin
import FRJ.Bridge
import FRJ.Complete
import FRJ.Minimal
import LaxLogic.RN.Rho

open FRJ FRJ.Search RhoOrder

namespace FRJVDemandTrace

def ppF : Form → String
  | .atom p => p
  | .bot => "F"
  | .and a b => s!"({ppF a}&{ppF b})"
  | .or a b => s!"({ppF a}|{ppF b})"
  | .imp a .bot => s!"~{ppF a}"
  | .imp a b => s!"({ppF a}>{ppF b})"
  | .circ a => s!"O{ppF a}"

inductive Ev where
  | pledge (a : Nat) (C : Form) (witOk : Bool) (why : String)
  | corner (a : Nat) (Z : Form) (why : String)
  | float (e : Nat) (B : Form) (why : String)
deriving Repr, BEq

def ppEv : Ev → String
  | .pledge a C ok why => s!"PLEDGE  a={a} C={ppF C} witness={ok}  <- {why}"
  | .corner a Z why => s!"CORNER(axIC-blocked)  a={a} Z={ppF Z}  <- {why}"
  | .float e B why => s!"FLOAT   e={e} B={ppF B}  <- {why}"

structure St where
  memo : List (Nat × Nat × Form) := []
  evs : List Ev := []
  log : List String := []

/-- The tracer, fuel-bounded.  Tiers: 0 = irregular, 1 = tagged, 2 = free. -/
partial def trace (T : Tab) (G : Form) : St := Id.run do
  match h : T.okB, hr : decide (T.root < T.n) with
  | true, true =>
    let K := T.toKripke h (of_decide_eq_true hr)
    let idxOf : K.W → Nat := fun w =>
      (K.elems.findIdx? (fun x => decide (x = w))).getD 999
    let lam := fun (a : K.W) => lamStar K a G
    let circCarrying := fun (a : K.W) => decide (circPart (lam a) ≠ [])
    let bodies := fun (a : K.W) => (circPart (lam a)).filterMap
      (fun X => match X with | .circ Y => some Y | _ => none)
    let infall := fun (u : K.W) => !(decide (K.Fal u))
    let force := fun (u : K.W) (X : Form) => decide (K.force u X)
    let witA' := fun (a : K.W) (C : Form) => K.elems.any (fun u =>
      decide (K.Rm a u) && infall u && (bodies a).all (force u) && !(force u C))
    let axicOk := fun (Z : Form) (a : K.W) =>
      (lam a).all (fun X => classForce [] X) && !(classForce [] Z)
    let minimals := fun (base : K.W) (p : K.W → Bool) =>
      let cands := K.elems.filter (fun e => decide (K.le base e) && p e)
      cands.filter (fun e => cands.all (fun e' =>
        !(decide (K.le e' e)) || decide (e' = e)))
    let rec leaves (a : K.W) (X : Form) (fu : Nat) : List Form :=
      match fu with
      | 0 => [X]
      | fu + 1 =>
        match X with
        | .bot => []
        | .imp A B => if force a A && !(force a B) then leaves a B fu else [X]
        | .circ Z => if !(force a Z) then leaves a Z fu else [X]
        | .or C1 C2 =>
            if !(force a C1) && !(force a C2) then
              leaves a C1 fu ++ leaves a C2 fu else [X]
        | .and C1 C2 =>
            if !(force a C1) then leaves a C1 fu
            else if !(force a C2) then leaves a C2 fu else [X]
        | _ => [X]
    let mut st : St := {}
    let mut work : List (K.W × Nat × Form × String) := [(K.root, 2, G, "root")]
    let mut fuel := 4000
    while fuel > 0 do
      fuel := fuel - 1
      match work with
      | [] => break
      | (a, t, C, why) :: rest =>
        work := rest
        let key := (idxOf a, t, C)
        if st.memo.contains key then continue
        st := { st with memo := key :: st.memo }
        if force a C then continue
        st := { st with log := s!"({idxOf a},{t},{ppF C}) <- {why}" :: st.log }
        let me := s!"({idxOf a},{t},{ppF C})"
        match t, C with
        | 0, .atom _ | 0, .bot => pure ()
        | 0, .and C1 C2 =>
            if !(force a C1) then work := (a, 0, C1, me) :: work
            else work := (a, 0, C2, me) :: work
        | 0, .or C1 C2 =>
            work := (a, 0, C1, me) :: (a, 0, C2, me) :: work
        | 0, .imp A B =>
            for e in minimals a (fun e => force e A && !(force e B)) do
              if decide (e = a) then work := (a, 0, B, me) :: work
              else work := (e, 2, B, me) :: work
        | 0, .circ Z =>
            if axicOk Z a then pure ()
            else
              let cornerHyp := K.elems.all (fun u =>
                !(decide (K.le a u)) || decide (u = a) || force u Z)
              if cornerHyp then
                st := { st with evs := .corner (idxOf a) Z why :: st.evs }
              else
                for e in minimals a (fun e => !(decide (e = a)) && !(force e Z)) do
                  work := (e, 1, Z, me) :: work
        | 1, .atom _ | 1, .bot =>
            if circCarrying a then
              st := { st with evs := .pledge (idxOf a) C (witA' a C) why :: st.evs }
              for u in K.elems.filter (fun u => decide (K.Rm a u) && infall u &&
                  (bodies a).all (force u) && !(force u C)) do
                work := (u, 1, C, me) :: work
            for A in (upsPrime K a G) do work := (a, 0, A, me) :: work
        | 1, .and C1 C2 =>
            if !(force a C1) then work := (a, 1, C1, me) :: work
            else work := (a, 1, C2, me) :: work
        | 1, .or C1 C2 =>
            if circCarrying a then
              st := { st with evs := .pledge (idxOf a) C (witA' a C) why :: st.evs }
              for u in K.elems.filter (fun u => decide (K.Rm a u) && infall u &&
                  (bodies a).all (force u) && !(force u C)) do
                work := (u, 1, C, me) :: work
            for L in (leaves a C1 12 ++ leaves a C2 12) do
              work := (a, 0, L, me) :: work
            for A in (upsPrime K a G) do work := (a, 0, A, me) :: work
        | 1, .imp A B =>
            for e in minimals a (fun e => force e A && !(force e B)) do
              if decide (e = a) then work := (a, 1, B, me) :: work
              else
                st := { st with evs := .float (idxOf e) B me :: st.evs }
                work := (e, 1, B, me) :: work
        | 1, .circ Z =>
            for b in minimals a (fun b => K.elems.all (fun c =>
                !(decide (K.Rm b c)) || !(force c Z))) do
              work := (b, 1, Z, me) :: work
        | _, .atom _ | _, .bot => pure ()
        | n+2, .and C1 C2 =>
            if !(force a C1) then work := (a, n+2, C1, me) :: work
            else work := (a, n+2, C2, me) :: work
        | _+2, .or C1 C2 =>
            for L in (leaves a C1 12 ++ leaves a C2 12) do
              work := (a, 0, L, me) :: work
            for A in (upsPrime K a G) do work := (a, 0, A, me) :: work
        | n+2, .imp A B =>
            for e in minimals a (fun e => force e A && !(force e B)) do
              work := (e, n+2, B, me) :: work
        | _+2, .circ Z =>
            work := (a, 1, .circ Z, me) :: work
    return st
  | _, _ => return {}

def mkTab (n root : Nat) (leT rmT : List (List Bool)) (falT : List Bool) : Tab :=
  { n := n, root := root, leT := leT, rmT := rmT, falT := falT,
    atomsT := List.replicate n [] }

def sepM : Tab := mkTab 5 0
  [[true,true,true,true,true],[false,true,true,true,false],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,false,true]]
  [[true,false,false,false,false],[false,true,false,false,false],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,false,true]]
  [false,false,false,true,false]

def fr9900 : Tab := mkTab 5 0
  [[true,true,true,true,true],[false,true,true,true,true],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,true,true]]
  [[true,false,false,false,false],[false,true,true,false,false],[false,false,true,false,false],
   [false,false,false,true,false],[false,false,false,true,true]]
  [false,false,false,true,false]

def fr2012 : Tab := mkTab 5 0
  [[true,true,true,true,true],[false,true,true,true,true],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,false,true]]
  [[true,false,false,false,false],[false,true,false,false,true],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,false,true]]
  [false,false,false,true,false]

def goalF (i j : Nat) : Form := ofPLL (PLLFormula.ifThen (rhoF i) (rhoF j))

#eval show IO Unit from do
  let cells : List (String × Tab × Form) :=
    [ ("sepM/G80", sepM, goalF 12 9), ("sepM/(12,18)", sepM, goalF 12 18),
      ("sepM/(13,18)", sepM, goalF 13 18),
      ("9900/(19,18)", fr9900, goalF 19 18), ("9900/(20,18)", fr9900, goalF 20 18),
      ("2012/(20,12)", fr2012, goalF 20 12), ("2012/(20,13)", fr2012, goalF 20 13) ]
  for (nm, T, G) in cells do
    IO.println s!"{nm}:"
    let s := trace T G
    let evs := s.evs.eraseDups
    if evs.isEmpty then IO.println "    (no pledge/corner/float events)"
    for e in evs do IO.println s!"    {ppEv e}"

/-- Full demand-graph dump for one cell (provenance per demand). -/
def dump (T : Tab) (G : Form) : IO Unit := do
  for l in (trace T G).log.reverse do IO.println l

#eval dump sepM (goalF 12 9)

end FRJVDemandTrace

namespace FRJVDemandTrace

def lamdump (T : Tab) (G : Form) : List String := Id.run do
  match h : T.okB, hr : decide (T.root < T.n) with
  | true, true =>
    let K := T.toKripke h (of_decide_eq_true hr)
    let mut out : List String := []
    let mut i := 0
    for a in K.elems do
      let l := lamStar K a G
      out := s!"world {i}: lam = {l.map ppF}  cl = {l.map (fun X => classForce [] X)}" :: out
      i := i + 1
    return out.reverse
  | _, _ => return ["bad tab"]

#eval lamdump sepM (goalF 12 9)

end FRJVDemandTrace
