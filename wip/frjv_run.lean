/-
# Runner for the modular engine (`Ops`) — differential + the V-instance

  lake exe frjvrun diff    -- Core+paperOps ≟ legacy Engine.saturate, 8 goals
  lake exe frjvrun cells   -- V-instance (RefAt calculus) on witnesses #80/#81
-/
import FRJ.Search.Core
import FRJ.Search.OpsV
import FRJ.Bridge
import LaxLogic.RN.Rho

open FRJ FRJ.Search RhoOrder

namespace FRJVRun

def ppF : Form → String
  | .atom p => p
  | .bot => "⊥"
  | .and a b => s!"({ppF a} ∧ {ppF b})"
  | .or a b => s!"({ppF a} ∨ {ppF b})"
  | .imp a .bot => s!"¬{ppF a}"
  | .imp a b => s!"({ppF a} ⊃ {ppF b})"
  | .circ a => s!"◯{ppF a}"

def ppL (l : List Form) : String :=
  if l.isEmpty then "·" else String.intercalate ", " (l.map ppF)

def ppTag : Tag → String
  | .barren => "barren"
  | .chain D => s!"chain {ppF D}"
  | .blocked => "blocked"

def goal (i j : Nat) : Form := ofPLL (PLLFormula.ifThen (rhoF i) (rhoF j))

def cfg : Config := { rounds := 12, lamCap := 20, maxRS := 2000, maxIS := 2000 }

def sameSet (a b : List Form) : Bool := subB a b && subB b a

def p : Form := .atom "p"

def diffOne (nm : String) (G : Form) : IO Bool := do
  let (dbL, _) := saturate G cfg
  let (dbC, _) := saturateO (paperOps G) cfg
  -- both engines' rows, projected to (tag, ctx, rhs)
  let rowsL : List (Tag × List Form × Form) := dbL.rs.map (fun r => (r.t, r.ctx, r.rhs))
  let rowsC : List (Tag × List Form × Form) := dbC.rs.map (fun r => (r.t, r.ctx, r.rhs))
  let irowsL : List (List Form × List Form × Form) := dbL.is.map (fun i => (i.stab, i.th, i.rhs))
  let irowsC : List (List Form × List Form × Form) := dbC.is.map (fun i => (i.stab, i.th, i.rhs))
  let matchR : (Tag × List Form × Form) → List (Tag × List Form × Form) → Bool :=
    fun (t, c, r) l => l.any (fun (t', c', r') =>
      decide (t = t') && sameSet c c' && decide (r = r'))
  let matchI : (List Form × List Form × Form) → List (List Form × List Form × Form) → Bool :=
    fun (s, th, r) l => l.any (fun (s', th', r') =>
      sameSet s s' && sameSet th th' && decide (r = r'))
  let ok := rowsL.all (fun x => matchR x rowsC) && rowsC.all (fun x => matchR x rowsL)
    && irowsL.all (fun x => matchI x irowsC) && irowsC.all (fun x => matchI x irowsL)
  IO.println s!"{nm}: legacy RS={dbL.rs.length} IS={dbL.is.length}  core/paperOps RS={dbC.rs.length} IS={dbC.is.length}  {if ok then "AGREE" else "MISMATCH"}"
  return ok

def diffMain : IO Unit := do
  let cases : List (String × Form) :=
    [ ("rho12-9", goal 12 9), ("rho13-6", goal 13 6),
      ("unit", .imp p (.circ p)), ("mult", .imp (.circ (.circ p)) (.circ p)),
      ("notthm-circp-p", .imp (.circ p) p), ("notthm-negcircbot", .imp (.circ .bot) .bot),
      ("rho10-2", goal 10 2), ("rho8-4", goal 8 4) ]
  let mut allOK := true
  for (nm, G) in cases do
    allOK := allOK && (← diffOne nm G)
    (← IO.getStdout).flush
  IO.println (if allOK then "DIFF: ALL AGREE — the functor with paperOps is the legacy engine"
    else "DIFF: MISMATCH — fix the Core transcription")

def cellMain (i j : Nat) : IO Unit := do
  let G := goal i j
  let t0 ← IO.monoMsNow
  let (db, st) := saturateO (V.vOps G) cfg
  let t1 ← IO.monoMsNow
  IO.println s!"== V-ENGINE (typed RefAt calculus) on ρ{i}⊃ρ{j}  [{t1 - t0} ms]  r={st.roundsUsed} RS={st.rsSize} IS={st.isSize} lamCapped={st.lamCapped} dbCapped={st.dbCapped}"
  match db.rs.find? (fun r => decide (r.rhs = G)) with
  | some r =>
      IO.println s!"   HIT (an FRJVr derivation): [{ppTag r.t}] {ppL r.ctx} ⇒ {ppF r.rhs}"
  | none => IO.println "   no hit"
  IO.println "-- regular rows:"
  for r in db.rs do IO.println s!"    [{ppTag r.t}] {ppL r.ctx} ⇒ {ppF r.rhs}"

def main (args : List String) : IO Unit := do
  match args.head? with
  | some "diff" => diffMain
  | some "cells" => do cellMain 12 9; cellMain 13 6
  | some "cell" => cellMain (((args.getD 1 "12").toNat?).getD 12) (((args.getD 2 "9").toNat?).getD 9)
  | _ => IO.println "usage: … [diff|cells]"

end FRJVRun

def main (args : List String) : IO Unit := FRJVRun.main args
