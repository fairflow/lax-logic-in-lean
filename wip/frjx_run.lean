/-
# FRJX runner — differential check, the two cells, and the ρ-sweep

  lake env lean --run wip/frjx_run.lean diff    -- FRJX(patch=off) ≟ reference engine
  lake env lean --run wip/frjx_run.lean cells   -- patched engine on #80/#81, full dump
  lake env lean --run wip/frjx_run.lean sweep   -- patched engine on all 462 ρ-cells
-/
import wip.frjx
import LaxLogic.RN.Rho
import wip.two_sided
import RNDB.DB

open FRJ FRJX RhoOrder

namespace FRJXRun

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

def cfg : Search.Config := { rounds := 12, lamCap := 20, maxRS := 2000, maxIS := 2000 }

def sameSet (a b : List Form) : Bool := Search.subB a b && Search.subB b a

/-! ## diff: transcription check against the reference engine -/

def diffOne (nm : String) (G : Form) : IO Bool := do
  let (dbT, _) := Search.saturate G cfg
  let (dbX, _) := FRJX.saturate false G cfg
  let matchR : Search.RS G → Bool := fun r =>
    dbX.rs.any (fun x => decide (x.rhs = r.rhs) && decide (x.t = r.t) && sameSet x.ctx r.ctx)
  let matchRX : FRJX.R → Bool := fun x =>
    dbT.rs.any (fun r => decide (x.rhs = r.rhs) && decide (x.t = r.t) && sameSet x.ctx r.ctx)
  let matchI : Search.IS G → Bool := fun i =>
    dbX.is.any (fun x => decide (x.rhs = i.rhs) && sameSet x.stab i.stab && sameSet x.th i.th)
  let matchIX : FRJX.I → Bool := fun x =>
    dbT.is.any (fun i => decide (x.rhs = i.rhs) && sameSet x.stab i.stab && sameSet x.th i.th)
  let mR := dbT.rs.filter (fun r => !matchR r)
  let mRX := dbX.rs.filter (fun x => !matchRX x)
  let mI := dbT.is.filter (fun i => !matchI i)
  let mIX := dbX.is.filter (fun x => !matchIX x)
  let ok := mR.isEmpty && mRX.isEmpty && mI.isEmpty && mIX.isEmpty
  IO.println s!"{nm}: typed RS={dbT.rs.length} IS={dbT.is.length}  frjx RS={dbX.rs.length} IS={dbX.is.length}  {if ok then "AGREE" else "MISMATCH"}"
  unless mR.isEmpty do
    IO.println "  typed-only regular rows:"
    for r in mR.take 6 do IO.println s!"    [{ppTag r.t}] {ppL r.ctx} ⇒ {ppF r.rhs}"
  unless mRX.isEmpty do
    IO.println "  frjx-only regular rows:"
    for r in mRX.take 6 do IO.println s!"    [{ppTag r.t}] {ppL r.ctx} ⇒ {ppF r.rhs}"
  unless mI.isEmpty do
    IO.println "  typed-only irregular rows:"
    for i in mI.take 6 do IO.println s!"    {ppL i.stab} ; {ppL i.th} → {ppF i.rhs}"
  unless mIX.isEmpty do
    IO.println "  frjx-only irregular rows:"
    for i in mIX.take 6 do IO.println s!"    {ppL i.stab} ; {ppL i.th} → {ppF i.rhs}"
  return ok

def p : Form := .atom "p"
def q : Form := .atom "q"

def diffMain : IO Unit := do
  let cases : List (String × Form) :=
    [ ("rho12-9", goal 12 9), ("rho13-6", goal 13 6),
      ("unit", .imp p (.circ p)), ("mult", .imp (.circ (.circ p)) (.circ p)),
      ("notthm-circp-p", .imp (.circ p) p), ("notthm-negcircbot", .imp (.circ .bot) .bot),
      ("rho10-2", goal 10 2), ("rho8-4", goal 8 4) ]
  let mut allOK := true
  for (nm, G) in cases do
    let ok ← diffOne nm G
    allOK := allOK && ok
    (← IO.getStdout).flush
  IO.println (if allOK then "DIFF: ALL AGREE" else "DIFF: MISMATCHES — fix before trusting the patch runs")

/-! ## cells: the patched engine on the two witnesses -/

def cellMain (i j : Nat) : IO Unit := do
  let G := goal i j
  let t0 ← IO.monoMsNow
  let (db, st) := FRJX.saturate true G cfg
  let t1 ← IO.monoMsNow
  IO.println s!"== PATCHED FRJX on ρ{i}⊃ρ{j}  [{t1 - t0} ms]  r={st.roundsUsed} RS={st.rsSize} IS={st.isSize} lamCapped={st.lamCapped} dbCapped={st.dbCapped}"
  match db.rs.find? (fun r => decide (r.rhs = G)) with
  | some r => IO.println s!"   HIT: [{ppTag r.t}] {ppL r.ctx} ⇒ {ppF r.rhs}"
  | none => IO.println "   no hit"
  IO.println "-- regular rows:"
  for r in db.rs do IO.println s!"    [{ppTag r.t}] {ppL r.ctx} ⇒ {ppF r.rhs}"
  IO.println "-- irregular rows:"
  for r in db.is do IO.println s!"    {ppL r.stab} ; {ppL r.th} → {ppF r.rhs}"

/-! ## sweep: all 462 ρ-order cells, patched -/

section
open PLLND PLLND.RNC.CFX PLLFormula LJFO Rewrite TwoSidedLink

/-- Per-cell two-sided ground truth, copied verbatim from
`Tools/Cover.lean` `RhoCover.statusMat` (that module's `_root_.main`
collides with this runner's, so the 25 lines are inlined).  Two cells the
raw machinery leaves `none` are settled by banked kernel entries and
patched in afterwards: ρ20 ⊬ ρ10 (entry rho-0167) stays `some false`;
ρ12 ⊢? ρ15 stays genuinely open. -/
def statusMat (maxF : Nat) : IO (Array (Array (Option Bool))) := do
  let bat := battery ++ framesRooted5.toArray
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  let mut mat : Array (Array (Option Bool)) := #[]
  for i in [0:n] do
    let mut row : Array (Option Bool) := #[]
    for j in [0:n] do
      if i == j then
        row := row.push (some true)
      else
        let s : Option Bool :=
          match firstSep bat (vecs.getD i #[]) (vecs.getD j #[]) with
          | some _ => some false
          | none =>
              if provedAt 20000 [rhoF i] (rhoF j) then some true
              else if provedAt 100000 [rhoF i] (rhoF j) then some true
              else if (TwoSided.fuelLadder maxF).any
                       (fun f => searchProves f [rhoF i] (rhoF j)) then some true
              else none
        row := row.push s
    mat := mat.push row
  -- the DB overlay of 2026-08-25: ρ20 ⊬ ρ10 is kernel-banked
  mat := mat.modify 20 (fun r => r.set! 10 (some false))
  return mat

end

def sweepMain : IO Unit := do
  IO.println "computing the two-sided ground truth (battery + G4c + LJF◯ ladder)…"
  (← IO.getStdout).flush
  let mat ← statusMat 48
  let stat : Nat → Nat → Option Bool := fun i j => (mat.getD i #[]).getD j none
  let mut alarms := 0
  let mut hitsRef := 0
  let mut hitsOpen := 0
  let mut missRef := 0
  for i in List.range 22 do
    for j in List.range 22 do
      if i ≠ j then
        let G := goal i j
        let t0 ← IO.monoMsNow
        let (db, st) := FRJX.saturate true G cfg
        let t1 ← IO.monoMsNow
        let hit := FRJX.derivable G db
        let truth := match stat i j with
          | some true => "⊢"
          | some false => "⊬"
          | none => "open"
        let mark := match hit, stat i j with
          | true, some true => "*** ALARM: HIT on a PROVED cell — patch UNSOUND ***"
          | true, some false => "ok (refutable, found)"
          | true, none => "HIT on the open cell"
          | false, some false => "miss (refutable, not found)"
          | _, _ => ""
        match hit, stat i j with
        | true, some true => alarms := alarms + 1
        | true, some false => hitsRef := hitsRef + 1
        | true, none => hitsOpen := hitsOpen + 1
        | false, some false => missRef := missRef + 1
        | _, _ => pure ()
        IO.println s!"rho {i} {j}\t{if hit then "HIT" else "none"}\ttruth={truth}\t{t1 - t0}ms\tr={st.roundsUsed} RS={st.rsSize} IS={st.isSize}{if st.dbCapped then " DBCAP" else ""}{if st.lamCapped then " LAMCAP" else ""}\t{mark}"
        (← IO.getStdout).flush
  IO.println s!"-- SWEEP SUMMARY: ALARMS={alarms}  refutable-found={hitsRef}  refutable-missed={missRef}  open-hit={hitsOpen}"

/-- Raised-budget single cell, all caps settable and all cap flags
printed — the re-run tool for sweep misses (`none_at` discipline: a miss
re-runs at a raised budget, and a run is only evidence of anything if no
cap was binding). -/
def cellAtMain (i j rounds lam jm pm : Nat) : IO Unit := do
  let c : Search.Config := { rounds := rounds, lamCap := lam, maxRS := 8000, maxIS := 8000,
                             jmax := jm, pmax := pm }
  let G := goal i j
  let t0 ← IO.monoMsNow
  let (db, st) := FRJX.saturate true G c
  let t1 ← IO.monoMsNow
  let hit := db.rs.any (fun r => decide (r.rhs = G))
  IO.println s!"XCELL {i} {j} {if hit then "HIT" else "MISS"} {t1 - t0}ms rounds={rounds} lamCap={lam} jmax={jm} pmax={pm} r={st.roundsUsed} RS={st.rsSize} IS={st.isSize} lamCapped={st.lamCapped} dbCapped={st.dbCapped} jmaxBinding={st.jmaxBinding} pmaxBinding={st.pmaxBinding}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  match args.head? with
  | some "diff" => diffMain
  | some "cells" => do cellMain 12 9; cellMain 13 6
  | some "cell" => cellMain (((args.getD 1 "12").toNat?).getD 12) (((args.getD 2 "9").toNat?).getD 9)
  | some "cellat" =>
      cellAtMain (((args.getD 1 "12").toNat?).getD 12) (((args.getD 2 "18").toNat?).getD 18)
                 (((args.getD 3 "16").toNat?).getD 16) (((args.getD 4 "20").toNat?).getD 20)
                 (((args.getD 5 "4").toNat?).getD 4) (((args.getD 6 "3").toNat?).getD 3)
  | some "sweep" => sweepMain
  | _ => IO.println "usage: … [diff|cells|cell i j|cellat i j rounds lamCap jmax pmax|sweep]"

end FRJXRun

def main (args : List String) : IO Unit := FRJXRun.main args
