/-
# `wscreen` — the dichotomy screening runner

Per cell (a named `PLLFormula`), runs the FRJW engine (`wOps`
saturation) beside the G4c certificate oracle (`PLLND.Search.settle`)
and prints one line: cell, oracle verdict, W-engine hit, root
irregular coverage, budget flags, verdict.

Verdicts (three-valued, per the testing discipline):
* `PASS`  — oracle-invalid ∧ W-hit (the dichotomy's W-side delivered),
            or oracle-valid ∧ no hit (control).
* `FLAG`  — oracle-invalid ∧ no hit at this budget (candidate
            counterexample to reachable saturation: RE-RUN at a raised
            budget, never drop), or oracle unknown.
* `ALARM` — oracle-valid ∧ W-hit.  A hit carries an `FRJWr` derivation
            and `soundnessW` refutes validity, so an alarm means a bug
            in the oracle or the engine registration — escalate to
            kernel level immediately.

No silent caps: the engine's `Stats` flags are printed per cell.
-/
import FRJ.Search.OpsW
import FRJ.Bridge
import LaxLogic.RN.Rho
import LaxLogic.PLLSearch
import wip.ljfo_link

open FRJ FRJ.Search Form

namespace WScreen

abbrev P := PLLFormula

def p : P := .prop "p"
def q : P := .prop "q"
def r : P := .prop "r"
def z : P := .prop "z"

def cells : List (String × P) := [
  -- valid controls (expect NO hit)
  ("p ⊃ p            [valid]", .ifThen p p),
  ("⊥ ⊃ ⊥            [valid]", .ifThen .falsePLL .falsePLL),
  ("p ⊃ ◯p           [valid]", .ifThen p (.somehow p)),
  ("◯◯p ⊃ ◯p         [valid]", .ifThen (.somehow (.somehow p)) (.somehow p)),
  ("◯p ⊃ ◯◯p         [valid]", .ifThen (.somehow p) (.somehow (.somehow p))),
  ("(◯p∧◯q) ⊃ ◯(p∧q) [valid]", .ifThen ((PLLFormula.somehow p).and (.somehow q))
      (.somehow (p.and q))),
  ("licence cell w    [valid]", .ifThen (.somehow ((PLLFormula.ifThen (.somehow p) r).and
      (.somehow p))) ((PLLFormula.somehow r).or z)),
  -- invalid cells (expect a W-hit: the dichotomy's disproof side)
  ("p                 [inv]", p),
  ("⊥                 [inv]", .falsePLL),
  ("◯⊥                [inv]", .somehow .falsePLL),
  ("¬◯⊥               [inv]", .ifThen (.somehow .falsePLL) .falsePLL),
  ("◯p ⊃ p   (Gcr)    [inv]", .ifThen (.somehow p) p),
  ("◯(◯p ⊃ p) (Gcc)   [inv]", .somehow (.ifThen (.somehow p) p)),
  ("◯(p∨q) ⊃ ◯p∨◯q    [inv]", .ifThen (.somehow (p.or q))
      ((PLLFormula.somehow p).or (.somehow q))),
  ("big-ante variant  [inv]", .ifThen (.somehow ((PLLFormula.ifThen (.somehow p) q).and
      (.somehow p))) (.somehow r)),
  ("p ∨ ¬p            [inv]", p.or (.ifThen p .falsePLL)),
  ("Peirce            [inv]", .ifThen (.ifThen (.ifThen p q) p) p),
  ("◯p ∨ ¬◯p          [inv]", (PLLFormula.somehow p).or (.ifThen (.somehow p) .falsePLL))
]

def engineCfg : Config := { rounds := 16, lamCap := 24, maxRS := 3000, maxIS := 3000 }

def oracle (φ : P) : String :=
  match PLLND.Search.settle {} [] φ with
  | .proved _ => "valid"
  | .refuted _ _ _ => "invalid"
  | .unknown => "unknown"

def flags (st : Stats) : String :=
  let l := [(st.lamCapped, "lamCap"), (st.dbCapped, "dbCap"),
            (st.jmaxBinding, "jmax"), (st.pmaxBinding, "pmax")]
  match (l.filter (·.1)).map (·.2) with
  | [] => "-"
  | fs => String.intercalate "," fs

def runCell (nm : String) (φ : P) : IO Bool := do
  let G := ofPLL φ
  let (db, st) := saturateO (W.wOps G) engineCfg
  let hit := db.rs.any (fun rr => decide (rr.rhs = G))
  let rootIrr := db.is.any (fun i => decide (i.rhs = G))
  let ov := oracle φ
  let verdict :=
    match ov, hit with
    | "valid", true => "ALARM"
    | "valid", false => "PASS"
    | "invalid", true => "PASS"
    | "invalid", false => "FLAG"
    | _, _ => "FLAG(oracle)"
  IO.println s!"{verdict.take 5}  {nm}  oracle={ov}  wHit={hit}  rootIrr={rootIrr}  rs={db.rs.length} is={db.is.length} rounds={st.roundsUsed} caps={flags st}"
  pure (verdict == "ALARM")

def main : IO UInt32 := do
  IO.println s!"wscreen: {cells.length} cells, engine cfg rounds={engineCfg.rounds} lamCap={engineCfg.lamCap}"
  let mut alarms := 0
  for (nm, φ) in cells do
    if (← runCell nm φ) then alarms := alarms + 1
  if alarms > 0 then
    IO.println s!"{alarms} ALARM(S) — escalate to kernel level"
    pure 1
  else
    IO.println "no alarms"
    pure 0

/-- The ρ-corpus stratum: all 462 directed cells `ρi ⊃ ρj`, W-engine
beside the G4c oracle.  Heavier than the curated set — run in the
background and read the tail. -/
def rhoMain : IO UInt32 := do
  IO.println s!"wscreen rho: 462 directed ρ-cells, engine cfg rounds={engineCfg.rounds} lamCap={engineCfg.lamCap}"
  let mut alarms := 0
  for i in List.range 22 do
    for j in List.range 22 do
      if i ≠ j then
        let φ : P := .ifThen (RhoOrder.rhoF i) (RhoOrder.rhoF j)
        let bad ← runCell s!"ρ{i} ⊃ ρ{j}" φ
        if bad then alarms := alarms + 1
  IO.println s!"done; alarms={alarms} (PASS/FLAG counts in the lines above)"
  pure (if alarms > 0 then 1 else 0)

/-! ## The semi-naive differential (`snd`)

`Config.semiNaive` must reach the SAME FIXPOINT.  Per cell this runs the
W-engine twice, flag off and flag on, and compares the two stores under
three notions, weakest last:

* `EXACT`  — the two row lists agree ELEMENTWISE on the projections
  `(tag, ctx, rhs)` and `(stab, th, rhs)`, zones compared as lists:
  same rows, same order.
* `PERM`   — the same rows, zones still compared as LISTS, matched in
  both directions with equal lengths: same rows, different order.
* `SET`    — matched only up to SET-equality of the zones.  This is the
  equivalence the store dedupes by (`rsLeO`/`isLeO` both ways), so a
  `SET` line means the two runs kept different representatives of a
  mutual-subsumption class — allowed, since the class is the same.

A `DIFFER` line is a failure of the fixpoint claim: it prints both
sizes, and the runner exits 1. -/

def projR {G : Form} (db : DBO (W.wOps G)) : List (Tag × List Form × Form) :=
  db.rs.map (fun r => (r.t, r.ctx, r.rhs))

def projI {G : Form} (db : DBO (W.wOps G)) : List (List Form × List Form × Form) :=
  db.is.map (fun i => (i.stab, i.th, i.rhs))

def sameSet (a b : List Form) : Bool := subB a b && subB b a

def matchR (x : Tag × List Form × Form) (l : List (Tag × List Form × Form)) : Bool :=
  l.any (fun y => decide (x.1 = y.1) && sameSet x.2.1 y.2.1 && decide (x.2.2 = y.2.2))

def matchI (x : List Form × List Form × Form) (l : List (List Form × List Form × Form)) :
    Bool :=
  l.any (fun y => sameSet x.1 y.1 && sameSet x.2.1 y.2.1 && decide (x.2.2 = y.2.2))

/-- Returns `true` on a DIFFERING store. -/
def sndCellCfg (cfg : Config) (nm : String) (φ : P) : IO Bool := do
  let G := ofPLL φ
  let t0 ← IO.monoMsNow
  let (dbA, stA) := saturateO (W.wOps G) cfg
  let t1 ← IO.monoMsNow
  let (dbB, stB) := saturateO (W.wOps G) { cfg with semiNaive := true }
  let t2 ← IO.monoMsNow
  let rA := projR dbA; let rB := projR dbB
  let iA := projI dbA; let iB := projI dbB
  let exact := decide (rA = rB) && decide (iA = iB)
  let perm :=
    rA.all (fun x => rB.any (fun y => decide (x = y)))
      && rB.all (fun x => rA.any (fun y => decide (x = y)))
      && iA.all (fun x => iB.any (fun y => decide (x = y)))
      && iB.all (fun x => iA.any (fun y => decide (x = y)))
      && decide (rA.length = rB.length) && decide (iA.length = iB.length)
  let setEq :=
    rA.all (fun x => matchR x rB) && rB.all (fun x => matchR x rA)
      && iA.all (fun x => matchI x iB) && iB.all (fun x => matchI x iA)
      && decide (rA.length = rB.length) && decide (iA.length = iB.length)
  let hitA := dbA.rs.any (fun rr => decide (rr.rhs = G))
  let hitB := dbB.rs.any (fun rr => decide (rr.rhs = G))
  let verdict :=
    if !setEq || hitA != hitB then "DIFFER"
    else if exact then "EXACT " else if perm then "PERM  " else "SET   "
  IO.println s!"{verdict}  {nm}  naive rs={dbA.rs.length} is={dbA.is.length} \
r={stA.roundsUsed} [{t1 - t0}ms]  semi rs={dbB.rs.length} is={dbB.is.length} \
r={stB.roundsUsed} [{t2 - t1}ms]  hit={hitA}/{hitB} caps={flags stA}/{flags stB}"
  pure (verdict == "DIFFER")

def sndCell (nm : String) (φ : P) : IO Bool := sndCellCfg engineCfg nm φ

/-! The two cells `docs/engine-profile.md` measures, at the profile's own
budget and at the raised one, ENGINE TIME ONLY — `lake exe pll` also
pays `checkClosed` and the decision extraction, which dominate it. -/

def profA : P := .ifThen ((PLLFormula.somehow (.somehow p)).and (.somehow q))
  (.somehow ((PLLFormula.somehow p).and q))

def profB : P := .ifThen (.somehow ((PLLFormula.somehow p).or (.somehow q)))
  ((PLLFormula.somehow p).or (.somehow q))

def profMain : IO UInt32 := do
  let budgets : List (String × Config) :=
    [ ("rounds=16 jmax=3 pmax=2 (profile)",
        { rounds := 16, jmax := 3, pmax := 2, lamCap := 24, maxRS := 3000, maxIS := 3000 }),
      ("rounds=40 jmax=5 pmax=4 (raised)",
        { rounds := 40, jmax := 5, pmax := 4, lamCap := 24, maxRS := 3000, maxIS := 3000 }) ]
  let mut bad := 0
  for (bn, c) in budgets do
    IO.println s!"-- {bn}"
    if ← sndCellCfg c "(◯◯p ∧ ◯q) ⊃ ◯(◯p ∧ q)" profA then bad := bad + 1
    (← IO.getStdout).flush
    if ← sndCellCfg c "◯(◯p ∨ ◯q) ⊃ (◯p ∨ ◯q)" profB then bad := bad + 1
    (← IO.getStdout).flush
  IO.println s!"prof: differing cells = {bad} / 4"
  pure (if bad > 0 then 1 else 0)

def sndMain : IO UInt32 := do
  IO.println s!"wscreen snd: {cells.length} cells, naive vs semiNaive stores"
  let mut bad := 0
  for (nm, φ) in cells do
    if ← sndCell nm φ then bad := bad + 1
  IO.println s!"snd: differing cells = {bad} / {cells.length}"
  pure (if bad > 0 then 1 else 0)

/-- The same comparison over the 462 directed ρ-cells.  The budget is an
argument because the sweep at `engineCfg` is hours long: single cells
there cost minutes (`ρ1 ⊃ ρ17`: 82 s naive, 29 s semi). -/
def sndRhoMain (cfg : Config) : IO UInt32 := do
  IO.println s!"wscreen snd-rho: 462 directed ρ-cells, naive vs semiNaive stores \
(rounds={cfg.rounds} jmax={cfg.jmax} pmax={cfg.pmax} lamCap={cfg.lamCap})"
  let mut bad := 0
  for i in List.range 22 do
    for j in List.range 22 do
      if i ≠ j then
        let φ : P := .ifThen (RhoOrder.rhoF i) (RhoOrder.rhoF j)
        if ← sndCellCfg cfg s!"ρ{i} ⊃ ρ{j}" φ then bad := bad + 1
        (← IO.getStdout).flush
  IO.println s!"snd-rho: differing cells = {bad} / 462"
  pure (if bad > 0 then 1 else 0)

/-- `wscreen semi`: the 18-cell screen with `semiNaive := true`. -/
def semiMain : IO UInt32 := do
  IO.println s!"wscreen (semiNaive): {cells.length} cells"
  let mut alarms := 0
  for (nm, φ) in cells do
    let G := ofPLL φ
    let (db, st) := saturateO (W.wOps G) { engineCfg with semiNaive := true }
    let hit := db.rs.any (fun rr => decide (rr.rhs = G))
    let ov := oracle φ
    let verdict :=
      match ov, hit with
      | "valid", true => "ALARM"
      | "valid", false => "PASS"
      | "invalid", true => "PASS"
      | "invalid", false => "FLAG"
      | _, _ => "FLAG(oracle)"
    IO.println s!"{verdict.take 5}  {nm}  oracle={ov}  wHit={hit}  rs={db.rs.length} \
is={db.is.length} rounds={st.roundsUsed} caps={flags st}"
    if verdict == "ALARM" then alarms := alarms + 1
  IO.println (if alarms > 0 then s!"{alarms} ALARM(S)" else "no alarms")
  pure (if alarms > 0 then 1 else 0)

end WScreen

def main : List String → IO UInt32
  | ["rho"] => WScreen.rhoMain
  | ["snd"] => WScreen.sndMain
  | ["prof"] => WScreen.profMain
  | "snd-rho" :: rest =>
      let n := fun (k : Nat) (d : Nat) => ((rest.getD k "").toNat?).getD d
      WScreen.sndRhoMain { WScreen.engineCfg with
        rounds := n 0 WScreen.engineCfg.rounds,
        jmax := n 1 WScreen.engineCfg.jmax,
        pmax := n 2 WScreen.engineCfg.pmax }
  | ["semi"] => WScreen.semiMain
  | _ => WScreen.main
