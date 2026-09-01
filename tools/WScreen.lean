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

end WScreen

def main : List String → IO UInt32
  | ["rho"] => WScreen.rhoMain
  | _ => WScreen.main
