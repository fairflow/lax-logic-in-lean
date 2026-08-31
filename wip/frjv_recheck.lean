import FRJ.Search.Core
import FRJ.Search.OpsV
import FRJ.Bridge
import LaxLogic.RN.Rho
open FRJ FRJ.Search RhoOrder

def goal (i j : Nat) : Form := ofPLL (PLLFormula.ifThen (rhoF i) (rhoF j))

def cells : List (Nat × Nat) :=
  [(12,18),(13,18),(19,18),(20,12),(20,13),(20,18)]

def main : IO Unit := do
  for (r, l) in [(12,20),(30,60)] do
    let c : Config := { rounds := r, lamCap := l, maxRS := 20000, maxIS := 20000 }
    IO.println s!"== rounds={r} lamCap={l} maxRS/IS=20000"
    for (i,j) in cells do
      let G := goal i j
      let t0 ← IO.monoMsNow
      let (db, st) := saturateO (V.vOps G) c
      let t1 ← IO.monoMsNow
      let hit := db.rs.any (fun rr => decide (rr.rhs = G))
      IO.println s!"  rho{i}->rho{j}: {if hit then "HIT" else "MISS"} {t1-t0}ms r={st.roundsUsed} RS={st.rsSize} IS={st.isSize} lamCapped={st.lamCapped} dbCapped={st.dbCapped}"
      (← IO.getStdout).flush
