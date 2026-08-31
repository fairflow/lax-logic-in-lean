import FRJ.Search.Core
import FRJ.Search.OpsV
import FRJ.Bridge
import LaxLogic.RN.Rho
open FRJ FRJ.Search RhoOrder

def goal (i j : Nat) : Form := ofPLL (PLLFormula.ifThen (rhoF i) (rhoF j))

def cells : List (Nat × Nat) := [(12,18)]

def main : IO Unit := do
  for (jm, pm) in [(3,2),(4,2),(4,3),(5,3)] do
    let c : Config := { rounds := 12, jmax := jm, pmax := pm,
                        lamCap := 20, maxRS := 20000, maxIS := 20000 }
    IO.println s!"== jmax={jm} pmax={pm}"
    for (i,j) in cells do
      let G := goal i j
      let t0 ← IO.monoMsNow
      let (db, st) := saturateO (V.vOps G) c
      let t1 ← IO.monoMsNow
      let hit := db.rs.any (fun rr => decide (rr.rhs = G))
      IO.println s!"  rho{i}->rho{j}: {if hit then "HIT" else "MISS"} {t1-t0}ms r={st.roundsUsed} RS={st.rsSize} IS={st.isSize} lamCapped={st.lamCapped} dbCapped={st.dbCapped} jmaxBinding={st.jmaxBinding} pmaxBinding={st.pmaxBinding}"
      (← IO.getStdout).flush
