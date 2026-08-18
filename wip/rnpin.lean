/-
# Turning a search hit into a pinned countermodel

`lake exe rnpin <cell> <dir>` runs the fast FRJ(◯) search on one direction
of one RN(◯,{}) dictionary cell, and, if it finds a derivation, extracts the
model the derivation builds, minimises it, and prints it as Lean source
together with the statement to paste.

The emitted certificate does not mention the search: it is a finite table,
a frame check (`Tab.okB`, `decide`), and a refutation
(`FRJ.not_entails_of_countermodel`).  That is the discover-then-pin
discipline — discovery untrusted, the result kernel-checked.
-/
import FRJ.Search.Fast
import FRJ.Search.Pin
import wip.rnBank

open FRJ

namespace RNPin

def hitModel (G : Form) (cfg : Search.Config) : Option Kripke :=
  let (db, _) := Search.saturateFast G cfg
  (db.rs.find? (fun r => decide (r.rhs = G))).map (fun r => modR r.der)

def run (cellName dir : String) (cfg : Search.Config) : IO Unit := do
  match RNBank.cells.find? (fun c => c.name == cellName) with
  | none => IO.println s!"no such cell: {cellName}"
  | some c =>
    let φ : PLLFormula :=
      if dir == "→" || dir == "fwd" then .ifThen c.lhs c.rhs else .ifThen c.rhs c.lhs
    let G := ofPLL φ
    IO.println s!"cell {c.name} [{c.status.toString}] direction {dir}"
    let t0 ← IO.monoMsNow
    match hitModel G cfg with
    | none => IO.println "no derivation at this budget — nothing to pin"
    | some K =>
      let t1 ← IO.monoMsNow
      let T := Search.tabOf K (Search.atomsOf G)
      IO.println s!"search {t1 - t0}ms; extracted model: {T.n} worlds, frame-ok={T.okB}, refutes={T.refutes G}"
      let M := T.minimise G
      let t2 ← IO.monoMsNow
      IO.println s!"minimised to {M.n} worlds ({t2 - t1}ms), frame-ok={M.okB}, refutes={M.refutes G}"
      IO.println "-- BEGIN CERTIFICATE --"
      IO.println (Search.render M ("cm_" ++ c.name ++ (if dir == "→" then "_fwd" else "_bwd")))
      IO.println "-- END CERTIFICATE --"
    (← IO.getStdout).flush

end RNPin

def main (args : List String) : IO Unit := do
  let cell := args.getD 0 "cAnd_10_13"
  let dir := args.getD 1 "←"
  let rounds := ((args.getD 2 "10").toNat?).getD 10
  RNPin.run cell dir { rounds := rounds }
