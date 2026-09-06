import wip.ui_routeB_r_cells
import Rewrite
import LJF.OBridge
set_option autoImplicit false
open LJFO
def v1 : List Neg := [.imp (.down (.circ (.atom "p"))) (.up (.atom "r")), .circ (.atom "q")]
def v2 : List Neg := [.imp (.down (.circ (.atom "p"))) (.up (.atom "r")), .imp (.atom "s") (.circ (.atom "p"))]
def s1b : List Neg :=
  [ .imp (.down (.circ (.down (.imp (.atom "d") (.up (.atom "p")))))) (.up (.atom "a"))
  , .imp (.atom "c") (.circ (.atom "p")) ]
def sizeF : PLLFormula → Nat
  | .prop _ => 1 | .falsePLL => 1
  | .and a b => sizeF a + sizeF b + 1 | .or a b => sizeF a + sizeF b + 1
  | .ifThen a b => sizeF a + sizeF b + 1 | .somehow a => sizeF a + 1
def nrm (φ : PLLFormula) : PLLFormula := Rewrite.simplifyWith Rewrite.fullSetC 200 φ
def row (nm : String) (done : List Neg) (g : Option Neg) (f : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let raw := interpR "p" f [] done g []
  let n := sizeNeg raw
  let nn := sizeF (nrm (eraseNeg raw))
  let t1 ← IO.monoMsNow
  IO.println s!"{nm} f={f}: |raw|={n}  |nrm|={nn}  ({t1-t0} ms)"
  (← IO.getStdout).flush
def main : IO Unit := do
  for f in [3:15] do
    row "v2 A" v2 (some (.up (.atom "r"))) f
  for f in [3:15] do
    row "v2 E" v2 none f
  for f in [3:20] do
    row "s1b A" s1b (some (.up (.atom "a"))) f
  for f in [3:20] do
    row "s1b E" s1b none f
