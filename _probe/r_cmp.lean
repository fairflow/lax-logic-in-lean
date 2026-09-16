import wip.ui_routeB_r_def
import wip.ui_routeB_n4q_cells
set_option autoImplicit false
open LJFO
def cmpRQ (nm : String) (done : List Neg) (g : Option Neg) (hi : Nat) : IO Unit := do
  let mut s := ""
  for f in [0:hi+1] do
    let r := interpR "p" f [] done g []
    let q := interpQ "p" f [] done g []
    s := s ++ (if r = q then "=" else "X")
  IO.println s!"{nm}: {s}"
def main : IO Unit := do
  cmpRQ "(i)  A  cell1 " cell1 (some goal1) 8
  cmpRQ "(i)  E  cell1 " cell1 none 8
  cmpRQ "(iii)A  cell3 " cell3 (some goal3) 16
  cmpRQ "(vi) A  cell6 " cell6 (some goal6d) 10
  cmpRQ "(m6) A  m6    " m6 (some (.up (.atom "c"))) 12
  cmpRQ "(m10)A  m10   " m10 (some (.circ (.atom "g"))) 12
  cmpRQ "cStation goals" cStation (some (.up (.atom "e"))) 6
