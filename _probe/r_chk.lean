import wip.ui_routeB_r_def
import wip.ui_routeB_n4q_cells
set_option autoImplicit false
open LJFO

def g6c : Option Neg := some (.up (.atom "c"))
def gm10 : Option Neg := some (.circ (.atom "g"))

def eqAt (done : List Neg) (g : Option Neg) (i j : Nat) : Bool :=
  decide (interpR "p" i [] done g [] = interpR "p" j [] done g [])

def main : IO Unit := do
  IO.println s!"cell3 E  9=10: {eqAt cell3 none 9 10}   10=11: {eqAt cell3 none 10 11}"
  IO.println s!"m6 A     5=6:  {eqAt m6 g6c 5 6}   6=7: {eqAt m6 g6c 6 7}"
  IO.println s!"m10 E    33=34: {eqAt m10 none 33 34}  34=35: {eqAt m10 none 34 35}  35=36: {eqAt m10 none 35 36}  32=33: {eqAt m10 none 32 33}"
  IO.println s!"gate cell3 12=13: {eqAt cell3 (some goal3) 12 13}"
  IO.println s!"gate m10   33=34: {eqAt m10 gm10 33 34}"
