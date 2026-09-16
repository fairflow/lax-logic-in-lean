/- Step 1 of the refutation prong: print A_f (and E_f) at the GZ-candidate
station, in the unit normal form (`simpF`) and in the PLL-aware normal
form (`pnf`).  Both are untrusted; `pnf` is what the θ-conjecture is read
off, and is engine-verified against the raw value in ljfo_theta_run. -/
import wip.ljfo_theta

open Theta

def line (name : String) (f : PLLFormula) : IO Unit := do
  let n1 := Theta.simpF f
  let n2 := Theta.pnf f
  IO.println s!"{name}: raw {Theta.sz f}  unit-nf {Theta.sz n1}  pll-nf {Theta.sz n2}"
  IO.println s!"    {PLLFormula.toString n2}"
  IO.println ""
  (← IO.getStdout).flush

def main : IO Unit := do
  IO.println "==== A-chain (∀p mode), station [◯p ⊃ r, ◯q], goal ↑↓◯p ===="
  for f in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] do
    line s!"A_{f}" (Theta.A f)
  IO.println "==== E-chain (∃p mode), same station ===="
  for f in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] do
    line s!"E_{f}" (Theta.E f)
  IO.println "PRINT-DONE"
