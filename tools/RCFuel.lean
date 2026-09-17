import wip.ljfo_link
import LaxLogic.RN.Rho
import tools.RCells

open RCells (cells)

open PLLND RhoOrder TwoSidedLink


def mkOp : String → PLLFormula → PLLFormula → PLLFormula
  | "and", a, b => a.and b
  | "or",  a, b => a.or b
  | "imp", a, b => a.ifThen b
  | _,     a, _ => a.somehow

def fuels : List Nat := [8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 56]

def findFuel (Γ : List PLLFormula) (φ : PLLFormula) : Option Nat :=
  fuels.find? (fun f => searchProves f Γ φ)

def main : IO Unit := do
  for (op, i, j, k) in cells do
    let lhs := mkOp op (rhoF i) (rhoF j)
    let rhs := rhoF k
    if lhs == rhs then
      IO.println s!"TRIV {op} {i} {j} {k}"
    else
      match findFuel [lhs] rhs, findFuel [rhs] lhs with
      | some f1, some f2 => IO.println s!"CELL {op} {i} {j} {k} {f1} {f2}"
      | o1, o2 => IO.println s!"SKIP {op} {i} {j} {k} fwd={o1} bwd={o2}"
    (← IO.getStdout).flush
  IO.println "RCFUEL-DONE"
