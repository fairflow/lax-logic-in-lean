import wip.ui_routeB_n4q_cells
import Rewrite

set_option autoImplicit false
open LJFO

def sizeF : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and a b => sizeF a + sizeF b + 1
  | .or a b => sizeF a + sizeF b + 1
  | .ifThen a b => sizeF a + sizeF b + 1
  | .somehow a => sizeF a + 1

/-- number of implication nodes: the exponent the decider pays. -/
def impsF : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and a b => impsF a + impsF b
  | .or a b => impsF a + impsF b
  | .ifThen a b => impsF a + impsF b + 1
  | .somehow a => impsF a

def nrm (φ : PLLFormula) : PLLFormula := Rewrite.simplifyWith Rewrite.fullSetC 200 φ

def row (nm : String) (done : List Neg) (g : Option Neg) (f : Nat) : IO Unit := do
  let mp := eraseNeg (interpP "p" f [] done g)
  let mq := eraseNeg (interpQ "p" f [] done g [])
  let np := nrm mp
  let nq := nrm mq
  IO.println s!"{nm} f={f} | P raw {sizeF mp}/{impsF mp} nrm {sizeF np}/{impsF np} | Q raw {sizeF mq}/{impsF mq} nrm {sizeF nq}/{impsF nq} | eq={decide (np = nq)}"

def main : IO Unit := do
  for f in [1,2,3,4] do
    row "i-A " cell1 (some goal1) f
  for f in [1,2,3,4] do
    row "i-E " cell1 none f
  for f in [1,2,3] do
    row "iii-A" cell3 (some goal3) f
  for f in [1,2,3] do
    row "vi-A" cell6 (some goal6d) f
  for f in [1,2,3] do
    row "m1-A" m1 (some (.circ (.atom "b"))) f
