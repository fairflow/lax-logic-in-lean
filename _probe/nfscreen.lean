/-
WP10 Stage 0, the normal-form screen: for each designed cell, goal mode and
fuel, erase both interpolants and normalise with the CERTIFIED simpset
(`Rewrite.simplifyWith Rewrite.fullSetC`, `simplifyWith_interd`).  Equal
normal forms PROVE interderivability; unequal ones go to the decider.
-/
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

def nrm (φ : PLLFormula) : PLLFormula := Rewrite.simplifyWith Rewrite.fullSetC 200 φ

def gm1 : Neg := .circ (.atom "b")
def gm6 : Neg := .up (.atom "c")
def gm10 : Neg := .circ (.atom "g")

def row (nm : String) (done : List Neg) (g : Option Neg) (f : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mp := eraseNeg (interpP "p" f [] done g)
  let mq := eraseNeg (interpQ "p" f [] done g [])
  let np := nrm mp
  let nq := nrm mq
  let t1 ← IO.monoMsNow
  let e := decide (np = nq)
  IO.println s!"{nm} f={f} raw {sizeF mp}/{sizeF mq} nrm {sizeF np}/{sizeF nq} NFEQ={e} ({t1-t0}ms)"
  (← IO.getStdout).flush

def cells : List (String × List Neg × Option Neg) :=
  [("i  -E", cell1, none), ("i  -A", cell1, some goal1),
   ("iii-E", cell3, none), ("iii-A", cell3, some goal3),
   ("vi -E", cell6, none), ("vi -A", cell6, some goal6d),
   ("m1 -E", m1, none),    ("m1 -A", m1, some gm1),
   ("m6 -E", m6, none),    ("m6 -A", m6, some gm6),
   ("m10-E", m10, none),   ("m10-A", m10, some gm10)]

def main (args : List String) : IO Unit := do
  let hi := match args with | [n] => n.toNat! | _ => 4
  for (nm, done, g) in cells do
    for f in List.range (hi + 1) do
      if f ≥ 1 then row nm done g f
