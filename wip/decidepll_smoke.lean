/-
# `decidePLL` smoke probe — untrusted engineering evidence

Runs `decidePLL` (wip/gbu_frjw_saturate.lean) on tiny formulas with
verdicts fixed IN ADVANCE.  This is `#eval`-level evidence that the
construction computes at the bottom of the scale — it taints nothing
and proves nothing (the `#guard_msgs` axiom pins are the kernel gates);
a timeout is a FLAG (the object is a proof witness, not a practical
procedure), never a verdict.

Run one cell per invocation:  `lake env lean --run wip/decidepll_smoke.lean <name>`
-/
import wip.gbu_frjw_saturate

open FRJ FRJ.Gbu.W Form

def cells : List (String × Form × Bool) := [
  ("atom",    .atom "p", false),
  ("bot",     .bot, false),
  ("circbot", .circ .bot, false),
  ("impid",   .imp (.atom "p") (.atom "p"), true),
  ("unit",    .imp (.atom "p") (.circ (.atom "p")), true)
]

def runCell (name : String) (G : Form) (expected : Bool) : IO Unit := do
  let verdict := @decide (PLL G) (decidePLL G)
  let mark := if verdict == expected then "PASS" else "FAIL"
  IO.println s!"{name}: decidePLL={verdict} expected={expected} {mark}"

def main (args : List String) : IO Unit := do
  match args with
  | [name] =>
      match cells.find? (fun c => c.1 == name) with
      | some (n, G, e) => runCell n G e
      | none => IO.println s!"unknown cell {name}"
  | _ => IO.println "usage: --run wip/decidepll_smoke.lean <cell>"
