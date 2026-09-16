/-
WP12 Stage 0, R1: the size trace of `interpR`'s chain at a cell, to tell a
late threshold from a genuine non-termination.
-/
import wip.ui_routeB_r_def
import wip.ui_routeB_n4q_cells

set_option autoImplicit false
open LJFO

def qInnerR : Neg := .imp (.down (.circ (.atom "a"))) (.up (.atom "b"))

def trace (nm : String) (done : List Neg) (g : Option Neg) (lo hi : Nat) : IO Unit := do
  IO.println s!"--- {nm} ---"
  let mut prev : Option Neg := none
  for f in [lo:hi+1] do
    let t0 ← IO.monoMsNow
    let v := interpR "p" f [] done g []
    let t1 ← IO.monoMsNow
    let eq := match prev with | none => "-" | some w => if w = v then "SAME" else "diff"
    IO.println s!"  f={f}  |I|={sizeNeg v}  vs f-1: {eq}   ({t1-t0} ms)"
    (← IO.getStdout).flush
    prev := some v

def main (args : List String) : IO Unit := do
  match args with
  | [which, lo, hi] =>
      let l := lo.toNat!; let h := hi.toNat!
      match which with
      | "m6A" => trace "(m6) A  m6 ⇒ ↑c" m6 (some (.up (.atom "c"))) l h
      | "m6E" => trace "(m6) E  m6" m6 none l h
      | "m10A" => trace "(m10) A  m10 ⇒ ◯g" m10 (some (.circ (.atom "g"))) l h
      | "m10E" => trace "(m10) E  m10" m10 none l h
      | "s1A" => trace "(S1) A  s1Station ⇒ ↑e" s1Station (some (.up (.atom "e"))) l h
      | "s1C" => trace "(S1) A  s1Station ⇒ ◯g" s1Station (some (.circ (.atom "g"))) l h
      | "s1E" => trace "(S1) E  s1Station" s1Station none l h
      | _ => IO.println "unknown cell"
  | _ => IO.println "usage: r_trace <cell> <lo> <hi>"
