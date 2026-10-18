/-
# `clpcompare` — the mortgage program, compiled, against SWI-Prolog's clpq

    .lake/build/bin/clpcompare time D REPS     one JSON line of timings for duration D
    .lake/build/bin/clpcompare emit D DIR      write the kernel-check files for D into DIR

`time` runs, REPS times each after one untimed warm-up: the search (the engine,
eager pruning), the arithmetic producer (Fourier–Motzkin: a witness, then the
Farkas multipliers fixing P), and the four Boolean checkers (the tree, the
witness, the two refutations).  Wall-clock nanoseconds from `IO.monoNanosNow`;
each timed computation reads its input from an `IO.Ref` after the clock starts,
so the compiler cannot move it out of the timed region, and its result is used
in the output.  `emit` writes `D.lean` (the tree as a literal and the verdict of
`answerK`, kernel-checked), `D_base.lean` (the same definitions without the
verdict, for the baseline) and `D_arith.lean` (the witness and the Farkas
refutations, checked by `decide +kernel` outside lean-certify).
See `LaxLogic/QLL/CLPCompare.lean` and `scripts/clp-compare/`.
-/
import LaxLogic.QLL.CLPCompare

open LaxLogic.QLL LaxLogic.QLL.Engine LaxLogic.QLL.LinQ LaxLogic.QLL.Compare

def median (xs : List Nat) : Nat :=
  let s := (xs.toArray.qsort (· < ·)).toList
  s.getD (s.length / 2) 0

def ms (ns : Nat) : String :=
  let us := ns / 1000
  s!"{us / 1000}.{toString (1000 + us % 1000) |>.drop 1}"

def jlist (xs : List Nat) : String := "[" ++ ", ".intercalate (xs.map ms) ++ "]"

/-- Time `f` on the input held in `r`, `reps` times after one warm-up.  The
result is written to `sink` before the clock stops, so it is computed inside
the timed region. -/
def timeRef {α β : Type} (r : IO.Ref α) (f : α → β) (reps : Nat) (use : β → Nat) :
    IO (List Nat × Nat) := do
  let sink ← IO.mkRef 0
  sink.set (use (f (← r.get)))
  let mut ts : List Nat := []
  let mut acc := (← sink.get)
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let x ← r.get
    sink.set (use (f x))
    let t1 ← IO.monoNanosNow
    acc := acc + (← sink.get)
    ts := ts ++ [t1 - t0]
  return (ts, acc)

def treeSize : CProof → Nat
  | .top | .cstr _ _ => 1
  | .andI p q => treeSize p + treeSize q + 1
  | .orL p | .orR p | .exI _ p | .clause _ _ p => treeSize p + 1

def ratStr (q : ℚ) : String := s!"{q.num}/{q.den}"

def timeCmd (d reps : Nat) : IO UInt32 := do
  let dRef ← IO.mkRef d
  let (tSearch, _) ← timeRef dRef search reps (fun o => match o with | some p => treeSize p | none => 0)
  let some p := search d | do IO.println s!"\{\"system\": \"lean-compiled\", \"D\": {d}, \"error\": \"no answer\"}"; return 1
  let pRef ← IO.mkRef p
  let (tArith, _) ← timeRef pRef arith reps (fun o => match o with | some r => r.below.length | none => 0)
  let some r := arith p | do IO.println s!"\{\"system\": \"lean-compiled\", \"D\": {d}, \"error\": \"no arithmetic certificate\"}"; return 1
  let rRef ← IO.mkRef r
  let b2n (b : Bool) : Nat := if b then 1 else 0
  let (tTree, okTree) ← timeRef rRef (checkTree d) reps b2n
  let (tSat, okSat) ← timeRef rRef checkSat reps b2n
  let (tBelow, okBelow) ← timeRef rRef checkBelow reps b2n
  let (tAbove, okAbove) ← timeRef rRef checkAbove reps b2n
  let allOK := okTree == reps + 1 && okSat == reps + 1 && okBelow == reps + 1 && okAbove == reps + 1
  IO.println s!"\{\"system\": \"lean-compiled\", \"D\": {d}, \"reps\": {reps}, \"tree_nodes\": {treeSize p}, \"constraints\": {r.cons.length}, \"checks_pass\": {allOK}, \"search_ms\": {ms (median tSearch)}, \"arith_ms\": {ms (median tArith)}, \"check_tree_ms\": {ms (median tTree)}, \"check_sat_ms\": {ms (median tSat)}, \"check_below_ms\": {ms (median tBelow)}, \"check_above_ms\": {ms (median tAbove)}, \"search_all_ms\": {jlist tSearch}, \"arith_all_ms\": {jlist tArith}, \"tree_all_ms\": {jlist tTree}, \"sat_all_ms\": {jlist tSat}, \"below_all_ms\": {jlist tBelow}, \"above_all_ms\": {jlist tAbove}, \"P\": \"{ratStr r.value}\"}"
  return (if allOK then 0 else 2)

def header : String :=
  "import LaxLogic.QLL.CLPCompare\nopen LaxLogic.QLL LaxLogic.QLL.Compare LaxLogic.QLL.LinQ LaxLogic.QLL.CLPExamples\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"

def litRat (q : ℚ) : String := s!"(mkRat ({q.num}) {q.den})"

def litPairs (w : List (String × ℚ)) : String :=
  "[" ++ ", ".intercalate (w.map fun (x, q) => s!"({x.quote}, {litRat q})") ++ "]"

def litRats (l : List ℚ) : String := "[" ++ ", ".intercalate (l.map litRat) ++ "]"

def emitCmd (d : Nat) (dir : String) : IO UInt32 := do
  let some p := search d | do IO.println "no answer"; return 1
  let some r := arith p | do IO.println "no arithmetic certificate"; return 1
  let defs := s!"def tree : CProof :=\n  {litTree p}\n"
  IO.FS.writeFile s!"{dir}/{d}_base.lean" (header ++ defs)
  IO.FS.writeFile s!"{dir}/{d}.lean" (header ++ defs ++
    s!"\nset_option profiler true in\nset_option profiler.threshold 1 in\ntheorem answer : Prv mortgage.forms (.imp tree.total (mgQuery {d})) :=\n  answerK.verdict (isLinC, mortgage, mgQuery {d}, tree.total) tree\n\n#print axioms answer\n")
  let adefs := defs ++ s!"\ndef wit : List (String × ℚ) := {litPairs r.witness}\ndef val : ℚ := {litRat r.value}\ndef below : List ℚ := {litRats r.below}\ndef above : List ℚ := {litRats r.above}\ndef cert : Produced := ⟨tree, [], wit, val, below, above⟩\n"
  IO.FS.writeFile s!"{dir}/{d}_arith_base.lean" (header ++ adefs)
  IO.FS.writeFile s!"{dir}/{d}_arith.lean" (header ++ adefs ++
    "\nset_option profiler true\nset_option profiler.threshold 1\ntheorem sat : checkSat cert = true := by decide +kernel\ntheorem lo : checkBelow cert = true := by decide +kernel\ntheorem hi : checkAbove cert = true := by decide +kernel\nset_option profiler false\n\n#print axioms sat\n#print axioms lo\n#print axioms hi\n")
  IO.println s!"wrote {dir}/{d}.lean, {d}_base.lean, {d}_arith.lean, {d}_arith_base.lean; tree {treeSize p} nodes"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["time", d, reps] => timeCmd d.toNat! reps.toNat!
  | ["emit", d, dir] => emitCmd d.toNat! dir
  | _ => do
    IO.println "usage: clpcompare time D REPS | clpcompare emit D DIR"
    return 64
