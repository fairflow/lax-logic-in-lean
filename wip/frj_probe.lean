/-
Empirical input to the FRJ(G)-lifting design (docs/frj-lifting.md).

THE QUESTION.  Refuting `◯A` at `v` means: NO `Rm`-successor of `v`
forces `A`.  By persistence (`Rm ⊆ Ri`, forcing hereditary), a world
forces `A` only if every world above it does, so

    ∀u ∈ Rm-cone(v). u ⊮ A   ⟺   ∀u MAXIMAL in Rm-cone(v). u ⊮ A

and the ARITY of the ◯-refutation rule is the number of `Rm`-maximal
successors.  If that is 1 the rule is UNARY (one premise, like FRJ's
own ⊃-rules); if it is unbounded the rule is a schema over lists,
which is Goranko's `Alt_n` phenomenon and much heavier to mechanise.

This probe measures the distribution over the frames we actually use.
-/
import LaxLogic.PLLCountermodelEmit

open PLLND PLLND.FinCM

namespace FRJProbe

def mk (n : Nat) (ri rm : List (Nat × Nat)) (fal : List Nat) : FinCM :=
  ⟨n, ri, rm, fal, []⟩

def wf (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all (fun x => M.riB x x && M.rmB x x) &&
  ws.all (fun x => ws.all fun y => ws.all fun z =>
    (!(M.riB x y && M.riB y z) || M.riB x z) &&
    (!(M.rmB x y && M.rmB y z) || M.rmB x z)) &&
  ws.all (fun x => ws.all fun y =>
    (!(M.rmB x y) || M.riB x y) &&
    (!(M.fallB x && M.riB x y) || M.fallB y))

def confl (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all fun x => ws.all fun w => ws.all fun v =>
    !(M.rmB x w && M.riB x v) || ws.any fun u => M.riB w u && M.rmB v u

/-- REDUCED: no two distinct worlds are Ri-equivalent (a partial
order, not a preorder).  Matthew's canonical-form condition. -/
def reduced (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all fun x => ws.all fun y =>
    !(M.riB x y && M.riB y x) || decide (x = y)

def pairsOf (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun x => (List.range n).map fun y => (x, y)

def subsetOf (l : List (Nat × Nat)) (code : Nat) : List (Nat × Nat) :=
  (l.zipIdx.filter fun p => (code / 2 ^ p.2) % 2 = 1).map (·.1)

def framesN (n : Nat) : List FinCM :=
  let ps := pairsOf n
  let cap := 2 ^ ps.length
  (List.range cap).flatMap fun ci =>
    (List.range cap).flatMap fun cm =>
      (List.range (2 ^ n)).map fun cf =>
        mk n (subsetOf ps ci ++ (List.range n).map fun x => (x, x))
             (subsetOf ps cm ++ (List.range n).map fun x => (x, x))
             ((List.range n).filter fun x => (cf / 2 ^ x) % 2 = 1)

/-- The `Rm`-maximal successors of `w`: successors with no strictly
greater successor (strict = not Ri-below it). -/
def rmMaximals (M : FinCM) (w : Nat) : List Nat :=
  (List.range M.n).filter fun u =>
    M.rmB w u &&
      !((List.range M.n).any fun z =>
        M.rmB w z && M.riB u z && !(M.riB z u))

structure Stats where
  frames : Nat := 0
  worlds : Nat := 0
  arity1 : Nat := 0
  arity2 : Nat := 0
  arity3plus : Nat := 0
  maxArity : Nat := 0

def tally (fs : List FinCM) : Stats := Id.run do
  let mut s : Stats := {}
  for M in fs do
    s := { s with frames := s.frames + 1 }
    for w in List.range M.n do
      let k := (rmMaximals M w).length
      s := { s with worlds := s.worlds + 1,
                    maxArity := max s.maxArity k }
      if k ≤ 1 then s := { s with arity1 := s.arity1 + 1 }
      else if k == 2 then s := { s with arity2 := s.arity2 + 1 }
      else s := { s with arity3plus := s.arity3plus + 1 }
  return s

def report (nm : String) (fs : List FinCM) : IO Unit := do
  let s := tally fs
  let pct (a : Nat) : Nat := if s.worlds == 0 then 0 else a * 100 / s.worlds
  IO.println s!"{nm}: {s.frames} frames, {s.worlds} worlds"
  IO.println s!"  ◯-rule arity 1 (UNARY): {s.arity1} ({pct s.arity1}%)"
  IO.println s!"  arity 2: {s.arity2} ({pct s.arity2}%)   arity ≥3: {s.arity3plus} ({pct s.arity3plus}%)"
  IO.println s!"  max arity seen: {s.maxArity}"
  (← IO.getStdout).flush

def main : IO Unit := do
  IO.println "FRJ-lifting probe: arity of the ◯-refutation rule"
  IO.println "(= number of Rm-MAXIMAL successors of a world)"
  IO.println ""
  for n in [2, 3] do
    let all := (framesN n).filter wf
    report s!"n={n} all well-formed          " all
    report s!"n={n} REDUCED (partial orders) " (all.filter reduced)
    report s!"n={n} confluent (PCLL class)   " (all.filter confl)
    report s!"n={n} reduced AND confluent    " (all.filter fun M => reduced M && confl M)
    IO.println ""
  IO.println "FRJ-PROBE-DONE"

end FRJProbe

def main : IO Unit := FRJProbe.main
