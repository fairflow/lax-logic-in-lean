/- The raw-value bridge.  Everything above runs on `pnf(A_f)`, produced by
an UNTRUSTED simplifier; for the results to be about the fuel chain itself
the bridge `A_f ⟛ pnf(A_f)` must be certified.  It is certified for
f ≤ 5 at 400k; this file pushes f = 6, 7, 8 at a large budget, and also
attacks the raw plateau `A_7 ⊢ A_6` directly.

Where the bridge is not certified, the pnf-level results stand as results
about `pnf(A_f)` only, and the transfer is OPEN. -/
import wip.ljfo_theta

open Theta PLLND

def verd (budget : Nat) (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match PLLND.Search.prove?Bounded budget Γ C with
  | some _ => "yes"
  | none =>
    match PLLND.Search.refute? {} Γ C with
    | some _ => "NO"
    | none => "unk"

def main (args : List String) : IO Unit := do
  let stage := args.headD "bridge"
  let b := (args.getD 1 "8000000").toNat!
  if stage == "bridge" then
    for f in [6, 7, 8] do
      let a := Theta.A f
      let n := Theta.pnf a
      IO.println s!"A_{f} (raw {Theta.sz a}) ⊢ pnf (|{Theta.sz n}|) : {verd b [a] n}"
      (← IO.getStdout).flush
      IO.println s!"pnf ⊢ A_{f} : {verd b [n] a}"
      (← IO.getStdout).flush
  if stage == "rawplateau" then
    IO.println s!"raw A_7 ⊢ raw A_6 : {verd b [Theta.A 7] (Theta.A 6)}"
    (← IO.getStdout).flush
    IO.println s!"raw A_8 ⊢ raw A_6 : {verd b [Theta.A 8] (Theta.A 6)}"
    (← IO.getStdout).flush
  if stage == "unit" then
    -- the cheaper intermediate: the unit normal form
    for f in [6, 7] do
      let a := Theta.A f
      let u := Theta.simpF a
      let n := Theta.pnf a
      IO.println s!"A_{f}: raw {Theta.sz a}, unit-nf {Theta.sz u}, pnf {Theta.sz n}"
      IO.println s!"  A_{f} ⊢ unit-nf : {verd b [a] u}"
      (← IO.getStdout).flush
      IO.println s!"  unit-nf ⊢ A_{f} : {verd b [u] a}"
      (← IO.getStdout).flush
      IO.println s!"  unit-nf ⊢ pnf : {verd b [u] n}"
      (← IO.getStdout).flush
      IO.println s!"  pnf ⊢ unit-nf : {verd b [n] u}"
      (← IO.getStdout).flush
  IO.println "BRIDGE-DONE"
