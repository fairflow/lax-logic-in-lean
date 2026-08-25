/- The decisive sequent: does the fuel chain stabilise at f = 6?

`A_7 ⊢ A_6` is PROVED (pnf level), so the chain has a plateau at 6/7.
The question is `A_8 ⊢ A_6`.  Two routes:

  (1) the whole sequent at a large node budget;
  (2) `∨`-decomposition — `pnf(A_8)` is a disjunction `◯B ∨ (A_7 ∧ ρ)`,
      so `A_8 ⊢ A_6` reduces to the two branch sequents, each far smaller.

Route (2)'s two branches plus `∨`-elimination (a rule of LaxND) give the
sequent; route (1) gives a single certificate for it directly. -/
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
  let stage := args.headD "all"
  let bigBud := (args.getD 1 "4000000").toNat!

  let x6 := Theta.pnf (Theta.A 6)
  let x7 := Theta.pnf (Theta.A 7)
  let x8 := Theta.pnf (Theta.A 8)
  let x9 := Theta.pnf (Theta.A 9)
  let t3 := Theta.theta 3

  if stage == "all" || stage == "split" then
    IO.println "==== ∨-decomposition of pnf(A_8) ===="
    let ds := Theta.disjs x8
    IO.println s!"pnf(A_8) has {ds.length} top-level disjuncts, sizes \
{ds.map Theta.sz}"
    for (d, i) in ds.zipIdx do
      IO.println s!"  disjunct {i} (|{Theta.sz d}|) = {PLLFormula.toString d}"
    IO.println ""
    for (d, i) in ds.zipIdx do
      IO.println s!"  disjunct {i} ⊢ θ_3 : {verd bigBud [d] t3}"
      (← IO.getStdout).flush
      IO.println s!"  disjunct {i} ⊢ pnf(A_6) : {verd bigBud [d] x6}"
      (← IO.getStdout).flush

  if stage == "all" || stage == "whole" then
    IO.println ""
    IO.println s!"==== whole sequents at budget {bigBud} ===="
    IO.println s!"pnf(A_8) ⊢ θ_3      : {verd bigBud [x8] t3}"
    (← IO.getStdout).flush
    IO.println s!"pnf(A_8) ⊢ pnf(A_6) : {verd bigBud [x8] x6}"
    (← IO.getStdout).flush
    IO.println s!"pnf(A_8) ⊢ pnf(A_7) : {verd bigBud [x8] x7}"
    (← IO.getStdout).flush
    IO.println s!"pnf(A_9) ⊢ θ_3      : {verd bigBud [x9] t3}"
    (← IO.getStdout).flush

  if stage == "all" || stage == "nine" then
    IO.println ""
    IO.println "==== ∨-decomposition of pnf(A_9), pnf(A_10) ===="
    for f in [9, 10, 11] do
      let x := Theta.pnf (Theta.A f)
      let ds := Theta.disjs x
      IO.println s!"pnf(A_{f}): {ds.length} disjuncts, sizes {ds.map Theta.sz}"
      for (d, i) in ds.zipIdx do
        IO.println s!"  A_{f} disjunct {i} ⊢ θ_3 : {verd bigBud [d] t3}"
        (← IO.getStdout).flush

  IO.println "PUSH-DONE"
