/- The decisive test.  The θ-family read off the chain STABILISES at k = 3
(θ_4 ⊢ θ_3 is a `prove?Bounded` certificate).  Either the family is
unfaithful past k = 3, or the raw fuel chain itself stabilises at f = 6 —
in which case W holds at this cell and the cell is not a
Ghilardi–Zawadowski witness.  This file settles it on the chain itself,
on the PLL-normal forms (which stage 1 of ljfo_theta_run certifies
interderivable with the raw interpF values).

Every line is labelled: `yes` = prove?Bounded certificate, `NO` = refute?
countermodel certified by FinCM.checkB, `unk` = neither at this budget. -/
import wip.ljfo_theta

open Theta PLLND

def bud : Nat := 400000

def verd (budget : Nat) (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match PLLND.Search.prove?Bounded budget Γ C with
  | some _ => "yes"
  | none =>
    match PLLND.Search.refute? {} Γ C with
    | some _ => "NO"
    | none => "unk"

def showCM (name : String) (Γ : List PLLFormula) (C : PLLFormula) : IO Unit := do
  match PLLND.Search.refute? {} Γ C with
  | some w =>
      IO.println s!"{name}: REFUTED, {w.summary}"
      IO.println (w.render)
  | none => IO.println s!"{name}: no countermodel from refute?"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let stage := args.headD "all"

  if stage == "all" || stage == "a" then
    IO.println "==== consecutive steps of the chain, on pnf forms ===="
    for f in [1, 2, 3, 4, 5, 6, 7, 8, 9] do
      let x := Theta.pnf (Theta.A f)
      let y := Theta.pnf (Theta.A (f + 1))
      IO.println s!"A_{f} (|{Theta.sz x}|) vs A_{f+1} (|{Theta.sz y}|):  \
asc {verd bud [x] y}   desc {verd bud [y] x}"
      (← IO.getStdout).flush

  if stage == "all" || stage == "b" then
    IO.println ""
    IO.println "==== does the chain fall back to A_6? ===="
    let a6 := Theta.pnf (Theta.A 6)
    for f in [7, 8, 9, 10, 11] do
      let x := Theta.pnf (Theta.A f)
      IO.println s!"A_{f} (|{Theta.sz x}|) ⊢ A_6:  {verd bud [x] a6}"
      (← IO.getStdout).flush

  if stage == "all" || stage == "c" then
    IO.println ""
    IO.println "==== countermodels at the certified strict steps ===="
    showCM "A_2 ⊬ A_1" [Theta.pnf (Theta.A 2)] (Theta.pnf (Theta.A 1))
    showCM "A_4 ⊬ A_3" [Theta.pnf (Theta.A 4)] (Theta.pnf (Theta.A 3))
    showCM "A_6 ⊬ A_5" [Theta.pnf (Theta.A 6)] (Theta.pnf (Theta.A 5))
    showCM "θ_2 ⊬ θ_1" [Theta.theta 2] (Theta.theta 1)
    showCM "θ_3 ⊬ θ_2" [Theta.theta 3] (Theta.theta 2)
    showCM "θ'_2 ⊬ θ'_1" [Theta.theta' 2] (Theta.theta' 1)
    showCM "θ'_3 ⊬ θ'_2" [Theta.theta' 3] (Theta.theta' 2)

  if stage == "all" || stage == "d" then
    IO.println ""
    IO.println "==== raw values, no normaliser (A_6 vs A_7, A_7 vs A_8) ===="
    let r6 := Theta.A 6
    let r7 := Theta.A 7
    let r8 := Theta.A 8
    IO.println s!"raw A_6 ⊢ A_7: {verd bud [r6] r7}"
    (← IO.getStdout).flush
    IO.println s!"raw A_7 ⊢ A_6: {verd bud [r7] r6}"
    (← IO.getStdout).flush
    IO.println s!"raw A_8 ⊢ A_6: {verd bud [r8] r6}"
    (← IO.getStdout).flush

  IO.println "CHAIN-DONE"
