/- Recursive reduction of `pnf(A_f) ⊢ θ₃`.

The whole sequent is past the searcher's reach for f ≥ 9, but the reduction

  * `X ∨ Y ⊢ C`  from  `X ⊢ C` and `Y ⊢ C`   (∨-elimination)
  * `X ∧ Y ⊢ C`  from  `X ⊢ C`  or  `Y ⊢ C`  (∧-elimination)

is sound in LaxND, so a reduction tree whose leaves are `prove?Bounded`
certificates certifies the root sequent.  `red` prints the tree; `OK` at
the root means the sequent is derivable. -/
import wip.ljfo_theta

open Theta PLLND

def prv (budget : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  (PLLND.Search.prove?Bounded budget Γ C).isSome

partial def red (budget : Nat) (C : PLLFormula) (depth : Nat) (X : PLLFormula) :
    IO Bool := do
  let pad := String.ofList (List.replicate (2 * depth) ' ')
  if prv budget [X] C then
    IO.println s!"{pad}leaf |{Theta.sz X}| : OK"
    (← IO.getStdout).flush
    return true
  match X with
  | .or a b =>
      IO.println s!"{pad}∨ |{Theta.sz X}| : split"
      (← IO.getStdout).flush
      let l ← red budget C (depth + 1) a
      if !l then return false
      red budget C (depth + 1) b
  | .and a b =>
      IO.println s!"{pad}∧ |{Theta.sz X}| : try left"
      (← IO.getStdout).flush
      if ← red budget C (depth + 1) a then return true
      IO.println s!"{pad}∧ |{Theta.sz X}| : try right"
      (← IO.getStdout).flush
      red budget C (depth + 1) b
  | _ =>
      IO.println s!"{pad}leaf |{Theta.sz X}| : UNSETTLED"
      (← IO.getStdout).flush
      return false

def main (args : List String) : IO Unit := do
  let b := (args.headD "4000000").toNat!
  let t3 := Theta.theta 3
  for f in [8, 9, 10, 11] do
    let x := Theta.pnf (Theta.A f)
    IO.println s!"==== pnf(A_{f}) (|{Theta.sz x}|) ⊢ θ_3 ===="
    let ok ← red b t3 0 x
    IO.println s!"==== pnf(A_{f}) ⊢ θ_3 : {if ok then "DERIVABLE" else "unsettled"}"
    (← IO.getStdout).flush
  IO.println "RED-DONE"
