/- Steps 3 and 4 of the refutation prong.

Stage 1 (the untrusted normaliser is discharged):  pnf(A_f) ⟛ A_f, both
directions, by `prove?Bounded`.
Stage 2 (the conjecture):  θ_k ⟛ pnf(A_{2k}) and θ'_k ⟛ pnf(A_{2k}).
Stage 3 (strict ascent):   `refute?` on θ_{k+1} ⊢ θ_k, printing the
certified countermodel in full, and the ascending direction θ_k ⊢ θ_{k+1}.

Every line is labelled: `yes` = `prove?Bounded` certificate, `NO` =
`refute?` countermodel certified by `FinCM.checkB`, `unk` = neither at
this budget (a non-verdict). -/
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

def both (budget : Nat) (name : String) (a b : PLLFormula) : IO Unit := do
  IO.println s!"{name}:  → {verd budget [a] b}   ← {verd budget [b] a}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let stage := args.headD "all"

  if stage == "all" || stage == "1" then
    IO.println "==== Stage 1: pnf(A_f) ⟛ A_f  (discharges the normaliser) ===="
    for f in [1, 2, 3, 4, 5, 6, 7] do
      let a := Theta.A f
      let n := Theta.pnf a
      IO.println s!"A_{f} (raw {Theta.sz a}, pnf {Theta.sz n})"
      both bud s!"  A_{f} vs pnf" a n

  if stage == "all" || stage == "2" then
    IO.println ""
    IO.println "==== Stage 2: θ_k ⟛ pnf(A_2k),  θ'_k ⟛ pnf(A_2k) ===="
    for k in [1, 2, 3, 4, 5] do
      let n := Theta.pnf (Theta.A (2 * k))
      let t := Theta.theta k
      let t' := Theta.theta' k
      IO.println s!"k={k}: |pnf A_{2*k}| = {Theta.sz n}, |θ_{k}| = {Theta.sz t}, |θ'_{k}| = {Theta.sz t'}"
      IO.println s!"    θ_{k}  = {PLLFormula.toString t}"
      IO.println s!"    θ'_{k} = {PLLFormula.toString t'}"
      both bud s!"    θ_{k} vs pnf(A_{2*k})" t n
      both bud s!"    θ'_{k} vs pnf(A_{2*k})" t' n
      both bud s!"    θ_{k} vs θ'_{k}" t t'

  if stage == "all" || stage == "3" then
    IO.println ""
    IO.println "==== Stage 3: strict ascent of the θ-family ===="
    for k in [1, 2, 3, 4, 5, 6] do
      let a := Theta.theta k
      let b := Theta.theta (k + 1)
      IO.println s!"-- k={k}: θ_{k} ⊢ θ_{k+1} (ascending) = {verd bud [a] b}"
      (← IO.getStdout).flush
      match PLLND.Search.refute? {} [b] a with
      | some w =>
          IO.println s!"-- k={k}: θ_{k+1} ⊬ θ_{k}  REFUTED, {w.summary}"
          IO.println (w.render)
      | none =>
          IO.println s!"-- k={k}: θ_{k+1} ⊢ θ_{k} = {verd bud [b] a} (no countermodel found)"
      (← IO.getStdout).flush

  if stage == "all" || stage == "4" then
    IO.println ""
    IO.println "==== Stage 4: same, boxed-body form θ'_k ===="
    for k in [1, 2, 3, 4, 5, 6] do
      let a := Theta.theta' k
      let b := Theta.theta' (k + 1)
      IO.println s!"-- k={k}: θ'_{k} ⊢ θ'_{k+1} = {verd bud [a] b}"
      (← IO.getStdout).flush
      match PLLND.Search.refute? {} [b] a with
      | some w =>
          IO.println s!"-- k={k}: θ'_{k+1} ⊬ θ'_{k}  REFUTED, {w.summary}"
          IO.println (w.render)
      | none =>
          IO.println s!"-- k={k}: θ'_{k+1} ⊢ θ'_{k} = {verd bud [b] a} (no countermodel found)"
      (← IO.getStdout).flush

  IO.println "RUN-DONE"
