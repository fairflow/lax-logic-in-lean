/- The parametric countermodel family.

The two certified strict steps use the models

  M₁ :  w₀                              (one reflexive point, nothing forced)
  M₂ :  w₀ ⊑ w₁ ⊑ w₂,  w₁ ⊳ w₂,  w₂ fallible,  q at w₀, w₁

which are the k = 1, 2 members of the obvious family: the (k+1)-point
`Rᵢ`-chain with a fallible top, one `Rₘ` edge into it, and `q` forced
everywhere below the top —

  Mk :  n = k+1,  Rᵢ = { (i,j) : i < j },  Rₘ = { (k-1, k) },
        fallible {k},  q at 0 … k-1.

`◯⊥` is then first forced at `w_{k-1}`, so the `q ⊃ ◯⊥` of θ₂ fails
`k-1` steps down.  This file runs `FinCM.checkB` on `Mk` for
`θ_{k+1} ⊢ θ_k`, k = 1 … 6, and on the raw chain `A_{2k+2} ⊢ A_{2k+1}`,
and reports where the family stops working. -/
import wip.ljfo_theta

open Theta PLLND

/-- `Mk` — the (k+1)-point chain with fallible top. -/
def chainM (k : Nat) : FinCM :=
  { n := k + 1
    ri := (List.range (k+1)).flatMap (fun i =>
            (List.range (k+1)).filterMap (fun j => if i < j then some (i, j) else none))
    rm := if k = 0 then [] else [(k - 1, k)]
    fall := [k]
    val := (List.range k).map (fun i => (i, "q")) }

def report (name : String) (M : FinCM) (Γ : List PLLFormula) (C : PLLFormula) :
    IO Unit := do
  let wf := M.wellB
  let ok := FinCM.checkB M 0 Γ C
  IO.println s!"{name}: wellFormed={wf}  checkB@w0={ok}"
  (← IO.getStdout).flush

def main : IO Unit := do
  IO.println "==== chainM k, as a countermodel to θ_{k+1} ⊢ θ_k ===="
  for k in [1, 2, 3, 4, 5, 6] do
    report s!"chainM {k} ⊨ θ_{k+1}, ⊭ θ_{k}" (chainM k)
      [Theta.theta (k+1)] (Theta.theta k)
  IO.println ""
  IO.println "==== chainM k against the RAW chain A_{2k+2} ⊢ A_{2k+1} ===="
  for k in [1, 2, 3, 4] do
    report s!"chainM {k} : A_{2*k+2} ⊢ A_{2*k+1}" (chainM k)
      [Theta.A (2*k+2)] (Theta.A (2*k+1))
  IO.println ""
  IO.println "==== chainM k against RAW A_{2k+2} ⊢ A_{2k} ===="
  for k in [1, 2, 3, 4] do
    report s!"chainM {k} : A_{2*k+2} ⊢ A_{2*k}" (chainM k)
      [Theta.A (2*k+2)] (Theta.A (2*k))
  IO.println ""
  IO.println "==== sweep: does ANY chainM (k ≤ 12) refute θ_4 ⊢ θ_3 ? ===="
  let hits := (List.range 13).filter (fun k =>
    FinCM.checkB (chainM k) 0 [Theta.theta 4] (Theta.theta 3))
  IO.println s!"hits: {hits}"
  IO.println "FAMILY-DONE"
