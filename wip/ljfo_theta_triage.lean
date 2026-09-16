/- Countermodel-only triage on the RAW chain values.

`Search.refute?` normalises the sequent before running the frame battery
and the closure emitter, and gates every candidate through `FinCM.checkB`
on the original — so it is cheap even where `prove?Bounded` is hopeless,
and a hit is a certificate about the raw values themselves.

Calibration first: `refute?` must find the KNOWN strict steps at the raw
level (A_2 ⊬ A_1, A_4 ⊬ A_3, A_6 ⊬ A_5).  Then the descending steps
A_7 ⊢ A_6, A_8 ⊢ A_6, … are probed.  A miss is not a proof, but a miss on
a battery that hits every genuine strict step at the same shapes is the
strongest cheap evidence available. -/
import wip.ljfo_theta

open Theta PLLND

def probe (name : String) (Γ : List PLLFormula) (C : PLLFormula) : IO Unit := do
  match PLLND.Search.refute? {} Γ C with
  | some w => IO.println s!"{name}: REFUTED (certified) — {w.summary}"
  | none => IO.println s!"{name}: no countermodel"
  (← IO.getStdout).flush

def main : IO Unit := do
  IO.println "==== calibration: the known strict steps, RAW ===="
  probe "raw A_2 ⊬ A_1?" [Theta.A 2] (Theta.A 1)
  probe "raw A_4 ⊬ A_3?" [Theta.A 4] (Theta.A 3)
  probe "raw A_6 ⊬ A_5?" [Theta.A 6] (Theta.A 5)
  IO.println ""
  IO.println "==== the plateaus and the question, RAW ===="
  probe "raw A_3 ⊬ A_2?" [Theta.A 3] (Theta.A 2)
  probe "raw A_5 ⊬ A_4?" [Theta.A 5] (Theta.A 4)
  probe "raw A_7 ⊬ A_6?" [Theta.A 7] (Theta.A 6)
  probe "raw A_8 ⊬ A_6?" [Theta.A 8] (Theta.A 6)
  probe "raw A_9 ⊬ A_6?" [Theta.A 9] (Theta.A 6)
  probe "raw A_10 ⊬ A_6?" [Theta.A 10] (Theta.A 6)
  probe "raw A_11 ⊬ A_6?" [Theta.A 11] (Theta.A 6)
  IO.println ""
  IO.println "==== the same on the θ-family ===="
  for k in [1, 2, 3, 4, 5, 6, 7] do
    probe s!"θ_{k+1} ⊬ θ_{k}?" [Theta.theta (k+1)] (Theta.theta k)
  IO.println "TRIAGE-DONE"
