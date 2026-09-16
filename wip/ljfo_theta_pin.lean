/- Emit paste-ready, kernel-checkable snippets for the certified facts of
the θ-family: the two strict steps (countermodels, via
`FinCM.not_provable_of_check`) and the stabilisation (proof terms, via
`Search.proved_sound`). -/
import wip.ljfo_theta

open Theta PLLND

def emitRef (name : String) (Γ : List PLLFormula) (C : PLLFormula) : IO Unit := do
  match PLLND.Search.refute? {} Γ C with
  | some w => IO.println (w.snippet name)
  | none => IO.println s!"-- {name}: no countermodel"
  (← IO.getStdout).flush

def emitPrf (name : String) (budget : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) : IO Unit := do
  match PLLND.Search.prove?Bounded budget Γ C with
  | some t =>
      let s := t.snippet name
      IO.println s!"-- {name}: proof-term snippet, {s.length} chars"
      if s.length < 60000 then IO.println s
      else IO.println s!"-- (suppressed: {s.length} chars)"
  | none => IO.println s!"-- {name}: not proved at budget {budget}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let stage := args.headD "cm"
  if stage == "cm" then
    emitRef "theta2_not_theta1" [Theta.theta 2] (Theta.theta 1)
    emitRef "theta3_not_theta2" [Theta.theta 3] (Theta.theta 2)
    emitRef "thetaP2_not_thetaP1" [Theta.theta' 2] (Theta.theta' 1)
    emitRef "thetaP3_not_thetaP2" [Theta.theta' 3] (Theta.theta' 2)
    emitRef "pnfA4_not_pnfA3" [Theta.pnf (Theta.A 4)] (Theta.pnf (Theta.A 3))
    emitRef "pnfA6_not_pnfA5" [Theta.pnf (Theta.A 6)] (Theta.pnf (Theta.A 5))
  if stage == "prf" then
    emitPrf "theta4_le_theta3" 400000 [Theta.theta 4] (Theta.theta 3)
    emitPrf "theta3_le_theta4" 400000 [Theta.theta 3] (Theta.theta 4)
  if stage == "prf2" then
    emitPrf "pnfA7_le_pnfA6" 400000 [Theta.pnf (Theta.A 7)] (Theta.pnf (Theta.A 6))
    emitPrf "pnfA6_le_pnfA7" 400000 [Theta.pnf (Theta.A 6)] (Theta.pnf (Theta.A 7))
  IO.println "PIN-DONE"
