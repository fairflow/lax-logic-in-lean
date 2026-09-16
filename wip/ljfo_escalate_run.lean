/- Parallel escalation driver: the φ★ minimality direction and
representative flagged CimpAnt cells, at 10x budget (400k nodes). -/
import wip.ljfo_attack
import wip.ljfo_crosscheck

open LJFO PLLND LJFOAttack

def vB (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match PLLND.Search.prove?Bounded 400000 Γ C with
  | some _ => "yes"
  | none =>
    match PLLND.Search.refute? {} Γ C with
    | some _ => "NO-certified"
    | none => "unk"

def cellB (done rest : List Neg) (Q' : Pos) (K : List Neg) : String × String :=
  let e := interp pv [] done none
  let a := interp pv [] rest (some (.up (.down (.circ Q'))))
  (vB ((done ++ K).map negF) (.somehow (posF Q')),
   vB ((e :: K).map negF) (negF a))

def pr2 (label : String) (x : String × String) : IO Unit := do
  IO.println s!"== {label}: hyp={x.1} concl={x.2}"
  (← IO.getStdout).flush

def main : IO Unit := do
  IO.println "== phistar E ⊢ ¬¬◯⊥ @400k"
  IO.println (X.verdictBig [X.negF X.E] X.nnOBot)
  (← IO.getStdout).flush
  pr2 "[◯p→r, ◯p] K=[] @400k" (cellB [hyp, boxP] [boxP] aP [])
  pr2 "[◯p→r, ◯p] K=[◯q] @400k" (cellB [hyp, boxP] [boxP] aP [boxQ])
  pr2 "[◯p→r, ◯↓◯p] K=[] @400k" (cellB [hyp, boxBoxP] [boxBoxP] aP [])
  pr2 "[◯p→r, ◯q→r] K=[] @400k" (cellB [hyp, hypQ] [hypQ] aP [])
  pr2 "[◯p→r] joinχ [◯p→◯p] K=[] @400k" (cellB [joinP, hyp] [hyp] aP [])
  pr2 "[GZ2 ◯↓◯p→r, ◯p] K=[] @400k" (cellB [cimpNest, boxP] [boxP] (.down (.circ aP)) [])
  IO.println "ESC-DONE"
