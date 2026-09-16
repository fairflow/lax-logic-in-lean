/- Native driver for the CimpAnt frontier attack + the φ★ cross-check.
Compiled (the repo's oracle pattern): `lake build attackrun` then
`.lake/build/bin/attackrun`.  Streams chunk results as they finish. -/
import wip.ljfo_attack
import wip.ljfo_crosscheck

open LJFOAttack

def pr {α : Type} [Repr α] (label : String) (x : α) : IO Unit := do
  IO.println s!"== {label}"
  IO.println (repr x)
  (← IO.getStdout).flush

def main : IO Unit := do
  pr "phistar: sum3, szE" (X.sum3probe, X.szEprobe)
  pr "phistar: ¬¬◯⊥ ⊢ E (soundness dir)" (X.verdict [X.nnOBot] (X.negF X.E))
  pr "phistar: E ⊢ ¬¬◯⊥ @40k (minimality dir)" (X.verdict [X.negF X.E] X.nnOBot)
  pr "cimp small A (controls+boundary+p-placements)" (runChunk (smallBank.take 11))
  pr "cimp small B (crossed-χ, size-3, GZ2, or-family)" (runChunk (smallBank.drop 11))
  pr "cimp mid (no-row corner, GZ3, unboxed blocker)" (runChunk midBank)
  pr "cimp horizon (reported only)" (runChunk horizonBank)
  pr "minimality small A" (runMinChunk (smallBank.take 11))
  pr "minimality small B" (runMinChunk (smallBank.drop 11))
  pr "phistar: E ⊢ ¬¬◯⊥ @400k (escalation)" (X.verdictBig [X.negF X.E] X.nnOBot)
  IO.println "ALL-DONE"
