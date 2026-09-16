/-
# `#decide` — the decider as an elaboration-time command

    #decide φ to "out.svg"                -- view = min (the default)
    #decide φ to "out.svg" view calc
    #decide φ to "out.svg" view both      -- writes out.min.svg AND out.calc.svg

`φ` is a `PLLFormula` term.  Runs the untrusted W-engine at the default
budget, certifies its store with the VERIFIED `checkClosed`, decides, and
for a refuted formula writes the countermodel SVG(s) and prints the
verdict; for a proved one prints the `Tm` proof term.  The engine runs
INTERPRETED here, so use it on small formulas; `lake exe pll` is the
compiled tool and the one that emits kernel-checked certificates.

Modelled on `#draw` (`LaxLogic/PLLDiagramCmd.lean`).  A scan of the
`command` parser category found no existing `#decide`
(`docs/decider-outputs-design.md` §6, D5).
-/
import tools.Decide

/-- `#decide φ to "out.svg"` — decide `φ`, draw the (minimised)
countermodel if refuted, print the proof term if proved. -/
macro (name := decideCmd) "#decide " φ:term " to " path:term : command =>
  `(command| #eval (do
      IO.println (← PLLTools.decideReport $φ $path "min") : IO Unit))

@[inherit_doc decideCmd]
macro "#decide " φ:term " to " path:term " view " v:ident : command =>
  `(command| #eval (do
      IO.println (← PLLTools.decideReport $φ $path
        $(Lean.quote v.getId.toString)) : IO Unit))
