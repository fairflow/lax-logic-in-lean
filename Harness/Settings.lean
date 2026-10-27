import Harness.Tools

/-! # Lean certify settings for lax-logic-in-lean: the project's decider

2026-10-27 (F0 plan step 4; `docs/engine-adoption-statements.md` §3 and §9,
`docs/f0-step4-STATUS.md`).  The one project-wide settings file: the
executable `plldecide` (`Harness/Main.lean`) reads it.  Edit only the lines
marked EDIT.  A tool is named by a string from `Harness.tools`; a misspelt
name is an error when this file is compiled (`#certify_decider`).  To fall
back on one side only, repeat the other side's tool in the pair.  For
readers who do not know Lean: `docs/deciders.md` in lean-certify.

**THE ORDER OF THE PAIRS IS PROVISIONAL.**  It is set by the pre-registered
comparison (gate G4), whose result is recorded in TOOLS.md, never chosen
here by hand.  Until then the first two pairs are those of
`tools/SubTab/Settings.lean` (`subtabdecide`), unchanged, and the pair of
the engines adopted in step 4 is appended.  The tableau's producer ignores
the budget and always returns a certificate (`pass` or `fail`, never
`flag`), so a pair after `("subtab", "subtab")` is reached only when a
certificate is REJECTED (a tool defect); whether the tableau gets a budget
or the last place is decision M6.

This file and `tools/SubTab/Settings.lean` both declare `Harness.tools` and
`Harness.decider`, so no module may import both.  `Harness.config` (read by
the lints) is the one in `CertifyAdoption.lean`, imported through
`Harness.Tools`. -/

open PLLND.SubTab PLLDecider

/-- The tools this project offers, by name (written once, by the project). -/
def Harness.tools : Harness.Registry PLLFormula Holds :=
  [ .pair "subtab" (Certify.Prover.ofEngine engine "subtab")
      (Certify.Disprover.ofEngine engine "subtab"),
    .disprover "enum" enumDisprover,
    .disprover "fincm" fincmDisprover,
    .prover "ljfo" ljfoProver ]
  -- "g4c" (M2), "frjw" (M4, M8) and "reject" (M3, M8) wait for Matthew;
  -- "f0db", the F0 database engine, is step 6 of the plan.

/-- The decider.  PROVISIONAL ORDER, until the comparison (G4). -/
def Harness.decider : Harness.DeciderConfig where
  prover    := "subtab"                                   -- EDIT
  disprover := "enum"                                     -- EDIT
  fallback  := [("subtab", "subtab"), ("ljfo", "fincm")]  -- EDIT: pairs, tried in order
  run       := { mode := .race,                           -- EDIT: .race | .sequential
                 budget := 1000,
                 flagReruns := 0,
                 budgetFactor := 4,
                 deadlineSec := 120 }

#certify_decider Harness.decider           -- checks every name against Harness.tools
