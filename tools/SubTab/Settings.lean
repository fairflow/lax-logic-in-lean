import tools.SubTab.Engine

/-! # Lean certify settings for the subframe-tableau decider

2026-10-15.  Edit only the lines marked EDIT.  A tool is named by
a string from `Harness.tools`; a misspelt name is an error when this file
is compiled (`#certify_decider`).  To fall back on one side only, repeat
the other side's tool in the pair.  For readers who do not know Lean:
`docs/deciders.md` in lean-certify. -/

open PLLND.SubTab

/-- The finite-model enumeration as a disprover: smallest-first models on
at most 6 worlds, at most `50 · budget` models, as `SubCM` tables (no
fallible world). -/
def enumDisprover : Certify.Disprover PLLFormula Holds where
  name := "enum"
  RCert := SubCM
  certifier := no
  produce φ b := (PllFast.firstHitCap φ 6 (50 * b)).map
    fun m => PllFast.bmToSubCM m (PllFast.atomsL φ).eraseDups

/-- The tools this project offers, by name (written once, by the project). -/
def Harness.tools : Harness.Registry PLLFormula Holds :=
  [ .pair "subtab" (Certify.Prover.ofEngine engine "subtab")
      (Certify.Disprover.ofEngine engine "subtab"),
    .disprover "enum" enumDisprover ]

/-- The decider: the tableau proves; small countermodels come from the
enumeration (minimal certificates), large ones from the tableau. -/
def Harness.decider : Harness.DeciderConfig where
  prover    := "subtab"                    -- EDIT
  disprover := "enum"                      -- EDIT
  fallback  := [("subtab", "subtab")]      -- EDIT: pairs, tried in order
  run       := { mode := .race,            -- EDIT: .race | .sequential
                 budget := 1000,
                 flagReruns := 0,
                 deadlineSec := 120 }

#certify_decider Harness.decider           -- checks every name against Harness.tools
