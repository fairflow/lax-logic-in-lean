import tools.SubTab.Settings
import tools.Decide

/-! `subtabdecide "<formula>"`: the lean-certify decider of
`tools/SubTab/Settings.lean`.  2026-10-15. -/

def main (args : List String) : IO UInt32 :=
  Certify.Cli.main Harness.tools PLLTools.parseFormula Harness.decider args
