import tools.SubTab.Settings
import LaxLogic.PLL.Syntax.Parse

/-! `subtabdecide "<formula>"`: the lean-certify decider of
`tools/SubTab/Settings.lean`.  2026-10-15.  Since 2026-10-27 the parser is the
library's (`LaxLogic/PLL/Syntax/Parse.lean`), so the import closure holds no
`wip/` module and no `tools/` module but the settings. -/

def main (args : List String) : IO UInt32 :=
  Certify.Cli.main Harness.tools PLLTools.parseFormula Harness.decider args
