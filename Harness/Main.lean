import Harness.Settings
import LaxLogic.PLL.Syntax.Parse

/-! `plldecide "<formula>"`: the project's lean-certify decider, configured by
`Harness/Settings.lean`.  2026-10-27 (F0 plan step 4).  The entry point only:
a library module must not declare a root-level `main` (TOOLS.md §6), so this
module is the executable's root and is outside the `Harness` library.

Exit codes are lean-certify's: 0 yes, 1 no, 2 usage or parse error, 3 flag
(not decided within the budgets and the deadline; never a verdict).  They
differ from `pll`'s and `pllfast`'s.  Options for one run: `--deadline=N`,
`--budget=N`, `--mode=race|sequential`; `--json` prints the settings.

**The process exits as soon as the answer is printed.**  In race mode
lean-certify v0.3's `Decider.run` returns at the first certified answer or
at the deadline, but the other producer's thread runs on, and the Lean
runtime waits for every running task before the process ends.  Watched
2026-10-27 (`docs/f0-step4-STATUS.md`): `ljfo` forced alone on Peirce's law
with `--deadline=5` printed `FLAG` at 5.04 s, and the process lived until
`gtimeout` killed it at 30 s, its piped output lost.  So `main` flushes
standard output and calls `IO.Process.exit` with the decider's code; the
deadline then bounds the run.  (In sequential mode the deadline is checked
only between attempts, so a producer can still run past it.) -/

def main (args : List String) : IO UInt32 := do
  let rc ← Certify.Cli.main Harness.tools PLLTools.parseFormula Harness.decider args
  (← IO.getStdout).flush
  IO.Process.exit rc.toUInt8
