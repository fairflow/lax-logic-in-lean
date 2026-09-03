/-
# `lake exe pll` entry point

Split from `tools/Decide.lean` on 2026-09-03 so that `Decide` exports no
root `main`: `tools/Bench.lean` imports it for the formula parser and the
`Answer` seam, and two root `main`s in one import closure is an error.
-/
import tools.Decide

def main (args : List String) : IO UInt32 := do
  match PLLTools.parseArgs args with
  | .error e =>
      IO.println s!"error: {e}"
      IO.println "usage: lake exe pll \"◯p ⊃ p\" [--out=NAME] [--view=min|calc|both] \
[--check] [--check-term] [--proof-object] [--rounds=N] [--jmax=N] [--pmax=N] \
[--lamCap=N] [--maxRS=N] [--maxIS=N]"
      return 2
  | .ok (f, a) => PLLTools.run f a
