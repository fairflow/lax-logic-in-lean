import VersoManual
import SemPaper.Paper

open Verso.Genre.Manual

/-- Vanilla Verso (Manual genre): HTML and TeX from one source.  Render with
`scripts/sem-paper.sh`. -/
def main (args : List String) : IO UInt32 :=
  manualMain (%doc SemPaper.Paper) (options := args)
    (config := { sourceLink := some "https://github.com/fairflow/lax-logic-in-lean",
                 issueLink := some "https://github.com/fairflow/lax-logic-in-lean/issues" })
