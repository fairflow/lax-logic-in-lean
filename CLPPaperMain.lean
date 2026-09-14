import VersoManual
import CLPPaper.Paper

open Verso.Genre.Manual

/-- Vanilla Verso (Manual genre): HTML and TeX from one source.  Render with
`scripts/clp-paper.sh`. -/
def main (args : List String) : IO UInt32 :=
  manualMain (%doc CLPPaper.Paper) (options := args)
