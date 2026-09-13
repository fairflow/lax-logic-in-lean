import VersoManual
import VersoBlueprint.PreviewManifest
import CLPPaper.Paper

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc CLPPaper.Paper)
    args
    (extensionImpls := by exact extension_impls%)
