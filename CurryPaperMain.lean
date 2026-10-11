import VersoManual
import VersoBlueprint.PreviewManifest
import CurryPaper.Paper

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc CurryPaper.Paper)
    args
    (extensionImpls := by exact extension_impls%)
