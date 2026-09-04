import VersoManual
import VersoBlueprint.PreviewManifest
import LaxBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LaxBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
