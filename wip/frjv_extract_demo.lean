/-
# The FRJ◯-native direction, demonstrated: derivation ⟶ countermodel

The four hand witnesses were built MODEL-FIRST (the countermodels were
banked a day earlier by the battery/Tab machinery; the trees transcribe
them).  FRJ◯'s own constructive content runs the OTHER way: `modR`
extracts a Kripke countermodel FROM a refutation derivation — the
computational heart of `soundnessV`.  This demo closes the circle: it
runs `modR` on the hand-built proof term `W1918.goal` and prints the
extracted model, to compare with the banked battery frame `sep-86`
(5 worlds: root, bad world, ¬a-world, fallible top, a-world).
-/
import FRJ.WitnessV1918
import FRJ.ExtractV

open FRJ FRJ.V FRJ.WitnessV1918

def M : Kripke := modR W1918.goal

def n : Nat := M.elems.length

def idxOf (w : M.W) : Nat :=
  (M.elems.zipIdx.find? (fun p => decide (p.1 = w))).map (·.2) |>.getD 999

#eval s!"worlds: {n}"
#eval s!"root: {idxOf M.root}"
#eval "le matrix (row w ≤ column v):"
#eval M.elems.map (fun w => M.elems.map (fun v => decide (M.le w v)))
#eval "Rm matrix:"
#eval M.elems.map (fun w => M.elems.map (fun v => decide (M.Rm w v)))
#eval "fallible:"
#eval M.elems.map (fun w => decide (M.Fal w))

-- the control: the extracted model REFUTES the goal at its root
-- (this is soundnessV's computational content, displayed)
#eval decide (M.force M.root G1918)
