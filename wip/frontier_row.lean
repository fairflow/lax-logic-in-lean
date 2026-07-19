import LaxLogic.PLLSearch
import LaxLogic.PLLSemUILaw

/-!
# The frontier row `((p⊃◯⊥)⊃p)⊃p`, investigated

The corrected-law sweep left exactly one ∀-side UNKNOWN at weight 8.
Hand analysis predicts: every closed substitution instance of the row
collapses to ⊤; both transforms `lowT`, `sideT` are equivalent to
¬¬◯⊥; the true ∀p-value is ◯⊥; and the law-refuting countermodel is
the RIGID-Rₘ 3-chain (0 < 1 < 2, Rₘ = identity, top fallible, p at
{1,2}) — a frame the default battery does not contain, which is why
the sweep said UNKNOWN.  This probe machine-checks each prediction,
exercising `PLLSearch`'s extensible `Config` for the missing frame.

Run compiled: `lake build frontrow && .lake/build/bin/frontrow`.
-/

open PLLFormula PLLND PLLND.Search PLLND.SemUI

namespace FrontierRow

def pV : PLLFormula := .prop "p"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL

/-- The frontier row. -/
def M0 : PLLFormula := ((pV.ifThen gB).ifThen pV).ifThen pV

/-- The seven rungs of the closed ladder at weight ≤ 8. -/
def rungs : List (String × PLLFormula) :=
  [("⊥", .falsePLL), ("◯⊥", gB), ("⊤", truePLL), ("¬◯⊥", nF gB),
   ("◯¬◯⊥", (nF gB).somehow), ("¬¬◯⊥", nF (nF gB)),
   ("¬◯⊥∨◯⊥", (nF gB).or gB)]

/-- The rigid-Rₘ 3-chain missing from the default battery. -/
def rigidChain3 : Frame := ⟨3, [(0,1),(1,2),(0,2)], [], [2]⟩

def extCfg : Config := { frames := defaultFrames ++ [rigidChain3] }

def prov (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  (prove? Γ C).isSome

def showW {Γ C} : Option (Witness Γ C) → String
  | some ⟨M, w, _⟩ => s!"REFUTED (n={M.n} ri={M.ri} rm={M.rm} fall={M.fall} val={M.val} @w{w})"
  | none => "no countermodel found (battery+emit)"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== the frontier row ((p⊃◯⊥)⊃p)⊃p =="
  -- (a) substitution instances collapse to ⊤
  for (nm, χ) in rungs.take 3 do
    let inst := substP "p" χ M0
    pl s!"(a) M0[{nm}]: derivable = {prov [] inst}"
  -- (b) the transforms are ¬¬◯⊥
  let lo := lowT "p" M0
  let si := sideT "p" M0
  let nn := nF (nF gB)
  pl s!"(b) lowT  ≡ ¬¬◯⊥: {prov [lo] nn} ∧ {prov [nn] lo}   (lowT = {lo.toString})"
  pl s!"    sideT ≡ ¬¬◯⊥: {prov [si] nn} ∧ {prov [nn] si}"
  -- (c) the rung scan: which rungs derive M0
  for (nm, χ) in rungs do
    pl s!"(c) [{nm}] ⊢ M0: {prov [χ] M0}"
  -- (d) the law sequent: countermodel hunt ONLY (`refute?` cannot
  -- grind — the earlier `decide` version froze in the find fallback
  -- on this unprovable raw sequent)
  let vd := refute? extCfg (poolAll "p" M0) M0
  pl s!"(d) poolAll ⊢ M0 (extended battery): {showW vd}"
  -- (e) the same countermodel separates ¬¬◯⊥ from M0
  let ve := refute? extCfg [nn] M0
  pl s!"(e) [¬¬◯⊥] ⊢ M0 (extended battery): {showW ve}"
  -- (f) control: the default battery misses it
  let vf := refute? {} (poolAll "p" M0) M0
  pl s!"(f) poolAll ⊢ M0 (default battery): {showW vf}"
  pl "== done =="

end FrontierRow

def main : IO Unit := FrontierRow.main
