import tools.Decide
import LaxLogic.PLL.SubTab.Sound

/-!
# Certificates of the subframe tableau as Lean source (library, no `main`)

The two source printers of the tableau's certificates, used by `refbench fact`
to write the facts of `LaxLogic/PLL/SubTab/Facts.lean`.  They print formulas
with `pll`'s printer `PLLTools.srcOfP`, so they stay in `tools/` when the
tableau itself is in the library (split out of `Tableau.lean` 2026-10-22,
names unchanged).
-/

namespace SubTab

/-- A closed tableau as Lean source (expected type `TCert`). -/
def tcertSrc : PLLND.SubTab.TCert → String
  | .bot => ".bot"
  | .ax A => s!"(.ax {PLLTools.srcOfP A})"
  | .andL A B c => s!"(.andL {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c})"
  | .orL A B c₁ c₂ => s!"(.orL {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c₁} {tcertSrc c₂})"
  | .impL A B c₁ c₂ => s!"(.impL {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c₁} {tcertSrc c₂})"
  | .boxL A c => s!"(.boxL {PLLTools.srcOfP A} {tcertSrc c})"
  | .andR A B c₁ c₂ => s!"(.andR {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c₁} {tcertSrc c₂})"
  | .orR A B c => s!"(.orR {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c})"
  | .impLoc A B c => s!"(.impLoc {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c})"
  | .boxLoc A c => s!"(.boxLoc {PLLTools.srcOfP A} {tcertSrc c})"
  | .impR A B c => s!"(.impR {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c})"
  | .boxR A c => s!"(.boxR {PLLTools.srcOfP A} {tcertSrc c})"

/-- Countermodel tables as Lean source (expected type `SubCM`). -/
def subcmSrc (m : PLLND.SubTab.SubCM) : String :=
  s!"\{ n := {m.n}, root := {m.root}, le := {m.le}, S := {m.S}, val := {repr m.val} }"

end SubTab
