import LaxLogic.PLL.Syntax.Parse
import LaxLogic.PLL.SubTab.Sound

/-!
# Certificates of the subframe tableau as Lean source (library, no `main`)

The two source printers of the tableau's certificates, used by `refbench fact`
to write the facts of `LaxLogic/PLL/SubTab/Facts.lean`, and the `Repr` instance
of `TCert`.  They print formulas with `PLLTools.srcOfP`
(`LaxLogic/PLL/Syntax/Parse.lean`, within `[propext]`).  Split out of
`Tableau.lean` into `tools/SubTab/Source.lean` on 2026-10-22, because `srcOfP`
was then in `tools/Decide.lean`; moved here on 2026-10-27, when `srcOfP` moved
to the library (F0 re-implementation plan, step 3).  Names unchanged.
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

/-- A closed tableau prints as the Lean source `tcertSrc` writes.  Written by
hand (2026-10-27): the instance that `deriving Repr` gave `TCert` printed
formulas through `PLLFormula`'s `Repr`, which reaches `Classical.choice`
(`PLLFormula.toString`, then `stripParens` and Lean's `String.Slice` lemmas),
and was removed on 2026-10-22. -/
instance instReprTCert : Repr PLLND.SubTab.TCert where
  reprPrec c _ := Std.Format.text (tcertSrc c)

end SubTab
