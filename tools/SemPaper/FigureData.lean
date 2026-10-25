/-
The data of the semantics paper's figure (2026-10-24), computed by Lean.

    lake env lean tools/SemPaper/FigureData.lean

prints one line `SEMFIGURES <json>` that `scripts/sem-figures.py` turns into
the figure.  Nothing in it is typed by hand:

* the countermodel is the `SubCM` certificate inside the proof of `fact_24`
  (`LaxLogic/PLL/SubTab/Facts.lean`: `⊬ ◯(p ∨ q) ↠ ◯p ∨ ◯q`, produced by the
  subframe tableau engine and checked by the kernel), read from the proof
  term and evaluated;
* its order is drawn by its covering pairs, computed here from the table;
* the formulas written at each world are the atoms and the `◯`-subformulas
  of the refuted formula, each with its forcing at that world computed by
  `SubCM.forceB`, the evaluator the kernel check runs; `SubCM.refutes` is
  evaluated again.
-/
import LaxLogic.PLL.SubTab.Facts
import LaxLogic.PLL.SubTab.Steps

open Lean Meta Elab Command
open PLLND PLLND.SubTab

/-- A formula as a JSON tree. -/
def fJson : PLLFormula → Json
  | .falsePLL => Json.mkObj [("op", "bot")]
  | .prop a => Json.mkObj [("op", "atom"), ("name", Json.str a)]
  | .and a b => Json.mkObj [("op", "and"), ("args", Json.arr #[fJson a, fJson b])]
  | .or a b => Json.mkObj [("op", "or"), ("args", Json.arr #[fJson a, fJson b])]
  | .ifThen a b => Json.mkObj [("op", "imp"), ("args", Json.arr #[fJson a, fJson b])]
  | .somehow a => Json.mkObj [("op", "box"), ("args", Json.arr #[fJson a])]

/-- The atoms, then the `◯`-subformulas, of a formula, without repetition. -/
def shown (φ : PLLFormula) : List PLLFormula :=
  let all := subs φ
  let atoms := all.filter fun | .prop _ => true | _ => false
  let boxes := all.filter fun | .somehow _ => true | _ => false
  (atoms ++ boxes).eraseDups

/-- The covering pairs of the order of the table. -/
def covers (m : SubCM) : List (Nat × Nat) :=
  (List.range m.n).flatMap fun i => ((List.range m.n).filter fun j =>
    i != j && m.leB i j &&
      !((List.range m.n).any fun k => k != i && k != j && m.leB i k && m.leB k j)).map (i, ·)

unsafe def emit : MetaM Unit := do
  let ci ← getConstInfo `fact_24
  let .thmInfo ti := ci | throwError "fact_24 is not a theorem"
  let v := ti.value
  -- the proof is `no.verdict φ m _`: its formula and its countermodel
  let mut phiE? : Option Expr := none
  let mut cmE? : Option Expr := none
  for a in v.getAppArgs do
    let ty ← whnf (← inferType a)
    if ty.isConstOf ``PLLFormula then phiE? := some a
    if ty.isConstOf ``SubCM then cmE? := some a
  let some phiE := phiE? | throwError "no formula argument"
  let some cmE := cmE? | throwError "no countermodel argument"
  let φ ← evalExpr PLLFormula (mkConst ``PLLFormula) phiE
  let m ← evalExpr SubCM (mkConst ``SubCM) cmE
  let worlds := (List.range m.n).map fun i =>
    Json.mkObj [("S", toJson (m.SB i)), ("val", toJson (m.val.getD i [])),
      ("forced", Json.arr ((shown φ).map fun ψ => toJson (m.forceB i ψ)).toArray)]
  let data := Json.mkObj [
    ("theorem", "fact_24"),
    ("formula", fJson φ),
    ("shown", Json.arr ((shown φ).map fJson).toArray),
    ("root", toJson m.root),
    ("refutes", toJson (m.refutes φ)),
    ("rootForcesFormula", toJson (m.forceB m.root φ)),
    ("covers", toJson ((covers m).map fun (i, j) => #[i, j])),
    ("worlds", Json.arr worlds.toArray)]
  IO.println ("SEMFIGURES " ++ data.compress)

#eval emit
