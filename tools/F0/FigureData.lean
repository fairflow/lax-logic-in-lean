/-
The data of the F0 paper's figures (v0.3, 2026-10-23), computed by Lean.

    lake env lean tools/F0/FigureData.lean

prints one line `F0FIGURES <json>` that `scripts/f0-figures.py` turns into
the figures.  Nothing in a figure is typed by hand:

* `rungs`: the covering pairs of the rung order on `t₀ … t₁₁` (and on
  `t₀ … t₇`, `t₀ … t₅`; v0.4 draws the self-similarity ladders on six
  rungs, so that the figure fits the text block with labels at text size),
  decided by `rungCovers`, which is `rungLe` (`wip/ladder8.lean`);
  `rnSub_order` proves `rungLe i j = true ↔ t_i ⊢ t_j`;
* `bottom`: the elements of `↓t₅` (the list `D5_list` of `wip/f0Covers.lean`,
  each matched to its rung) and the cover theorems of that file, read off
  their types `Covers (rnSub i) (rnSub j)`;
* `formulas`: the formula trees of `t₀ … t₅`, for the labels;
* `selfsim`: `σ(⊥) = t₃` and `σ(t₃) = ◯t₃ ∨ g₁`, decided by `decide` on the
  formula trees (`sig_t3` proves the second by `rfl`).
-/
import wip.f0Covers
import wip.ladder8
import wip.f0SelfSim

open Lean Meta Elab Command
open PLLND PLLND.F0 PLLND.RNEmbed

/-- A formula as a JSON tree. -/
def fJson : PLLFormula → Json
  | .falsePLL => Json.mkObj [("op", "bot")]
  | .prop a => Json.mkObj [("op", "atom"), ("name", Json.str a)]
  | .and a b => Json.mkObj [("op", "and"), ("args", Json.arr #[fJson a, fJson b])]
  | .or a b => Json.mkObj [("op", "or"), ("args", Json.arr #[fJson a, fJson b])]
  | .ifThen a b => Json.mkObj [("op", "imp"), ("args", Json.arr #[fJson a, fJson b])]
  | .somehow a => Json.mkObj [("op", "box"), ("args", Json.arr #[fJson a])]

/-- The rung index of a formula among `t₀ … t₁₁`, if it is one. -/
def rungIndex (φ : PLLFormula) : Option Nat :=
  (List.range 12).find? fun k => decide (rnSub k = φ)

/-- The covering pairs of the rung order on `t₀ … t_{b-1}`. -/
def rungCoverPairs (b : Nat) : List (Nat × Nat) :=
  (List.range b).flatMap fun i =>
    ((List.range b).filter fun j => rungCovers b i j).map fun j => (i, j)

/-- `Covers (rnSub i) (rnSub j)` with numerals `i`, `j`, read off a type. -/
def coverPair? (ty : Expr) : Option (Nat × Nat) :=
  match ty.consumeMData.getAppFnArgs with
  | (``PLLND.F0.Covers, #[u, v]) =>
    match u.consumeMData.getAppFnArgs, v.consumeMData.getAppFnArgs with
    | (``PLLND.RNEmbed.rnSub, #[i]), (``PLLND.RNEmbed.rnSub, #[j]) =>
      match i.consumeMData.rawNatLit?, j.consumeMData.rawNatLit?,
        i.consumeMData.nat?, j.consumeMData.nat? with
      | some a, some b, _, _ => some (a, b)
      | _, _, some a, some b => some (a, b)
      | _, _, _, _ => none
    | _, _ => none
  | _ => none

/-- The cover theorems of `wip/f0Covers.lean`, with their pairs. -/
def coverTheorems : CommandElabM (Array (Name × Nat × Nat)) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? `wip.f0Covers | throwError "wip.f0Covers is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  let mut out := #[]
  for n in names do
    if let some (.thmInfo ti) := env.find? n then
      if let some (i, j) := coverPair? ti.type then
        out := out.push (n, i, j)
  return out

#eval show CommandElabM Unit from do
  let covers ← coverTheorems
  let coverJson := covers.map fun (n, i, j) =>
    Json.mkObj [("theorem", Json.str n.toString), ("lo", toJson i), ("hi", toJson j)]
  let bottomNodes := D5_list.filterMap rungIndex
  let pairs (b : Nat) := toJson ((rungCoverPairs b).map fun (i, j) => #[i, j])
  let data := Json.mkObj [
    ("rungs12", pairs 12),
    ("rungs8", pairs 8),
    ("rungs6", pairs 6),
    ("bottomNodes", toJson bottomNodes),
    ("bottomListLength", toJson D5_list.length),
    ("covers", Json.arr coverJson),
    ("formulas", Json.arr ((List.range 6).map fun k => fJson (rnSub k)).toArray),
    ("sigBotIsT3", toJson (decide (Sig.sig .falsePLL = F0.t3))),
    ("sigT3IsC1OrG1", toJson (decide (Sig.sig F0.t3 = (chainF 1).or (gap 1))))]
  IO.println ("F0FIGURES " ++ data.compress)
