import LaxLogic.PLL.SubTab.Explore
import ProofTools.Explore

/-!
# The tactic `subtab`: the subframe tableau, a move at a time

2026-11-19.  `subtab` is `apply_move` of `proof-tools`, fixed to the proof
system `STab` of `Explore.lean`:

    subtab m          make the move `m` at the first goal
    subtab m at k     at goal `k`
    subtab            offer the moves that apply; make none
    subtab an         offer those whose names begin with `an`

A goal is an attempt `Att STab true s` or a derivation `Der STab s`, shown
as its sequent: `Γ ⇒ Δ` at a world outside S, `Γ ⇒ ◯[Δ]` at an S-point,
after the reading of a signed sequent (`Translate.lean`).

This file is code for the editor; none of it is trusted.  The node the
tactic builds carries the equation `STab.step m s = .ok ps`, which the
kernel proves by evaluating `step`.

**Atoms by name.**  A move is suggested in the notation of `PLLND`, an atom
`.prop "p"` as `p`.  So a file that uses `subtab` declares its atoms under
their own names: `def p : PLLFormula := .prop "p"`.
-/

open PLLFormula ProofTools

namespace PLLND
namespace SubTab

/-! ## A sequent and a move as text -/

/-- A list of formulas, with commas. -/
def showFs (l : List PLLFormula) : String := ", ".intercalate (l.map showF)

/-- A sequent: `Γ ⇒ Δ`, or `Γ ⇒ ◯[Δ]` at an S-point. -/
def showS (s : SSeq) : String :=
  let l := showFs s.ant
  let r := if s.isS then "◯[" ++ showFs s.suc ++ "]" else showFs s.suc
  (if l.isEmpty then "" else l ++ " ") ++ "⇒" ++ (if r.isEmpty then "" else " " ++ r)

/-- A formula as an argument: in parentheses unless an atom or `⊥`. -/
def argF : PLLFormula → String
  | .prop a => a
  | .falsePLL => "⊥"
  | .somehow A => "(" ++ showF (.somehow A) ++ ")"
  | X => showF X

/-- A move as Lean source, with the constructors of `Move` open. -/
def Move.src : Move → String
  | .bot => "bot"
  | .ax A => s!"ax {argF A}"
  | .andL A B => s!"andL {argF A} {argF B}"
  | .orL A B => s!"orL {argF A} {argF B}"
  | .impL A B => s!"impL {argF A} {argF B}"
  | .boxL A => s!"boxL {argF A}"
  | .andR A B => s!"andR {argF A} {argF B}"
  | .orR A B => s!"orR {argF A} {argF B}"
  | .impLoc A B => s!"impLoc {argF A} {argF B}"
  | .boxLoc A => s!"boxLoc {argF A}"
  | .impR A B => s!"impR {argF A} {argF B}"
  | .boxR A => s!"boxR {argF A}"

/-! ## The moves to propose -/

/-- The moves a true formula suggests. -/
def movesL : PLLFormula → List Move
  | .and A B => [.andL A B]
  | .or A B => [.orL A B]
  | .ifThen A B => [.impL A B]
  | .somehow A => [.boxL A]
  | _ => []

/-- The moves a false formula suggests: the local rule, then the rule that
makes a new world. -/
def movesR : PLLFormula → List Move
  | .and A B => [.andR A B]
  | .or A B => [.orR A B]
  | .ifThen A B => [.impLoc A B, .impR A B]
  | .somehow A => [.boxLoc A, .boxR A]
  | _ => []

/-- **The moves that apply at a sequent**: the closing rules first, then
the rules of the true formulas, then those of the false ones. -/
def candidates (s : SSeq) : List Move :=
  let close := (if mem .falsePLL s.ant then [Move.bot] else []) ++
    (s.ant.filter fun A => mem A s.suc).map Move.ax
  ((close ++ s.ant.flatMap movesL ++ s.suc.flatMap movesR).eraseDups).filter
    fun m => (m.rule s).ok

/-- A premise adds nothing to its conclusion: the same kind of world, and
no formula that was not there. -/
def within (p j : SSeq) : Bool :=
  p.isS == j.isS && p.ant.all (fun A => mem A j.ant) && p.suc.all (fun A => mem A j.suc)

deriving instance Lean.ToExpr for PLLFormula
deriving instance Lean.ToExpr for SSeq
deriving instance Lean.ToExpr for Move

instance : Explore.Explorable STab where
  candidates := candidates
  showJudg := showS
  showMove := Move.src
  quoteJudg := inferInstanceAs (Lean.ToExpr SSeq)
  quoteMove := inferInstanceAs (Lean.ToExpr Move)
  within := within
  moveSource m := some m.src

open Lean Meta Elab

declare_move_tactic subtab for STab

/-- See `evalSSeq`. -/
unsafe def evalSSeqU (e : Expr) : MetaM SSeq := evalExpr SSeq (mkConst ``SSeq) e
/-- Evaluate a closed term of type `SSeq`. -/
@[implemented_by evalSSeqU] opaque evalSSeq (e : Expr) : MetaM SSeq

open PrettyPrinter Delaborator SubExpr in
/-- A goal `Att STab o s` with a closed `s`, shown as the sequent. -/
@[delab app.ProofTools.Explore.Att]
def delabGoal : Delab := do
  let e ← getExpr
  let some (o, s) := (match e.getAppFnArgs with
    | (``Explore.Att, #[sys, o, s]) => if sys.isConstOf ``STab then some (o, s) else none
    | _ => none) | failure
  if s.hasLooseBVars || s.hasFVar || s.hasMVar then failure
  let seq ← try evalSSeq s catch _ => failure
  let head := if o.isConstOf ``Bool.true then "Att STab" else "Der STab"
  let text := head ++ "   " ++ showS seq
  return ⟨Syntax.node .none strLitKind #[Syntax.atom .none text]⟩

end SubTab
end PLLND
