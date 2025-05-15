import LaxLogic.FormattingUtils
import Mathlib.Tactic
inductive PLLFormula where
| prop (constantName: String)
| falsePLL
| and (a: PLLFormula)(b: PLLFormula)
| or (a: PLLFormula)(b: PLLFormula)
| ifThen (antecedant: PLLFormula)(consequent: PLLFormula)
| somehow (a: PLLFormula)
deriving Inhabited, DecidableEq

open Std (Format)
namespace PLLFormula


abbrev notPLL (F: PLLFormula) : PLLFormula := ifThen F falsePLL
def PropositionalConstant := {F: PLLFormula // ∃ (name:String ), F =  prop name }

-- I originally used a sub-type for this, but I could not figure out how to derive DecidableEq
inductive Conditional where
| mk (F: PLLFormula) (h: ∃ (P Q:PLLFormula), F = ifThen P Q)
deriving DecidableEq

def Conditional.val (C: Conditional) :=
match C with
 | mk F _ => F

def Conditional.prop (C: Conditional):  ∃ P Q, C.val = ifThen P Q :=
match C with
 | mk _ h => h


def Conditional.antecedant (F: Conditional) :=
 match F with
 | ⟨ifThen P _, _ ⟩  => P
 | _ => F.val -- This case is never reached due to the property

def Conditional.consequent (F: Conditional) :=
 match F with
 | ⟨ifThen _ Q, _ ⟩  => Q
 | _ => F.val -- This case is never reached due to the property

private def parens (f : Format) : Format :=
  Format.text "(" ++ f ++ Format.text ")"

/-- Pretty-printer using the required logical symbols. -/
private def reprAux : PLLFormula → Nat → Format
| prop s,        _ => Format.text s
| falsePLL,      _ => Format.text "False"
| and p q,       _ => parens (reprAux p 0 ++ Format.text " ∧ " ++ reprAux q 0)
| or  p q,       _ => parens (reprAux p 0 ++ Format.text " ∨ " ++ reprAux q 0)
| ifThen p q,    _ => parens (reprAux p 0 ++ Format.text " ⊃  " ++ reprAux q 0) -- Symbol shortcut is \ssup
| somehow p,     _ => parens (Format.text "◯" ++ reprAux p 0)

/-- `Repr` instance that first prints with `reprAux` and then
    strips one pair of outer parentheses. -/
instance : Repr PLLFormula where
  reprPrec := stripParens reprAux

-- Demontstrating Repr
#eval (ifThen (prop "P") (somehow (and (prop "Q") falsePLL))) -- removes outer parents form
#eval prop "P" -- deals with no parens


end PLLFormula
