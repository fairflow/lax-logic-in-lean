import LaxLogic.Util.FormattingUtils
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

-- We use false implies false to as our cannoncial true value.
abbrev truePLL := ifThen falsePLL falsePLL

def PropositionalConstant := {F: PLLFormula // ∃ (name:String ), F =  prop name }

-- I originally used a sub-type for this, but I could not figure out how to derive DecidableEq
inductive Conditional where
| mk (F: PLLFormula) (h: ∃ (P Q:PLLFormula), F = ifThen P Q)
deriving DecidableEq

@[simp]
def Conditional.val (C: Conditional) :=
match C with
 | mk F _ => F

@[simp]
def Conditional.prop (C: Conditional):  ∃ P Q, C.val = ifThen P Q :=
match C with
 | mk _ h => h

instance : BEq Conditional where
  beq c1 c2 :=  c1.val == c2.val

@[simp]
def Conditional.antecedant (F: Conditional) :=
 match F with
  | ⟨ifThen P _, _ ⟩  => P
  | ⟨PLLFormula.prop _, p⟩ => by simp_all only [reduceCtorEq, exists_const]
  | ⟨falsePLL, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨and a b, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨or a b, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨somehow a, p⟩ => by simp_all only [reduceCtorEq, exists_const]

@[simp]
def Conditional.consequent (F: Conditional) :=
 match F with
 | ⟨ifThen _ Q, _ ⟩  => Q
 | ⟨PLLFormula.prop _, p⟩ => by simp_all only [reduceCtorEq, exists_const]
  | ⟨falsePLL, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨and a b, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨or a b, p⟩  => by simp_all only [reduceCtorEq, exists_const]
  | ⟨somehow a, p⟩ => by simp_all only [reduceCtorEq, exists_const]

@[simp]
def subformulasOf (F: PLLFormula) : Set PLLFormula :=
    match F with
    | PLLFormula.prop str   => {PLLFormula.prop str }
    | falsePLL => {falsePLL}
    | somehow P =>   {somehow P} ∪ P.subformulasOf
    | ifThen P Q   =>  {ifThen P Q} ∪ P.subformulasOf ∪ Q.subformulasOf
    | and P Q =>  {and P Q} ∪ P.subformulasOf ∪ Q.subformulasOf
    | or P Q => {or P Q} ∪ P.subformulasOf ∪ Q.subformulasOf


@[simp] -- Predicate
def isSomehowFormula (F: PLLFormula) : Prop := ∃(P: PLLFormula), F = somehow P
-- Subtype
def SomehowFormula := {F: PLLFormula // isSomehowFormula F}

@[simp] -- If all subformulas of F are not somehow formuas then F is somehowFree
def isSomehowFree (F: PLLFormula): Prop := ∀ (P: F.subformulasOf), ¬ isSomehowFormula P

def SomehowFree := {F: PLLFormula // isSomehowFree F}

@[simp]
private def eraseSomehowRaw (F: PLLFormula) : PLLFormula   :=
    match F with

    | PLLFormula.prop str   => PLLFormula.prop str
    | falsePLL => falsePLL
    | somehow P =>  P.eraseSomehowRaw
    | ifThen P Q   =>  ifThen P.eraseSomehowRaw Q.eraseSomehowRaw
    | and P Q =>  and P.eraseSomehowRaw Q.eraseSomehowRaw
    | or P Q => or P.eraseSomehowRaw Q.eraseSomehowRaw

lemma somehow_is_erased (F: PLLFormula) : ∀ (F_erased: PLLFormula ), F_erased = F.eraseSomehowRaw → ∀ (P: F_erased.subformulasOf), ¬ isSomehowFormula P := by
    simp
    intro P Q hP hEq
    subst hEq
    induction F with
    | prop str =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q

    | falsePLL =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
    | and P' Q' ihP ihQ =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, or_self]
    | or P Q ihP ihQ =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, or_self]
    | ifThen P Q ihP ihQ =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, or_self]
    | somehow P ihP =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, not_true_eq_false]



-- This returns an erased PLLFormula packaged with a proof of the property that it is somehow free.
def eraseSomehow (F: PLLFormula) : SomehowFree :=
    let P := F.eraseSomehowRaw
    ⟨P, by
        simp
        have h := somehow_is_erased F P (by rfl)
        intro a b x
        simp_all only [isSomehowFormula, not_exists, Subtype.forall, not_false_eq_true, P]
    ⟩














/-- Pretty-printer using the required logical symbols. -/
def toString (F: PLLFormula) : String :=
(stripParens printF) F where printF (F: PLLFormula) :=
  match F with
  | prop s  =>  s
  | falsePLL =>  "⊥"
  | and p q => addParens (printF p  ++  " ∧ " ++ printF q )
  | or p q => addParens (printF p  ++  " ∨ " ++ printF q )
  | ifThen falsePLL falsePLL =>  "⊤"
  | ifThen p q => addParens (printF p  ++  " ⊃ " ++ printF q ) -- Symbol shortcut is \ssup
  | somehow p => addParens ( "◯" ++ printF p )

/-- `Repr` instance that first prints with `reprAux` and then
    strips one pair of outer parentheses. -/
instance : Repr PLLFormula where
  reprPrec := getReprFn  toString

-- Demontstrating Repr
#eval (ifThen (prop "P") (somehow (and (prop "Q") falsePLL))) -- removes outer parents form
#eval prop "P" -- deals with no parens
#eval and truePLL (prop "P") -- True ∧ P

end PLLFormula

/-! ### Formula notation (scoped to `PLLND`)

`◯A`, `A ∧ B`, `A ∨ B`, `A ↠ B` (implication), `⊥`: the same inside a sequent
(`Γ, A ⊢ B`, `LaxLogic/Util/Turnstile.lean`) and outside it.  `↠` sits just
above a sequent (27), so `Γ ⊢ A ↠ B` needs no parentheses; `→` between sequents
stays outside.  In the typeset paper implication is `⊃`.

`∧`, `∨` and `⊥` keep Lean's and Mathlib's tokens and precedences (35, 30,
atom).  They are not overloaded: overloaded notations are elaborated
alternative by alternative without postponement, which reports
`a ⊆ b ∧ c ⊆ d` as ambiguous when the operand types are not yet known and lets
the formula `⊥` win against `Bot.bot` under `=`.  Instead, inside `PLLND`, a
macro sends them to one elaborator that takes the formula connective exactly
when a formula is expected, or, with no expected type, when the left operand
elaborates to a formula; in every other case it elaborates `And`, `Or` or
`Bot.bot` as before.  An unknown expected type is first waited for, so in
`A = ⊥` the `⊥` takes the type of `A`. -/
namespace PLLND

@[inherit_doc] scoped prefix:max "◯" => PLLFormula.somehow
@[inherit_doc] scoped infixr:27 " ↠ " => PLLFormula.ifThen

open Lean Elab Term Meta in
/-- Does this type reduce to `PLLFormula`? -/
def isFormulaType (T : Expr) : MetaM Bool := do
  return (← whnfR (← instantiateMVars T)).isConstOf ``PLLFormula

open Lean Elab Term Meta in
/-- Formula or proposition: the expected type decides; without one, the left operand. -/
def formulaWanted (expectedType? : Option Expr) (lhs? : Option Syntax) : TermElabM Bool := do
  tryPostponeIfNoneOrMVar expectedType?
  if let some T := expectedType? then
    let T ← instantiateMVars T
    if ← isFormulaType T then return true
    unless T.getAppFn.isMVar do return false
  let some lhs := lhs? | return false
  let s ← saveState
  try
    let e ← withoutErrToSorry <| elabTerm lhs none
    let isF ← isFormulaType (← inferType e)
    s.restore (restoreInfo := true)
    return isF
  catch _ =>
    s.restore (restoreInfo := true)
    return false

/-- Internal: `∧` inside `PLLND`. -/
syntax (name := pllAnd) "pll_and% " term:max term:max : term
/-- Internal: `∨` inside `PLLND`. -/
syntax (name := pllOr) "pll_or% " term:max term:max : term
/-- Internal: `⊥` inside `PLLND`. -/
syntax (name := pllBot) "pll_bot%" : term

open Lean Elab Term in
@[term_elab pllAnd] def elabPllAnd : TermElab := fun stx expectedType? => do
  let a : Term := ⟨stx[1]⟩; let b : Term := ⟨stx[2]⟩
  if ← formulaWanted expectedType? a then elabTerm (← `(PLLFormula.and $a $b)) expectedType?
  else elabTerm (← `(And $a $b)) expectedType?

open Lean Elab Term in
@[term_elab pllOr] def elabPllOr : TermElab := fun stx expectedType? => do
  let a : Term := ⟨stx[1]⟩; let b : Term := ⟨stx[2]⟩
  if ← formulaWanted expectedType? a then elabTerm (← `(PLLFormula.or $a $b)) expectedType?
  else elabTerm (← `(Or $a $b)) expectedType?

open Lean Elab Term in
@[term_elab pllBot] def elabPllBot : TermElab := fun _ expectedType? => do
  if ← formulaWanted expectedType? none then elabTerm (← `(PLLFormula.falsePLL)) expectedType?
  else elabTerm (← `(Bot.bot)) expectedType?

scoped macro_rules | `($a ∧ $b) => `(pll_and% ($a) ($b))
scoped macro_rules | `($a ∨ $b) => `(pll_or% ($a) ($b))
scoped macro_rules | `(⊥) => `(pll_bot%)

/-- Print `PLLFormula.and A B` as `A ∧ B`. -/
@[scoped app_unexpander PLLFormula.and]
def unexpandAnd : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a ∧ $b)
  | _ => throw ()

/-- Print `PLLFormula.or A B` as `A ∨ B`. -/
@[scoped app_unexpander PLLFormula.or]
def unexpandOr : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a ∨ $b)
  | _ => throw ()

/-- Print `PLLFormula.falsePLL` as `⊥`. -/
@[scoped app_unexpander PLLFormula.falsePLL]
def unexpandFalse : Lean.PrettyPrinter.Unexpander
  | `($_) => `(⊥)

end PLLND
