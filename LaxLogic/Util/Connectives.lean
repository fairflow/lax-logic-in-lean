/-
Copyright (c) 2026 Matthew Fairtlough. All rights reserved.
-/
import Lean

/-!
# Formula connectives shared by the developments

A deep embedding has its own `and`, `or`, implication, `⊥` and `⊤`
constructors; this module lets each development write them `A ∧ B`, `A ∨ B`,
`A ↠ B`, `⊥`, `⊤`, and read them back that way, without a second notation per
development and without overloading Lean's own `∧ ∨` or Mathlib's `⊥ ⊤`.

**Registration** is scoped, so the notation is active exactly where the
development's namespace is open:

    attribute [scoped connective and] PLLFormula.and
    attribute [scoped connective imp] PLLFormula.ifThen
    attribute [scoped connective bot] PLLFormula.falsePLL

The roles are `and`, `or`, `imp`, `bot`, `top`; the formula type is the result
type of the constant.

**Input.**  `↠` (precedence 27, right) is syntax of this module.  `∧`, `∨`
(Lean core) and `⊥`, `⊤` (Mathlib) keep their parsers; a development sends them
here with a scoped macro:

    scoped macro_rules | `($a ∧ $b) => `(fm_and% ($a) ($b))

The elaborators decide by type.  The expected type is waited for if it is not
yet known; a registered formula type selects the constructor; with no expected
type at all the left operand's type decides; in every other case `∧ ∨ ⊥ ⊤` are
`And`, `Or`, `Bot.bot`, `Top.top` as before.  Notations are not overloaded
because Lean elaborates overloaded alternatives without postponement: that
reports `a[i]!.x ⊆ b ∧ …` as ambiguous while the operand types are unknown, and
picks the formula `⊥` against `Bot.bot` under `=`.

**Printing.**  An application of an active connective prints with its symbol;
`⊥`/`⊤` only where Mathlib's `⊥`/`⊤` syntax exists.
-/

open Lean Elab Term Meta PrettyPrinter Delaborator SubExpr

namespace LaxLogic.Connectives

/-- An active connective: its role (`and`, `or`, `imp`, `bot`, `top`), the formula
type, and the constructor. -/
structure Entry where
  role : Name
  type : Name
  ctor : Name
  deriving Inhabited

/-- The connectives of the open scopes. -/
initialize connectives : ScopedEnvExtension Entry Entry (Array Entry) ←
  registerScopedEnvExtension {
    mkInitial := pure #[]
    ofOLeanEntry := fun _ e => pure e
    toOLeanEntry := id
    addEntry := fun s e => s.push e
  }

def roles : List Name := [`and, `or, `imp, `bot, `top]

/-- The head constant of the result type of `c`. -/
def resultType (c : Name) : MetaM Name := do
  let info ← getConstInfo c
  forallTelescopeReducing info.type fun _ r => do
    let some n := (← whnfR r).getAppFn.constName? |
      throwError "the result type of `{c}` is not a constant"
    return n

initialize registerBuiltinAttribute {
    name := `connective
    descr := "make a constructor the formula connective `and`, `or`, `imp`, `bot` or `top` of its \
      type (`attribute [scoped connective and] F.and`)"
    applicationTime := .afterTypeChecking
    add := fun decl stx kind => do
      let arg := stx[1]
      unless arg.getNumArgs > 0 do throwError "`connective` needs a role: one of {roles}"
      let role := arg[0].getId
      unless roles.contains role do throwError "unknown connective role `{role}`: one of {roles}"
      let type ← (resultType decl).run'
      connectives.add { role, type, ctor := decl } kind
  }

/-- The active constructor for `role` on the formula type `type`. -/
def ctorFor? (env : Environment) (type role : Name) : Option Name :=
  (connectives.getState env).findSome? fun e => if e.type == type && e.role == role then some e.ctor else none

/-- The active role of a constructor. -/
def roleOf? (env : Environment) (ctor : Name) : Option Name :=
  (connectives.getState env).findSome? fun e => if e.ctor == ctor then some e.role else none

/-- The head constant of a type. -/
def headConst? (T : Expr) : MetaM (Option Name) := do
  return (← whnfR (← instantiateMVars T)).getAppFn.constName?

/-- The constructor for `role` if a formula is wanted here: by the expected type, or,
with none, by the type of the left operand. -/
def ctorWanted? (role : Name) (expectedType? : Option Expr) (lhs? : Option Syntax) :
    TermElabM (Option Name) := do
  tryPostponeIfNoneOrMVar expectedType?
  let env ← getEnv
  if let some T := expectedType? then
    let T ← instantiateMVars T
    if let some c ← headConst? T then
      if let some k := ctorFor? env c role then return some k
    unless T.getAppFn.isMVar do return none
  let some lhs := lhs? | return none
  let s ← saveState
  try
    let e ← withoutErrToSorry <| elabTerm lhs none
    let ty ← inferType e
    s.restore (restoreInfo := true)
    match ← headConst? ty with
    | some c => return ctorFor? env c role
    | none => return none
  catch _ =>
    s.restore (restoreInfo := true)
    return none

/-- Internal: `∧` inside a development. -/
syntax (name := fmAnd) "fm_and% " term:max term:max : term
/-- Internal: `∨` inside a development. -/
syntax (name := fmOr) "fm_or% " term:max term:max : term
/-- Internal: `⊥` inside a development. -/
syntax (name := fmBot) "fm_bot%" : term
/-- Internal: `⊤` inside a development. -/
syntax (name := fmTop) "fm_top%" : term

/-- `A ↠ B`: implication of the formula type in scope. -/
syntax:27 term:28 " ↠ " term:27 : term

@[term_elab fmAnd] def elabAnd : TermElab := fun stx expectedType? => do
  let a : Term := ⟨stx[1]⟩; let b : Term := ⟨stx[2]⟩
  match ← ctorWanted? `and expectedType? a with
  | some k => elabTerm (← `($(mkCIdent k) $a $b)) expectedType?
  | none => elabTerm (← `(And $a $b)) expectedType?

@[term_elab fmOr] def elabOr : TermElab := fun stx expectedType? => do
  let a : Term := ⟨stx[1]⟩; let b : Term := ⟨stx[2]⟩
  match ← ctorWanted? `or expectedType? a with
  | some k => elabTerm (← `($(mkCIdent k) $a $b)) expectedType?
  | none => elabTerm (← `(Or $a $b)) expectedType?

@[term_elab fmBot] def elabBot : TermElab := fun _ expectedType? => do
  match ← ctorWanted? `bot expectedType? none with
  | some k => elabTerm (mkCIdent k) expectedType?
  -- Mathlib's `Bot.bot`, named without hygiene: this module does not import Mathlib
  | none => elabTerm (mkCIdent `Bot.bot) expectedType?

@[term_elab fmTop] def elabTop : TermElab := fun _ expectedType? => do
  match ← ctorWanted? `top expectedType? none with
  | some k => elabTerm (mkCIdent k) expectedType?
  | none => elabTerm (mkCIdent `Top.top) expectedType?

elab_rules : term <= expectedType
  | `($a ↠ $b) => do
    match ← ctorWanted? `imp (some expectedType) a with
    | some k => elabTerm (← `($(mkCIdent k) $a $b)) expectedType
    | none =>
      -- no expected formula type: try the left operand
      match ← ctorWanted? `imp none a with
      | some k => elabTerm (← `($(mkCIdent k) $a $b)) expectedType
      | none => throwError "`↠` needs a formula type with an implication in scope \
          (open the development that declares one)"

/-- Mathlib's `⊥`/`⊤` syntax, when it is loaded. -/
def atomSyntax? (kind : Name) (tk : String) : DelabM (Option Term) := do
  if Parser.isValidSyntaxNodeKind (← getEnv) kind then
    return some ⟨Syntax.node .none kind #[Syntax.atom .none tk]⟩
  return none

@[delab app]
def delabConnective : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let .const c _ := e.getAppFn | failure
  let some role := roleOf? (← getEnv) c | failure
  match role, e.getAppNumArgs with
  | `and, 2 => do
    let a ← withAppFn (withAppArg delab); let b ← withAppArg delab; `($a ∧ $b)
  | `or, 2 => do
    let a ← withAppFn (withAppArg delab); let b ← withAppArg delab; `($a ∨ $b)
  | `imp, 2 => do
    let a ← withAppFn (withAppArg delab); let b ← withAppArg delab; `($a ↠ $b)
  | `bot, 0 => do
    let some s ← atomSyntax? `«term⊥» "⊥" | failure
    pure s
  | `top, 0 => do
    let some s ← atomSyntax? `«term⊤» "⊤" | failure
    pure s
  | _, _ => failure

end LaxLogic.Connectives
