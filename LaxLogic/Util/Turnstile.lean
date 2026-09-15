/-
Copyright (c) 2026 Matthew Fairtlough. All rights reserved.
-/
import Lean

/-!
# Turnstiles with a true-argument tag

One notation for every consequence relation of the development, in place of a
glyph per relation (`⊢-`, `⊨-`, `⊢q`, `⊫`, `⊩q`, …).

    Γ ⊢[R] A     is   R Γ A              derivability in the calculus R
    Γ ⊨[R] A     is   R Γ A              semantic consequence R
    Γ ⊬[R] A     is   ¬ R Γ A            when R Γ A : Prop
                      ¬ Nonempty (R Γ A)  when R Γ A : Type (derivations are data)
    Γ ⊭[R] A     likewise for ⊨

The tag `R` is an ordinary term: the relation itself, possibly partially
applied (`Γ ⊢[G4h n] C` is `G4h n Γ C`).  So a theorem can quantify over it
(`∀ R, … Γ ⊢[R] A …`), hovering the tag shows the calculus, and a new calculus
needs no new glyph.

**Plain `⊢ ⊨ ⊬ ⊭`, when unambiguous.**  A development declares its default
relations, scoped to its namespace:

    attribute [turnstile] LaxND                 -- register (global)
    attribute [scoped turnstile_default] LaxND  -- the plain ⊢ inside `PLLND`

`Γ ⊢ A` elaborates to the in-scope default of that kind; with several in scope
(for instance PLL and QLL both open, or a list- and a set-context relation) it
takes the one whose context and formula types fit, and asks for a tag if that
still leaves more than one or none.

**Printing.**  An application of a registered relation prints as `Γ ⊢ A` when
the relation is an in-scope default and no other in-scope default of the same
kind has the same type, and as `Γ ⊢[R] A` otherwise.  `¬ R Γ A` and
`¬ Nonempty (R Γ A)` print with `⊬`/`⊭` under the same rule.

Precedence is 55 throughout, with both sides at 56: `A :: Γ ⊢ B` is
`(A :: Γ) ⊢ B`, and `¬ Γ ⊢ A` is `¬ (Γ ⊢ A)`.
-/

open Lean Elab Term Meta PrettyPrinter Delaborator SubExpr

namespace LaxLogic.Turnstile

/-- The two kinds of consequence relation. -/
inductive Kind where
  /-- syntactic: `⊢`, `⊬` -/
  | derive
  /-- semantic: `⊨`, `⊭` -/
  | consequence
  deriving BEq, Inhabited, Repr

/-- Every registered relation and its kind (global). -/
initialize registry : SimplePersistentEnvExtension (Name × Kind) (NameMap Kind) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, k) => m.insert n k
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (n, k) => m.insert n k) m) {}
  }

/-- The default relations of the open scopes. -/
initialize defaults : ScopedEnvExtension Name Name NameSet ←
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ n => pure n
    toOLeanEntry := id
    addEntry := fun s n => s.insert n
  }

def kindOf? (env : Environment) (n : Name) : Option Kind :=
  (registry.getState env).find? n

initialize registerBuiltinAttribute {
    name := `turnstile
    descr := "register a consequence relation `R : … → Ctx → Fm → Sort u` for `⊢[R]`/`⊨[R]`; \
      `@[turnstile consequence]` for a semantic one"
    applicationTime := .afterTypeChecking
    add := fun decl stx kind => do
      unless kind == .global do throwError "`turnstile` is global; use `turnstile_default` for scoped defaults"
      let k := if stx[1].getNumArgs > 0 then Kind.consequence else Kind.derive
      modifyEnv (registry.addEntry · (decl, k))
  }

initialize registerBuiltinAttribute {
    name := `turnstile_default
    descr := "make a registered relation the plain `⊢`/`⊨` of the current scope \
      (`attribute [scoped turnstile_default] R`)"
    applicationTime := .afterTypeChecking
    add := fun decl _ kind => do
      if (kindOf? (← getEnv) decl).isNone then
        throwError "`{decl}` is not registered: add `attribute [turnstile] {decl}` first"
      defaults.add decl kind
  }

/-! ## Syntax -/

/-- `Γ ⊢[R] A`: derivability of `A` from `Γ` in the calculus `R`, i.e. `R Γ A`. -/
syntax:55 term:56 " ⊢[" term "] " term:56 : term
/-- `Γ ⊨[R] A`: semantic consequence of `A` from `Γ` under `R`, i.e. `R Γ A`. -/
syntax:55 term:56 " ⊨[" term "] " term:56 : term
/-- `Γ ⊬[R] A`: `A` is not derivable from `Γ` in `R`. -/
syntax:55 term:56 " ⊬[" term "] " term:56 : term
/-- `Γ ⊭[R] A`: `A` is not a consequence of `Γ` under `R`. -/
syntax:55 term:56 " ⊭[" term "] " term:56 : term
/-- `Γ ⊢ A`: derivability in the default calculus of the open scope. -/
syntax:55 term:56 " ⊢ " term:56 : term
/-- `Γ ⊨ A`: consequence under the default semantics of the open scope. -/
syntax:55 term:56 " ⊨ " term:56 : term
/-- `Γ ⊬ A`: not derivable in the default calculus of the open scope. -/
syntax:55 term:56 " ⊬ " term:56 : term
/-- `Γ ⊭ A`: not a consequence under the default semantics of the open scope. -/
syntax:55 term:56 " ⊭ " term:56 : term

/-! ## Elaboration -/

/-- `¬ e` for a proposition, `¬ Nonempty e` for a type of derivations. -/
def negate (e : Expr) : TermElabM Expr := do
  let ty ← whnf (← inferType e)
  if ty.isProp then return mkNot e
  return mkNot (← mkAppM ``Nonempty #[e])

/-- The explicit binder types of a constant's type, in order. -/
def explicitBinderTypes (n : Name) : MetaM (Array Expr) := do
  forallTelescopeReducing (← getConstInfo n).type fun xs _ => do
    let mut out := #[]
    for x in xs do
      if (← x.fvarId!.getBinderInfo).isExplicit then out := out.push (← inferType x)
    return out

/-- Does `ty` unify with the type of the argument `i` (from the end) of `n`? -/
def fitsArg (n : Name) (iFromEnd : Nat) (ty : Expr) : MetaM Bool := do
  let tys ← explicitBinderTypes n
  if tys.size < 2 then return false
  let t := tys[tys.size - iFromEnd]!
  if t.hasLooseBVars then return true   -- a dependent type: do not filter on it
  withNewMCtxDepth <| isDefEq t ty

/-- The default relation of kind `k` for `Γ` and `A`. -/
def chooseDefault (k : Kind) (sym : String) (Γ A : Term) : TermElabM Name := do
  let env ← getEnv
  let ds := (defaults.getState env).toList.filter fun n => kindOf? env n == some k
  let ds ← ds.filterM fun n => return (← explicitBinderTypes n).size == 2
  match ds with
  | [] => throwError "no default relation for `{sym}` in scope: write `Γ {sym}[R] A`, or open the \
      development that declares one"
  | [d] => return d
  | _ =>
    let γ ← elabTerm Γ none
    let γty ← instantiateMVars (← inferType γ)
    let ds ← ds.filterM fun d => fitsArg d 2 γty
    if let [d] := ds then return d
    let a ← elabTerm A none
    let aty ← instantiateMVars (← inferType a)
    let ds ← ds.filterM fun d => fitsArg d 1 aty
    match ds with
    | [d] => return d
    | [] => throwError "no default relation for `{sym}` fits a context of type {γty}"
    | ds => throwError "`{sym}` is ambiguous here ({ds}): write `Γ {sym}[R] A`"

macro_rules
  | `($Γ ⊢[$R] $A) => `($R $Γ $A)
  | `($Γ ⊨[$R] $A) => `($R $Γ $A)

elab_rules : term
  | `($Γ ⊬[$R] $A) => do negate (← elabTerm (← `($R $Γ $A)) none)
  | `($Γ ⊭[$R] $A) => do negate (← elabTerm (← `($R $Γ $A)) none)
  | `($Γ ⊢ $A) => do
      let d ← chooseDefault .derive "⊢" Γ A
      elabTerm (← `($(mkCIdent d) $Γ $A)) none
  | `($Γ ⊨ $A) => do
      let d ← chooseDefault .consequence "⊨" Γ A
      elabTerm (← `($(mkCIdent d) $Γ $A)) none
  | `($Γ ⊬ $A) => do
      let d ← chooseDefault .derive "⊬" Γ A
      negate (← elabTerm (← `($(mkCIdent d) $Γ $A)) none)
  | `($Γ ⊭ $A) => do
      let d ← chooseDefault .consequence "⊭" Γ A
      negate (← elabTerm (← `($(mkCIdent d) $Γ $A)) none)

/-! ## Printing -/

/-- The number of arguments a full application of `n` takes, and whether the
last two are explicit. -/
def arity (n : Name) : MetaM (Option Nat) := do
  forallTelescopeReducing (← getConstInfo n).type fun xs _ => do
    if xs.size < 2 then return none
    let b1 ← xs[xs.size - 1]!.fvarId!.getBinderInfo
    let b2 ← xs[xs.size - 2]!.fvarId!.getBinderInfo
    return if b1.isExplicit && b2.isExplicit then some xs.size else none

/-- Print without a tag: `n` is an in-scope default and no other in-scope
default of the same kind has the same type. -/
def printPlain (n : Name) (k : Kind) : MetaM Bool := do
  let env ← getEnv
  let ds := defaults.getState env
  unless ds.contains n do return false
  let ty := (← getConstInfo n).type
  for d in ds.toList do
    if d != n && kindOf? env d == some k then
      if (← getConstInfo d).type == ty then return false
  return true

/-- The pieces of `R … Γ A` for a registered `R`: kind, plain?, tag, Γ, A. -/
def turnstileParts : DelabM (Kind × Bool × Term × Term × Term) := do
  let e ← getExpr
  let .const c _ := e.getAppFn | failure
  let some k := kindOf? (← getEnv) c | failure
  let some n ← arity c | failure
  unless e.getAppNumArgs == n do failure
  let plain ← printPlain c k
  let Γ ← withAppFn <| withAppArg delab
  let A ← withAppArg delab
  let R ← withAppFn <| withAppFn delab
  return (k, plain, R, Γ, A)

@[delab app]
def delabTurnstile : Delab := whenPPOption getPPNotation do
  let (k, plain, R, Γ, A) ← turnstileParts
  match k, plain with
  | .derive, true => `($Γ ⊢ $A)
  | .derive, false => `($Γ ⊢[$R] $A)
  | .consequence, true => `($Γ ⊨ $A)
  | .consequence, false => `($Γ ⊨[$R] $A)

@[delab app.Not]
def delabNotTurnstile : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  unless e.getAppNumArgs == 1 do failure
  let inner := e.appArg!
  -- `¬ R Γ A` for a Prop-valued R, `¬ Nonempty (R Γ A)` for a Type-valued one
  let viaNonempty := inner.isAppOfArity ``Nonempty 1
  let (k, plain, R, Γ, A) ←
    if viaNonempty then withAppArg <| withAppArg turnstileParts else withAppArg turnstileParts
  -- only the matching negation form prints as ⊬/⊭
  let rel := if viaNonempty then inner.appArg! else inner
  let isProp ← withNewMCtxDepth do return (← whnf (← inferType rel)).isProp
  unless isProp != viaNonempty do failure
  match k, plain with
  | .derive, true => `($Γ ⊬ $A)
  | .derive, false => `($Γ ⊬[$R] $A)
  | .consequence, true => `($Γ ⊭ $A)
  | .consequence, false => `($Γ ⊭[$R] $A)

end LaxLogic.Turnstile
