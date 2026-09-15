/-
Copyright (c) 2026 Matthew Fairtlough. All rights reserved.
-/
import LaxLogic.QLL.Syntax
import LaxLogic.Util.Connectives

/-!
# `LaxLogic.QLL.Notation` — formulas as Lean terms

Scoped to `LaxLogic.QLL`; the same inside a sequent (`Γ, A ⊢ B`,
`LaxLogic/Util/Turnstile.lean`) and outside it, in input and in printing.

| notation | formula | |
| :-- | :-- | :-- |
| `◯[∀] A`, `◯[∃] A` | `.circ .all A`, `.circ .ex A` | the two lax modalities |
| `◯[q] A` | `.circ q A` | for a modality variable `q : Q` |
| `A ∧ B`, `A ∨ B`, `A ↠ B` | `.and`, `.or`, `.imp` | shared connectives |
| `⊥`, `⊤` | `.bot`, `.top` | where Mathlib's `⊥ ⊤` are loaded: `LaxLogic.QLL.NotationOrder` |
| `∀' A`, `∃' A` | `.forall_ A`, `.exists_ A` | `A` a body: index 0 is the bound individual |
| `∀ x, A`, `∃ x, A` | `.forall_ (A.closeWith "x")` | `x : Tm` in `A` stands for `.fvar "x"` |
| `P(t, u)`, `P()` | `.pred "P" [t, u]`, `.pred "P" []` | a predicate applied to individual terms |
| `f(t, u)`, `c()` | `.fn "f" [t, u]`, `.fn "c" []` | a function term, where a `Tm` is expected |

**Predicates** are written as in mathematics and in `qf[…]`: the symbol, then its
arguments in parentheses with no space (Lean itself rejects `f(x)`, so the form is
free).  Inside the parentheses an identifier that names nothing in Lean is a free
individual: `P(x, a)` with `x` bound by `∀ x,` and `a` unbound is
`.pred "P" [x, .fvar "a"]`, and prints back the same way.  A computed symbol is
written with the constructor, `.pred c ts`.

`◯[·]`, `∀'`, `∃'` bind as tightly as application arguments, so
`◯[∀] (A ∧ B)` and `∀' (A ↠ B)` need their parentheses.  `∀ x, A` reaches as
far right as it can, as in Lean.  `∀'`/`∃'` follow Mathlib's model theory, where
they are the de Bruijn quantifiers of `BoundedFormula`.

**Named quantifiers.**  Inside `LaxLogic.QLL`, `∀ x, A` and `∃ x, A` with a
single untyped binder are formulas exactly when a formula is expected (after
waiting for the expected type); anywhere else they are Lean's `∀` and `∃`.
`∀ x : T, …` and `∀ x y, …` are always Lean's.

**Printing.**  `.forall_ (A.closeWith "x")` prints `∀ x, A`.  A body built
from constructors alone is opened with a fresh name from `x y z x1 …` and
printed the same way; the printed term elaborates to one definitionally equal
to the original (`closeWith` computes the body back).  Any other body prints
`∀' A`.
-/

open Lean Elab Term Meta PrettyPrinter Delaborator SubExpr

namespace LaxLogic.QLL

attribute [scoped connective and] Form.and
attribute [scoped connective or] Form.or
attribute [scoped connective imp] Form.imp
attribute [scoped connective bot] Form.bot
attribute [scoped connective top] Form.top
attribute [scoped connective var] Tm.fvar
attribute [scoped connective var] Pf.fvar

scoped macro_rules | `($a ∧ $b) => `(fm_and% ($a) ($b))
scoped macro_rules | `($a ∨ $b) => `(fm_or% ($a) ($b))

/-! ## Modalities and de Bruijn quantifiers -/

/-- `◯[∀] A`: the lax modality `◯∀`. -/
scoped syntax:max "◯[∀] " term:max : term
/-- `◯[∃] A`: the lax modality `◯∃`. -/
scoped syntax:max "◯[∃] " term:max : term
/-- `◯[q] A`: the lax modality `q`. -/
scoped syntax:max "◯[" term "] " term:max : term
/-- `∀' A`: the universal quantifier over a body `A`, its bound individual at index 0. -/
scoped syntax:max "∀' " term:max : term
/-- `∃' A`: the existential quantifier over a body `A`, its bound individual at index 0. -/
scoped syntax:max "∃' " term:max : term

macro_rules
  | `(◯[∀] $A) => `(LaxLogic.QLL.Form.circ LaxLogic.QLL.Q.all $A)
  | `(◯[∃] $A) => `(LaxLogic.QLL.Form.circ LaxLogic.QLL.Q.ex $A)
  | `(◯[$q] $A) => `(LaxLogic.QLL.Form.circ $q $A)
  | `(∀' $A) => `(LaxLogic.QLL.Form.forall_ $A)
  | `(∃' $A) => `(LaxLogic.QLL.Form.exists_ $A)

/-! ## Predicates and function terms -/

/-- `P(t, …)`: the predicate `P` on individual terms; `f(t, …)` where a `Tm` is expected:
the function term `f`. -/
scoped syntax:max (name := qllSymApp) ident noWs "(" term,* ")" : term

/-- A list literal of type `List α`. -/
def mkListLit (α : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun h t => mkApp3 (mkConst ``List.cons [Level.zero]) α h t)
    (mkApp (mkConst ``List.nil [Level.zero]) α)

@[term_elab qllSymApp] def elabSymApp : TermElab := fun stx expectedType? => do
  let sym := stx[0].getId.eraseMacroScopes.toString
  let args := stx[2].getSepArgs
  tryPostponeIfNoneOrMVar expectedType?
  let isTm ← match expectedType? with
    | some T => pure ((← Connectives.headConst? T) == some ``Tm)
    | none => pure false
  let tm := Lean.mkConst ``Tm
  let xs ← args.mapM fun a => Connectives.elabFree a tm
  let e := mkApp2 (Lean.mkConst (if isTm then ``Tm.fn else ``Form.pred)) (mkStrLit sym) (mkListLit tm xs)
  match expectedType? with
  | some T => ensureHasType T e
  | none => pure e

/-! ## Named quantifiers -/

namespace Notation

/-- Is the formula notation of `LaxLogic.QLL` active here? -/
def active : MetaM Bool :=
  return (Connectives.ctorFor? (← getEnv) ``Form `and).isSome

/-- A formula is expected here (waiting for the expected type if need be). -/
def formWanted (expectedType? : Option Expr) : TermElabM Bool := do
  tryPostponeIfNoneOrMVar expectedType?
  let some T := expectedType? | return false
  let some c ← Connectives.headConst? T | return false
  return c == ``Form && (← active)

/-- `∀ x, A` / `∃ x, A` as a formula: `A` elaborated with `x : Tm`, then `x` replaced by
`.fvar "x"` and closed. -/
def elabNamed (ctor : Name) (x : Ident) (b : Term) : TermElabM Expr := do
  let s := x.getId.eraseMacroScopes.toString
  let name := mkApp (mkConst ``Tm.fvar) (mkStrLit s)
  withLocalDeclD x.getId (mkConst ``Tm) fun xv => do
    let e ← elabTermEnsuringType b (mkConst ``Form)
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let body := e.replaceFVar xv name
    if body.containsFVar xv.fvarId! then
      throwErrorAt x "the bound individual `{x}` is used where it cannot be named"
    return mkApp (mkConst ctor) (mkApp2 (mkConst ``Form.closeWith) (mkStrLit s) body)

/-- Internal: `∀ x, A` inside `LaxLogic.QLL`. -/
syntax (name := qllAll) "qll_all% " ident term:max : term
/-- Internal: `∃ x, A` inside `LaxLogic.QLL`. -/
syntax (name := qllEx) "qll_ex% " ident term:max : term

@[term_elab qllAll] def elabAll : TermElab := fun stx expectedType? => do
  let x : Ident := ⟨stx[1]⟩; let b : Term := ⟨stx[2]⟩
  if ← formWanted expectedType? then elabNamed ``Form.forall_ x b
  -- Lean's own `∀`, elaborated directly so that this macro does not fire again
  else elabForall (← `(∀ $x:ident, $b)) expectedType?

@[term_elab qllEx] def elabEx : TermElab := fun stx expectedType? => do
  let x : Ident := ⟨stx[1]⟩; let b : Term := ⟨stx[2]⟩
  if ← formWanted expectedType? then elabNamed ``Form.exists_ x b
  -- Lean's own expansion of `∃ x, b`
  else elabTerm (← `(Exists fun $x:ident => $b)) expectedType?

end Notation

scoped macro_rules | `(∀ $x:ident, $b) => `(qll_all% $x ($b))
scoped macro_rules | `(∃ $x:ident, $b) => `(qll_ex% $x ($b))

/-! ## Printing -/

namespace Notation

/-- A string literal. -/
def strLit? : Expr → Option String
  | .lit (.strVal s) => some s
  | .mdata _ e => strLit? e
  | _ => none

/-- `x y z x1 y1 z1 …` -/
def indivName (n : Nat) : String :=
  let letter := ["x", "y", "z"][n % 3]!
  if n / 3 = 0 then letter else letter ++ toString (n / 3)

/-- A list literal's elements. -/
partial def listElems? : Expr → Option (Array Expr)
  | e =>
    match e.consumeMData.getAppFnArgs with
    | (``List.nil, #[_]) => some #[]
    | (``List.cons, #[_, h, t]) => (listElems? t).map (#[h] ++ ·)
    | _ => none

/-- Rebuild a list literal of element type `α`. -/
def mkList (α : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun h t => mkApp3 (mkConst ``List.cons [Level.zero]) α h t)
    (mkApp (mkConst ``List.nil [Level.zero]) α)

/-- A term built from constructors, literals and local individuals, with `.bvar d`
replaced by the loose bound variable 0. -/
partial def tmStatic (d : Nat) : Expr → Option Expr
  | e =>
    let e := e.consumeMData
    if e.isFVar then some e else
    match e.getAppFnArgs with
    | (``Tm.bvar, #[n]) => n.nat?.map fun k => if k = d then .bvar 0 else e
    | (``Tm.fvar, #[s]) => (strLit? s).map fun _ => e
    | (``Tm.fn, #[f, ts]) => do
      let _ ← strLit? f
      let xs ← (← listElems? ts).mapM (tmStatic d)
      some (mkApp2 (mkConst ``Tm.fn) f (mkList (mkConst ``Tm) xs))
    | _ => none

/-- A formula built from constructors, with the individual at binder depth `d` replaced
by the loose bound variable 0. -/
partial def formStatic (d : Nat) : Expr → Option Expr
  | e =>
    let e := e.consumeMData
    match e.getAppFnArgs with
    | (``Form.top, #[]) | (``Form.bot, #[]) => some e
    | (``Form.pred, #[P, ts]) => do
      let _ ← strLit? P
      let xs ← (← listElems? ts).mapM (tmStatic d)
      some (mkApp2 (mkConst ``Form.pred) P (mkList (mkConst ``Tm) xs))
    | (``Form.and, #[a, b]) => return mkApp2 (mkConst ``Form.and) (← formStatic d a) (← formStatic d b)
    | (``Form.or, #[a, b]) => return mkApp2 (mkConst ``Form.or) (← formStatic d a) (← formStatic d b)
    | (``Form.imp, #[a, b]) => return mkApp2 (mkConst ``Form.imp) (← formStatic d a) (← formStatic d b)
    | (``Form.circ, #[q, a]) =>
      if q.consumeMData.isConstOf ``Q.all || q.consumeMData.isConstOf ``Q.ex || q.isFVar then
        return mkApp2 (mkConst ``Form.circ) q (← formStatic d a)
      else none
    | (``Form.forall_, #[a]) => return mkApp (mkConst ``Form.forall_) (← formStatic (d + 1) a)
    | (``Form.exists_, #[a]) => return mkApp (mkConst ``Form.exists_) (← formStatic (d + 1) a)
    | _ => none

/-- The names a printed body could clash with: its string literals and the names of
its local individuals. -/
def namesIn (e : Expr) : MetaM (List String) := do
  let fvs := (collectFVars {} e).fvarIds
  let names ← fvs.toList.mapM fun f => return (← f.getUserName).toString
  return collectStrings e [] ++ names
where
  collectStrings (e : Expr) (acc : List String) : List String :=
    match e with
    | .lit (.strVal s) => s :: acc
    | .app f a => collectStrings f (collectStrings a acc)
    | .mdata _ b => collectStrings b acc
    | _ => acc

/-- The body of a quantifier, opened: a name for the bound individual and the body with
the loose bound variable 0 in its place. -/
def openBody? (a : Expr) : MetaM (Option (String × Expr)) := do
  let a := a.consumeMData
  if a.isAppOfArity ``Form.closeWith 2 then
    if let some s := strLit? a.appFn!.appArg! then
      let name := mkApp (mkConst ``Tm.fvar) (mkStrLit s)
      let body := a.appArg!.replace fun t => if t == name then some (.bvar 0) else none
      return some (s, body)
  let some body := formStatic 0 a | return none
  let avoid ← namesIn a
  let rec fresh (n : Nat) (fuel : Nat) : String :=
    match fuel with
    | 0 => indivName n
    | fuel + 1 => if avoid.contains (indivName n) then fresh (n + 1) fuel else indivName n
  return some (fresh 0 1000, body)

/-- `∀ x, A` or `∀' A`. -/
def delabQuant (named : Ident → Term → DelabM Term) (body : Term → DelabM Term) : Delab :=
  whenPPOption getPPNotation do
    unless ← active do failure
    let e ← getExpr
    unless e.getAppNumArgs == 1 do failure
    match ← openBody? e.appArg! with
    | some (s, b) =>
      withLocalDeclD (Name.mkSimple s) (mkConst ``Tm) fun xv => do
        let b := b.instantiate1 xv
        let bs ← withAppArg <| withTheReader SubExpr (fun se => { se with expr := b }) delab
        named (mkIdent (Name.mkSimple s)) bs
    | none => body (← withAppArg delab)

@[delab app.LaxLogic.QLL.Form.forall_]
def delabForall : Delab := delabQuant (fun x b => `(∀ $x:ident, $b)) (fun a => `(∀' $a))

@[delab app.LaxLogic.QLL.Form.exists_]
def delabExists : Delab := delabQuant (fun x b => `(∃ $x:ident, $b)) (fun a => `(∃' $a))

/-- A symbol that prints as an identifier and reads back as the same string. -/
def symbolIdent? (s : String) : Option Ident :=
  let n := Name.mkSimple s
  if !s.isEmpty && n.toString == s && isIdFirst (s.get 0) && s.toList.all isIdRest then
    some (mkIdent n)
  else none

/-- The elements of a list literal, each printed as a term with free names. -/
partial def delabArgs : DelabM (Option (Array Term)) := do
  let e ← getExpr
  if e.isAppOfArity ``List.nil 1 then return some #[]
  if e.isAppOfArity ``List.cons 3 then
    let h ← withAppFn (withAppArg Connectives.delabFree)
    let some t ← withAppArg delabArgs | return none
    return some (#[h] ++ t)
  return none

/-- `P(t, …)` and `f(t, …)`. -/
def delabSymApp : Delab := whenPPOption getPPNotation do
  unless ← active do failure
  let e ← getExpr
  unless e.getAppNumArgs == 2 do failure
  let some s := strLit? e.appFn!.appArg! | failure
  let some P := symbolIdent? s | failure
  let some args ← withAppArg delabArgs | failure
  `($P:ident($args,*))

@[delab app.LaxLogic.QLL.Form.pred] def delabPred : Delab := delabSymApp
@[delab app.LaxLogic.QLL.Tm.fn] def delabFn : Delab := delabSymApp

@[delab app.LaxLogic.QLL.Form.circ]
def delabCirc : Delab := whenPPOption getPPNotation do
  unless ← active do failure
  let e ← getExpr
  unless e.getAppNumArgs == 2 do failure
  let A ← withAppArg delab
  let q := e.appFn!.appArg!.consumeMData
  if q.isConstOf ``Q.all then `(◯[∀] $A)
  else if q.isConstOf ``Q.ex then `(◯[∃] $A)
  else
    let qs ← withAppFn (withAppArg delab)
    `(◯[$qs] $A)

end Notation

end LaxLogic.QLL
