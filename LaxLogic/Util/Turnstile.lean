/-
Copyright (c) 2026 Matthew Fairtlough. All rights reserved.
-/
import Lean
import LaxLogic.Util.Connectives

/-!
# Turnstiles with a true-argument tag

One notation for every consequence relation of the development, in place of a
glyph per relation (`⊢-`, `⊨-`, `⊢q`, `⊫`, `⊩q`, …).

    Γ ⊢[R] A     is   R Γ A              derivability in the calculus R
    Γ ⊨[R] A     is   R Γ A              semantic consequence R
    Γ ⊬[R] A     is   ¬ R Γ A            when R Γ A : Prop
                      ¬ Nonempty (R Γ A)  when R Γ A : Type (derivations are data)
    Γ ⊭[R] A     likewise for ⊨
    Γ ⊢[R] p : A is   R p Γ A            a typing judgement: p proves A from Γ

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

**Contexts.**  `Γ, A, B ⊢ C` is `B :: A :: Γ` for a list context and
`insert B (insert A Γ)` for a set; `⊢ C` is the empty context (printed only when
no other default could read it); `A, B ⊢ C` with no context variable is
`[A, B] ⊢ C`; a single context term (`A :: Γ`, `Γ ++ Δ`, `[p, q]`) still works.
Before a comma the first entry is an identifier (the context variable, or the first
formula of a context without one); it is never the type or bound of an unbracketed
binder, so `∀ x : T, Γ ⊢ A` and `∀ φ ∈ Ds, Γ, φ ⊢ χ` read as intended.

**Typing judgements.**  A relation registered with `attribute [turnstile typing] R`
takes a proof term before the context, `R p Γ A`, and is written `Γ ⊢ p : A`; its
context entries are written `u : B` (the pair `(u, B)`), so `Γ, u : B ⊢ p : A` is
`R p ((u, B) :: Γ) A`.  In the proof-term position and on the left of an entry, an
identifier that names nothing in Lean is the free variable of that name
(`LaxLogic/Util/Connectives.lean`).  When no typing judgement applies,
`Γ ⊢ A : T` is the sequent `Γ ⊢ A` ascribed the type `T`, as before.

**Formulas** are the development's own scoped notation (for PLL: `◯A`, `A ∧ B`,
`A ∨ B`, `A ↠ B`, `⊥`), the same inside and outside a sequent.

Precedence: a sequent is 26, its context side 56, its formula side 27.  A
sequent directly followed by a `Prop` connective is parenthesised,
`(Γ ⊢ A) ∧ P`,.
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

/-- Every registered relation, its kind, and whether it is a typing judgement `R p Γ A`
(global). -/
initialize registry : SimplePersistentEnvExtension (Name × Kind × Bool) (NameMap (Kind × Bool)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, k, t) => m.insert n (k, t)
    addImportedFn := fun as =>
      as.foldl (fun m a => a.foldl (fun m (n, k, t) => m.insert n (k, t)) m) {}
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
  ((registry.getState env).find? n).map (·.1)

/-- Is `n` a registered typing judgement `R p Γ A`? -/
def typedOf (env : Environment) (n : Name) : Bool :=
  ((registry.getState env).find? n).map (·.2) |>.getD false

initialize registerBuiltinAttribute {
    name := `turnstile
    descr := "register a consequence relation `R : … → Ctx → Fm → Sort u` for `⊢[R]`/`⊨[R]`; \
      `@[turnstile consequence]` for a semantic one, `@[turnstile typing]` for a typing \
      judgement `R : … → Pf → Ctx → Fm → Sort u` written `Γ ⊢[R] p : A`"
    applicationTime := .afterTypeChecking
    add := fun decl stx kind => do
      unless kind == .global do throwError "`turnstile` is global; use `turnstile_default` for scoped defaults"
      let arg : Name := if stx[1].getNumArgs > 0 then stx[1][0].getId else .anonymous
      let (k, t) ← match arg with
        | .anonymous => pure (Kind.derive, false)
        | `consequence => pure (Kind.consequence, false)
        | `typing => pure (Kind.derive, true)
        | a => throwError "unknown `turnstile` option `{a}`: `consequence` or `typing`"
      modifyEnv (registry.addEntry · (decl, k, t))
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

/-! ## The context variable of a comma context

In `∀ x : T, Γ ⊢ A` and `∀ x ∈ S, Γ ⊢ A` the comma belongs to the binder, but a
parser for `Γ, A ⊢ B` would read `T, Γ ⊢ A` as a sequent.  So the identifier that
opens a comma context is refused when it is the type of an unbracketed binder
(`∀ ∃ Σ Π ∑ ∏ ⋃ ⋂ ⨆ ⨅ λ` followed by names and `:`) or the right side of a binder
predicate (`∈ ∉ ⊆ ⊂ ⊇ ⊃ ≤ < ≥ > ≠`).  The check reads the characters just before
the identifier; it consumes nothing. -/

namespace Guard

/-- Up to `n` characters before `pos`, nearest first. -/
def charsBefore (s : String) (pos : String.Pos.Raw) : Nat → List Char
  | 0 => []
  | n + 1 =>
    if pos.byteIdx == 0 then [] else
      let p := String.Pos.Raw.prev s pos
      String.Pos.Raw.get s p :: charsBefore s p n

/-- A nearest-first character list ends (in text order) with `w`. -/
def endsWith (cs : List Char) (w : String) : Bool := w.toList.reverse.isPrefixOf cs

def binderPreds : List String := ["∈", "∉", "⊆", "⊂", "⊇", "⊃", "≤", "≥", "≠", "<"]
def binderHeads : List String := ["∀", "∃", "Σ", "Π", "∑", "∏", "⋃", "⋂", "⨆", "⨅", "λ"]

/-- Names back to a binder head: `∀ x y :`. -/
def namesToHead : Nat → List Char → Bool → Bool
  | 0, _, _ => false
  | fuel + 1, cs, seen =>
    let cs := cs.dropWhile Char.isWhitespace
    let word := cs.takeWhile isIdRest
    if word.isEmpty then seen && binderHeads.any (endsWith cs)
    else if word.reverse == "forall".toList || word.reverse == "exists".toList then true
    else namesToHead fuel (cs.drop word.length) true

/-- Is the text before this position the binder part `∀ x :` or `x ∈`? -/
def binderBound (cs : List Char) : Bool :=
  let cs := cs.dropWhile Char.isWhitespace
  if binderPreds.any (endsWith cs) then true
  else if endsWith cs ">" then !(endsWith cs "->" || endsWith cs "=>")
  else match cs with
    | ':' :: ':' :: _ => false
    | ':' :: rest => namesToHead 16 rest false
    | _ => false

open Lean.Parser in
/-- Fails, consuming nothing, at the type or bound of an unbracketed binder. -/
def notBinderBoundFn : ParserFn := fun c s =>
  if binderBound (charsBefore c.inputString s.pos 160) then
    s.mkUnexpectedError "a binder's type or bound is not a sequent context"
  else s

open Lean.Parser in
def notBinderBound : Parser := { fn := notBinderBoundFn, info := epsilonInfo }

@[combinator_formatter notBinderBound]
def notBinderBound.formatter : Lean.PrettyPrinter.Formatter := pure ()

@[combinator_parenthesizer notBinderBound]
def notBinderBound.parenthesizer : Lean.PrettyPrinter.Parenthesizer := pure ()

open Lean.Parser in
/-- The context variable of `Γ, A ⊢ B`: an identifier that is not a binder's type or bound. -/
@[run_parser_attribute_hooks]
def ctxIdent : Parser :=
  withAntiquot (mkAntiquot "ident" identKind) (notBinderBound >> identNoAntiquot)

end Guard

/-! ## Syntax

A sequent has precedence 26, below the formula connectives, and its right side
and every context entry after a comma are parsed at 27, so a formula
(`∧` 35, `∨` 30, `↠` 27) needs no parentheses there and cannot swallow a
sequent: `Γ, A ∧ B ⊢ C ↠ D`.  `→` (25) and `↔` (20) stay outside:
`Γ ⊢ A → Δ ⊢ B` is an implication between sequents.  `¬` takes its argument at
40, so its sequent needs parentheses, or use `⊬`.  The right side and each entry
may be typed, `p : A`. -/

/-- A context entry: a formula `A`, or a typed entry `u : A`. -/
declare_syntax_cat turnstileEntry
syntax term:27 (" : " term:27)? : turnstileEntry

/-- `Γ ⊢ A`: derivability in the default calculus of the open scope; `Γ ⊢ p : A` for a typing judgement. -/
syntax:26 term:56 " ⊢ " term:27 (" : " term:27)? : term
syntax:26 Guard.ctxIdent atomic((", " turnstileEntry)+ " ⊢ ") term:27 (" : " term:27)? : term
syntax:26 " ⊢ " term:27 (" : " term:27)? : term

/-- `Γ ⊨ A`: consequence under the default semantics of the open scope; `Γ ⊨ p : A` for a typing judgement. -/
syntax:26 term:56 " ⊨ " term:27 (" : " term:27)? : term
syntax:26 Guard.ctxIdent atomic((", " turnstileEntry)+ " ⊨ ") term:27 (" : " term:27)? : term
syntax:26 " ⊨ " term:27 (" : " term:27)? : term

/-- `Γ ⊬ A`: not derivable in the default calculus of the open scope; `Γ ⊬ p : A` for a typing judgement. -/
syntax:26 term:56 " ⊬ " term:27 (" : " term:27)? : term
syntax:26 Guard.ctxIdent atomic((", " turnstileEntry)+ " ⊬ ") term:27 (" : " term:27)? : term
syntax:26 " ⊬ " term:27 (" : " term:27)? : term

/-- `Γ ⊭ A`: not a consequence under the default semantics of the open scope; `Γ ⊭ p : A` for a typing judgement. -/
syntax:26 term:56 " ⊭ " term:27 (" : " term:27)? : term
syntax:26 Guard.ctxIdent atomic((", " turnstileEntry)+ " ⊭ ") term:27 (" : " term:27)? : term
syntax:26 " ⊭ " term:27 (" : " term:27)? : term

/-- `Γ ⊢[R] A` is `R Γ A`; `Γ ⊢[R] p : A` is `R p Γ A`. -/
syntax:26 term:56 " ⊢[" term "] " term:27 (" : " term:27)? : term
syntax:26 Guard.ctxIdent atomic((", " turnstileEntry)+ " ⊢[") term "] " term:27 (" : " term:27)? : term
syntax:26 " ⊢[" term "] " term:27 (" : " term:27)? : term

/-- `Γ ⊨[R] A` is `R Γ A`; `Γ ⊨[R] p : A` is `R p Γ A`. -/
syntax:26 term:56 " ⊨[" term "] " term:27 (" : " term:27)? : term
syntax:26 Guard.ctxIdent atomic((", " turnstileEntry)+ " ⊨[") term "] " term:27 (" : " term:27)? : term
syntax:26 " ⊨[" term "] " term:27 (" : " term:27)? : term

/-- `Γ ⊬[R] A` is not `R Γ A`; `Γ ⊬[R] p : A` is not `R p Γ A`. -/
syntax:26 term:56 " ⊬[" term "] " term:27 (" : " term:27)? : term
syntax:26 Guard.ctxIdent atomic((", " turnstileEntry)+ " ⊬[") term "] " term:27 (" : " term:27)? : term
syntax:26 " ⊬[" term "] " term:27 (" : " term:27)? : term

/-- `Γ ⊭[R] A` is not `R Γ A`; `Γ ⊭[R] p : A` is not `R p Γ A`. -/
syntax:26 term:56 " ⊭[" term "] " term:27 (" : " term:27)? : term
syntax:26 Guard.ctxIdent atomic((", " turnstileEntry)+ " ⊭[") term "] " term:27 (" : " term:27)? : term
syntax:26 " ⊭[" term "] " term:27 (" : " term:27)? : term

/-! ## Elaboration -/

/-- `¬ e` for a proposition, `¬ Nonempty e` for a type of derivations. -/
def negate (e : Expr) : TermElabM Expr := do
  let ty ← whnf (← inferType e)
  if ty.isProp then return mkNot e
  return mkNot (← mkAppM ``Nonempty #[e])

/-- The head constant of a type. -/
def headName? (T : Expr) : MetaM (Option Name) := do
  return (← whnfR (← instantiateMVars T)).getAppFn.constName?

/-- The number of explicit arguments of `R`. -/
def explicitCount (R : Expr) : MetaM Nat := do
  let (_, bis, _) ← forallMetaTelescopeReducing (← inferType R)
  return (bis.filter (·.isExplicit)).size

/-- The types of the last explicit arguments of `R`: context and formula, or proof term,
context and formula for a typing judgement. -/
def argTypes (R : Expr) (typed : Bool) : MetaM (Array Expr) := do
  let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType R)
  let expl := (xs.zip bis).filter (·.2.isExplicit) |>.map (·.1)
  let n := if typed then 3 else 2
  unless expl.size ≥ n do
    throwError "`{R}` does not take {if typed then "a proof term, " else ""}a context and a formula"
  (expl.extract (expl.size - n) expl.size).mapM inferType

/-- Elaborate at exactly the type `T`: no coercion is inserted, pending instances are
settled, so a failure here is a failure (a list is not taken for a set).  An unbound
identifier is a free variable where `T` has one. -/
def elabAt (t : Term) (T : Expr) : TermElabM Expr := do
  let e ← Connectives.elabFree t T
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq (← inferType e) T do
    throwErrorAt t "expected {T}, got {← inferType e}"
  return e

/-- A context entry: the term, and its typing if it is written `u : A`. -/
def entryParts (e : TSyntax `turnstileEntry) : Term × Option Term :=
  match e with
  | `(turnstileEntry| $t:term $[: $T]?) => (t, T)
  | _ => (⟨e.raw⟩, none)

/-- An entry at element type `E`: `u : A` is the pair `(u, A)` when `E` is a product,
and `(u : A)` otherwise. -/
def elabEntry (E : Expr) (entry : Term × Option Term) : TermElabM Expr := do
  match entry with
  | (t, none) => elabAt t E
  | (t, some T) =>
    let E' ← whnfR (← instantiateMVars E)
    if E'.isAppOfArity ``Prod 2 then
      mkAppM ``Prod.mk #[← elabAt t E'.appFn!.appArg!, ← elabAt T E'.appArg!]
    else elabAt (← `(($t : $T))) E

/-- The context `first, rest…` at context type `C`, element type `E`: `Γ, A, B` is
`B :: A :: Γ` (or `insert B (insert A Γ)`); a first entry that is not a context is an
element (`A, B` is `[A, B]`); no entries is the empty context. -/
def elabCtx (C E : Expr) (first : Option Term) (rest : Array (Term × Option Term)) :
    TermElabM Expr := do
  let container ← headName? C
  let cons (a acc : Expr) : TermElabM Expr := do
    match container with
    | some ``List => mkAppM ``List.cons #[a, acc]
    | some `Set => mkAppOptM ``Insert.insert #[E, C, none, a, acc]
    | _ => throwError "`Γ, A` needs a `List` or `Set` context, not {C}"
  let empty : TermElabM Expr := do
    match container with
    | some ``List => mkAppOptM ``List.nil #[E]
    | some `Set => mkAppOptM ``EmptyCollection.emptyCollection #[C, none]
    | _ => throwError "the empty context needs a `List` or `Set` context, not {C}"
  match first with
  | none => empty
  | some t =>
    let s ← saveState
    let asContext ← try some <$> withoutErrToSorry (elabAt t C) catch _ => s.restore; pure none
    match asContext with
    | some Γ =>
      (← rest.mapM (elabEntry E)).foldlM (fun acc a => cons a acc) Γ
    | none =>
      if rest.isEmpty then return ← elabAt t C   -- report the real error
      let fs ← (#[(t, none)] ++ rest).mapM (elabEntry E)
      fs.foldrM (fun a acc => cons a acc) (← empty)

/-- The element type of a context type `List E` or `Set E`. -/
def elemType (C : Expr) : MetaM Expr := do
  let C' ← whnfR (← instantiateMVars C)
  if C'.getAppNumArgs ≥ 1 then return C'.appArg!
  throwError "a context type `List E` or `Set E` was expected, not {C}"

/-- `R ctx A`, or `R p ctx A` for a typing judgement. -/
def elabSequentWith (R : Expr) (typed : Bool) (first : Option Term)
    (rest : Array (Term × Option Term)) (pf : Option Term) (A : Term) : TermElabM Expr := do
  let ts ← argTypes R typed
  if typed then
    let some pf := pf | throwError "a typing judgement is written `Γ ⊢ p : A`"
    let ctx ← elabCtx ts[1]! (← elemType ts[1]!) first rest
    let p ← elabAt pf ts[0]!
    let a ← elabAt A ts[2]!
    mkAppM' R #[p, ctx, a]
  else
    let ctx ← elabCtx ts[0]! ts[1]! first rest
    let a ← elabAt A ts[1]!
    mkAppM' R #[ctx, a]

/-- The right side `X`, or `X : Y`: a typing judgement's proof term and formula, or a
formula and the type it is ascribed. -/
structure Rhs where
  x : Term
  y : Option Term

/-- `e`, ascribed the type written after `:` if there is one. -/
def ascribe (e : Expr) (T? : Option Term) : TermElabM Expr := do
  let some T := T? | return e
  ensureHasType (← elabType T) e

/-- Try each candidate relation; exactly one must fit. -/
def pickOne (sym : String) (cands : List (Name × Bool)) (run : Expr → Bool → TermElabM Expr)
    (ctxless : Bool) : TermElabM Expr := do
  let s0 ← saveState
  let mut ok : Array (Name × Expr × Term.SavedState) := #[]
  let mut lastErr : Option Exception := none
  for (d, typed) in cands do
    s0.restore
    try
      let e ← withoutErrToSorry do
        let e ← run (← mkConstWithFreshMVarLevels d) typed
        synthesizeSyntheticMVarsNoPostponing
        pure e
      ok := ok.push (d, e, ← saveState)
    catch ex => lastErr := some ex
  match ok, lastErr with
  | #[(_, e, s)], _ => s.restore; return e
  | #[], some ex => s0.restore; throw ex
  | #[], none => s0.restore; throwError "no default relation for `{sym}` fits"
  | _, _ =>
    s0.restore
    let hint := if ctxless then
      " (a context without a context variable could be a list or a set: write `[A, B]` or `{A, B}`)"
      else ""
    let names := ", ".intercalate (ok.toList.map (·.1.toString))
    throwError "`{sym}` is ambiguous here ({names}): write `Γ {sym}[R] A`{hint}"

/-- A plain sequent: the unique in-scope default it type-checks against.  With `X : Y`
a typing judgement is tried first, then the sequent `Γ ⊢ X` ascribed `Y`. -/
def elabPlain (k : Kind) (sym : String) (first : Option Term)
    (rest : Array (Term × Option Term)) (rhs : Rhs) : TermElabM Expr := do
  let env ← getEnv
  let ds := (defaults.getState env).toList.filter fun n => kindOf? env n == some k
  if ds.isEmpty then
    throwError "no default relation for `{sym}` in scope: write `Γ {sym}[R] A`, or open the \
      development that declares one"
  let ctxless := first.isNone || !rest.isEmpty
  let untyped := (ds.filter fun d => !typedOf env d).map (·, false)
  let typed := (ds.filter fun d => typedOf env d).map (·, true)
  let asSequent : TermElabM Expr :=
    pickOne sym untyped (fun R t => elabSequentWith R t first rest none rhs.x) ctxless
  match rhs.y with
  | none =>
    if untyped.isEmpty then
      throwError "the default relation for `{sym}` here is a typing judgement: write `Γ {sym} p : A`"
    asSequent
  | some y =>
    if typed.isEmpty then return ← ascribe (← asSequent) (some y)
    let s ← saveState
    try
      pickOne sym typed (fun R t => elabSequentWith R t first rest (some rhs.x) y) ctxless
    catch ex =>
      if untyped.isEmpty then throw ex
      let sT ← saveState
      s.restore
      try ascribe (← asSequent) (some y)
      catch _ => sT.restore; throw ex

/-- `Γ ⊢[R] A`, or `Γ ⊢[R] p : A` when `R` is a typing judgement. -/
def elabTagged (R : Term) (first : Option Term) (rest : Array (Term × Option Term)) (rhs : Rhs) :
    TermElabM Expr := do
  let r ← elabTerm R none
  synthesizeSyntheticMVarsNoPostponing
  let r ← instantiateMVars r
  match rhs.y with
  | none => elabSequentWith r false first rest none rhs.x
  | some y =>
    let typed ← match r.getAppFn.constName? with
      | some c => pure (typedOf (← getEnv) c)
      | none => do pure (decide ((← explicitCount r) ≥ 3))   -- a relation variable
    if typed then elabSequentWith r true first rest (some rhs.x) y
    else ascribe (← elabSequentWith r false first rest none rhs.x) (some y)

elab_rules : term
  | `($Γ:term ⊢ $A $[: $B]?) => elabPlain .derive "⊢" Γ #[] ⟨A, B⟩
  | `($Γ:ident $[, $rest]* ⊢ $A $[: $B]?) =>
    elabPlain .derive "⊢" (some ⟨Γ.raw⟩) (rest.map entryParts) ⟨A, B⟩
  | `(⊢ $A $[: $B]?) => elabPlain .derive "⊢" none #[] ⟨A, B⟩
  | `($Γ:term ⊨ $A $[: $B]?) => elabPlain .consequence "⊨" Γ #[] ⟨A, B⟩
  | `($Γ:ident $[, $rest]* ⊨ $A $[: $B]?) =>
    elabPlain .consequence "⊨" (some ⟨Γ.raw⟩) (rest.map entryParts) ⟨A, B⟩
  | `(⊨ $A $[: $B]?) => elabPlain .consequence "⊨" none #[] ⟨A, B⟩
  | `($Γ:term ⊬ $A $[: $B]?) => do negate (← elabPlain .derive "⊬" Γ #[] ⟨A, B⟩)
  | `($Γ:ident $[, $rest]* ⊬ $A $[: $B]?) =>
    do negate (← elabPlain .derive "⊬" (some ⟨Γ.raw⟩) (rest.map entryParts) ⟨A, B⟩)
  | `(⊬ $A $[: $B]?) => do negate (← elabPlain .derive "⊬" none #[] ⟨A, B⟩)
  | `($Γ:term ⊭ $A $[: $B]?) => do negate (← elabPlain .consequence "⊭" Γ #[] ⟨A, B⟩)
  | `($Γ:ident $[, $rest]* ⊭ $A $[: $B]?) =>
    do negate (← elabPlain .consequence "⊭" (some ⟨Γ.raw⟩) (rest.map entryParts) ⟨A, B⟩)
  | `(⊭ $A $[: $B]?) => do negate (← elabPlain .consequence "⊭" none #[] ⟨A, B⟩)
  | `($Γ:term ⊢[$R] $A $[: $B]?) => elabTagged R Γ #[] ⟨A, B⟩
  | `($Γ:ident $[, $rest]* ⊢[$R] $A $[: $B]?) =>
    elabTagged R (some ⟨Γ.raw⟩) (rest.map entryParts) ⟨A, B⟩
  | `(⊢[$R] $A $[: $B]?) => elabTagged R none #[] ⟨A, B⟩
  | `($Γ:term ⊨[$R] $A $[: $B]?) => elabTagged R Γ #[] ⟨A, B⟩
  | `($Γ:ident $[, $rest]* ⊨[$R] $A $[: $B]?) =>
    elabTagged R (some ⟨Γ.raw⟩) (rest.map entryParts) ⟨A, B⟩
  | `(⊨[$R] $A $[: $B]?) => elabTagged R none #[] ⟨A, B⟩
  | `($Γ:term ⊬[$R] $A $[: $B]?) => do negate (← elabTagged R Γ #[] ⟨A, B⟩)
  | `($Γ:ident $[, $rest]* ⊬[$R] $A $[: $B]?) =>
    do negate (← elabTagged R (some ⟨Γ.raw⟩) (rest.map entryParts) ⟨A, B⟩)
  | `(⊬[$R] $A $[: $B]?) => do negate (← elabTagged R none #[] ⟨A, B⟩)
  | `($Γ:term ⊭[$R] $A $[: $B]?) => do negate (← elabTagged R Γ #[] ⟨A, B⟩)
  | `($Γ:ident $[, $rest]* ⊭[$R] $A $[: $B]?) =>
    do negate (← elabTagged R (some ⟨Γ.raw⟩) (rest.map entryParts) ⟨A, B⟩)
  | `(⊭[$R] $A $[: $B]?) => do negate (← elabTagged R none #[] ⟨A, B⟩)

/-! ## Printing -/

/-- The number of arguments of a full application of `n`, if its last `k` are explicit. -/
def arity (n : Name) (k : Nat) : MetaM (Option Nat) := do
  forallTelescopeReducing (← getConstInfo n).type fun xs _ => do
    if xs.size < k then return none
    for i in [0:k] do
      unless (← xs[xs.size - 1 - i]!.fvarId!.getBinderInfo).isExplicit do return none
    return some xs.size

/-- Print without a tag: `n` is an in-scope default and no other in-scope default
of the same kind has the same type. -/
def printPlain (n : Name) (k : Kind) : MetaM Bool := do
  let env ← getEnv
  let ds := defaults.getState env
  unless ds.contains n do return false
  let ty := (← getConstInfo n).type
  for d in ds.toList do
    if d != n && kindOf? env d == some k then
      if (← getConstInfo d).type == ty then return false
  return true

/-- Is there an in-scope default of kind `k` other than `n`? -/
def otherDefault (n : Name) (k : Kind) : MetaM Bool := do
  let env ← getEnv
  return (defaults.getState env).toList.any fun d => d != n && kindOf? env d == some k

/-- A context entry: `u : A` for a pair when `typed`, the element itself otherwise. -/
def delabEntry (typed : Bool) : DelabM (TSyntax `turnstileEntry) := do
  let e ← getExpr
  if typed && e.isAppOfArity ``Prod.mk 4 then
    let u ← withAppFn (withAppArg Connectives.delabFree)
    let A ← withAppArg delab
    `(turnstileEntry| $u:term : $A)
  else
    let t ← delab
    `(turnstileEntry| $t:term)

/-- A context as `first, rest…` (`none`: the empty context, printed only when unambiguous). -/
partial def delabCtx (typed emptyOk : Bool) :
    DelabM (Option Term × Array (TSyntax `turnstileEntry)) := do
  let e ← getExpr
  if e.isAppOfArity ``List.cons 3 && e.listLit?.isNone then
    let (first, rest) ← withAppArg (delabCtx typed false)
    return (first, rest.push (← withAppFn (withAppArg (delabEntry typed))))
  if e.isAppOfArity ``Insert.insert 5 then
    let (first, rest) ← withAppArg (delabCtx typed false)
    return (first, rest.push (← withAppFn (withAppArg (delabEntry typed))))
  if emptyOk && (e.isAppOfArity ``List.nil 1 || e.isAppOfArity ``EmptyCollection.emptyCollection 2) then
    return (none, #[])
  return (some (← delab), #[])

/-- The pieces of a registered relation's application. -/
structure Parts where
  kind : Kind
  plain : Bool
  tag : Term
  first : Option Term
  rest : Array (TSyntax `turnstileEntry)
  rhs : Term
  typing : Option Term

/-- The pieces of `R … Γ A`, or `R … p Γ A` for a typing judgement. -/
def turnstileParts : DelabM Parts := do
  let e ← getExpr
  let .const c _ := e.getAppFn | failure
  let env ← getEnv
  let some k := kindOf? env c | failure
  let typed := typedOf env c
  let some n ← arity c (if typed then 3 else 2) | failure
  unless e.getAppNumArgs == n do failure
  let plain ← printPlain c k
  let emptyOk := plain && !(← otherDefault c k)
  let (first, rest) ← withAppFn <| withAppArg (delabCtx typed emptyOk)
  let A ← withAppArg delab
  let (x, y, tag) ← if typed then do
      let p ← withAppFn <| withAppFn <| withAppArg Connectives.delabFree
      let tag ← withAppFn <| withAppFn <| withAppFn delab
      pure (p, some A, tag)
    else do
      let tag ← withAppFn <| withAppFn delab
      pure (A, none, tag)
  -- before commas the first entry must be an identifier; otherwise print the context whole
  let (first, rest) ← match first with
    | some f =>
      if rest.isEmpty || f.raw.isIdent then pure (some f, rest)
      else pure (some (← withAppFn <| withAppArg delab), #[])
    | none => pure (none, rest)
  return { kind := k, plain, tag, first, rest, rhs := x, typing := y }

/-- The sequent syntax. -/
def mkSequent (neg : Bool) (P : Parts) : DelabM Term := do
  let A := P.rhs; let B := P.typing; let R := P.tag
  match P.kind, neg, P.plain, P.first, P.rest.isEmpty with
  | .derive, false, true, some Γ, true => `($Γ ⊢ $A $[: $B]?)
  | .derive, false, true, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $(P.rest)]* ⊢ $A $[: $B]?)
  | .derive, false, true, none, _ => `(⊢ $A $[: $B]?)
  | .derive, false, false, some Γ, true => `($Γ ⊢[$R] $A $[: $B]?)
  | .derive, false, false, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $(P.rest)]* ⊢[$R] $A $[: $B]?)
  | .derive, false, false, none, _ => `(⊢[$R] $A $[: $B]?)
  | .consequence, false, true, some Γ, true => `($Γ ⊨ $A $[: $B]?)
  | .consequence, false, true, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $(P.rest)]* ⊨ $A $[: $B]?)
  | .consequence, false, true, none, _ => `(⊨ $A $[: $B]?)
  | .consequence, false, false, some Γ, true => `($Γ ⊨[$R] $A $[: $B]?)
  | .consequence, false, false, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $(P.rest)]* ⊨[$R] $A $[: $B]?)
  | .consequence, false, false, none, _ => `(⊨[$R] $A $[: $B]?)
  | .derive, true, true, some Γ, true => `($Γ ⊬ $A $[: $B]?)
  | .derive, true, true, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $(P.rest)]* ⊬ $A $[: $B]?)
  | .derive, true, true, none, _ => `(⊬ $A $[: $B]?)
  | .derive, true, false, some Γ, true => `($Γ ⊬[$R] $A $[: $B]?)
  | .derive, true, false, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $(P.rest)]* ⊬[$R] $A $[: $B]?)
  | .derive, true, false, none, _ => `(⊬[$R] $A $[: $B]?)
  | .consequence, true, true, some Γ, true => `($Γ ⊭ $A $[: $B]?)
  | .consequence, true, true, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $(P.rest)]* ⊭ $A $[: $B]?)
  | .consequence, true, true, none, _ => `(⊭ $A $[: $B]?)
  | .consequence, true, false, some Γ, true => `($Γ ⊭[$R] $A $[: $B]?)
  | .consequence, true, false, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $(P.rest)]* ⊭[$R] $A $[: $B]?)
  | .consequence, true, false, none, _ => `(⊭[$R] $A $[: $B]?)

@[delab app]
def delabTurnstile : Delab := whenPPOption getPPNotation do
  mkSequent false (← turnstileParts)

@[delab app.Not]
def delabNotTurnstile : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  unless e.getAppNumArgs == 1 do failure
  let inner := e.appArg!
  let viaNonempty := inner.isAppOfArity ``Nonempty 1
  let P ← if viaNonempty then withAppArg <| withAppArg turnstileParts else withAppArg turnstileParts
  let rel := if viaNonempty then inner.appArg! else inner
  let isProp ← withNewMCtxDepth do return (← whnf (← inferType rel)).isProp
  unless isProp != viaNonempty do failure
  mkSequent true P

end LaxLogic.Turnstile
