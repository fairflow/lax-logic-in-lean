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

**Contexts.**  `Γ, A, B ⊢ C` is `B :: A :: Γ` for a list context and
`insert B (insert A Γ)` for a set; `⊢ C` is the empty context (printed only when
no other default could read it); `A, B ⊢ C` with no context variable is
`[A, B] ⊢ C`; a single context term (`A :: Γ`, `Γ ++ Δ`, `[p, q]`) still works.
Before a comma the first entry is an identifier (the context variable, or the first
formula of a context without one); it is never the type or bound of an unbracketed
binder, so `∀ x : T, Γ ⊢ A` and `∀ φ ∈ Ds, Γ, φ ⊢ χ` read as intended.

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
40, so its sequent needs parentheses, or use `⊬`. -/

/-- `Γ ⊢ A`: derivability in the default calculus of the open scope. -/
syntax:26 term:56 " ⊢ " term:27 : term
syntax:26 Guard.ctxIdent atomic((", " term:27)+ " ⊢ ") term:27 : term
syntax:26 " ⊢ " term:27 : term

/-- `Γ ⊨ A`: consequence under the default semantics of the open scope. -/
syntax:26 term:56 " ⊨ " term:27 : term
syntax:26 Guard.ctxIdent atomic((", " term:27)+ " ⊨ ") term:27 : term
syntax:26 " ⊨ " term:27 : term

/-- `Γ ⊬ A`: not derivable in the default calculus of the open scope. -/
syntax:26 term:56 " ⊬ " term:27 : term
syntax:26 Guard.ctxIdent atomic((", " term:27)+ " ⊬ ") term:27 : term
syntax:26 " ⊬ " term:27 : term

/-- `Γ ⊭ A`: not a consequence under the default semantics of the open scope. -/
syntax:26 term:56 " ⊭ " term:27 : term
syntax:26 Guard.ctxIdent atomic((", " term:27)+ " ⊭ ") term:27 : term
syntax:26 " ⊭ " term:27 : term

/-- `Γ ⊢[R] A`: derivability of `A` from `Γ` in the calculus `R`, i.e. `R Γ A`. -/
syntax:26 term:56 " ⊢[" term "] " term:27 : term
syntax:26 Guard.ctxIdent atomic((", " term:27)+ " ⊢[") term "] " term:27 : term
syntax:26 " ⊢[" term "] " term:27 : term

/-- `Γ ⊨[R] A`: semantic consequence of `A` from `Γ` under `R`, i.e. `R Γ A`. -/
syntax:26 term:56 " ⊨[" term "] " term:27 : term
syntax:26 Guard.ctxIdent atomic((", " term:27)+ " ⊨[") term "] " term:27 : term
syntax:26 " ⊨[" term "] " term:27 : term

/-- `Γ ⊬[R] A`: `A` is not derivable from `Γ` in `R`. -/
syntax:26 term:56 " ⊬[" term "] " term:27 : term
syntax:26 Guard.ctxIdent atomic((", " term:27)+ " ⊬[") term "] " term:27 : term
syntax:26 " ⊬[" term "] " term:27 : term

/-- `Γ ⊭[R] A`: `A` is not a consequence of `Γ` under `R`. -/
syntax:26 term:56 " ⊭[" term "] " term:27 : term
syntax:26 Guard.ctxIdent atomic((", " term:27)+ " ⊭[") term "] " term:27 : term
syntax:26 " ⊭[" term "] " term:27 : term

/-! ## Elaboration -/

/-- `¬ e` for a proposition, `¬ Nonempty e` for a type of derivations. -/
def negate (e : Expr) : TermElabM Expr := do
  let ty ← whnf (← inferType e)
  if ty.isProp then return mkNot e
  return mkNot (← mkAppM ``Nonempty #[e])

/-- The head constant of a type. -/
def headName? (T : Expr) : MetaM (Option Name) := do
  return (← whnfR (← instantiateMVars T)).getAppFn.constName?

/-- The types of the last two explicit arguments of `R`: context and formula. -/
def ctxFmTypes (R : Expr) : MetaM (Expr × Expr) := do
  let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType R)
  let expl := (xs.zip bis).filter (·.2.isExplicit) |>.map (·.1)
  unless expl.size ≥ 2 do throwError "`{R}` does not take a context and a formula"
  return (← inferType expl[expl.size - 2]!, ← inferType expl[expl.size - 1]!)

/-- Elaborate at exactly the type `T`: no coercion is inserted, pending instances are
settled, so a failure here is a failure (a list is not taken for a set). -/
def elabAt (t : Term) (T : Expr) : TermElabM Expr := do
  let e ← elabTerm t T
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq (← inferType e) T do
    throwErrorAt t "expected {T}, got {← inferType e}"
  return e

/-- The context `first, rest…` at context type `C`, formula type `F`: `Γ, A, B` is
`B :: A :: Γ` (or `insert B (insert A Γ)`); a first entry that is not a context is a
formula (`A, B` is `[A, B]`); no entries is the empty context. -/
def elabCtx (C F : Expr) (first : Option Term) (rest : Array Term) : TermElabM Expr := do
  let container ← headName? C
  let cons (a acc : Expr) : TermElabM Expr := do
    match container with
    | some ``List => mkAppM ``List.cons #[a, acc]
    | some `Set => mkAppOptM ``Insert.insert #[F, C, none, a, acc]
    | _ => throwError "`Γ, A` needs a `List` or `Set` context, not {C}"
  let empty : TermElabM Expr := do
    match container with
    | some ``List => mkAppOptM ``List.nil #[F]
    | some `Set => mkAppOptM ``EmptyCollection.emptyCollection #[C, none]
    | _ => throwError "the empty context needs a `List` or `Set` context, not {C}"
  match first with
  | none => empty
  | some t =>
    let s ← saveState
    let asContext ← try some <$> withoutErrToSorry (elabAt t C) catch _ => s.restore; pure none
    match asContext with
    | some Γ =>
      (← rest.mapM (elabAt · F)).foldlM (fun acc a => cons a acc) Γ
    | none =>
      if rest.isEmpty then return ← elabAt t C   -- report the real error
      let fs ← (#[t] ++ rest).mapM (elabAt · F)
      fs.foldrM (fun a acc => cons a acc) (← empty)

/-- `R ctx A` for a relation term `R`. -/
def elabSequentWith (R : Expr) (first : Option Term) (rest : Array Term) (A : Term) :
    TermElabM Expr := do
  let (C, F) ← ctxFmTypes R
  let ctx ← elabCtx C F first rest
  let a ← elabAt A F
  mkAppM' R #[ctx, a]

/-- A plain sequent: the unique in-scope default it type-checks against. -/
def elabPlain (k : Kind) (sym : String) (first : Option Term) (rest : Array Term) (A : Term) :
    TermElabM Expr := do
  let env ← getEnv
  let ds := (defaults.getState env).toList.filter fun n => kindOf? env n == some k
  if ds.isEmpty then
    throwError "no default relation for `{sym}` in scope: write `Γ {sym}[R] A`, or open the \
      development that declares one"
  let s0 ← saveState
  let mut ok : Array (Name × Expr × Term.SavedState) := #[]
  let mut lastErr : Option Exception := none
  for d in ds do
    s0.restore
    try
      let e ← withoutErrToSorry do
        let e ← elabSequentWith (← mkConstWithFreshMVarLevels d) first rest A
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
    let hint := if first.isNone || !rest.isEmpty then
      " (a context without a context variable could be a list or a set: write `[A, B]` or `{A, B}`)"
      else ""
    let names := ", ".intercalate (ok.toList.map (·.1.toString))
    throwError "`{sym}` is ambiguous here ({names}): write `Γ {sym}[R] A`{hint}"

def elabTagged (R : Term) (first : Option Term) (rest : Array Term) (A : Term) : TermElabM Expr := do
  let r ← elabTerm R none
  synthesizeSyntheticMVarsNoPostponing
  elabSequentWith (← instantiateMVars r) first rest A

elab_rules : term
  | `($Γ:term ⊢ $A) => elabPlain .derive "⊢" Γ #[] A
  | `($Γ:ident $[, $rest]* ⊢ $A) => elabPlain .derive "⊢" (some ⟨Γ.raw⟩) rest A
  | `(⊢ $A) => elabPlain .derive "⊢" none #[] A
  | `($Γ:term ⊨ $A) => elabPlain .consequence "⊨" Γ #[] A
  | `($Γ:ident $[, $rest]* ⊨ $A) => elabPlain .consequence "⊨" (some ⟨Γ.raw⟩) rest A
  | `(⊨ $A) => elabPlain .consequence "⊨" none #[] A
  | `($Γ:term ⊬ $A) => do negate (← elabPlain .derive "⊬" Γ #[] A)
  | `($Γ:ident $[, $rest]* ⊬ $A) => do negate (← elabPlain .derive "⊬" (some ⟨Γ.raw⟩) rest A)
  | `(⊬ $A) => do negate (← elabPlain .derive "⊬" none #[] A)
  | `($Γ:term ⊭ $A) => do negate (← elabPlain .consequence "⊭" Γ #[] A)
  | `($Γ:ident $[, $rest]* ⊭ $A) => do negate (← elabPlain .consequence "⊭" (some ⟨Γ.raw⟩) rest A)
  | `(⊭ $A) => do negate (← elabPlain .consequence "⊭" none #[] A)
  | `($Γ:term ⊢[$R] $A) => elabTagged R Γ #[] A
  | `($Γ:ident $[, $rest]* ⊢[$R] $A) => elabTagged R (some ⟨Γ.raw⟩) rest A
  | `(⊢[$R] $A) => elabTagged R none #[] A
  | `($Γ:term ⊨[$R] $A) => elabTagged R Γ #[] A
  | `($Γ:ident $[, $rest]* ⊨[$R] $A) => elabTagged R (some ⟨Γ.raw⟩) rest A
  | `(⊨[$R] $A) => elabTagged R none #[] A
  | `($Γ:term ⊬[$R] $A) => do negate (← elabTagged R Γ #[] A)
  | `($Γ:ident $[, $rest]* ⊬[$R] $A) => do negate (← elabTagged R (some ⟨Γ.raw⟩) rest A)
  | `(⊬[$R] $A) => do negate (← elabTagged R none #[] A)
  | `($Γ:term ⊭[$R] $A) => do negate (← elabTagged R Γ #[] A)
  | `($Γ:ident $[, $rest]* ⊭[$R] $A) => do negate (← elabTagged R (some ⟨Γ.raw⟩) rest A)
  | `(⊭[$R] $A) => do negate (← elabTagged R none #[] A)

/-! ## Printing -/

/-- The number of arguments of a full application of `n`, if its last two are explicit. -/
def arity (n : Name) : MetaM (Option Nat) := do
  forallTelescopeReducing (← getConstInfo n).type fun xs _ => do
    if xs.size < 2 then return none
    let b1 ← xs[xs.size - 1]!.fvarId!.getBinderInfo
    let b2 ← xs[xs.size - 2]!.fvarId!.getBinderInfo
    return if b1.isExplicit && b2.isExplicit then some xs.size else none

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

/-- A context as `first, rest…` (`none`: the empty context, printed only when unambiguous). -/
partial def delabCtx (emptyOk : Bool) : DelabM (Option Term × Array Term) := do
  let e ← getExpr
  if e.isAppOfArity ``List.cons 3 && e.listLit?.isNone then
    let (first, rest) ← withAppArg (delabCtx false)
    return (first, rest.push (← withAppFn (withAppArg delab)))
  if e.isAppOfArity ``Insert.insert 5 then
    let (first, rest) ← withAppArg (delabCtx false)
    return (first, rest.push (← withAppFn (withAppArg delab)))
  if emptyOk && (e.isAppOfArity ``List.nil 1 || e.isAppOfArity ``EmptyCollection.emptyCollection 2) then
    return (none, #[])
  return (some (← delab), #[])

/-- The pieces of `R … Γ A` for a registered `R`. -/
def turnstileParts : DelabM (Kind × Bool × Term × Option Term × Array Term × Term) := do
  let e ← getExpr
  let .const c _ := e.getAppFn | failure
  let some k := kindOf? (← getEnv) c | failure
  let some n ← arity c | failure
  unless e.getAppNumArgs == n do failure
  let plain ← printPlain c k
  let emptyOk := plain && !(← otherDefault c k)
  let (first, rest) ← withAppFn <| withAppArg (delabCtx emptyOk)
  let A ← withAppArg delab
  let R ← withAppFn <| withAppFn delab
  -- before commas the first entry must be an identifier; otherwise print the context whole
  let (first, rest) ← match first with
    | some f =>
      if rest.isEmpty || f.raw.isIdent then pure (some f, rest)
      else pure (some (← withAppFn <| withAppArg delab), #[])
    | none => pure (none, rest)
  return (k, plain, R, first, rest, A)

/-- The sequent syntax. -/
def mkSequent (k : Kind) (neg plain : Bool) (R : Term) (first : Option Term)
    (rest : Array Term) (A : Term) : DelabM Term := do
  match k, neg, plain, first, rest.isEmpty with
  | .derive, false, true, some Γ, true => `($Γ ⊢ $A)
  | .derive, false, true, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $rest]* ⊢ $A)
  | .derive, false, true, none, _ => `(⊢ $A)
  | .derive, false, false, some Γ, true => `($Γ ⊢[$R] $A)
  | .derive, false, false, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $rest]* ⊢[$R] $A)
  | .derive, false, false, none, _ => `(⊢[$R] $A)
  | .derive, true, true, some Γ, true => `($Γ ⊬ $A)
  | .derive, true, true, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $rest]* ⊬ $A)
  | .derive, true, true, none, _ => `(⊬ $A)
  | .derive, true, false, some Γ, true => `($Γ ⊬[$R] $A)
  | .derive, true, false, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $rest]* ⊬[$R] $A)
  | .derive, true, false, none, _ => `(⊬[$R] $A)
  | .consequence, false, true, some Γ, true => `($Γ ⊨ $A)
  | .consequence, false, true, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $rest]* ⊨ $A)
  | .consequence, false, true, none, _ => `(⊨ $A)
  | .consequence, false, false, some Γ, true => `($Γ ⊨[$R] $A)
  | .consequence, false, false, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $rest]* ⊨[$R] $A)
  | .consequence, false, false, none, _ => `(⊨[$R] $A)
  | .consequence, true, true, some Γ, true => `($Γ ⊭ $A)
  | .consequence, true, true, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $rest]* ⊭ $A)
  | .consequence, true, true, none, _ => `(⊭ $A)
  | .consequence, true, false, some Γ, true => `($Γ ⊭[$R] $A)
  | .consequence, true, false, some Γ, false => `($(⟨Γ.raw⟩):ident $[, $rest]* ⊭[$R] $A)
  | .consequence, true, false, none, _ => `(⊭[$R] $A)

@[delab app]
def delabTurnstile : Delab := whenPPOption getPPNotation do
  let (k, plain, R, first, rest, A) ← turnstileParts
  mkSequent k false plain R first rest A

@[delab app.Not]
def delabNotTurnstile : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  unless e.getAppNumArgs == 1 do failure
  let inner := e.appArg!
  let viaNonempty := inner.isAppOfArity ``Nonempty 1
  let (k, plain, R, first, rest, A) ←
    if viaNonempty then withAppArg <| withAppArg turnstileParts else withAppArg turnstileParts
  let rel := if viaNonempty then inner.appArg! else inner
  let isProp ← withNewMCtxDepth do return (← whnf (← inferType rel)).isProp
  unless isProp != viaNonempty do failure
  mkSequent k true plain R first rest A

end LaxLogic.Turnstile
