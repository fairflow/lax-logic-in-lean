/-
# `LaxLogic.QLL.Judgement` — `qj[Γ ⊢ p : A]`

`qf[…]` gives a formula and `qp[…]` a proof term; a *judgement* needs both at
once, together with a context, and writing the three brackets out by hand is
exactly the noise the surface layer exists to remove.  So:

    qj[u : A ↠ B, v : A ⊢ u v : B]      the proposition   (`Derivable`)
    qd[u : A ↠ B, v : A ⊢ u v : B]      the type of its derivations (`Derives`)

with `qj[J]` reducing to `Nonempty qd[J]` by definition, which is the whole of
`Derivable = Nonempty ∘ Derives`.  Both brackets are kept: a theorem is stated
with `qj`, a derivation is *built* at type `qd`.

This module, not `Surface`, is where the notation lives, because it is the
first thing in the surface layer that mentions the calculus.

## Context order

The context is written left to right in the conventional order — leftmost
entry bound first, so a repeated name is shadowed by the entry to its *right*,
matching `Ctx.lookup?`, which searches the head of the list first.  The macro
therefore reverses at expansion time, not at run time: the elaborated type
contains a literal list, with no `List.reverse` left in it to obscure the
goal display.

`renderJ` reverses to match, and `JudgementTests.lean` gates the round trip.

## In Lean terms

The same judgement is also a Lean term, `Γ, u : A ↠ B, v : A ⊢ p : B`
(`LaxLogic/Util/Turnstile.lean`, registered on `Derives` in `Deriv.lean`).  A
proof term built from constructors prints there as `qp[…]`, by rendering it and
reading the rendering back, so the infoview and `renderPf` cannot disagree.
-/
import Lean
import LaxLogic.QLL.Surface
import LaxLogic.QLL.Deriv

namespace LaxLogic.QLL.Surface

open LaxLogic.QLL

/-! ## Printing -/

/-- A context entry, `p : A`. -/
def renderEntry (e : Pf × Form) : String :=
  renderPf e.1 ++ " : " ++ render e.2

/-- A context, in the conventional order: the list's *last* entry leftmost. -/
def renderCtx (Γ : Ctx) : String :=
  ", ".intercalate (Γ.reverse.map renderEntry)

/-- A judgement.  The result parses back inside `qj[…]` and `qd[…]`. -/
def renderJ (p : Pf) (Γ : Ctx) (A : Form) : String :=
  (if Γ.isEmpty then "" else renderCtx Γ ++ " ") ++ "⊢ " ++ renderPf p ++ " : " ++ render A

/-! ## Input notation -/

declare_syntax_cat qllEntry
declare_syntax_cat qllJudge

/-- `p : A` — a context entry.  The left-hand side is a full proof term, not
just a variable, because a residual obligation need not be a variable. -/
syntax qllPf:0 " : " qllForm:0 : qllEntry

syntax qllEntry,* " ⊢ " qllPf:0 " : " qllForm:0 : qllJudge

/-- A single context entry, as a `Pf × Form`. -/
syntax "qe[" qllEntry "]" : term
macro_rules | `(qe[$p:qllPf : $A:qllForm]) => `((qp[$p], qf[$A]))

/-- A context in surface syntax, as a `Ctx`. -/
syntax "qc[" qllEntry,* "]" : term
macro_rules
  | `(qc[$[$es],*]) => do
      let es := es.reverse
      `(([$[qe[$es]],*] : Ctx))

/-- The *type of derivations* of a judgement: `Derives p Γ A`. -/
syntax "qd[" qllJudge "]" : term

/-- A judgement as a proposition: `Derivable p Γ A`. -/
syntax "qj[" qllJudge "]" : term

macro_rules
  | `(qd[$[$es],* ⊢ $p:qllPf : $A:qllForm]) => do
      let es := es.reverse
      `(Derives qp[$p] [$[qe[$es]],*] qf[$A])
  | `(qj[$[$es],* ⊢ $p:qllPf : $A:qllForm]) => do
      let es := es.reverse
      `(Derivable qp[$p] [$[qe[$es]],*] qf[$A])

/-! ## Proof terms in the infoview -/

open Lean Meta PrettyPrinter Delaborator SubExpr

/-- A string literal. -/
def strLit? : Expr → Option String
  | .lit (.strVal s) => some s
  | .mdata _ e => strLit? e
  | _ => none

/-- The elements of a list literal. -/
partial def listLit? (e : Expr) : Option (List Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, #[_]) => some []
  | (``List.cons, #[_, h, t]) => (listLit? t).map (h :: ·)
  | _ => none

/-- An individual term built from constructors and literals. -/
partial def reflectTm (e : Expr) : Option Tm :=
  match e.consumeMData.getAppFnArgs with
  | (``Tm.bvar, #[n]) => n.nat?.map .bvar
  | (``Tm.fvar, #[s]) => (strLit? s).map .fvar
  | (``Tm.fn, #[f, ts]) => do
    let f ← strLit? f
    let ts ← listLit? ts
    return .fn f (← ts.mapM reflectTm)
  | _ => none

/-- A modality constructor. -/
def reflectQ (e : Expr) : Option Q :=
  if e.consumeMData.isConstOf ``Q.all then some .all
  else if e.consumeMData.isConstOf ``Q.ex then some .ex else none

/-- A formula built from constructors and literals. -/
partial def reflectForm (e : Expr) : Option Form :=
  match e.consumeMData.getAppFnArgs with
  | (``Form.top, #[]) => some .top
  | (``Form.bot, #[]) => some .bot
  | (``Form.pred, #[P, ts]) => do
    let P ← strLit? P
    return .pred P (← (← listLit? ts).mapM reflectTm)
  | (``Form.and, #[a, b]) => return .and (← reflectForm a) (← reflectForm b)
  | (``Form.or, #[a, b]) => return .or (← reflectForm a) (← reflectForm b)
  | (``Form.imp, #[a, b]) => return .imp (← reflectForm a) (← reflectForm b)
  | (``Form.circ, #[q, a]) => return .circ (← reflectQ q) (← reflectForm a)
  | (``Form.forall_, #[a]) => return .forall_ (← reflectForm a)
  | (``Form.exists_, #[a]) => return .exists_ (← reflectForm a)
  | _ => none

/-- A proof term built from constructors and literals. -/
partial def reflectPf (e : Expr) : Option Pf :=
  match e.consumeMData.getAppFnArgs with
  | (``Pf.bvar, #[n]) => n.nat?.map .bvar
  | (``Pf.fvar, #[s]) => (strLit? s).map .fvar
  | (``Pf.star, #[]) => some .star
  | (``Pf.pair, #[p, q]) => return .pair (← reflectPf p) (← reflectPf q)
  | (``Pf.fst, #[p]) => return .fst (← reflectPf p)
  | (``Pf.snd, #[p]) => return .snd (← reflectPf p)
  | (``Pf.inl, #[p]) => return .inl (← reflectPf p)
  | (``Pf.inr, #[p]) => return .inr (← reflectPf p)
  | (``Pf.caseOr, #[r, p, q]) => return .caseOr (← reflectPf r) (← reflectPf p) (← reflectPf q)
  | (``Pf.lam, #[p]) => return .lam (← reflectPf p)
  | (``Pf.app, #[p, q]) => return .app (← reflectPf p) (← reflectPf q)
  | (``Pf.val, #[q, p]) => return .val (← reflectQ q) (← reflectPf p)
  | (``Pf.letQ, #[q, p, b]) => return .letQ (← reflectQ q) (← reflectPf p) (← reflectPf b)
  | (``Pf.gen, #[p]) => return .gen (← reflectPf p)
  | (``Pf.inst, #[t, p]) => return .inst (← reflectTm t) (← reflectPf p)
  | (``Pf.pack, #[t, p]) => return .pack (← reflectTm t) (← reflectPf p)
  | (``Pf.caseEx, #[r, p]) => return .caseEx (← reflectPf r) (← reflectPf p)
  | (``Pf.exf, #[A, p]) => return .exf (← reflectForm A) (← reflectPf p)
  | _ => none

/-- Drop source positions, so the formatter lays the syntax out afresh. -/
partial def stripInfo : Syntax → Syntax
  | .node _ k args => .node .none k (args.map stripInfo)
  | .atom _ v => .atom .none v
  | .ident _ raw n pre => .ident .none raw n pre
  | .missing => .missing

/-- A proof term built from constructors prints as `qp[…]`: its rendering, read back. -/
def delabPf : Delab := whenPPOption getPPNotation do
  unless ← LaxLogic.QLL.Notation.active do failure
  let some p := reflectPf (← getExpr) | failure
  match p with
  | .fvar _ | .bvar _ => failure
  | _ => pure ()
  match Parser.runParserCategory (← getEnv) `term ("qp[" ++ renderPf p ++ "]") with
  | .ok stx => pure ⟨stripInfo stx⟩
  | .error _ => failure

/-- A context built from literal pairs. -/
def reflectCtx (e : Expr) : Option Ctx := do
  let es ← listLit? e
  es.mapM fun x => match x.consumeMData.getAppFnArgs with
    | (``Prod.mk, #[_, _, p, A]) => return (← reflectPf p, ← reflectForm A)
    | _ => none

/-- A judgement whose proof term, context and formula are all literal prints whole in
surface syntax, `qd[…]` (or `qj[…]` for `Derivable`). -/
def delabJudgement (bracket : String) : Delab := whenPPOption getPPNotation do
  unless ← LaxLogic.QLL.Notation.active do failure
  let e ← getExpr
  unless e.getAppNumArgs == 3 do failure
  let args := e.getAppArgs
  let some p := reflectPf args[0]! | failure
  let some Γ := reflectCtx args[1]! | failure
  let some A := reflectForm args[2]! | failure
  match Parser.runParserCategory (← getEnv) `term (bracket ++ "[" ++ renderJ p Γ A ++ "]") with
  | .ok stx => pure ⟨stripInfo stx⟩
  | .error _ => failure

@[delab app.LaxLogic.QLL.Derives] def delabDerives : Delab := delabJudgement "qd"
@[delab app.LaxLogic.QLL.Derivable] def delabDerivable : Delab := delabJudgement "qj"

@[delab app.LaxLogic.QLL.Pf.star] def delabPfStar : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.pair] def delabPfPair : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.fst] def delabPfFst : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.snd] def delabPfSnd : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.inl] def delabPfInl : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.inr] def delabPfInr : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.caseOr] def delabPfCaseOr : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.lam] def delabPfLam : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.app] def delabPfApp : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.val] def delabPfVal : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.letQ] def delabPfLetQ : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.gen] def delabPfGen : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.inst] def delabPfInst : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.pack] def delabPfPack : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.caseEx] def delabPfCaseEx : Delab := delabPf
@[delab app.LaxLogic.QLL.Pf.exf] def delabPfExf : Delab := delabPf

end LaxLogic.QLL.Surface
