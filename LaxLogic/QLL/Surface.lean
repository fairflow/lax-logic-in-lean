/-
# `LaxLogic.QLL.Surface` — named variables, in and out

De Bruijn indices are right for algorithms and unreadable for people.  Named
free variables we already have; only *bound* occurrences are indices, and their
names are arbitrary — which is exactly what a printer should supply.

So this is a surface layer, not a representation change.  It sits outside the
trusted core: a wrong printer misleads a reader but cannot make a bad
derivation check.  Contrast genuine named binding, where a mistake in
capture-avoidance is a soundness bug.

**The printed form is the input form.**  Whatever `render` emits can be pasted
back inside `qf[…]` and elaborates to the term it came from.  That is a hard
requirement, not a convenience, and `SurfaceTests.lean` gates it — including
the two cases where it could fail silently: shadowing, and a binder that must
not steal a free name.

Formulas and individual terms only, so far.  Proof terms have the same shape of
solution and are not done.

**Distinct alphabets per sort**, following the usual mathematical convention:

| sort | alphabet |
| :-- | :-- |
| individuals (`∀`, `∃`, and arguments of predicates) | `x y z x₁ y₁ z₁ …` |
| proof variables (`λ`, the `case` branches, `let`) | `u v w u₁ v₁ w₁ …` |

The two sorts are the only two: the realiser `p` and the proof term are the
same thing, so `⊃I`/`⊃E` bind proof variables; the arguments of `pred` and the
things `∀`/`∃` quantify over are both individuals.  A third sort appears only
when Fig. 6's target constraint language does, and only if that is a deep
embedding rather than Lean itself.

The binder logic lives in `toForm`/`ofForm` and friends — ordinary total
functions over a named AST — rather than inside an elaborator, so it is
testable rather than merely trusted.
-/
import LaxLogic.QLL.Syntax

namespace LaxLogic.QLL.Surface

open LaxLogic.QLL

/-! ## The named syntax trees -/

/-- Individual terms with named variables. -/
inductive NTm where
  | var : String → NTm
  | fn  : String → List NTm → NTm
  deriving Inhabited

/-- Formulas with named binders. -/
inductive NForm where
  | top     : NForm
  | bot     : NForm
  | pred    : String → List NTm → NForm
  | and     : NForm → NForm → NForm
  | or      : NForm → NForm → NForm
  | imp     : NForm → NForm → NForm
  | circ    : Q → NForm → NForm
  | forall_ : String → NForm → NForm
  | exists_ : String → NForm → NForm
  deriving Inhabited

/-! ## Named → locally nameless

A variable is bound if it appears in the binder stack, and its index is the
distance to the nearest enclosing binder of its own sort. -/

/-- Index of the first occurrence, i.e. the nearest enclosing binder. -/
def idxOf? (bs : List String) (x : String) : Option Nat :=
  bs.findIdx? (· == x)

mutual
def NTm.toTm (bs : List String) : NTm → Tm
  | .var x   => match idxOf? bs x with
                | some i => .bvar i
                | none   => .fvar x
  | .fn f ts => .fn f (NTm.toTmList bs ts)
def NTm.toTmList (bs : List String) : List NTm → List Tm
  | []      => []
  | t :: ts => NTm.toTm bs t :: NTm.toTmList bs ts
end

def NForm.toForm (bs : List String) : NForm → Form
  | .top          => .top
  | .bot          => .bot
  | .pred P ts    => .pred P (NTm.toTmList bs ts)
  | .and M N      => .and (NForm.toForm bs M) (NForm.toForm bs N)
  | .or M N       => .or (NForm.toForm bs M) (NForm.toForm bs N)
  | .imp M N      => .imp (NForm.toForm bs M) (NForm.toForm bs N)
  | .circ q M     => .circ q (NForm.toForm bs M)
  | .forall_ x M  => .forall_ (NForm.toForm (x :: bs) M)
  | .exists_ x M  => .exists_ (NForm.toForm (x :: bs) M)

/-! ## Locally nameless → named

Binders are given names from the individual alphabet, avoiding anything already
in scope so the result cannot capture. -/

/-- `x y z x₁ y₁ z₁ x₂ …` -/
def indivName (n : Nat) : String :=
  let base := ["x", "y", "z"]
  let letter := base[n % 3]!
  let tier := n / 3
  if tier = 0 then letter else letter ++ toString tier

/-- `u v w u₁ v₁ w₁ u₂ …` -/
def proofName (n : Nat) : String :=
  let base := ["u", "v", "w"]
  let letter := base[n % 3]!
  let tier := n / 3
  if tier = 0 then letter else letter ++ toString tier

/-- The first name from the alphabet not already in scope. -/
partial def freshFrom (alphabet : Nat → String) (avoid : List String) : String :=
  let rec go (n : Nat) : String :=
    let c := alphabet n
    if c ∈ avoid then go (n + 1) else c
  go 0

mutual
def Tm.toN (bs : List String) : Tm → NTm
  | .bvar i  => .var (bs[i]?.getD s!"?{i}")
  | .fvar x  => .var x
  | .fn f ts => .fn f (Tm.toNList bs ts)
def Tm.toNList (bs : List String) : List Tm → List NTm
  | []      => []
  | t :: ts => Tm.toN bs t :: Tm.toNList bs ts
end

/-- `bs` is the stack of names given to enclosing individual binders; `avoid`
additionally holds the free names in scope. -/
def Form.toN (bs avoid : List String) : Form → NForm
  | .top       => .top
  | .bot       => .bot
  | .pred P ts => .pred P (Tm.toNList bs ts)
  | .and M N   => .and (Form.toN bs avoid M) (Form.toN bs avoid N)
  | .or M N    => .or (Form.toN bs avoid M) (Form.toN bs avoid N)
  | .imp M N   => .imp (Form.toN bs avoid M) (Form.toN bs avoid N)
  | .circ q M  => .circ q (Form.toN bs avoid M)
  | .forall_ M =>
      let x := freshFrom indivName (bs ++ avoid)
      .forall_ x (Form.toN (x :: bs) avoid M)
  | .exists_ M =>
      let x := freshFrom indivName (bs ++ avoid)
      .exists_ x (Form.toN (x :: bs) avoid M)

/-! ## Rendering

The output is input: every string below parses back inside `qf[…]`. -/

mutual
def NTm.render : NTm → String
  | .var x    => x
  | .fn f ts  => f ++ "(" ++ NTm.renderList ts ++ ")"
def NTm.renderList : List NTm → String
  | []      => ""
  | [t]     => NTm.render t
  | t :: ts => NTm.render t ++ ", " ++ NTm.renderList ts
end

/-- Precedence: `⊃` 25 (right), `∨` 30, `∧` 35, `◯` 40.  A quantifier's *body*
reaches down to 20 so it extends as far right as possible, but the quantifier
itself sits at 26 — otherwise `A ⊃ ∀x. P` would not parse, since `⊃`'s right
operand requires 25. -/
def NForm.render (prec : Nat) : NForm → String
  | .top          => "⊤"
  | .bot          => "⊥"
  | .pred P []    => P
  | .pred P ts    => P ++ "(" ++ NTm.renderList ts ++ ")"
  | .circ .all M  => "◯∀" ++ NForm.render 40 M
  | .circ .ex M   => "◯∃" ++ NForm.render 40 M
  | .and M N      =>
      let s := NForm.render 36 M ++ " ∧ " ++ NForm.render 35 N
      if prec > 35 then "(" ++ s ++ ")" else s
  | .or M N       =>
      let s := NForm.render 31 M ++ " ∨ " ++ NForm.render 30 N
      if prec > 30 then "(" ++ s ++ ")" else s
  | .imp M N      =>
      let s := NForm.render 26 M ++ " ⊃ " ++ NForm.render 25 N
      if prec > 25 then "(" ++ s ++ ")" else s
  | .forall_ x M  =>
      let s := "∀" ++ x ++ ". " ++ NForm.render 20 M
      if prec > 26 then "(" ++ s ++ ")" else s
  | .exists_ x M  =>
      let s := "∃" ++ x ++ ". " ++ NForm.render 20 M
      if prec > 26 then "(" ++ s ++ ")" else s

/-- Render a formula in surface syntax.  The result parses back inside `qf[…]`. -/
def render (M : Form) : String :=
  NForm.render 0 (Form.toN [] M.fv M)

instance : ToString Form := ⟨render⟩

/-! ## Input notation

`qf[∀x. P(x) ⊃ P(x)]` elaborates to the locally nameless `Form`.  The named
AST is built structurally by the macro; the name-to-index conversion is
`NForm.toForm`, an ordinary function, so nothing subtle happens inside the
elaborator. -/

declare_syntax_cat qllTm
declare_syntax_cat qllForm

syntax ident : qllTm
syntax ident noWs "(" qllTm,* ")" : qllTm

syntax "⊤" : qllForm
syntax "⊥" : qllForm
syntax ident noWs "(" qllTm,* ")" : qllForm
syntax ident : qllForm
syntax:40 "◯∀" qllForm:40 : qllForm
syntax:40 "◯∃" qllForm:40 : qllForm
syntax:35 qllForm:36 " ∧ " qllForm:35 : qllForm
syntax:30 qllForm:31 " ∨ " qllForm:30 : qllForm
syntax:25 qllForm:26 " ⊃ " qllForm:25 : qllForm
syntax:26 "∀" ident ". " qllForm:20 : qllForm
syntax:26 "∃" ident ". " qllForm:20 : qllForm
syntax "(" qllForm ")" : qllForm

syntax "nt[" qllTm "]" : term
syntax "nf[" qllForm "]" : term

macro_rules
  | `(nt[$x:ident])            => `(NTm.var $(Lean.quote x.getId.toString))
  | `(nt[$f:ident($ts,*)])     =>
      `(NTm.fn $(Lean.quote f.getId.toString) [$[nt[$ts]],*])

macro_rules
  | `(nf[⊤])                   => `(NForm.top)
  | `(nf[⊥])                   => `(NForm.bot)
  | `(nf[$P:ident($ts,*)])     =>
      `(NForm.pred $(Lean.quote P.getId.toString) [$[nt[$ts]],*])
  | `(nf[$P:ident])            => `(NForm.pred $(Lean.quote P.getId.toString) [])
  | `(nf[◯∀ $M])               => `(NForm.circ Q.all nf[$M])
  | `(nf[◯∃ $M])               => `(NForm.circ Q.ex nf[$M])
  | `(nf[$M ∧ $N])             => `(NForm.and nf[$M] nf[$N])
  | `(nf[$M ∨ $N])             => `(NForm.or nf[$M] nf[$N])
  | `(nf[$M ⊃ $N])             => `(NForm.imp nf[$M] nf[$N])
  | `(nf[∀ $x:ident . $M])     => `(NForm.forall_ $(Lean.quote x.getId.toString) nf[$M])
  | `(nf[∃ $x:ident . $M])     => `(NForm.exists_ $(Lean.quote x.getId.toString) nf[$M])
  | `(nf[($M)])                => `(nf[$M])

/-- A formula in surface syntax, as a locally nameless `Form`. -/
syntax "qf[" qllForm "]" : term
macro_rules | `(qf[$M]) => `(NForm.toForm [] nf[$M])

end LaxLogic.QLL.Surface
