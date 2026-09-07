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
  | .and A B      => .and (NForm.toForm bs A) (NForm.toForm bs B)
  | .or A B       => .or (NForm.toForm bs A) (NForm.toForm bs B)
  | .imp A B      => .imp (NForm.toForm bs A) (NForm.toForm bs B)
  | .circ q A     => .circ q (NForm.toForm bs A)
  | .forall_ x A  => .forall_ (NForm.toForm (x :: bs) A)
  | .exists_ x A  => .exists_ (NForm.toForm (x :: bs) A)

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
  | .and A B   => .and (Form.toN bs avoid A) (Form.toN bs avoid B)
  | .or A B    => .or (Form.toN bs avoid A) (Form.toN bs avoid B)
  | .imp A B   => .imp (Form.toN bs avoid A) (Form.toN bs avoid B)
  | .circ q A  => .circ q (Form.toN bs avoid A)
  | .forall_ A =>
      let x := freshFrom indivName (bs ++ avoid)
      .forall_ x (Form.toN (x :: bs) avoid A)
  | .exists_ A =>
      let x := freshFrom indivName (bs ++ avoid)
      .exists_ x (Form.toN (x :: bs) avoid A)

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
  | .circ .all A  => "◯∀ " ++ NForm.render 40 A
  | .circ .ex A   => "◯∃ " ++ NForm.render 40 A
  | .and A B      =>
      let s := NForm.render 36 A ++ " ∧ " ++ NForm.render 35 B
      if prec > 35 then "(" ++ s ++ ")" else s
  | .or A B       =>
      let s := NForm.render 31 A ++ " ∨ " ++ NForm.render 30 B
      if prec > 30 then "(" ++ s ++ ")" else s
  | .imp A B      =>
      let s := NForm.render 26 A ++ " ⊃ " ++ NForm.render 25 B
      if prec > 25 then "(" ++ s ++ ")" else s
  | .forall_ x A  =>
      let s := "∀" ++ x ++ ". " ++ NForm.render 20 A
      if prec > 26 then "(" ++ s ++ ")" else s
  | .exists_ x A  =>
      let s := "∃" ++ x ++ ". " ++ NForm.render 20 A
      if prec > 26 then "(" ++ s ++ ")" else s

/-- Render a formula in surface syntax.  The result parses back inside `qf[…]`. -/
def render (A : Form) : String :=
  NForm.render 0 (Form.toN [] A.fv A)

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
  | `(nf[◯∀ $A])               => `(NForm.circ Q.all nf[$A])
  | `(nf[◯∃ $A])               => `(NForm.circ Q.ex nf[$A])
  | `(nf[$A ∧ $B])             => `(NForm.and nf[$A] nf[$B])
  | `(nf[$A ∨ $B])             => `(NForm.or nf[$A] nf[$B])
  | `(nf[$A ⊃ $B])             => `(NForm.imp nf[$A] nf[$B])
  | `(nf[∀ $x:ident . $A])     => `(NForm.forall_ $(Lean.quote x.getId.toString) nf[$A])
  | `(nf[∃ $x:ident . $A])     => `(NForm.exists_ $(Lean.quote x.getId.toString) nf[$A])
  | `(nf[($A)])                => `(nf[$A])

/-- A formula in surface syntax, as a locally nameless `Form`. -/
syntax "qf[" qllForm "]" : term
macro_rules | `(qf[$A]) => `(NForm.toForm [] nf[$A])

/-! # Proof terms

The same three pieces again — a named AST, a name→index function, a printer —
but now with **two** binder stacks, because `λu. p` binds a proof variable,
`⟨p | x⟩` binds an individual, and `case r of [ι[x](u) → p]` binds one of each.
The stacks are independent, which is what makes that last case work.

Concrete syntax, following Fig. 5 as closely as it can be parsed:

| Fig. 5 | here |
| :-- | :-- |
| `*`, `(p,q)`, `π₁(r)`, `π₂(r)` | `*`, `(p, q)`, `π₁ r`, `π₂ r` |
| `ι₁(p)`, `ι₂(q)` | `ι₁ p`, `ι₂ q` |
| `case r of [ι₁(y) → p, ι₂(z) → q]` | the same |
| `λz.p`, `p q` | `λu. p`, `p q` |
| `val_Q(p)`, `let_Q z ⇐ p in q` | `val∀ p` / `val∃ p`, `let∀ u ⇐ p in q` |
| `⟨p \| x⟩`, `π_t(p)`, `ι_t(p)` | `⟨p \| x⟩`, `π[t] p`, `ι[t] p` |
| `case r of [ι_x(z) → p]` | `case r of [ι[x](u) → p]` |
| — (ours) | `exf[A] p` |
-/

/-- Proof terms with named binders. -/
inductive NPf where
  | var    : String → NPf
  | star   : NPf
  | pair   : NPf → NPf → NPf
  | fst    : NPf → NPf
  | snd    : NPf → NPf
  | inl    : NPf → NPf
  | inr    : NPf → NPf
  | caseOr : NPf → String → NPf → String → NPf → NPf
  | lam    : String → NPf → NPf
  | app    : NPf → NPf → NPf
  | val    : Q → NPf → NPf
  | letQ   : Q → String → NPf → NPf → NPf
  | gen    : String → NPf → NPf
  | inst   : NTm → NPf → NPf
  | pack   : NTm → NPf → NPf
  | caseEx : NPf → String → String → NPf → NPf
  | exf    : NForm → NPf → NPf
  deriving Inhabited

/-- `ps` is the proof-variable binder stack, `is` the individual one. -/
def NPf.toPf (ps is : List String) : NPf → Pf
  | .var x            => match idxOf? ps x with
                         | some i => .bvar i
                         | none   => .fvar x
  | .star             => .star
  | .pair p q         => .pair (NPf.toPf ps is p) (NPf.toPf ps is q)
  | .fst p            => .fst (NPf.toPf ps is p)
  | .snd p            => .snd (NPf.toPf ps is p)
  | .inl p            => .inl (NPf.toPf ps is p)
  | .inr p            => .inr (NPf.toPf ps is p)
  | .caseOr r y p z q => .caseOr (NPf.toPf ps is r)
                           (NPf.toPf (y :: ps) is p) (NPf.toPf (z :: ps) is q)
  | .lam u p          => .lam (NPf.toPf (u :: ps) is p)
  | .app p q          => .app (NPf.toPf ps is p) (NPf.toPf ps is q)
  | .val q p          => .val q (NPf.toPf ps is p)
  | .letQ q u p b     => .letQ q (NPf.toPf ps is p) (NPf.toPf (u :: ps) is b)
  | .gen x p          => .gen (NPf.toPf ps (x :: is) p)
  | .inst t p         => .inst (NTm.toTm is t) (NPf.toPf ps is p)
  | .pack t p         => .pack (NTm.toTm is t) (NPf.toPf ps is p)
  | .caseEx r x u p   => .caseEx (NPf.toPf ps is r)
                           (NPf.toPf (u :: ps) (x :: is) p)
  | .exf A p          => .exf (NForm.toForm is A) (NPf.toPf ps is p)

/-- Names for the two sorts, drawn from their own alphabets and avoiding what
is already in scope. -/
def Pf.toN (ps is avoidP avoidI : List String) : Pf → NPf
  | .bvar i       => .var (ps[i]?.getD s!"?{i}")
  | .fvar x       => .var x
  | .star         => .star
  | .pair p q     => .pair (Pf.toN ps is avoidP avoidI p) (Pf.toN ps is avoidP avoidI q)
  | .fst p        => .fst (Pf.toN ps is avoidP avoidI p)
  | .snd p        => .snd (Pf.toN ps is avoidP avoidI p)
  | .inl p        => .inl (Pf.toN ps is avoidP avoidI p)
  | .inr p        => .inr (Pf.toN ps is avoidP avoidI p)
  | .caseOr r p q =>
      let y := freshFrom proofName (ps ++ avoidP)
      let z := freshFrom proofName (y :: ps ++ avoidP)
      .caseOr (Pf.toN ps is avoidP avoidI r)
        y (Pf.toN (y :: ps) is avoidP avoidI p)
        z (Pf.toN (z :: ps) is avoidP avoidI q)
  | .lam p        =>
      let u := freshFrom proofName (ps ++ avoidP)
      .lam u (Pf.toN (u :: ps) is avoidP avoidI p)
  | .app p q      => .app (Pf.toN ps is avoidP avoidI p) (Pf.toN ps is avoidP avoidI q)
  | .val q p      => .val q (Pf.toN ps is avoidP avoidI p)
  | .letQ q p b   =>
      let u := freshFrom proofName (ps ++ avoidP)
      .letQ q u (Pf.toN ps is avoidP avoidI p) (Pf.toN (u :: ps) is avoidP avoidI b)
  | .gen p        =>
      let x := freshFrom indivName (is ++ avoidI)
      .gen x (Pf.toN ps (x :: is) avoidP avoidI p)
  | .inst t p     => .inst (Tm.toN is t) (Pf.toN ps is avoidP avoidI p)
  | .pack t p     => .pack (Tm.toN is t) (Pf.toN ps is avoidP avoidI p)
  | .caseEx r p   =>
      let x := freshFrom indivName (is ++ avoidI)
      let u := freshFrom proofName (ps ++ avoidP)
      .caseEx (Pf.toN ps is avoidP avoidI r) x u
        (Pf.toN (u :: ps) (x :: is) avoidP avoidI p)
  | .exf A p      => .exf (Form.toN is avoidI A) (Pf.toN ps is avoidP avoidI p)

/-- Precedence: application 80 (left), the prefix formers 90 with an atomic
argument, `λ`/`let`/`case` 20 reaching right, atoms above all of it. -/
def NPf.render (prec : Nat) : NPf → String
  | .var x     => x
  | .star      => "*"
  | .pair p q  => "(" ++ NPf.render 0 p ++ ", " ++ NPf.render 0 q ++ ")"
  | .fst p     => paren90 prec ("π₁ " ++ NPf.render 1000 p)
  | .snd p     => paren90 prec ("π₂ " ++ NPf.render 1000 p)
  | .inl p     => paren90 prec ("ι₁ " ++ NPf.render 1000 p)
  | .inr p     => paren90 prec ("ι₂ " ++ NPf.render 1000 p)
  | .val .all p => paren90 prec ("val∀ " ++ NPf.render 1000 p)
  | .val .ex p  => paren90 prec ("val∃ " ++ NPf.render 1000 p)
  | .inst t p  => paren90 prec ("π[" ++ NTm.render t ++ "] " ++ NPf.render 1000 p)
  | .pack t p  => paren90 prec ("ι[" ++ NTm.render t ++ "] " ++ NPf.render 1000 p)
  | .exf A p   => paren90 prec ("exf[" ++ NForm.render 0 A ++ "] " ++ NPf.render 1000 p)
  | .app p q   =>
      let s := NPf.render 80 p ++ " " ++ NPf.render 81 q
      if prec > 80 then "(" ++ s ++ ")" else s
  | .lam u p   => paren20 prec ("λ" ++ u ++ ". " ++ NPf.render 20 p)
  | .gen x p   => "⟨" ++ NPf.render 0 p ++ " | " ++ x ++ "⟩"
  | .letQ q u p b =>
      let kw := match q with | .all => "let∀ " | .ex => "let∃ "
      paren20 prec (kw ++ u ++ " ⇐ " ++ NPf.render 0 p ++ " in " ++ NPf.render 20 b)
  | .caseOr r y p z q =>
      paren20 prec ("case " ++ NPf.render 0 r ++ " of [ι₁(" ++ y ++ ") → " ++
        NPf.render 0 p ++ ", ι₂(" ++ z ++ ") → " ++ NPf.render 0 q ++ "]")
  | .caseEx r x u p =>
      paren20 prec ("case " ++ NPf.render 0 r ++ " of [ι[" ++ x ++ "](" ++ u ++
        ") → " ++ NPf.render 0 p ++ "]")
where
  paren90 (prec : Nat) (s : String) : String := if prec > 90 then "(" ++ s ++ ")" else s
  paren20 (prec : Nat) (s : String) : String := if prec > 20 then "(" ++ s ++ ")" else s

/-- Render a proof term in surface syntax.  Parses back inside `qp[…]`. -/
def renderPf (p : Pf) : String :=
  NPf.render 0 (Pf.toN [] [] p.fvP p.fvI p)

instance : ToString Pf := ⟨renderPf⟩

/-! ## Input notation for proof terms -/

declare_syntax_cat qllPf

syntax:max ident : qllPf
syntax:max "*" : qllPf
syntax:max "(" qllPf ", " qllPf ")" : qllPf
syntax:max "(" qllPf ")" : qllPf
syntax:max "⟨" qllPf " | " ident "⟩" : qllPf
syntax:90 "π₁" ppSpace qllPf:max : qllPf
syntax:90 "π₂" ppSpace qllPf:max : qllPf
syntax:90 "ι₁" ppSpace qllPf:max : qllPf
syntax:90 "ι₂" ppSpace qllPf:max : qllPf
syntax:90 "val∀" ppSpace qllPf:max : qllPf
syntax:90 "val∃" ppSpace qllPf:max : qllPf
syntax:90 "π" noWs "[" qllTm:0 "]" ppSpace qllPf:max : qllPf
syntax:90 "ι" noWs "[" qllTm:0 "]" ppSpace qllPf:max : qllPf
syntax:90 "exf" noWs "[" qllForm:0 "]" ppSpace qllPf:max : qllPf
syntax:80 qllPf:80 ppSpace qllPf:81 : qllPf
syntax:20 "λ" ident ". " qllPf:20 : qllPf
syntax:20 "let∀ " ident " ⇐ " qllPf:0 " in " qllPf:20 : qllPf
syntax:20 "let∃ " ident " ⇐ " qllPf:0 " in " qllPf:20 : qllPf
syntax:20 "case " qllPf " of " "[" "ι₁" "(" ident ")" " → " qllPf ", " "ι₂" "(" ident ")" " → " qllPf "]" : qllPf
syntax:20 "case " qllPf " of " "[" "ι" noWs "[" ident "]" "(" ident ")" " → " qllPf "]" : qllPf

syntax "np[" qllPf "]" : term

macro_rules
  | `(np[$x:ident])          => `(NPf.var $(Lean.quote x.getId.toString))
  | `(np[*])                 => `(NPf.star)
  | `(np[($p, $q)])          => `(NPf.pair np[$p] np[$q])
  | `(np[($p)])              => `(np[$p])
  | `(np[⟨$p | $x:ident⟩])   => `(NPf.gen $(Lean.quote x.getId.toString) np[$p])
  | `(np[π₁ $p])             => `(NPf.fst np[$p])
  | `(np[π₂ $p])             => `(NPf.snd np[$p])
  | `(np[ι₁ $p])             => `(NPf.inl np[$p])
  | `(np[ι₂ $p])             => `(NPf.inr np[$p])
  | `(np[val∀ $p])           => `(NPf.val Q.all np[$p])
  | `(np[val∃ $p])           => `(NPf.val Q.ex np[$p])
  | `(np[π[$t] $p])          => `(NPf.inst nt[$t] np[$p])
  | `(np[ι[$t] $p])          => `(NPf.pack nt[$t] np[$p])
  | `(np[exf[$A] $p])        => `(NPf.exf nf[$A] np[$p])
  | `(np[$p $q])             => `(NPf.app np[$p] np[$q])
  | `(np[λ $u:ident . $p])   => `(NPf.lam $(Lean.quote u.getId.toString) np[$p])
  | `(np[let∀ $u:ident ⇐ $p in $b]) =>
      `(NPf.letQ Q.all $(Lean.quote u.getId.toString) np[$p] np[$b])
  | `(np[let∃ $u:ident ⇐ $p in $b]) =>
      `(NPf.letQ Q.ex $(Lean.quote u.getId.toString) np[$p] np[$b])
  | `(np[case $r of [ι₁($y:ident) → $p, ι₂($z:ident) → $q]]) =>
      `(NPf.caseOr np[$r] $(Lean.quote y.getId.toString) np[$p]
                          $(Lean.quote z.getId.toString) np[$q])
  | `(np[case $r of [ι[$x:ident]($u:ident) → $p]]) =>
      `(NPf.caseEx np[$r] $(Lean.quote x.getId.toString)
                          $(Lean.quote u.getId.toString) np[$p])

/-- A proof term in surface syntax, as a locally nameless `Pf`. -/
syntax "qp[" qllPf "]" : term
macro_rules | `(qp[$p]) => `(NPf.toPf [] [] np[$p])

end LaxLogic.QLL.Surface
