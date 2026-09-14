/-
`{stmt}`Full.Name``: the conventional-notation statement of a declaration,
generated from its type.  Binders become quantifiers, hypotheses premises,
and the object language (`Prv`, `PEq`, `Form`, `Tm`, `Q`) is printed with its
usual symbols through the notation table below; everything else falls back
to a generic reading (connectives, `=`, `∈`, lists, numerals, applications
with implicit arguments dropped) and, last, to Lean's own printer in
typewriter.  Nothing is written by hand: the same declaration always gives
the same mathematics, and it cannot drift from the code.

A declaration whose type is not a proposition (a `def`, an `inductive`)
prints nothing.  Extend `objectLanguage` for another object language.
-/
import Lean
import Lean.DocString.Syntax
import VersoManual
import LaxLogic.QLL

open Lean Meta Elab
open Lean.Doc.Syntax
open Verso Doc Elab Genre Manual ArgParse

namespace CLPPaper.Math

/-- TeX-escape a string for use inside `\mathit{…}`/`\texttt{…}`. -/
def esc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '\\' => "\\backslash " | '{' => "\\{" | '}' => "\\}" | '_' => "\\_" | '#' => "\\#"
      | '%' => "\\%" | '&' => "\\&" | '$' => "\\$" | '^' => "\\^{}" | '~' => "\\~{}"
      | c => c.toString

def greek : List (Char × String) :=
  [('Γ', "\\Gamma"), ('Δ', "\\Delta"), ('Θ', "\\Theta"), ('Σ', "\\Sigma"), ('Π', "\\Pi"),
   ('Λ', "\\Lambda"), ('Φ', "\\Phi"), ('Ψ', "\\Psi"), ('Ω', "\\Omega"),
   ('α', "\\alpha"), ('β', "\\beta"), ('γ', "\\gamma"), ('δ', "\\delta"), ('ε', "\\varepsilon"),
   ('ζ', "\\zeta"), ('η', "\\eta"), ('θ', "\\theta"), ('ι', "\\iota"), ('κ', "\\kappa"),
   ('λ', "\\lambda"), ('μ', "\\mu"), ('ν', "\\nu"), ('ξ', "\\xi"), ('π', "\\pi"), ('ρ', "\\rho"),
   ('σ', "\\sigma"), ('τ', "\\tau"), ('φ', "\\varphi"), ('χ', "\\chi"), ('ψ', "\\psi"), ('ω', "\\omega")]

def subscriptDigits : List (Char × Char) :=
  [('₀','0'),('₁','1'),('₂','2'),('₃','3'),('₄','4'),('₅','5'),('₆','6'),('₇','7'),('₈','8'),('₉','9')]

/-- A variable or field name as mathematics: Greek letters, trailing digits
and subscript digits become subscripts, primes stay, multi-letter names are
set upright-italic. -/
def ident (s : String) : String := Id.run do
  let s := s.replace "✝" ""
  -- split trailing subscript digits / ASCII digits
  let chars := s.toList
  let isSub (c : Char) := subscriptDigits.any (·.1 == c)
  let body := chars.reverse.dropWhile (fun c => c.isDigit || isSub c || c == '\'') |>.reverse
  let tail := chars.drop body.length
  let sub := tail.filter (fun c => c != '\'') |>.map fun c =>
    (subscriptDigits.find? (·.1 == c)).map (·.2) |>.getD c
  let primes := tail.filter (· == '\'')
  let core : String :=
    match body with
    | [c] => (greek.find? (·.1 == c)).map (·.2) |>.getD (esc c.toString)
    | [] => ""
    | cs =>
      let parts := cs.map fun c => (greek.find? (·.1 == c)).map (fun g => g.2 ++ " ") |>.getD (esc c.toString)
      if cs.all (fun c => c.isAlpha && c.isLower || c.isUpper) && cs.all Char.isAlphanum then
        "\\mathit{" ++ String.join parts ++ "}"
      else String.join parts
  let sub := if sub.isEmpty then "" else "_{" ++ String.ofList sub ++ "}"
  core ++ sub ++ String.ofList primes

def paren (s : String) : String := "(" ++ s ++ ")"

/-- Which arguments of `f` are explicit, by its type. -/
def explicitArgs (f : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let mut ty ← inferType f
  let mut out := #[]
  for a in args do
    ty ← whnf ty
    match ty with
    | .forallE _ _ b bi =>
      if bi.isExplicit then out := out.push a
      ty := b.instantiate1 a
    | _ => out := out.push a
  return out

def lastName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

def strLit? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

partial def listLit? (e : Expr) : Option (List Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, a, l]) => (listLit? l).map (a :: ·)
  | _ => none

def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => match n with | .lit (.natVal k) => some k | _ => none
    | _ => none

/-- Precedences: 0 statement · 1 ⊃/⇒ · 2 ∨ · 3 ∧ · 4 prefix (◯, ¬) · 5 relations · 9 atoms. -/
structure St where
  bound : List String := []      -- names for de Bruijn binders of the object language
  depth : Nat := 0

def boundNames : Array String := #["x", "y", "z", "u", "v", "w", "s", "t"]

mutual
partial def tm (st : St) : Expr → MetaM String
  | e => do
    let e := e.consumeMData
    match e.getAppFnArgs with
    | (``LaxLogic.QLL.Tm.fvar, #[s]) => pure <| (strLit? s).map ident |>.getD "?"
    | (``LaxLogic.QLL.Tm.bvar, #[n]) =>
      pure <| match natLit? n with
        | Option.some k => st.bound.getD k s!"b_{k}"
        | Option.none => "b"
    | (``LaxLogic.QLL.Tm.fn, #[f, ts]) =>
      let args := (listLit? ts).getD []
      let f := (strLit? f).getD "f"
      match f, args with
      | "add", [a, b] => return s!"{← tm st a} + {← tm st b}"
      | "sub", [a, b] => return s!"{← tm st a} - {← tm st b}"
      | "mul", [a, b] => return s!"{← tm st a} \\cdot {← tm st b}"
      | f, [] => pure <| if f.all Char.isDigit then f else ident f
      | f, args => return s!"{ident f}({", ".intercalate (← args.mapM (tm st))})"
    | _ => generic st 9 e

partial def form (st : St) (p : Nat) : Expr → MetaM String
  | e => do
    let e := e.consumeMData
    let wrap (q : Nat) (s : String) := if q < p then paren s else s
    match e.getAppFnArgs with
    | (``LaxLogic.QLL.Form.top, _) => pure "\\top"
    | (``LaxLogic.QLL.Form.bot, _) => pure "\\bot"
    | (``LaxLogic.QLL.Form.and, #[a, b]) => return wrap 3 s!"{← form st 3 a} \\land {← form st 4 b}"
    | (``LaxLogic.QLL.Form.or, #[a, b]) => return wrap 2 s!"{← form st 2 a} \\lor {← form st 3 b}"
    | (``LaxLogic.QLL.Form.imp, #[a, b]) => return wrap 1 s!"{← form st 2 a} \\supset {← form st 1 b}"
    | (``LaxLogic.QLL.Form.circ, #[q, a]) =>
      let q ← match q.consumeMData.getAppFnArgs with
        | (``LaxLogic.QLL.Q.ex, _) => pure "\\exists"
        | (``LaxLogic.QLL.Q.all, _) => pure "\\forall"
        | _ => generic st 9 q
      return wrap 4 ("\\bigcirc_{" ++ q ++ "} " ++ (← form st 4 a))
    | (``LaxLogic.QLL.Form.forall_, #[a]) =>
      let x := boundNames.getD st.depth s!"x_{st.depth}"
      return wrap 0 s!"\\forall {x}.\\, {← form {st with bound := x :: st.bound, depth := st.depth + 1} 0 a}"
    | (``LaxLogic.QLL.Form.exists_, #[a]) =>
      let x := boundNames.getD st.depth s!"x_{st.depth}"
      return wrap 0 s!"\\exists {x}.\\, {← form {st with bound := x :: st.bound, depth := st.depth + 1} 0 a}"
    | (``LaxLogic.QLL.Form.pred, #[P, ts]) =>
      let args := (listLit? ts).getD []
      let P := (strLit? P).getD "P"
      match P, args with
      | "geq", [a, b] => return wrap 5 s!"{← tm st a} \\ge {← tm st b}"
      | "leq", [a, b] => return wrap 5 s!"{← tm st a} \\le {← tm st b}"
      | "gt", [a, b] => return wrap 5 s!"{← tm st a} > {← tm st b}"
      | "lt", [a, b] => return wrap 5 s!"{← tm st a} < {← tm st b}"
      | "eq", [a, b] => return wrap 5 s!"{← tm st a} = {← tm st b}"
      | P, [] => pure (ident P)
      | P, args => return s!"{ident P}({", ".intercalate (← args.mapM (tm st))})"
    | (``LaxLogic.QLL.Form.openWith, #[a, c]) => return s!"{← form st 9 a}({← tm st c})"
    | _ => generic st p e

/-- A context: a list literal is written as a sequence, `A :: Γ` as `A, Γ`,
`Θ.forms` as `Θ`. -/
partial def ctx (st : St) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  if let some fs := listLit? e then
    return ",\\ ".intercalate (← fs.mapM (form st 1))
  match e.getAppFnArgs with
  | (``List.cons, #[_, a, l]) => return s!"{← form st 1 a},\\ {← ctx st l}"
  | (``HAppend.hAppend, #[_, _, _, _, l, r]) => return s!"{← ctx st l},\\ {← ctx st r}"
  | (``LaxLogic.QLL.Program.forms, #[Θ]) => generic st 9 Θ
  | _ => generic st 9 e

/-- Propositions and everything else. -/
partial def generic (st : St) (p : Nat) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  let wrap (q : Nat) (s : String) := if q < p then paren s else s
  match e with
  | .fvar id =>
    let d ← id.getDecl
    return ident d.userName.toString
  | .lit (.natVal n) => pure (toString n)
  | .lit (.strVal s) => pure ("\\texttt{" ++ esc s ++ "}")
  | .sort u => pure (if u.isZero then "\\mathsf{Prop}" else "\\mathsf{Type}")
  | .forallE _ d b _ =>
    if !b.hasLooseBVars && !(← isProp d) && !(← isProp e) then
      let wrap (q : Nat) (s : String) := if q < p then paren s else s
      return wrap 1 ((← generic st 2 d) ++ " \\to " ++ (← generic st 1 (b.lowerLooseBVars 1 1)))
    else quant st p e
  | .lam .. =>
    lambdaTelescope e fun xs b => do
      let names ← xs.mapM fun x => do pure (ident (← x.fvarId!.getDecl).userName.toString)
      return wrap 0 s!"\\lambda {" ".intercalate names.toList}.\\, {← generic st 0 b}"
  | _ =>
  match e.getAppFnArgs with
  | (``LaxLogic.QLL.Prv, #[Γ, a]) => return wrap 0 s!"{← ctx st Γ} \\vdash {← form st 1 a}"
  | (``LaxLogic.QLL.PEq, #[a, b]) => return wrap 0 s!"{← form st 1 a} \\dashv\\vdash {← form st 1 b}"
  | (``Not, #[q]) =>
    match q.consumeMData.getAppFnArgs with
    | (``LaxLogic.QLL.Prv, #[Γ, a]) => return wrap 0 s!"{← ctx st Γ} \\nvdash {← form st 1 a}"
    | _ => return wrap 4 s!"\\lnot {← generic st 4 q}"
  | (``And, #[a, b]) => return wrap 3 s!"{← generic st 3 a} \\land {← generic st 4 b}"
  | (``Or, #[a, b]) => return wrap 2 s!"{← generic st 2 a} \\lor {← generic st 3 b}"
  | (``Iff, #[a, b]) => return wrap 1 s!"{← generic st 2 a} \\iff {← generic st 2 b}"
  | (``Eq, #[_, a, b]) =>
    if b.consumeMData.isConstOf ``Bool.true then generic st p a
    else return wrap 5 s!"{← generic st 6 a} = {← generic st 6 b}"
  | (``Ne, #[_, a, b]) => return wrap 5 s!"{← generic st 6 a} \\ne {← generic st 6 b}"
  | (``Membership.mem, #[_, _, _, coll, x]) => return wrap 5 s!"{← generic st 6 x} \\in {← generic st 6 coll}"
  | (``Exists, #[_, f]) =>
    lambdaTelescope f fun xs b => do
      let names ← xs.mapM fun x => do pure (ident (← x.fvarId!.getDecl).userName.toString)
      return wrap 0 s!"\\exists {" ".intercalate names.toList}.\\, {← generic st 0 b}"
  | (``True, _) => pure "\\mathsf{True}"
  | (``False, _) => pure "\\mathsf{False}"
  | (``Bool.true, _) => pure "\\mathsf{true}"
  | (``Bool.false, _) => pure "\\mathsf{false}"
  | (``Option.some, #[_, a]) => return "\\mathsf{some}(" ++ (← generic st 0 a) ++ ")"
  | (``Option.none, _) => pure "\\mathsf{none}"
  | (``OfNat.ofNat, #[_, n, _]) => generic st p n
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return wrap 6 s!"{← generic st 6 a} + {← generic st 6 b}"
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return wrap 6 s!"{← generic st 6 a} - {← generic st 7 b}"
  | (``HAppend.hAppend, #[_, _, _, _, a, b]) => return wrap 6 ((← generic st 6 a) ++ " \\mathbin{+\\!\\!+} " ++ (← generic st 7 b))
  | (``List.cons, #[_, a, l]) => return wrap 6 s!"{← generic st 7 a} :: {← generic st 6 l}"
  | (``List.nil, _) => pure "[\\,]"
  | (``Prod, #[a, b]) => return wrap 5 ((← generic st 6 a) ++ " \\times " ++ (← generic st 6 b))
  | (``LaxLogic.QLL.Consequence, #[Γ, a]) => return wrap 0 ((← ctx st Γ) ++ " \\Vdash " ++ (← form st 1 a))
  | (``Prod.mk, #[_, _, a, b]) => return s!"({← generic st 0 a}, {← generic st 0 b})"
  | (``Prod.fst, #[_, _, a]) => return s!"\\pi_1 {← generic st 9 a}"
  | (``Prod.snd, #[_, _, a]) => return s!"\\pi_2 {← generic st 9 a}"
  -- full applications only: a partial application falls through to the generic
  -- reading (otherwise `form`/`generic` would call each other forever)
  | (``LaxLogic.QLL.Form.top, #[]) | (``LaxLogic.QLL.Form.bot, #[]) | (``LaxLogic.QLL.Form.and, #[_, _])
  | (``LaxLogic.QLL.Form.or, #[_, _]) | (``LaxLogic.QLL.Form.imp, #[_, _]) | (``LaxLogic.QLL.Form.circ, #[_, _])
  | (``LaxLogic.QLL.Form.forall_, #[_]) | (``LaxLogic.QLL.Form.exists_, #[_]) | (``LaxLogic.QLL.Form.pred, #[_, _])
  | (``LaxLogic.QLL.Form.openWith, #[_, _]) => form st p e
  | (``LaxLogic.QLL.Tm.fvar, #[_]) | (``LaxLogic.QLL.Tm.bvar, #[_]) | (``LaxLogic.QLL.Tm.fn, #[_, _]) => tm st e
  | (``LaxLogic.QLL.Q.ex, _) => pure "\\exists"
  | (``LaxLogic.QLL.Q.all, _) => pure "\\forall"
  | (``Nat, _) => pure "\\mathbb{N}"
  | (``String, _) => pure "\\mathsf{String}"
  | (``List, #[a]) => return "\\mathsf{List}\\," ++ (← generic st 9 a)
  | (``Option, #[a]) => return "\\mathsf{Option}\\," ++ (← generic st 9 a)
  | (f, args) =>
    if let some fs := listLit? e then
      return "[" ++ ", ".intercalate (← fs.mapM (generic st 0)) ++ "]"
    if f.isAnonymous then
      match e.getAppFn with
      | .fvar _ =>
        let head ← generic st 9 e.getAppFn
        if args.isEmpty then pure head
        else return head ++ "(" ++ ", ".intercalate (← args.toList.mapM (generic st 0)) ++ ")"
      | _ =>
        let s ← ppExpr e
        pure ("\\texttt{" ++ esc (toString s) ++ "}")
    else
      let args ← explicitArgs (mkConst f e.getAppFn.constLevels!) args
      let isType := match (← getEnv).find? f with
        | Option.some (.inductInfo _) => true
        | _ => false
      let head := (if isType then "\\mathsf{" else "\\mathit{") ++ esc (lastName f) ++ "}"
      if args.isEmpty then pure head
      else return head ++ "(" ++ ", ".intercalate (← args.toList.mapM (generic st 0)) ++ ")"

/-- `∀`-binders: variables are quantified (grouped by type), propositions become
premises, instance arguments vanish. -/
partial def quant (st : St) (p : Nat) (e : Expr) : MetaM String :=
  forallTelescope e fun xs body => do
    let mut vars : Array (String × String) := #[]   -- (name, type)
    let mut prems : Array String := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then continue
      let ty := d.type
      if ← isProp ty then
        prems := prems.push (← generic st 1 ty)
      else
        vars := vars.push (ident d.userName.toString, ← generic st 9 ty)
    -- group consecutive variables of one type
    let mut groups : Array (Array String × String) := #[]
    for (v, t) in vars do
      if let some (vs, t') := groups.back? then
        if t' == t then groups := groups.pop.push (vs.push v, t); continue
      groups := groups.push (#[v], t)
    let binder := if groups.isEmpty then "" else
      "\\forall\\, " ++ ",\\ ".intercalate (groups.toList.map fun (vs, t) =>
        "\\, ".intercalate vs.toList ++ "{:}" ++ t) ++ ".\\; "
    let concl ← generic st 0 body
    if prems.isEmpty then
      return (if p > 0 then paren else id) (binder ++ concl)
    else if p > 0 then
      return paren (binder ++ " \\Longrightarrow ".intercalate (prems.toList ++ [concl]))
    else
      -- statement layout: one premise per line
      let lines := (if binder.isEmpty then #[] else #[binder]) ++
        prems.map (fun h => s!"\\quad {h} \\;\\Longrightarrow") ++ #[s!"\\qquad {concl}"]
      return "\\begin{aligned}" ++ " \\\\ ".intercalate (lines.toList.map ("&" ++ ·)) ++ "\\end{aligned}"
end

/-- The statement of `n` as TeX, or `none` when its type is not a proposition. -/
def stmtOf (n : Name) : MetaM (Option String) := do
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  unless ← isProp ci.type do return none
  return some (← generic {} 0 ci.type)

structure StmtConfig where
  ok : Unit := ()

instance {m : Type → Type} [Monad m] : FromArgs StmtConfig m := ⟨(fun _ => {}) <$> .done⟩

@[role]
def stmt : RoleExpanderOf StmtConfig
  | _, #[arg] => do
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected a code literal with the declaration name"
    let identStx := mkIdentFrom arg name.getString.toName (canonical := true)
    let n ← realizeGlobalConstNoOverloadWithInfo identStx
    match ← (stmtOf n : MetaM (Option String)) with
    | Option.some tex => `(Verso.Doc.Inline.math .display $(quote tex))
    | Option.none => `(Verso.Doc.Inline.concat #[])
  | _, _ => throwError "Expected exactly one code literal"

end CLPPaper.Math
