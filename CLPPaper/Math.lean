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

/-! ### Line breaking

Neither KaTeX nor TeX breaks display mathematics on its own.  A statement is
set on one row when it fits the measure (`width`); otherwise its premises are
filled into rows, the quantifier prefix on the first, and a piece still too
long is broken, greedily, at binary connectives: shallow parenthesis depth
first, and at that depth `⟺` and `⟹` before the others (v0.7, Matthew
2026-10-16: compact displays).  Continuation rows are indented.  Lengths are
estimated on the TeX source: a control word counts one (a long arrow three,
a quad two), braces and thin spaces none. -/

/-- The measure of a display row, in the estimated characters of `visLen`.
The estimate runs high (an italic word is narrower than its letter count),
so 95 fills about nine tenths of the A4 text width at 10pt; v0.6 used 78,
which left rows two-thirds full. -/
def rowMeasure : Nat := 95

/-- Estimated visible length of a TeX fragment. -/
def visLen (s : String) : Nat := Id.run do
  let mut n := 0
  let mut cs := s.toList
  while !cs.isEmpty do
    match cs with
    | '\\' :: c :: rest =>
      if c.isAlpha then
        let word := String.ofList (c :: rest.takeWhile Char.isAlpha)
        let rest := rest.dropWhile Char.isAlpha
        let w := if word == "Longrightarrow" || word == "iff" || word == "Longleftrightarrow" then 3
          else if word == "quad" || word == "twoheadrightarrow" then 2
          else if word == "qquad" then 4 else 1
        n := n + w; cs := rest
      else
        cs := rest   -- \, \; \{ etc.: spacing or an escaped symbol
        if c == '{' || c == '}' then n := n + 1
    | '{' :: rest | '}' :: rest => cs := rest
    | _ :: rest => n := n + 1; cs := rest
    | [] => pure ()
  return n

/-- Break positions: (index, depth, rank) just before a connective; rank 0
for the meta-level `⟺` and `⟹`, 1 for the others. -/
def breakPoints (s : String) : List (Nat × Nat × Nat) := Id.run do
  let cs := s.toList.toArray
  let mut depth := 0
  let mut out : List (Nat × Nat × Nat) := []
  let major := [" \\iff ", " \\Longrightarrow "]
  let minor := [" \\land ", " \\lor ", " \\vdash ", " \\dashv\\vdash ", " \\twoheadrightarrow ", " = "]
  for i in [0:cs.size] do
    let c := cs[i]!
    if c == '(' || c == '[' then depth := depth + 1
    else if c == ')' || c == ']' then depth := depth - 1
    else if c == ' ' then
      let rest := String.ofList (cs.toList.drop i)
      if major.any (rest.startsWith ·) then out := (i, depth, 0) :: out
      else if minor.any (rest.startsWith ·) then out := (i, depth, 1) :: out
  return out.reverse

/-- Break `s` into rows of visible length about `width`. -/
partial def breakRow (s : String) (width : Nat := rowMeasure) : List String :=
  if visLen s ≤ width then [s] else
  let pts := breakPoints s
  if pts.isEmpty then [s] else
  -- the rightmost point that keeps the first row within width, searched at the
  -- shallowest depth (`⟺`/`⟹` first, then the other connectives), then one
  -- level deeper
  let minDepth := pts.foldl (fun m p => min m p.2.1) 1000
  let fitsAt (d r : Nat) := pts.filter fun (i, k, r') =>
    k == d && r' == r && visLen (String.ofList (s.toList.take i)) ≤ width
  let candidates := pts.filter (·.2.1 ≤ minDepth + 1)
  let order := [(minDepth, 0), (minDepth, 1), (minDepth + 1, 0), (minDepth + 1, 1)]
  let pick := match order.findSome? (fun (d, r) => (fitsAt d r).reverse.head?) with
    | Option.some p => p
    | Option.none => candidates.head!
  let head := String.ofList (s.toList.take pick.1)
  let tail := String.ofList (s.toList.drop pick.1) |>.trimAscii.copy
  if head.trimAscii.isEmpty then [s] else
  head :: (breakRow tail width |>.map ("\\quad " ++ ·))

/-- Rows for `aligned`. -/
def rows (lines : List String) : String :=
  "\\begin{aligned}" ++ " \\\\ ".intercalate (lines.map ("&" ++ ·)) ++ "\\end{aligned}"

/-- `first` followed by `items`, on one row if that fits `width`; otherwise
filled: each row takes as many items as fit, the first row starts with
`first` (the quantifier prefix, never broken), later rows are indented, and
an item too long for a row of its own is broken by `breakRow`. -/
def fillRows (first : String) (items : List String) (width : Nat := rowMeasure) : String := Id.run do
  let one := first ++ " ".intercalate items
  if visLen one ≤ width then return one
  let mut acc : Array String := #[]
  let mut cur := first
  let mut fresh := true          -- `cur` holds only the prefix of its row
  for it in items do
    let cand := if fresh then cur ++ it else cur ++ " " ++ it
    if visLen cand ≤ width then
      cur := cand
    else if fresh then
      -- the first item does not fit after the prefix: it starts the next row
      -- if it fits there, else it is broken
      if !first.isEmpty && visLen ("\\quad " ++ it) ≤ width then
        acc := acc.push first.trimAsciiEnd.copy
        cur := "\\quad " ++ it
      else
        let rs := breakRow cand width
        acc := acc ++ rs.dropLast.toArray
        cur := rs.getLast!
    else
      acc := acc.push cur
      let rs := breakRow ("\\quad " ++ it) width
      acc := acc ++ rs.dropLast.toArray
      cur := rs.getLast!
    fresh := false
  acc := acc.push cur
  return rows acc.toList

/-- Precedences: 0 statement · 1 ↠/⇒ · 2 ∨ · 3 ∧ · 4 prefix (◯, ¬) · 5 relations · 9 atoms. -/
structure St where
  bound : List String := []      -- names for de Bruijn binders of the object language
  depth : Nat := 0
  /-- below the root: a quantified formula here is printed on one line -/
  nested : Bool := false

def boundNames : Array String := #["x", "y", "z", "u", "v", "w", "s", "t"]

/-- One-step relations whose runs are printed as chains, with their arrows:
Table 2's `⇝`, and `⟶` for the two machines of Section 7. -/
def stepArrows : List (Name × String) :=
  [(``LaxLogic.QLL.Step, "\\rightsquigarrow"),
   (``LaxLogic.QLL.SLD.SLDStep, "\\longrightarrow"),
   (``LaxLogic.QLL.SLD.SLDCStep, "\\longrightarrow")]

/-- The conjuncts of a right-nested conjunction. -/
partial def conjuncts (e : Expr) : List Expr :=
  match e.consumeMData.getAppFnArgs with
  | (``And, #[a, b]) => a :: conjuncts b
  | _ => [e.consumeMData]

/-- A run: `R ps s₀ s₁ ∧ R ps s₁ s₂ ∧ ⋯`, every conjunct the same step relation
with the same parameters, each conjunct's target the next one's source.
Returns the relation, its parameters and the states `s₀, s₁, …`. -/
def run? (e : Expr) : Option (Name × Array Expr × List Expr) := Id.run do
  let cs := conjuncts e
  if cs.length < 2 then return none
  let parts := cs.map fun c => c.getAppFnArgs
  let (f, args0) := parts.head!
  unless stepArrows.any (·.1 == f) && args0.size ≥ 2 do return none
  let n := args0.size
  let ps := args0.extract 0 (n - 2)
  let mut states : List Expr := [args0[n - 2]!]
  let mut prev := args0[n - 2]!
  for (g, args) in parts do
    unless g == f && args.size == n && args.extract 0 (n - 2) == ps && args[n - 2]! == prev do
      return none
    prev := args[n - 1]!
    states := states ++ [prev]
  return some (f, ps, states)

mutual
partial def tm (st : St) : Expr → MetaM String
  | e => do
    let e := e.consumeMData
    match e.getAppFnArgs with
    | (``LaxLogic.QLL.Tm.fvar, #[s]) => match strLit? s with
      | Option.some n =>
        -- the engine's fresh variables `_v0`, `_v1`, … are `v₀`, `v₁`, …
        if n.startsWith "_v" && (n.drop 2).all Char.isDigit && n.length > 2 then
          pure ("v_{" ++ (n.drop 2).toString ++ "}")
        else pure (ident n)
      | Option.none => generic st 9 s
    | (``LaxLogic.QLL.Tm.bvar, #[n]) =>
      pure <| match natLit? n with
        | Option.some k => st.bound.getD k s!"b_{k}"
        | Option.none => "b"
    | (``LaxLogic.QLL.Tm.fn, #[f0, ts]) =>
      -- a name or argument list that is a variable is printed as one: `f(ts)`
      match strLit? f0, listLit? ts with
      | Option.some _, Option.some _ => pure ()
      | _, _ => return s!"{← generic st 9 f0}({← generic st 0 ts})"
      let args := (listLit? ts).getD []
      let f := (strLit? f0).getD "f"
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
    -- object-level ∧ and ∨: a nested conjunction or disjunction is bracketed on
    -- either side, so the printed formula is the formula, not one up to ⊣⊢
    | (``LaxLogic.QLL.Form.and, #[a, b]) => return wrap 3 s!"{← form st 4 a} \\land {← form st 4 b}"
    | (``LaxLogic.QLL.Form.or, #[a, b]) => return wrap 2 s!"{← form st 3 a} \\lor {← form st 3 b}"
    | (``LaxLogic.QLL.Form.imp, #[a, b]) => return wrap 1 s!"{← form st 2 a} \\twoheadrightarrow {← form st 1 b}"
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
    | (``LaxLogic.QLL.Form.pred, #[P0, ts]) =>
      -- a predicate name or argument list that is a variable is printed as one: `p(us)`
      match strLit? P0, listLit? ts with
      | Option.some _, Option.some _ => pure ()
      | _, _ => return s!"{← generic st 9 P0}({← generic st 0 ts})"
      let args := (listLit? ts).getD []
      let P := (strLit? P0).getD "P"
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
partial def generic (st0 : St) (p : Nat) (e : Expr) : MetaM String := do
  let st := {st0 with nested := true}
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
    else quant st0 p e
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
  -- propositions: right-associated, as Lean reads them; a run of a step
  -- relation (a conjunction of steps, each from the previous target) is a chain
  -- under the relation's name: one state per row, each after the arrow
  | (``And, #[a, b]) =>
    if let some (f, ps, s0 :: ss) := run? e then
      let arrow := ((stepArrows.find? (·.1 == f)).map (·.2)).getD "\\longrightarrow"
      let ps ← explicitArgs (mkConst f (conjuncts e).head!.getAppFn.constLevels!) ps
      let head := "\\mathsf{" ++ esc (lastName f) ++ "}(" ++
        ", ".intercalate (← ps.toList.mapM (generic st 0)) ++ ")\\colon"
      let mut out := #[head, "\\quad " ++ (← generic st 0 s0)]
      for s in ss do
        out := out.push ("\\quad " ++ arrow ++ "\\; " ++ (← generic st 0 s))
      return rows out.toList
    return wrap 3 s!"{← generic st 4 a} \\land {← generic st 3 b}"
  | (``Or, #[a, b]) => return wrap 2 s!"{← generic st 3 a} \\lor {← generic st 2 b}"
  | (``Iff, #[a, b]) => return wrap 1 s!"{← generic st 2 a} \\iff {← generic st 2 b}"
  | (``Eq, #[_, a, b]) =>
    if b.consumeMData.isConstOf ``Bool.true then generic st p a
    else return wrap 5 s!"{← generic st 6 a} = {← generic st 6 b}"
  | (``Ne, #[_, a, b]) => return wrap 5 s!"{← generic st 6 a} \\ne {← generic st 6 b}"
  | (``LE.le, #[_, _, a, b]) => return wrap 5 s!"{← generic st 6 a} \\le {← generic st 6 b}"
  | (``LT.lt, #[_, _, a, b]) => return wrap 5 s!"{← generic st 6 a} < {← generic st 6 b}"
  | (``GE.ge, #[_, _, a, b]) => return wrap 5 s!"{← generic st 6 a} \\ge {← generic st 6 b}"
  | (``GT.gt, #[_, _, a, b]) => return wrap 5 s!"{← generic st 6 a} > {← generic st 6 b}"
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
  | (``List.cons, #[_, a, l]) =>
    -- a list literal `[a, b]` is printed as one; only an open tail gets `::`
    if let some fs := listLit? e then
      return "[" ++ ", ".intercalate (← fs.mapM (generic st 0)) ++ "]"
    return wrap 6 s!"{← generic st 7 a} :: {← generic st 6 l}"
  -- a goal or machine state `c □ φ₁, …, φₙ` (the 1997 report's notation), `ε` when empty
  | (``LaxLogic.QLL.Goal.mk, #[c, gs]) | (``LaxLogic.QLL.SLD.MState.mk, #[c, gs]) =>
    let rhs ← match listLit? gs with
      | Option.some [] => pure "\\varepsilon"
      | Option.some fs => pure (",\\ ".intercalate (← fs.mapM (generic st 1)))
      | Option.none => generic st 6 gs
    return wrap 5 ((← generic st 6 c) ++ " \\mathrel{\\square} " ++ rhs)
  | (``List.nil, _) => pure "[\\,]"
  | (``Prod, #[a, b]) => return wrap 5 ((← generic st 6 a) ++ " \\times " ++ (← generic st 6 b))
  | (``LaxLogic.QLL.Consequence, #[Γ, a]) => return wrap 0 ((← ctx st Γ) ++ " \\models " ++ (← form st 1 a))
  -- truth in a Herbrand interpretation: `I ⊨ A`
  | (``LaxLogic.QLL.HTrue, #[i, a]) => return wrap 0 ((← generic st 9 i) ++ " \\models " ++ (← form st 1 a))
  -- forcing `M, s ⊨ A`; the assignment is shown as a subscript unless it is the
  -- Herbrand one (names denote themselves, no index bound)
  | (``LaxLogic.QLL.KModel.force, #[m, a, s, ρ, β]) =>
    let dflt := ρ.consumeMData.isConstOf ``LaxLogic.QLL.Tm.fvar &&
      (listLit? β).map List.isEmpty == Option.some true
    let sub ← if dflt then pure "" else
      pure ("_{" ++ (← generic st 0 ρ) ++ ",\\," ++ (← generic st 0 β) ++ "}")
    return wrap 0 ((← generic st 9 m) ++ ",\\ " ++ (← generic st 9 s) ++ " \\models" ++ sub ++ " " ++
      (← form st 1 a))
  -- a bundled map applied to an argument (Mathlib's `⇑f x`): `f(x)`
  | (``DFunLike.coe, #[_, _, _, _, f, x]) => return s!"{← generic st 9 f}({← generic st 0 x})"
  -- the order of a Herbrand frame: `w ≤_F v`
  | (``LaxLogic.QLL.HFrame.le, #[fr, w, v]) =>
    return wrap 5 ((← generic st 6 w) ++ " \\le_{" ++ (← generic st 9 fr) ++ "} " ++ (← generic st 6 v))
  -- proof trees, partial proof trees and abstract proof trees, in the notation
  -- of their rules: an open leaf is `⟨S⟩`, a constraint leaf is its atom
  | (``LaxLogic.QLL.SLD.PTree.hole, #[S]) | (``LaxLogic.QLL.SLD.ATree.hole, #[S]) =>
    return "\\langle " ++ (← form st 0 S) ++ " \\rangle"
  | (``LaxLogic.QLL.CProof.top, #[]) | (``LaxLogic.QLL.SLD.PTree.top, #[]) => pure "{\\top}\\mathrm{I}"
  | (``LaxLogic.QLL.CProof.cstr, #[b, ts]) | (``LaxLogic.QLL.SLD.PTree.cstr, #[b, ts]) =>
    form st p (mkApp2 (mkConst ``LaxLogic.QLL.Form.pred) b ts)
  | (``LaxLogic.QLL.CProof.andI, #[l, r]) | (``LaxLogic.QLL.SLD.PTree.andI, #[l, r]) =>
    return "{\\land}\\mathrm{I}(" ++ (← generic st 0 l) ++ ",\\, " ++ (← generic st 0 r) ++ ")"
  | (``LaxLogic.QLL.CProof.orL, #[l]) | (``LaxLogic.QLL.SLD.PTree.orL, #[l]) =>
    return "{\\lor}\\mathrm{I}_1(" ++ (← generic st 0 l) ++ ")"
  | (``LaxLogic.QLL.CProof.orR, #[l]) | (``LaxLogic.QLL.SLD.PTree.orR, #[l]) =>
    return "{\\lor}\\mathrm{I}_2(" ++ (← generic st 0 l) ++ ")"
  | (``LaxLogic.QLL.CProof.exI, #[t, l]) | (``LaxLogic.QLL.SLD.PTree.exI, #[t, l]) =>
    return "{\\exists}\\mathrm{I}_{" ++ (← tm st t) ++ "}(" ++ (← generic st 0 l) ++ ")"
  | (``LaxLogic.QLL.CProof.clause, #[w, ts, l]) | (``LaxLogic.QLL.SLD.PTree.clause, #[w, ts, l]) =>
    return "\\mathit{clause}_{" ++ (← generic st 0 w) ++ "}" ++ (← clauseInst st ts) ++
      "(" ++ (← generic st 0 l) ++ ")"
  | (``LaxLogic.QLL.AProof.val, #[]) | (``LaxLogic.QLL.SLD.ATree.val, #[]) => pure "\\mathit{val}"
  | (``LaxLogic.QLL.AProof.andC, #[l, r]) | (``LaxLogic.QLL.SLD.ATree.andC, #[l, r]) =>
    return "{\\land}{\\bigcirc}(" ++ (← generic st 0 l) ++ ",\\, " ++ (← generic st 0 r) ++ ")"
  | (``LaxLogic.QLL.AProof.orL, #[l]) | (``LaxLogic.QLL.SLD.ATree.orL, #[l]) =>
    return "{\\lor}{\\bigcirc}_1(" ++ (← generic st 0 l) ++ ")"
  | (``LaxLogic.QLL.AProof.orR, #[l]) | (``LaxLogic.QLL.SLD.ATree.orR, #[l]) =>
    return "{\\lor}{\\bigcirc}_2(" ++ (← generic st 0 l) ++ ")"
  | (``LaxLogic.QLL.AProof.exC, #[t, l]) | (``LaxLogic.QLL.SLD.ATree.exC, #[t, l]) =>
    return "{\\exists}{\\bigcirc}_{" ++ (← tm st t) ++ "}(" ++ (← generic st 0 l) ++ ")"
  | (``LaxLogic.QLL.AProof.impC, #[w, ts, l]) | (``LaxLogic.QLL.SLD.ATree.impC, #[w, ts, l]) =>
    return "{\\twoheadrightarrow}{\\bigcirc}_{" ++ (← generic st 0 w) ++ "}" ++ (← clauseInst st ts) ++
      "(" ++ (← generic st 0 l) ++ ")"
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
      -- the names of the worked examples are read as variables: `θ3` is θ₃, `ex95` is ex₉₅
      let head := if (`LaxLogic.QLL.CLPExamples).isPrefixOf f then ident (lastName f)
        else (if isType then "\\mathsf{" else "\\mathit{") ++ esc (lastName f) ++ "}"
      if args.isEmpty then pure head
      else return head ++ "(" ++ ", ".intercalate (← args.toList.mapM (generic st 0)) ++ ")"

/-- The instance of a clause node: nothing when it has no terms, else the
terms as a superscript. -/
partial def clauseInst (st : St) (ts : Expr) : MetaM String := do
  match listLit? ts with
  | Option.some [] => pure ""
  | Option.some xs => return "^{" ++ ", ".intercalate (← xs.mapM (tm st)) ++ "}"
  | Option.none => return "^{" ++ (← generic st 0 ts) ++ "}"

/-- `∀`-binders: variables are quantified (grouped by type), propositions become
premises, instance arguments vanish. -/
partial def quant (st0 : St) (p : Nat) (e : Expr) : MetaM String :=
  forallTelescope e fun xs body => do
    let st := {st0 with nested := true}
    let mut vars : Array (String × String) := #[]   -- (name, type)
    let mut prems : Array String := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then continue
      let ty := d.type
      if ← isProp ty then
        -- bracketed if it is itself a `⟺` or `⟹`
        prems := prems.push (← generic st 2 ty)
      else
        vars := vars.push (ident d.userName.toString, ← generic st 9 ty)
    -- binders without type annotations (Matthew, 2026-09-14): `∀ q, A, B.`
    let binder := if vars.isEmpty then "" else
      "\\forall\\, " ++ ",\\ ".intercalate (vars.toList.map (·.1)) ++ ".\\; "
    -- after premises, a `⟺` conclusion is bracketed: `A ⟹ (B ⟺ C)`
    let isIff := body.consumeMData.isAppOfArity ``Iff 2
    let concl ← generic st (if prems.isEmpty || !isIff then 0 else 2) body
    if p > 0 || st0.nested then
      if prems.isEmpty then return paren (binder ++ concl)
      else return paren (binder ++ " \\Longrightarrow ".intercalate (prems.toList ++ [concl]))
    else
      -- statement layout: one row if it fits; else the premises filled into
      -- rows after the quantifier prefix, then the conclusion
      return fillRows binder ((prems.toList.map (· ++ " \\Longrightarrow")) ++ [concl])
end


/-- The statement of `n` as TeX, or `none` when its type is not a proposition. -/
def stmtOf (n : Name) : MetaM (Option String) := do
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  unless ← isProp ci.type do return none
  let s ← generic {} 0 ci.type
  -- a statement with no binders or premises is one row; break it if it is long
  if visLen s > rowMeasure && !s.startsWith "\\begin{aligned}" then
    return some (rows (breakRow s))
  return some s

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
