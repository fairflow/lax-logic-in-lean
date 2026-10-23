/-
`{stmt}`Full.Name`` for the F0 paper: the conventional-notation statement of a
declaration, generated from its type at build time.  The method and the layout
code are those of `CLPPaper/Math.lean` (docs/verso-paper-workflow.md §3); the
notation table is new, for propositional lax logic and the objects of the F0
development (`wip/f0Covers.lean`, `wip/f0Indep.lean`, `wip/f0Dyadic.lean`,
`wip/f0Rat.lean`, `wip/f0Minkowski.lean`, `wip/gapWidth.lean`,
`wip/embedNeg.lean`, `wip/floor.lean`, and for v0.2 `wip/f0T6.lean` and
`wip/f0SelfSim.lean`).

* Binders become quantifiers without type annotations; hypotheses, and
  derivations `p : Γ ⊢ A` taken as arguments, become premises; instance
  arguments vanish; a variable followed by the hypothesis `x ∈ C` is written
  `∀ x ∈ C`.
* The object language: `⊥ ∧ ∨ ↠ ◯`, `A ↠ ⊥` as `¬A`, `⊥ ↠ ⊥` as `⊤`; the
  judgements `Γ ⊢ A`, `Γ ⊬ A`, `A ⊣⊢ B`, `Γ ⊨ A`, forcing `M, w ⊩ A`, the cover
  relation `u ⋖ v`; the named formulas `t_n` (the substituted rungs), `r_n` (the
  rungs), `g_k` (the gaps), `◯⊥`, `¬◯⊥`; finite conjunctions and disjunctions
  over a list `⋀_{i ∈ S}`, `⋁_{j ∈ T}`; the models of the independence proof.
* Meta-level `∧`, `∨` are the words "and", "or", so that they are not read as
  the object-level connectives.
* A definition whose value is a proposition or a formula, and is not defined
  by recursion, prints its defining equation `lhs := rhs` (`:⟺` for a
  proposition); other definitions, structures and inductive types print
  nothing.

Nothing is written by hand: the same declaration always gives the same
mathematics.
-/
import Lean
import Lean.DocString.Syntax
import VersoManual
import wip.f0Covers
import wip.f0Indep
import wip.f0Dyadic
import wip.f0Rat
import wip.f0Minkowski
import wip.f0Nuclear
import wip.f0MacNeilleNonUnique
import wip.f0Structure
import wip.f0Hole
import wip.f0SelfSim
import wip.gapWidth
import wip.embedNeg
import wip.ladder8
import wip.floor

open Lean Meta Elab
open Lean.Doc.Syntax
open Verso Doc Elab Genre Manual ArgParse

namespace F0Paper.Math

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

/-- A variable name as mathematics: Greek letters, trailing digits and
subscript digits become subscripts, primes stay, multi-letter names are set
upright-italic. -/
def ident (s : String) : String := Id.run do
  let s := s.replace "✝" ""
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

def isBotF (e : Expr) : Bool := e.consumeMData.isConstOf ``PLLFormula.falsePLL

/-! ### Line breaking (as `CLPPaper/Math.lean`, v0.7) -/

/-- The measure of a display row, in the estimated characters of `visLen`. -/
def rowMeasure : Nat := 95

/-- The meta-level connectives, written as words. -/
def metaAnd : String := " \\;\\text{and}\\; "
def metaOr : String := " \\;\\text{or}\\; "

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
          else if word == "qquad" then 4
          else if word == "text" || word == "mathit" || word == "mathrm" || word == "mathsf"
            || word == "mathcal" || word == "mathbb" then 0
          else 1
        n := n + w; cs := rest
      else
        cs := rest
        if c == '{' || c == '}' then n := n + 1
    | '{' :: rest | '}' :: rest => cs := rest
    | _ :: rest => n := n + 1; cs := rest
    | [] => pure ()
  return n

/-- Break positions: (index, depth, rank) just before a connective; rank 0
for the meta level (`⟺`, `⟹`, "and", "or"), 1 for the others. -/
def breakPoints (s : String) : List (Nat × Nat × Nat) := Id.run do
  let cs := s.toList.toArray
  let mut depth := 0
  let mut out : List (Nat × Nat × Nat) := []
  let major := [" \\iff ", " \\Longrightarrow ", metaAnd, metaOr]
  let minor := [" \\land ", " \\lor ", " \\vdash ", " \\dashv\\vdash ", " \\twoheadrightarrow ",
    " = ", " \\Vdash ", " \\nvdash "]
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
filled, later rows indented, an item too long for a row broken by `breakRow`. -/
def fillRows (first : String) (items : List String) (width : Nat := rowMeasure) : String := Id.run do
  let one := first ++ " ".intercalate items
  if visLen one ≤ width then return one
  let mut acc : Array String := #[]
  let mut cur := first
  let mut fresh := true
  for it in items do
    let cand := if fresh then cur ++ it else cur ++ " " ++ it
    if visLen cand ≤ width then
      cur := cand
    else if fresh then
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

/-! ### The notation table -/

/-- Precedences: 0 statement · 1 ⟺/⟹ and object `↠` · 2 "or", object `∨` ·
3 "and", object `∧` · 4 prefix (`◯`, `¬`) · 5 relations · 6 `+ -` · 7 `·` ·
8 powers · 9 atoms. -/
structure St where
  /-- below the root: a quantified formula here is printed on one line -/
  nested : Bool := false
  /-- one line throughout, without brackets around the whole (the tables) -/
  flat : Bool := false

/-- Named variable-free formulas: the six formulas of `wip/f0Covers.lean` are
the rungs `t₀ … t₅` (`rnSub_0` … `rnSub_5`, all `rfl`). -/
def namedForms : List (Name × String × Nat) :=
  [(``PLLND.F0.bot, "t_{0}", 9), (``PLLND.F0.e, "t_{1}", 9), (``PLLND.F0.ne, "t_{2}", 9),
   (``PLLND.F0.t3, "t_{3}", 9), (``PLLND.F0.t4, "t_{4}", 9), (``PLLND.F0.t5, "t_{5}", 9),
   (``PLLND.RNEmbed.oBot, "\\bigcirc\\bot", 4), (``PLLND.RNEmbed.notOBot, "\\lnot\\bigcirc\\bot", 4),
   (``PLLFormula.truePLL, "\\top", 9),
   -- `wip/f0T6.lean`: `t6 = t5 ↠ t3`, `u = ◯¬◯⊥`, and regularity of `◯⊥`
   (``PLLND.F0.T6.t6F, "t_{6}", 9), (``PLLND.F0.T6.uF, "u", 9),
   (``PLLND.F0.T6.nne, "\\lnot\\lnot\\bigcirc\\bot", 4),
   (``PLLND.F0.T6.regE, "\\lnot\\lnot\\bigcirc\\bot \\twoheadrightarrow \\bigcirc\\bot", 1)]

/-- The tables' lists of `wip/f0Covers.lean` are read as the sets they list. -/
def tableLists : List Name :=
  [``PLLND.F0.D1_list, ``PLLND.F0.D2_list, ``PLLND.F0.D3_list, ``PLLND.F0.D4_list,
   ``PLLND.F0.D5_list]

/-- `2k+1` for an index `k`: a numeral is computed, a compound bracketed. -/
def isAtomic (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ | .lit _ => true
  | e => e.isAppOfArity ``OfNat.ofNat 3

mutual
/-- A formula. -/
partial def form (st : St) (p : Nat) : Expr → MetaM String
  | e => do
    let e := e.consumeMData
    let wrap (q : Nat) (s : String) := if q < p then paren s else s
    match e.getAppFnArgs with
    | (``PLLFormula.falsePLL, #[]) => pure "\\bot"
    | (``PLLFormula.prop, #[a]) => match strLit? a with
      | Option.some s => pure (ident s)
      | Option.none => generic st 9 a
    -- a nested conjunction or disjunction is bracketed on either side, so the
    -- printed formula is the formula, not one up to ⊣⊢
    | (``PLLFormula.and, #[a, b]) => return wrap 3 s!"{← form st 4 a} \\land {← form st 4 b}"
    | (``PLLFormula.or, #[a, b]) => return wrap 2 s!"{← form st 3 a} \\lor {← form st 3 b}"
    | (``PLLFormula.ifThen, #[a, b]) =>
      if isBotF b then
        if isBotF a then pure "\\top" else return wrap 4 ("\\lnot " ++ (← form st 4 a))
      else return wrap 1 s!"{← form st 2 a} \\twoheadrightarrow {← form st 1 b}"
    | (``PLLFormula.somehow, #[a]) => return wrap 4 ("\\bigcirc " ++ (← form st 4 a))
    | (``PLLFormula.notPLL, #[a]) => return wrap 4 ("\\lnot " ++ (← form st 4 a))
    | _ =>
      match namedForms.find? (fun (n, _, _) => e.isConstOf n) with
      | Option.some (_, s, q) => pure (wrap q s)
      | Option.none => generic st p e

/-- A context: a list literal is a comma sequence, `List.map (λ i. A) S` is
`{A : i ∈ S}`, `A :: Γ` is `A, Γ`. -/
partial def ctx (st : St) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  if let some fs := listLit? e then
    -- the empty context is an empty atom, so `⟹ ⊢ χ` keeps its spacing
    if fs.isEmpty then return "{}"
    return ",\\ ".intercalate (← fs.mapM (form st 1))
  match e.getAppFnArgs with
  | (``List.cons, #[_, a, l]) => return s!"{← form st 1 a},\\ {← ctx st l}"
  | (``HAppend.hAppend, #[_, _, _, _, l, r]) => return s!"{← ctx st l},\\ {← ctx st r}"
  | (``List.map, #[_, _, f, l]) =>
    if f.consumeMData.isLambda then
      lambdaTelescope f fun xs b => do
        let x ← xs.mapM fun x => do pure (ident (← x.fvarId!.getDecl).userName.toString)
        return "\\{" ++ (← form st 1 b) ++ " : " ++ " ".intercalate x.toList ++ " \\in " ++
          (← generic st 6 l) ++ "\\}"
    else
      -- a translation applied to every member of a context: `Γᵃ`, `Γ[⊥ := a]`
      match f.consumeMData.getAppFnArgs with
      | (``PLLND.F0.Sig.aTr, #[a]) => return (← generic st 9 l) ++ "^{" ++ (← form st 0 a) ++ "}"
      | (``PLLND.F0.Sig.subBot, #[a]) =>
        return (← generic st 9 l) ++ "[\\bot := " ++ (← form st 1 a) ++ "]"
      | _ => generic st 9 e
  | _ => generic st 9 e

/-- `⋀`/`⋁` over a list: `List.map (λ i. A) S` gives a bound index. -/
partial def bigOp (st : St) (p : Nat) (op : String) (l : Expr) : MetaM String := do
  let wrap (q : Nat) (s : String) := if q < p then paren s else s
  match l.consumeMData.getAppFnArgs with
  | (``List.map, #[_, _, f, s]) =>
    if f.consumeMData.isLambda then
      lambdaTelescope f fun xs b => do
        let x ← xs.mapM fun x => do pure (ident (← x.fvarId!.getDecl).userName.toString)
        return wrap 4 (op ++ "_{" ++ " ".intercalate x.toList ++ " \\in " ++ (← generic st 6 s) ++
          "} " ++ (← form st 4 b))
    else return wrap 4 (op ++ " " ++ (← generic st 9 l))
  | _ => return wrap 4 (op ++ " " ++ (← generic st 9 l))

/-- `2k+1` for the index `k`. -/
partial def oddIndex (st : St) (k : Expr) : MetaM String := do
  if let some n := natLit? k then return toString (2 * n + 1)
  if isAtomic k then return "2" ++ (← generic st 9 k) ++ " + 1"
  return "2(" ++ (← generic st 0 k) ++ ") + 1"

/-- `2k+2` for the index `k`. -/
partial def evenIndex (st : St) (k : Expr) : MetaM String := do
  if let some n := natLit? k then return toString (2 * n + 2)
  if isAtomic k then return "2" ++ (← generic st 9 k) ++ " + 2"
  return "2(" ++ (← generic st 0 k) ++ ") + 2"

/-- The rung pair `rnP k = (r_{2k+1}, r_{2k+2})`, projected: `some (k, odd?)`. -/
partial def rungProj? (e : Expr) : Option (Expr × Bool) :=
  match e.consumeMData.getAppFnArgs with
  | (``Prod.fst, #[_, _, pr]) => match pr.consumeMData.getAppFnArgs with
    | (``PLLND.RNEmbed.rnP, #[k]) => some (k, true)
    | _ => none
  | (``Prod.snd, #[_, _, pr]) => match pr.consumeMData.getAppFnArgs with
    | (``PLLND.RNEmbed.rnP, #[k]) => some (k, false)
    | _ => none
  | _ => none

/-- A world of a lifted model: `some x` is the skeleton world `x`. -/
partial def world (st : St) (w : Expr) : MetaM String := do
  match w.consumeMData.getAppFnArgs with
  | (``Option.some, #[_, a]) => generic st 9 a
  | (``Option.none, _) => pure "f"
  | _ => generic st 9 w

/-- A model of the development, by name. -/
partial def model (st : St) (m : Expr) : MetaM String := do
  match m.consumeMData.getAppFnArgs with
  | (``PLLND.F0.cmM, #[ms]) =>
    match ms.consumeMData.getAppFnArgs with
    | (``PLLND.F0.levels, #[t]) => return "\\mathcal{M}_{" ++ (← generic st 0 t) ++ "}"
    | _ => return "\\mathcal{M}(" ++ (← generic st 0 ms) ++ ")"
  | (``PLLND.RNEmbed.cmE, #[k]) => return "\\mathcal{E}_{" ++ (← generic st 0 k) ++ "}"
  | (``PLLND.RNEmbed.Skel.cm, #[s]) => return (← generic st 9 s) ++ "^{+}"
  | _ => generic st 9 m

/-- The head of an application `f(x)` of a bundled map: the nuclei and
embeddings of the completion section by name, anything else generically. -/
partial def funHead (st : St) (f : Expr) : MetaM String := do
  let f := f.consumeMData
  if f.isConstOf ``F0Nuclear.circNucleus then return "\\bigcirc"
  if f.isConstOf ``MacNeille.principalHom then return "{\\downarrow}"
  if f.isConstOf ``DedekindCut.principal then return "{\\downarrow}"
  match f.getAppFnArgs with
  | (``MacNeille.dmNucleus, #[_, _, j]) => return "\\overline{" ++ (← generic st 9 j) ++ "}"
  | (``MacNeille.JoinDenseHeytingEmbedding.extNucleus, #[_, _, _, _, emb, j]) =>
    return "\\overline{" ++ (← generic st 9 j) ++ "}^{" ++ (← generic st 9 emb) ++ "}"
  | (``MacNeille.JoinDenseHeytingEmbedding.leastExt, #[_, _, _, _, emb, j]) =>
    return "\\underline{" ++ (← generic st 9 j) ++ "}^{" ++ (← generic st 9 emb) ++ "}"
  | (``MacNeille.JoinDenseHeytingEmbedding.toHom, #[_, _, _, _, emb]) => generic st 9 emb
  | (``DedekindCut.principal, #[_, _]) => return "{\\downarrow}"
  | _ => generic st 9 f

/-- The edge set of the multi-edge lift. -/
partial def edges (st : St) (ms : Expr) : MetaM String := do
  match ms.consumeMData.getAppFnArgs with
  | (``PLLND.F0.levels, #[t]) => return "E_{" ++ (← generic st 0 t) ++ "}"
  | _ => return "E(" ++ (← generic st 0 ms) ++ ")"

/-- Propositions, terms and everything else. -/
partial def generic (st0 : St) (p : Nat) (e : Expr) : MetaM String := do
  let st := {st0 with nested := true}
  let e := e.consumeMData
  let wrap (q : Nat) (s : String) := if q < p then paren s else s
  -- named formulas and the tables' lists
  if let some (_, s, q) := namedForms.find? (fun (n, _, _) => e.isConstOf n) then
    return wrap q s
  if let some n := tableLists.find? (fun n => e.isConstOf n) then
    let some (.defnInfo dv) := (← getEnv).find? n | return ident (lastName n)
    let some fs := listLit? dv.value | return ident (lastName n)
    return "\\{" ++ ", ".intercalate (← fs.mapM (form st 1)) ++ "\\}"
  match e with
  | .fvar id =>
    let d ← id.getDecl
    return ident d.userName.toString
  | .lit (.natVal n) => pure (toString n)
  | .lit (.strVal s) => pure ("\\texttt{" ++ esc s ++ "}")
  | .sort u => pure (if u.isZero then "\\mathsf{Prop}" else "\\mathsf{Type}")
  | .forallE _ d b _ =>
    if !b.hasLooseBVars && !(← isProp d) && !(← isProp e) && !isJudgement d then
      return wrap 1 ((← generic st 2 d) ++ " \\to " ++ (← generic st 1 (b.lowerLooseBVars 1 1)))
    else quant st0 p e
  | .lam .. =>
    lambdaTelescope e fun xs b => do
      let names ← xs.mapM fun x => do pure (ident (← x.fvarId!.getDecl).userName.toString)
      return wrap 0 s!"\\lambda {" ".intercalate names.toList}.\\, {← generic st 0 b}"
  | _ =>
  match e.getAppFnArgs with
  -- judgements
  | (``PLLND.LaxND, #[Γ, a]) => return wrap 5 s!"{← ctx st Γ} \\vdash {← form st 1 a}"
  | (``PLLND.SemUI.Deriv, #[Γ, a]) => return wrap 5 s!"{← ctx st Γ} \\vdash {← form st 1 a}"
  | (``Nonempty, #[j]) =>
    if isJudgement j then generic st0 p j
    else return "\\mathsf{Nonempty}(" ++ (← generic st 0 j) ++ ")"
  | (``PLLND.SemUI.Interd, #[a, b]) => return wrap 5 s!"{← form st 1 a} \\dashv\\vdash {← form st 1 b}"
  | (``PLLND.Consequence, #[Γ, a]) => return wrap 5 s!"{← ctx st Γ} \\models {← form st 1 a}"
  | (``PLLND.F0.Covers, #[u, v]) => return wrap 5 s!"{← form st 1 u} \\lessdot {← form st 1 v}"
  | (``PLLND.ConstraintModel.force, #[m, w, a]) =>
    return wrap 5 s!"{← model st m},\\ {← world st w} \\Vdash {← form st 1 a}"
  | (``PLLND.RNEmbed.Skel.sat, #[s, a, w]) =>
    return wrap 5 s!"{← generic st 9 s},\\ {← generic st 9 w} \\Vdash {← form st 1 a}"
  | (``PLLND.RNEmbed.Skel.le, #[s, x, y]) =>
    let sub ← if s.consumeMData.isConstOf ``PLLND.RNEmbed.ladder then pure "" else
      pure ("_{" ++ (← generic st 0 s) ++ "}")
    return wrap 5 ((← generic st 6 x) ++ " \\preceq" ++ sub ++ " " ++ (← generic st 6 y))
  | (``PLLND.F0.IsEdge, #[ms, y]) => return wrap 5 s!"{← generic st 6 y} \\in {← edges st ms}"
  -- variable-freeness: `x ∈ Fm₀`
  | (``Eq, #[_, a, b]) =>
    match a.consumeMData.getAppFnArgs with
    | (``PLLND.LaxInfinite.atomFree, #[x]) =>
      if b.consumeMData.isConstOf ``Bool.true then
        return wrap 5 ((← form st 1 x) ++ " \\in \\mathrm{Fm}_0")
      else return wrap 5 ((← form st 1 x) ++ " \\notin \\mathrm{Fm}_0")
    | _ => return wrap 5 s!"{← generic st 6 a} = {← generic st 6 b}"
  -- the named formulas of the development
  | (``PLLND.RNEmbed.rnSub, #[n]) => return "t_{" ++ (← generic st 0 n) ++ "}"
  | (``PLLND.RNEmbed.rn, #[n]) => return "r_{" ++ (← generic st 0 n) ++ "}"
  | (``PLLND.RNEmbed.gap, #[k]) => return "g_{" ++ (← generic st 0 k) ++ "}"
  | (``PLLND.RNEmbed.chainF, #[k]) => return wrap 4 ("\\bigcirc t_{" ++ (← oddIndex st k) ++ "}")
  | (``PLLND.RNEmbed.Wit, #[b]) => return "W_{" ++ (← generic st 0 b) ++ "}"
  | (``PLLND.RNEmbed.embed, #[a]) =>
    -- `embed (rnP k).1` is the substituted rung `t_{2k+1}` (`rnSub` by definition)
    match rungProj? a with
    | Option.some (k, true) => return "t_{" ++ (← oddIndex st k) ++ "}"
    | Option.some (k, false) => return "t_{" ++ (← evenIndex st k) ++ "}"
    | Option.none => return (← form st 9 a) ++ "[p := \\bigcirc\\bot]"
  | (``Prod.fst, #[_, _, _]) | (``Prod.snd, #[_, _, _]) =>
    match rungProj? e with
    | Option.some (k, true) => return "r_{" ++ (← oddIndex st k) ++ "}"
    | Option.some (k, false) => return "r_{" ++ (← evenIndex st k) ++ "}"
    | Option.none =>
      let s ← ppExpr e
      pure ("\\texttt{" ++ esc (toString s) ++ "}")
  -- `wip/f0T6.lean` and `wip/f0SelfSim.lean`: relativisation, `⊥ ↦ a`, the A-translation
  | (``PLLND.F0.T6.rel, #[a]) => return "\\mathrm{rel}(" ++ (← form st 0 a) ++ ")"
  | (``PLLND.F0.T6.xc, #[k]) => return "x_{" ++ (← generic st 0 k) ++ "}"
  | (``PLLND.F0.Sig.sig, #[a]) => return "\\sigma(" ++ (← form st 0 a) ++ ")"
  | (``PLLND.F0.Sig.sigN, #[n, a]) =>
    return "\\sigma^{" ++ (← generic st 0 n) ++ "}(" ++ (← form st 0 a) ++ ")"
  | (``PLLND.F0.Sig.subBot, #[a, b]) =>
    return (← form st 9 b) ++ "[\\bot := " ++ (← form st 1 a) ++ "]"
  | (``PLLND.F0.Sig.aTr, #[a, b]) => return (← form st 9 b) ++ "^{" ++ (← form st 0 a) ++ "}"
  -- subframe models, and the extension by two top worlds
  | (``PLLND.SubframeModel.force, #[m, w, a]) =>
    return wrap 5 s!"{← generic st 9 m},\\ {← generic st 9 w} \\Vdash {← form st 1 a}"
  | (``PLLND.F0.Sig.ext, #[m]) => return "\\widehat{" ++ (← generic st 9 m) ++ "}"
  | (``PLLND.F0.Sig.XW.orig, #[_, x]) => generic st p x
  | (``PLLND.F0.Sig.XW.nT, #[_]) => pure "n_{T}"
  | (``PLLND.F0.Sig.XW.eT, #[_]) => pure "e_{T}"
  | (``PLLND.F0.Sig.isTopX, #[_, w]) => return wrap 5 ((← generic st 6 w) ++ " \\in \\{n_{T}, e_{T}\\}")
  | (``PLLND.SemUI.bigAnd, #[l]) => bigOp st p "\\bigwedge" l
  | (``PLLND.bigOr, #[l]) => bigOp st p "\\bigvee" l
  | (``PLLND.RNEmbed.ladder, #[]) => pure "\\mathcal{L}"
  -- lattice polynomials, the dyadic construction and the rationals
  | (``PLLND.F0.LPoly.den, #[q]) => return "[\\![ " ++ (← generic st 0 q) ++ " ]\\!]"
  | (``PLLND.F0.LPoly.eval, #[σ, q]) => return (← generic st 9 σ) ++ "(" ++ (← generic st 0 q) ++ ")"
  | (``PLLND.F0.LPoly.vars, #[q]) => return "\\mathrm{var}(" ++ (← generic st 0 q) ++ ")"
  | (``PLLND.F0.LPoly.var, #[n]) => return "x_{" ++ (← generic st 0 n) ++ "}"
  | (``PLLND.F0.F, #[n, m]) => return "F_{" ++ (← generic st 0 n) ++ "}(" ++ (← generic st 0 m) ++ ")"
  | (``PLLND.F0.thr, #[c, n]) => return "\\theta_{" ++ (← generic st 0 c) ++ "," ++ (← generic st 0 n) ++ "}"
  | (``PLLND.F0.thr, #[c, n, i]) =>
    return "\\theta_{" ++ (← generic st 0 c) ++ "," ++ (← generic st 0 n) ++ "}(" ++ (← generic st 0 i) ++ ")"
  | (``PLLND.F0.Dy.formula, #[d]) => return "f(" ++ (← generic st 0 d) ++ ")"
  | (``PLLND.F0.Dy.lt, #[d, d']) => return wrap 5 s!"{← generic st 6 d} < {← generic st 6 d'}"
  | (``PLLND.F0.Dy.mk, #[n, x, _]) =>
    -- m/2^0 is printed m
    if natLit? x == some 0 then generic st p n
    else return (← generic st 7 n) ++ "/2^{" ++ (← generic st 0 x) ++ "}"
  | (``PLLND.F0.ratFormula, #[q]) => return "f_{\\mathbb{Q}}(" ++ (← generic st 0 q) ++ ")"
  -- Minkowski's question-mark function (`wip/f0Minkowski.lean`)
  | (``PLLND.F0.ratFormulaCF, #[q]) => return "f'(" ++ (← generic st 0 q) ++ ")"
  | (``PLLND.F0.Mink.mink, #[q]) => return "\\mathord{?}(" ++ (← generic st 0 q) ++ ")"
  | (``PLLND.F0.Mink.qmP, #[a, b]) =>
    return "\\mathord{?}(" ++ (← generic st 7 a) ++ "/" ++ (← generic st 8 b) ++ ")"
  | (``PLLND.F0.Mink.sq, #[q]) => return "\\sigma(" ++ (← generic st 0 q) ++ ")"
  | (``PLLND.F0.Mink.eqv, #[a, b]) => return wrap 5 s!"{← generic st 6 a} \\equiv {← generic st 6 b}"
  | (``PLLND.F0.Mink.rq, #[n, d, _, _]) => return wrap 7 ((← generic st 7 n) ++ "/" ++ (← generic st 8 d))
  | (``PLLND.F0.levels, #[t]) => return "\\mathrm{lev}(" ++ (← generic st 0 t) ++ ")"
  | (``PLLND.F0.root, #[t]) => return "\\mathrm{root}(" ++ (← generic st 0 t) ++ ")"
  | (``Decidable.decide, #[q, _]) => return "[" ++ (← generic st 0 q) ++ "]"
  -- a bundled map applied to an argument (Mathlib's `⇑f x`): `f(x)`
  | (``DFunLike.coe, #[_, _, _, _, f, x]) => return s!"{← funHead st f}({← generic st 0 x})"
  -- the order of F0 as an algebra, and its MacNeille completion
  | (``PLLND.RNClass, #[]) => pure "F_0"
  | (``F0Nuclear.circNucleus, #[]) | (``MacNeille.dmNucleus, #[_, _, _])
  | (``MacNeille.JoinDenseHeytingEmbedding.extNucleus, #[_, _, _, _, _, _])
  | (``MacNeille.JoinDenseHeytingEmbedding.leastExt, #[_, _, _, _, _, _]) => funHead st e
  | (``DedekindCut, #[a, _]) => return "\\mathrm{DM}(" ++ (← generic st 0 a) ++ ")"
  | (``DedekindCut.principal, #[_, _, a]) => return "{\\downarrow}" ++ (← generic st 9 a)
  | (``DedekindCut.left, #[_, _, x]) => return "\\mathrm{L}(" ++ (← generic st 0 x) ++ ")"
  | (``DedekindCut.right, #[_, _, x]) => return "\\mathrm{U}(" ++ (← generic st 0 x) ++ ")"
  | (``F0Nuclear.himp, #[a, b]) => return wrap 6 s!"{← generic st 7 a} \\Rightarrow {← generic st 7 b}"
  | (``F0Nuclear.box, #[a]) => return "\\bigcirc " ++ (← generic st 9 a)
  | (``HImp.himp, #[_, _, a, b]) => return wrap 6 s!"{← generic st 7 a} \\Rightarrow {← generic st 7 b}"
  | (``Min.min, #[_, _, a, b]) => return wrap 7 s!"{← generic st 7 a} \\sqcap {← generic st 8 b}"
  | (``Max.max, #[_, _, a, b]) => return wrap 6 s!"{← generic st 6 a} \\sqcup {← generic st 7 b}"
  | (``Top.top, #[_, _]) => pure "\\top"
  | (``Bot.bot, #[_, _]) => pure "\\bot"
  | (``SupSet.sSup, #[_, _, s]) => return wrap 6 ("\\bigvee " ++ (← generic st 9 s))
  | (``InfSet.sInf, #[_, _, s]) => return wrap 6 ("\\bigwedge " ++ (← generic st 9 s))
  | (``Set.image, #[_, _, f, s]) => return (← funHead st f) ++ "[" ++ (← generic st 0 s) ++ "]"
  | (``Monotone, #[_, _, _, _, f]) => return wrap 5 ((← generic st 9 f) ++ "\\ \\text{monotone}")
  | (``iInf, #[_, _, _, f]) =>
    -- `⨅ (a) (_ : P a), b a` is `⋀ {b a : P a}`; `⨅ a, b a` is `⋀_a b a`
    lambdaTelescope f fun xs b => do
      let x ← xs.mapM fun x => do pure (ident (← x.fvarId!.getDecl).userName.toString)
      match b.consumeMData.getAppFnArgs with
      | (``iInf, #[_, P, _, g]) =>
        if ← isProp P then
          lambdaTelescope g fun _ b' => do
            return wrap 6 ("\\bigwedge \\{" ++ (← generic st 0 b') ++ " : " ++ (← generic st 0 P) ++ "\\}")
        else return wrap 6 ("\\bigwedge_{" ++ " ".intercalate x.toList ++ "} " ++ (← generic st 7 b))
      | _ => return wrap 6 ("\\bigwedge_{" ++ " ".intercalate x.toList ++ "} " ++ (← generic st 7 b))
  -- the structure results (`wip/f0Structure.lean`, `wip/f0Hole.lean`)
  | (``PLLND.F0.half, #[n]) =>
    if natLit? n == some 1 then return wrap 7 "1/2"
    else return wrap 7 ("1/2^{" ++ (← generic st 0 n) ++ "}")
  | (``PLLND.F0.idx, #[n, m]) => return "x_{" ++ (← generic st 0 n) ++ "," ++ (← generic st 0 m) ++ "}"
  | (``PLLND.F0.copyF, #[p, q, k, d]) =>
    return "e^{" ++ (← generic st 0 p) ++ "," ++ (← generic st 0 q) ++ "}_{" ++ (← generic st 0 k) ++
      "}(" ++ (← generic st 0 d) ++ ")"
  -- F0 as a quotient
  | (``Quotient, #[_, s]) =>
    if s.consumeMData.isConstOf ``PLLND.LaxInfinite.closedSetoid then pure "F_0"
    else return "\\mathsf{Quotient}(" ++ (← generic st 0 s) ++ ")"
  | (``Infinite, #[a]) => return wrap 5 ((← generic st 6 a) ++ "\\ \\text{is infinite}")
  -- negation
  | (``Not, #[q]) =>
    match q.consumeMData.getAppFnArgs with
    | (``Nonempty, #[j]) =>
      match j.consumeMData.getAppFnArgs with
      | (``PLLND.LaxND, #[Γ, a]) => return wrap 5 s!"{← ctx st Γ} \\nvdash {← form st 1 a}"
      | _ => return wrap 4 s!"\\lnot {← generic st 6 q}"
    | (``PLLND.SemUI.Deriv, #[Γ, a]) => return wrap 5 s!"{← ctx st Γ} \\nvdash {← form st 1 a}"
    | (``PLLND.ConstraintModel.force, #[m, w, a]) =>
      return wrap 5 s!"{← model st m},\\ {← world st w} \\nVdash {← form st 1 a}"
    | (``Membership.mem, #[_, _, _, coll, x]) =>
      return wrap 5 s!"{← generic st 6 x} \\notin {← generic st 6 coll}"
    | (``Exists, _) =>
      let s ← generic st 0 q
      return wrap 0 ("\\nexists" ++ (s.drop "\\exists".length).toString)
    | _ => return wrap 4 s!"\\lnot {← generic st 6 q}"
  -- the meta-level connectives, as words
  | (``And, #[a, b]) => return wrap 3 ((← generic st 4 a) ++ metaAnd ++ (← generic st 3 b))
  | (``Or, #[a, b]) => return wrap 2 ((← generic st 3 a) ++ metaOr ++ (← generic st 2 b))
  | (``Iff, #[a, b]) => return wrap 1 s!"{← generic st 2 a} \\iff {← generic st 2 b}"
  | (``Ne, #[_, a, b]) => return wrap 5 s!"{← generic st 6 a} \\ne {← generic st 6 b}"
  | (``LE.le, #[_, _, a, b]) => return wrap 5 s!"{← generic st 6 a} \\le {← generic st 6 b}"
  | (``LT.lt, #[_, _, a, b]) => return wrap 5 s!"{← generic st 6 a} < {← generic st 6 b}"
  | (``GE.ge, #[_, _, a, b]) => return wrap 5 s!"{← generic st 6 a} \\ge {← generic st 6 b}"
  | (``GT.gt, #[_, _, a, b]) => return wrap 5 s!"{← generic st 6 a} > {← generic st 6 b}"
  | (``Membership.mem, #[_, _, _, coll, x]) => return wrap 5 s!"{← generic st 6 x} \\in {← generic st 6 coll}"
  | (``Exists, #[_, f]) =>
    lambdaTelescope f fun xs b => do
      -- `∃ x, x ∈ C ∧ P` is `∃ x ∈ C. P`
      if xs.size == 1 then
        if let (``And, #[h, P]) := b.consumeMData.getAppFnArgs then
          if let (``Membership.mem, #[_, _, _, coll, y]) := h.consumeMData.getAppFnArgs then
            if y.consumeMData == xs[0]! then
              let x := ident (← xs[0]!.fvarId!.getDecl).userName.toString
              return wrap 0 s!"\\exists {x} \\in {← generic st 6 coll}.\\, {← generic st 0 P}"
      let names ← xs.mapM fun x => do pure (ident (← x.fvarId!.getDecl).userName.toString)
      return wrap 0 s!"\\exists {" ".intercalate names.toList}.\\, {← generic st 0 b}"
  | (``True, _) => pure "\\mathsf{True}"
  | (``False, _) => pure "\\mathsf{False}"
  | (``Bool.true, _) => pure "1"
  | (``Bool.false, _) => pure "0"
  | (``Option.some, #[_, a]) => return "\\mathsf{some}(" ++ (← generic st 0 a) ++ ")"
  | (``Option.none, _) => pure "\\mathsf{none}"
  -- numbers
  | (``OfNat.ofNat, #[_, n, _]) => generic st p n
  | (``Nat.cast, #[_, _, a]) => generic st0 p a
  | (``NatCast.natCast, #[_, _, a]) => generic st0 p a
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return wrap 6 s!"{← generic st 6 a} + {← generic st 7 b}"
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return wrap 6 s!"{← generic st 6 a} - {← generic st 7 b}"
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    -- `2k`, `2(k + 1)`: a numeral times a variable or a sum is juxtaposed
    let jux := (natLit? a).isSome &&
      (b.consumeMData.isFVar || b.consumeMData.isAppOfArity ``HAdd.hAdd 6 ||
       b.consumeMData.isAppOfArity ``HSub.hSub 6)
    if jux then return wrap 7 ((← generic st 7 a) ++ (← generic st 8 b))
    return wrap 7 s!"{← generic st 7 a} \\cdot {← generic st 8 b}"
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => return wrap 7 s!"{← generic st 7 a} / {← generic st 8 b}"
  | (``HPow.hPow, #[_, _, _, _, a, b]) =>
    return wrap 8 ((← generic st 9 a) ++ "^{" ++ (← generic st 0 b) ++ "}")
  | (``HAppend.hAppend, #[_, _, _, _, a, b]) =>
    return wrap 6 ((← generic st 6 a) ++ " \\mathbin{+\\!\\!+} " ++ (← generic st 7 b))
  | (``List.cons, #[_, a, l]) =>
    if let some fs := listLit? e then
      return "[" ++ ", ".intercalate (← fs.mapM (generic st 0)) ++ "]"
    return wrap 6 s!"{← generic st 7 a} :: {← generic st 6 l}"
  | (``List.nil, _) => pure "[\\,]"
  | (``Prod.mk, #[_, _, a, b]) => return s!"({← generic st 0 a}, {← generic st 0 b})"
  | (``Nat, _) => pure "\\mathbb{N}"
  | (``Rat, _) => pure "\\mathbb{Q}"
  | (``Bool, _) => pure "\\mathsf{Bool}"
  | (``String, _) => pure "\\mathsf{String}"
  | (``List, #[a]) => return "\\mathsf{List}\\," ++ (← generic st 9 a)
  -- full applications of the formula constructors go to `form`
  | (``PLLFormula.falsePLL, #[]) | (``PLLFormula.prop, #[_]) | (``PLLFormula.and, #[_, _])
  | (``PLLFormula.or, #[_, _]) | (``PLLFormula.ifThen, #[_, _]) | (``PLLFormula.somehow, #[_])
  | (``PLLFormula.notPLL, #[_]) => form st p e
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

/-- A derivation type `Γ ⊢ A` (`LaxND Γ A`), as a binder: a premise. -/
partial def isJudgement (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``PLLND.LaxND

/-- `∀`-binders: variables are quantified, propositions and derivations become
premises, instance arguments vanish, `x` followed by `x ∈ C` is `x ∈ C`. -/
partial def quant (st0 : St) (p : Nat) (e : Expr) : MetaM String :=
  forallTelescope e fun xs body => do
    let st := {st0 with nested := true}
    let mut vars : Array String := #[]
    let mut prems : Array String := #[]
    let mut skip : Option FVarId := none
    for i in [0:xs.size] do
      let x := xs[i]!
      if skip == some x.fvarId! then continue
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then continue
      let ty := d.type
      if (← isProp ty) || isJudgement ty then
        prems := prems.push (← generic st 3 ty)
      else
        let nm := ident d.userName.toString
        -- a bounded variable: the next binder is the hypothesis `x ∈ C`
        let mut done := false
        if h : i + 1 < xs.size then
          let hy ← xs[i + 1].fvarId!.getDecl
          if let (``Membership.mem, #[_, _, _, coll, y]) := hy.type.consumeMData.getAppFnArgs then
            if y.consumeMData == x then
              vars := vars.push (nm ++ " \\in " ++ (← generic st 6 coll))
              skip := some xs[i + 1].fvarId!
              done := true
        if !done then vars := vars.push nm
    let binder := if vars.isEmpty then "" else
      "\\forall\\, " ++ ",\\ ".intercalate vars.toList ++ ".\\; "
    let isIff := body.consumeMData.isAppOfArity ``Iff 2
    let concl ← generic st (if prems.isEmpty || !isIff then 0 else 2) body
    if p > 0 || st0.nested then
      if prems.isEmpty then return paren (binder ++ concl)
      else return paren (binder ++ " \\Longrightarrow ".intercalate (prems.toList ++ [concl]))
    else if st0.flat then
      return binder ++ " \\Longrightarrow ".intercalate (prems.toList ++ [concl])
    else
      return fillRows binder ((prems.toList.map (· ++ " \\Longrightarrow")) ++ [concl])
end

/-- A definition is printed by its defining equation when its value is a
proposition or a formula and it is not defined by recursion. -/
def defEquation? (n : Name) (flat : Bool := false) : MetaM (Option String) := do
  let env ← getEnv
  let some (.defnInfo dv) := env.find? n | return none
  let recursive := (dv.value.find? fun s => match s with
    | .const c _ => isAuxRecursor env c || Lean.Meta.isMatcherCore env c || isRecCore env c ||
        c == ``WellFounded.fix
    | _ => false).isSome
  if recursive then return none
  lambdaTelescope dv.value fun xs body => do
    let lhsE := mkAppN (mkConst n (dv.levelParams.map mkLevelParam)) xs
    let ty ← whnf (← inferType lhsE)
    let isP := ty.isProp
    let isF := ty.isConstOf ``PLLFormula
    unless isP || isF do return none
    let lhs ← generic {flat := flat} 0 lhsE
    let rhs ← generic {flat := flat} 0 body
    if lhs == rhs then return none
    let rel := if isP then " \\mathrel{:\\Longleftrightarrow} " else " \\mathrel{:=} "
    let s := lhs ++ rel ++ rhs
    if flat then return some s
    if s.startsWith "\\begin{aligned}" || (rhs.startsWith "\\begin{aligned}") then
      return some s
    if visLen s > rowMeasure then return some (rows (breakRow s))
    return some s

/-- The statement of `n` as TeX, or `none` when there is nothing to print. -/
def stmtOf (n : Name) : MetaM (Option String) := do
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  let judgement ← forallTelescope ci.type fun _ b => pure (isJudgement b)
  unless (← isProp ci.type) || judgement do return ← defEquation? n
  let s ← generic {} 0 ci.type
  if visLen s > rowMeasure && !s.startsWith "\\begin{aligned}" then
    return some (rows (breakRow s))
  return some s

/-- The statement of `n` on one line (the tables of supporting declarations). -/
def stmtFlat (n : Name) : MetaM (Option String) := do
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  let judgement ← forallTelescope ci.type fun _ b => pure (isJudgement b)
  unless (← isProp ci.type) || judgement do return ← defEquation? n (flat := true)
  generic {flat := true} 0 ci.type

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

end F0Paper.Math
