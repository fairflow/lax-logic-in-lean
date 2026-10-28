/-
The notation table shared by the Verso papers on this development (the F0
paper, `F0Paper/`, and the semantics paper, `SemPaper/`): `{stmt}`Full.Name`` prints the
conventional-notation statement of a declaration, generated from its type at
build time, and `stmtFlat` the one-line form of the tables.  The method and
the layout code are those of `CLPPaper/Math.lean`
(docs/verso-paper-workflow.md §3).  Factored out of `F0Paper/Math.lean` on
2026-10-24 without changing the F0 paper's output.

The table is one lookup by constant name.  Constants of the library modules
imported below are named with a double backtick, checked when this file is
compiled; those a paper brings from elsewhere (the F0 development in
`wip/`, the FRJ library, Mathlib's MacNeille completion) with a single backtick, a
plain name literal, so that this module imports no `wip/` file.  A case whose
constant is not in a paper's environment never fires.

* Binders become quantifiers without type annotations; hypotheses, and
  derivations `p : Γ ⊢ A` taken as arguments, become premises; instance
  arguments vanish; a variable followed by the hypothesis `x ∈ C` is written
  `∀ x ∈ C`.
* The object language: `⊥ ∧ ∨ ↠ ◯`, `A ↠ ⊥` as `¬A`, `⊥ ↠ ⊥` as `⊤`; the
  judgements `Γ ⊢ A`, `Γ ⊬ A`, `A ⊣⊢ B`, `Γ ⊨ A`, forcing `M, w ⊩ A`; for
  the F0 paper the cover relation `u ⋖ v`, the named formulas `t_n` (the
  substituted rungs), `r_n` (the rungs), `g_k` (the gaps), `◯⊥`, `¬◯⊥`,
  finite conjunctions and disjunctions over a list `⋀_{i ∈ S}`, `⋁_{j ∈ T}`,
  and the models of the independence proof.
* Meta-level `∧`, `∨` are the words "and", "or", so that they are not read as
  the object-level connectives.
* A definition prints its defining equation `lhs := rhs` (`:⟺` for a
  proposition or a Boolean test); a recursive definition prints its equation
  lemmas (`getEqnsFor?`), one per case; a structure-valued definition prints
  its type and its data fields; a value chosen by `Classical.choice` prints
  its type.  An inductive type prints its constructors: the rules of a
  derivation type, a grammar otherwise; a structure prints its fields.

Nothing is written by hand: the same declaration always gives the same
mathematics.
-/
import Lean
import Lean.DocString.Syntax
import VersoManual
import LaxLogic.PLL.Semantics.Subframe
import LaxLogic.ClosedFragmentLattice
import LaxLogic.Deriv
import LaxLogic.Interd
import LaxLogic.PLL.ND.Consequence
import LaxLogic.PLL.SemUI.SemUIFrag

open Lean Meta Elab
open Lean.Doc.Syntax
open Verso Doc Elab Genre Manual ArgParse

namespace PaperKit.Math

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
  -- a hygienic name `x._@.M._hyg.8` is `x`
  let s := (s.splitOn "._@.").headD s
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
  /-- the rung pairs `(rnP k).1`, `(rnP k).2` as projections, not `r_{2k+1}`,
  `r_{2k+2}` (the equations of `rn` itself, where the notation is circular) -/
  raw : Bool := false
  /-- rule schemata: no leading `∀` (the constructors of a derivation type) -/
  schematic : Bool := false

/-- Named variable-free formulas: the six formulas of `wip/f0Covers.lean` are
the rungs `t₀ … t₅` (`rnSub_0` … `rnSub_5`, all `rfl`). -/
def namedForms : List (Name × String × Nat) :=
  [(`PLLND.F0.bot, "t_{0}", 9), (`PLLND.F0.e, "t_{1}", 9), (`PLLND.F0.ne, "t_{2}", 9),
   (`PLLND.F0.t3, "t_{3}", 9), (`PLLND.F0.t4, "t_{4}", 9), (`PLLND.F0.t5, "t_{5}", 9),
   (`PLLND.RNEmbed.oBot, "\\bigcirc\\bot", 4), (`PLLND.RNEmbed.notOBot, "\\lnot\\bigcirc\\bot", 4),
   (``PLLFormula.truePLL, "\\top", 9),
   -- `wip/f0T6.lean`: `t6 = t5 ↠ t3`, `u = ◯¬◯⊥`, and regularity of `◯⊥`
   (`PLLND.F0.T6.t6F, "t_{6}", 9), (`PLLND.F0.T6.uF, "u", 9),
   (`PLLND.F0.T6.nne, "\\lnot\\lnot\\bigcirc\\bot", 4),
   (`PLLND.F0.T6.regE, "\\lnot\\lnot\\bigcirc\\bot \\twoheadrightarrow \\bigcirc\\bot", 1),
   -- `wip/f0NotIso.lean`: `c₁ = ◯t₃`, `g₁ = c₁ ↠ t₃`, and `t₆` again
   (`PLLND.F0.NotIso.c1F, "c_{1}", 9), (`PLLND.F0.NotIso.g1F, "g_{1}", 9),
   (`PLLND.F0.NotIso.t6F, "t_{6}", 9)]

/-- The tables' lists of `wip/f0Covers.lean` are read as the sets they list. -/
def tableLists : List Name :=
  [`PLLND.F0.D1_list, `PLLND.F0.D2_list, `PLLND.F0.D3_list, `PLLND.F0.D4_list,
   `PLLND.F0.D5_list]

/-- A name for a variable of type `ty` not among `used`: `q` for an atom's
name (a `String`), `φ ψ χ` for formulas, `a b c` for numbers, else `x y z`. -/
def varName (ty : Expr) (used : List String) : Name :=
  let cands :=
    if ty.isConstOf ``String then ["q", "q'", "q''"]
    else if ty.isConstOf ``PLLFormula then ["φ", "ψ", "χ", "φ'", "ψ'"]
    else if ty.isConstOf ``Nat then ["a", "b", "c", "a'", "b'"]
    else ["x", "y", "z", "x'", "y'"]
  Name.mkSimple ((cands.find? (!used.contains ·)).getD (cands.head! ++ "'''"))

/-- `f` as a `λ` over named variables (`varName`), so that two arguments of
the same type do not print with the same name. -/
partial def etaNamed (f : Expr) : MetaM Expr := do
  let rec go (e ty : Expr) (xs : Array Expr) (used : List String) : MetaM Expr := do
    match ← whnf ty with
    | .forallE _ d b bi =>
      let nm := varName d used
      withLocalDecl nm bi d fun x => go (mkApp e x) (b.instantiate1 x) (xs.push x) (nm.toString :: used)
    | _ => mkLambdaFVars xs e
  go f (← inferType f) #[] []

/-- `2k+1` for an index `k`: a numeral is computed, a compound bracketed. -/
def isAtomic (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ | .lit _ => true
  | e => e.isAppOfArity ``OfNat.ofNat 3

/-- Which paper's notation is in force: `"f0"`, the default, is the table as
the F0 paper prints it; `"sem"` adds the cases of the semantics paper (`semCase?`).  A
paper's sections set it with `set_option paperkit.notation "sem"`, so that
adding a case for one paper never changes another's output. -/
register_option paperkit.notation : String := {
  defValue := "f0"
  descr := "the notation cases in force: \"f0\" (the F0 paper) or \"sem\" (the semantics paper)"
}

/-- The Boolean checkers of the semantics paper: `check s c = true` is printed as
`check(s, c)`, `= false` as its negation. -/
def isCheckHead (a : Expr) : Bool :=
  match a.consumeMData.getAppFn.constName? with
  | Option.some n => [`PLLND.SubTab.check, `Certify.Certifier.check, `PLLND.SubTab.SubCM.refutes,
      `PLLND.SubTab.SubCM.okB, `PLLND.SubTab.SubCM.forceB].contains n
  | Option.none => false

/-- Instance arguments that state a condition on a model, printed as premises
under the semantics paper's notation (others, the algebraic structure, vanish). -/
def isConditionClass (ty : Expr) : Bool :=
  match ty.consumeMData.getAppFn.constName? with
  | Option.some n => [``Finite, `PLLND.SubframeModel.CF.FinDec].contains n
  | Option.none => false

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
      | (`PLLND.F0.Sig.aTr, #[a]) => return (← generic st 9 l) ++ "^{" ++ (← form st 0 a) ++ "}"
      | (`PLLND.F0.Sig.subBot, #[a]) =>
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

/-- `k'` when `k` is `k' + 1` (or `Nat.succ k'`) with `k'` atomic. -/
partial def succOf? (k : Expr) : Option Expr :=
  match k.consumeMData.getAppFnArgs with
  | (``Nat.succ, #[a]) => if isAtomic a then some a else none
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => if natLit? b == some 1 && isAtomic a then some a else none
  | _ => none

/-- `2k+1` for the index `k`. -/
partial def oddIndex (st : St) (k : Expr) : MetaM String := do
  if let some n := natLit? k then return toString (2 * n + 1)
  if isAtomic k then return "2" ++ (← generic st 9 k) ++ " + 1"
  if let some a := succOf? k then return "2" ++ (← generic st 9 a) ++ " + 3"
  return "2(" ++ (← generic st 0 k) ++ ") + 1"

/-- `2k+2` for the index `k`. -/
partial def evenIndex (st : St) (k : Expr) : MetaM String := do
  if let some n := natLit? k then return toString (2 * n + 2)
  if isAtomic k then return "2" ++ (← generic st 9 k) ++ " + 2"
  if let some a := succOf? k then return "2" ++ (← generic st 9 a) ++ " + 4"
  return "2(" ++ (← generic st 0 k) ++ ") + 2"

/-- The rung pair `rnP k = (r_{2k+1}, r_{2k+2})`, projected: `some (k, odd?)`. -/
partial def rungProj? (e : Expr) : Option (Expr × Bool) :=
  match e.consumeMData.getAppFnArgs with
  | (``Prod.fst, #[_, _, pr]) => match pr.consumeMData.getAppFnArgs with
    | (`PLLND.RNEmbed.rnP, #[k]) => some (k, true)
    | _ => none
  | (``Prod.snd, #[_, _, pr]) => match pr.consumeMData.getAppFnArgs with
    | (`PLLND.RNEmbed.rnP, #[k]) => some (k, false)
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
  | (`PLLND.F0.cmM, #[ms]) =>
    match ms.consumeMData.getAppFnArgs with
    | (`PLLND.F0.levels, #[t]) => return "\\mathcal{M}_{" ++ (← generic st 0 t) ++ "}"
    | _ => return "\\mathcal{M}(" ++ (← generic st 0 ms) ++ ")"
  | (`PLLND.RNEmbed.cmE, #[k]) => return "\\mathcal{E}_{" ++ (← generic st 0 k) ++ "}"
  | (`PLLND.RNEmbed.Skel.cm, #[s]) => return (← generic st 9 s) ++ "^{+}"
  | _ => generic st 9 m

/-- The head of an application `f(x)` of a bundled map: the nuclei and
embeddings of the completion section by name, anything else generically. -/
partial def funHead (st : St) (f : Expr) : MetaM String := do
  let f := f.consumeMData
  if f.isConstOf `F0Nuclear.circNucleus then return "\\bigcirc"
  if f.isConstOf `MacNeille.principalHom then return "{\\downarrow}"
  if f.isConstOf `DedekindCut.principal then return "{\\downarrow}"
  match f.getAppFnArgs with
  | (`MacNeille.dmNucleus, #[_, _, j]) => return "\\overline{" ++ (← generic st 9 j) ++ "}"
  | (`MacNeille.JoinDenseHeytingEmbedding.extNucleus, #[_, _, _, _, emb, j]) =>
    return "\\overline{" ++ (← generic st 9 j) ++ "}^{" ++ (← generic st 9 emb) ++ "}"
  | (`MacNeille.JoinDenseHeytingEmbedding.leastExt, #[_, _, _, _, emb, j]) =>
    return "\\underline{" ++ (← generic st 9 j) ++ "}^{" ++ (← generic st 9 emb) ++ "}"
  | (`MacNeille.JoinDenseHeytingEmbedding.toHom, #[_, _, _, _, emb]) => generic st 9 emb
  | (`DedekindCut.principal, #[_, _]) => return "{\\downarrow}"
  | _ => generic st 9 f

/-- The edge set of the multi-edge lift. -/
partial def edges (st : St) (ms : Expr) : MetaM String := do
  match ms.consumeMData.getAppFnArgs with
  | (`PLLND.F0.levels, #[t]) => return "E_{" ++ (← generic st 0 t) ++ "}"
  | _ => return "E(" ++ (← generic st 0 ms) ++ ")"

/-- The cases of the semantics paper (`paperkit.notation = "sem"`): provability `⊢ φ`,
signed sequents `Γ ⇒ Δ`, the certifiers' checks, the carriers and relations
of the models, the FRJ calculi and `G4c`, and the semantic order of F0. -/
partial def semCase? (st : St) (p : Nat) (e : Expr) : MetaM (Option String) := do
  let wrap (q : Nat) (s : String) := if q < p then paren s else s
  -- `P → False` is `¬P`
  if let .forallE _ d b _ := e then
    if !b.hasLooseBVars && b.consumeMData.isConstOf ``False && (← isProp d) then
      return some (← generic st p (mkNot d))
  match e.getAppFnArgs with
  | (`PLLND.SubTab.Holds, #[φ]) => return some (wrap 5 ("{} \\vdash " ++ (← form st 1 φ)))
  | (``Not, #[q]) =>
    match q.consumeMData.getAppFnArgs with
    | (`PLLND.SubTab.Holds, #[φ]) => return some (wrap 5 ("{} \\nvdash " ++ (← form st 1 φ)))
    | (``PLLND.SubframeModel.force, #[m, w, a]) =>
      return some (wrap 5 s!"{← generic st 9 m},\\ {← generic st 9 w} \\nVdash {← form st 1 a}")
    | _ => return none
  | (`PLLND.SubTab.SSeq.mk, #[b, Γ, Δ]) =>
    let arrow ← if b.consumeMData.isConstOf ``Bool.true then pure "\\Rightarrow_{S}"
      else if b.consumeMData.isConstOf ``Bool.false then pure "\\Rightarrow"
      else pure ("\\Rightarrow_{" ++ (← generic st 0 b) ++ "}")
    return some (wrap 5 ((← ctx st Γ) ++ " " ++ arrow ++ " " ++ (← ctx st Δ)))
  | (``Eq, #[_, a, b]) =>
    if isCheckHead a then
      if b.consumeMData.isConstOf ``Bool.true then return some (← generic st p a)
      if b.consumeMData.isConstOf ``Bool.false then
        return some (wrap 4 ("\\lnot " ++ (← generic st 6 a)))
    return none
  | (`Certify.Certifier.check, #[_, _, _, c, x, y]) =>
    return some ((← generic st 9 c) ++ ".\\mathit{check}(" ++ (← generic st 0 x) ++ ", " ++
      (← generic st 0 y) ++ ")")
  | (``PLLND.SubframeModel.W, #[M]) => return some ("W_{" ++ (← generic st 0 M) ++ "}")
  | (``PLLND.ConstraintModel.W, #[C]) => return some ("W_{" ++ (← generic st 0 C) ++ "}")
  | (``PLLND.ConstraintModel.Ri, #[_, a, b]) =>
    return some (wrap 5 ((← generic st 6 a) ++ " \\mathrel{R_i} " ++ (← generic st 6 b)))
  | (``PLLND.ConstraintModel.Rm, #[_, a, b]) =>
    return some (wrap 5 ((← generic st 6 a) ++ " \\mathrel{R_m} " ++ (← generic st 6 b)))
  | (``PLLND.SubframeModel.le, #[_, a, b]) =>
    return some (wrap 5 ((← generic st 6 a) ++ " \\le " ++ (← generic st 6 b)))
  | (``Finite, #[a]) => return some (wrap 5 ((← generic st 6 a) ++ "\\ \\text{finite}"))
  | (``Subtype.val, #[_, _, a]) => return some (← generic st p a)
  | (``Decidable, #[q]) => return some ("\\mathsf{Decidable}(" ++ (← generic st 0 q) ++ ")")
  | (``PSum, #[a, b]) => return some (wrap 2 ((← generic st 3 a) ++ " \\oplus " ++ (← generic st 3 b)))
  -- the FRJ calculi: semantic `PLL` is validity in the finite rooted poset models
  | (`FRJ.PLL, #[A]) => return some (wrap 5 ("\\models_{\\mathrm{fin}} " ++ (← generic st 6 A)))
  | (`FRJ.ofPLL, #[φ]) => return some (← form st p φ)
  | (`FRJ.Kripke.valid, #[K, A]) =>
    return some (wrap 5 ((← generic st 6 K) ++ " \\models " ++ (← generic st 6 A)))
  | (`FRJ.Gbu.ProvableGbuC, #[G]) =>
    return some (wrap 5 ("\\vdash_{\\mathrm{Gbu}\\bigcirc} " ++ (← generic st 6 G)))
  | (`FRJ.DisprovableW, #[G]) =>
    return some (wrap 5 ("\\mathrm{Disprovable}_{\\mathrm{FRJW}}(" ++ (← generic st 0 G) ++ ")"))
  | (`PLLND.G4c, #[Γ, C]) =>
    return some (wrap 5 ((← ctx st Γ) ++ " \\vdash_{\\mathrm{G4c}} " ++ (← form st 1 C)))
  | (``Nonempty, #[j]) =>
    match j.consumeMData.getAppFnArgs with
    | (`PLLND.Tm, #[Γ, φ]) =>
      return some (wrap 5 ((← ctx st Γ) ++ " \\vdash_{\\mathrm{Tm}} " ++ (← form st 1 φ)))
    | _ => return none
  | (`PLLND.Tm, #[Γ, φ]) =>
    return some (wrap 5 ((← ctx st Γ) ++ " \\vdash_{\\mathrm{Tm}} " ++ (← form st 1 φ)))
  | (``PLLND.LaxInfinite.Le, #[a, b]) =>
    return some (wrap 5 ((← form st 1 a) ++ " \\models " ++ (← form st 1 b)))
  | (``PLLND.LaxInfinite.LaxEquiv, #[a, b]) =>
    return some (wrap 5 ((← form st 1 a) ++ " \\equiv " ++ (← form st 1 b)))
  -- the Esakia dual (`wip/esakiaNuclearGen.lean`) and the sets it is made of
  | (`EsakiaNuclear.Gen.phi, #[_, _, a]) => return some ("\\varphi(" ++ (← generic st 0 a) ++ ")")
  | (`EsakiaNuclear.Gen.Nj, #[_, _, j]) => return some ("N_{" ++ (← generic st 0 j) ++ "}")
  | (`EsakiaNuclear.Gen.Spec, #[A, _]) => return some ("X_{" ++ (← generic st 0 A) ++ "}")
  | (`EsakiaNuclear.Gen.IsNuclear, #[_, _, _, N]) =>
    return some (wrap 5 ((← generic st 6 N) ++ "\\ \\text{nuclear}"))
  | (`IsClosed, #[_, _, s]) => return some (wrap 5 ((← generic st 6 s) ++ "\\ \\text{closed}"))
  | (`IsClopen, #[_, _, s]) => return some (wrap 5 ((← generic st 6 s) ++ "\\ \\text{clopen}"))
  | (`lowerClosure, #[_, _, s]) => return some ("{\\downarrow}" ++ (← generic st 9 s))
  | (`SetLike.coe, #[_, _, _, s]) => return some (← generic st p s)
  | (`HasCompl.compl, #[_, _, s]) | (`Compl.compl, #[_, _, s]) =>
    return some ((← generic st 9 s) ++ "^{c}")
  | (`SDiff.sdiff, #[_, _, a, b]) =>
    return some (wrap 6 ((← generic st 6 a) ++ " \\setminus " ++ (← generic st 7 b)))
  | (`Inter.inter, #[_, _, a, b]) =>
    return some (wrap 6 ((← generic st 6 a) ++ " \\cap " ++ (← generic st 7 b)))
  | (`Union.union, #[_, _, a, b]) =>
    return some (wrap 6 ((← generic st 6 a) ++ " \\cup " ++ (← generic st 7 b)))
  | (`HasSubset.Subset, #[_, _, a, b]) =>
    return some (wrap 5 ((← generic st 6 a) ++ " \\subseteq " ++ (← generic st 6 b)))
  | _ => return none

/-- The cases added for the F0 paper's v0.5 (2026-10-25: the filters
`[p, ⊤]` of `wip/f0FilterIso.lean`, the points of the completion in
`wip/f0MacNeillePoints.lean`), in force only under the F0 paper's notation
(`"f0"`), so that the semantics paper's output does not change. -/
partial def f0Case? (st : St) (p : Nat) (e : Expr) : MetaM (Option String) := do
  let wrap (q : Nat) (s : String) := if q < p then paren s else s
  match e.getAppFnArgs with
  -- an element of a filter `[p, ⊤]` is written as the element of F0 it is
  | (``Subtype.val, #[_, _, a]) => return some (← generic st p a)
  | (``Subtype.mk, #[_, _, v, _]) => return some (← generic st p v)
  -- the Heyting negation `x ⇒ ⊥`
  | (`HasCompl.compl, #[_, _, a]) | (`Compl.compl, #[_, _, a]) =>
    return some (wrap 4 ("\\lnot " ++ (← generic st 9 a)))
  -- the semantic order of formulas: every world forcing `a` forces `b`
  | (``PLLND.LaxInfinite.Le, #[a, b]) =>
    return some (wrap 5 ((← form st 1 a) ++ " \\models " ++ (← form st 1 b)))
  -- the completion of F0, its implication, cardinals, the reals
  | (`DedekindCut, #[a, _]) =>
    if a.consumeMData.isConstOf ``PLLND.RNClass then return some "F^{*}" else return none
  | (`MacNeille.cutHimp, #[_, _, x, y]) =>
    return some (wrap 6 s!"{← generic st 7 x} \\Rightarrow {← generic st 7 y}")
  | (`Cardinal.mk, #[a]) => return some ("|" ++ (← generic st 0 a) ++ "|")
  | (`Cardinal.continuum, #[]) => return some "2^{\\aleph_0}"
  | (``Function.Injective, #[_, _, f]) =>
    return some (wrap 5 ((← generic st 9 f) ++ "\\ \\text{is one-to-one}"))
  | (`Rat.cast, #[_, _, q]) => return some (← generic st p q)
  | (`Real, #[]) => return some "\\mathbb{R}"
  -- `wip/f0MacNeillePoints.lean`
  | (`PLLND.F0.Points.cl, #[φ, _]) => return some (← form st p φ)
  | (`PLLND.F0.Points.fq, #[]) => return some "f'"
  | (`PLLND.F0.Points.fq, #[q]) => return some ("f'(" ++ (← generic st 0 q) ++ ")")
  | (`PLLND.F0.Points.X, #[]) => return some "X"
  | (`PLLND.F0.Points.X, #[r]) => return some ("X_{" ++ (← generic st 0 r) ++ "}")
  | (`PLLND.F0.Points.gapCut, #[]) => return some "x_{\\mathrm{gap}}"
  | (`PLLND.F0.Points.gaps, #[]) => return some "\\mathcal{G}"
  -- `wip/f0FilterIso.lean`: the classes of the bottom of F0, and the case shapes
  | (`PLLND.F0.FilterIso.E, #[]) => return some "t_{1}"
  | (`PLLND.F0.FilterIso.NE, #[]) => return some "t_{2}"
  | (`PLLND.F0.FilterIso.T4c, #[]) => return some "t_{4}"
  | (`PLLND.F0.FilterIso.T5c, #[]) => return some "t_{5}"
  | (`PLLND.F0.FilterIso.C1, #[]) => return some "c_{1}"
  | (`PLLND.F0.FilterIso.C1n, #[n]) => return some ("\\sigma^{" ++ (← generic st 0 n) ++ "}(c_{1})")
  | (`PLLND.F0.FilterIso.CoversC, #[u, v]) =>
    return some (wrap 5 ((← generic st 6 u) ++ " \\lessdot " ++ (← generic st 6 v)))
  | (`PLLND.F0.FilterIso.MeetPrime, #[x]) =>
    return some (wrap 5 ((← generic st 6 x) ++ "\\ \\text{meet-prime}"))
  -- `wip/f0Normal.lean`: the non-normal filter `F₇` and the suprema
  | (`PLLND.F0.Normal.ρ, #[k]) | (`PLLND.F0.Normal.ρF, #[k]) =>
    return some ("\\rho_{" ++ (← generic st 0 k) ++ "}")
  | (`PLLND.F0.Normal.ρ, #[]) => return some "\\rho"
  | (`PLLND.F0.Normal.d, #[k]) | (`PLLND.F0.Normal.dF, #[k]) =>
    return some ("d_{" ++ (← generic st 0 k) ++ "}")
  | (`PLLND.F0.Normal.odd, #[k]) | (`PLLND.F0.Normal.oddF, #[k]) =>
    return some ("t_{" ++ (← oddIndex st k) ++ "}")
  | (`PLLND.F0.Normal.t7, #[]) | (`PLLND.F0.Normal.t7F, #[]) => return some "t_{7}"
  | (`PLLND.F0.Normal.F7, #[]) => return some "F_{7}"
  | (`PLLND.F0.Normal.cls, #[φ, _]) => return some (← form st p φ)
  | (`PLLND.F0.Normal.IsFilter, #[s]) =>
    return some (wrap 5 ((← generic st 6 s) ++ "\\ \\text{a filter}"))
  | (`upperBounds, #[_, _, s]) =>
    match s.consumeMData.getAppFnArgs with
    | (`lowerBounds, #[_, _, t]) => return some ("{" ++ (← generic st 9 t) ++ "}^{lu}")
    | _ => return some ("{" ++ (← generic st 9 s) ++ "}^{u}")
  | (`lowerBounds, #[_, _, s]) => return some ("{" ++ (← generic st 9 s) ++ "}^{l}")
  | (`IsGLB, #[_, _, s, a]) =>
    return some (wrap 5 ((← generic st 6 a) ++ " = \\bigwedge " ++ (← generic st 9 s)))
  | (`IsLUB, #[_, _, s, a]) =>
    return some (wrap 5 ((← generic st 6 a) ++ " = \\bigvee " ++ (← generic st 9 s)))
  | (`Set.range, #[_, _, f]) =>
    let f := f.consumeMData
    if f.isConstOf `PLLND.F0.Normal.ρ then return some "\\{\\rho_{k} : k \\in \\mathbb{N}\\}"
    if f.isConstOf `PLLND.F0.Normal.odd then return some "\\{t_{2k+1} : k \\in \\mathbb{N}\\}"
    return none
  | (`Set.Iic, #[_, _, a]) => return some ("{\\downarrow}" ++ (← generic st 9 a))
  -- v0.6 (2026-10-28): free Heyting algebras in F0 (`wip/f0FreeHAn.lean`,
  -- `f0FreeIPL`, `f0FreePair`, `f0FreeBase3`, `f0MeetCount`)
  | (``Eq, #[_, a, b]) =>
    -- the Boolean side conditions: ◯-free, the variables in use
    unless b.consumeMData.isConstOf ``Bool.true do return none
    match a.consumeMData.getAppFnArgs with
    | (`PLLND.SemUI.boxFree, #[x]) =>
      return some (wrap 5 ((← form st 4 x) ++ "\\ \\text{is}\\ \\bigcirc\\text{-free}"))
    | (`PLLND.F0.FreeHAn.varsBelow, #[n, x]) =>
      let vs ← if natLit? n == some 1 then pure "\\{p_{0}\\}"
        else if natLit? n == some 2 then pure "\\{p_{0}, p_{1}\\}"
        else do pure ("\\{p_{0}, \\ldots, p_{" ++ (← generic st 6 n) ++ " - 1}\\}")
      return some (wrap 5 ("\\mathrm{var}(" ++ (← form st 0 x) ++ ") \\subseteq " ++ vs))
    | (`PLLND.F0.FreeIPL.onlyP, #[x]) =>
      return some (wrap 5 ("\\mathrm{var}(" ++ (← form st 0 x) ++ ") \\subseteq \\{p\\}"))
    | _ => return none
  -- the relativisation `A[a := x(a), ⊥ := b]`; the generator assignments by name
  | (`PLLND.F0.FreeHAn.relB, #[b, x, a]) =>
    let xs := x.consumeMData
    let hd ← if xs.isConstOf `PLLND.F0.Base3.x3 then pure "x"
      else if xs.isConstOf `PLLND.F0.Base3.xω then pure "x^{\\omega}"
      else if xs.isConstOf `PLLND.F0.Pair.xs then pure "y"
      else generic st 9 xs
    return some ((← form st 9 a) ++ "[q := " ++ hd ++ "(q),\\ \\bot := " ++ (← form st 1 b) ++ "]")
  | (`PLLND.F0.FreeIPL.relG, #[x, a]) =>
    return some ((← form st 9 a) ++ "[q := " ++ (← generic st 9 x) ++ "(q),\\ \\bot := t_{3}]")
  | (`PLLND.F0.FreeIPL.Rneg, #[a]) =>
    return some (wrap 1 ((← form st 2 a) ++ " \\twoheadrightarrow t_{3}"))
  | (`PLLND.F0.FreeIPL.sgn, #[s, x]) =>
    return some ((← form st 9 x) ++ "^{" ++ (← generic st 0 s) ++ "}")
  | (`PLLND.F0.Pair.pP, #[]) => return some "p_{0}"
  | (`PLLND.F0.Pair.qP, #[]) => return some "p_{1}"
  | (`PLLND.F0.Pair.negF, #[a]) => return some (wrap 4 ("\\lnot " ++ (← form st 4 a)))
  -- the order of a subframe model, as in the semantics paper
  | (``PLLND.SubframeModel.le, #[_, a, b]) =>
    return some (wrap 5 ((← generic st 6 a) ++ " \\le " ++ (← generic st 6 b)))
  | (`PLLND.F0.FreeIPL.h1, #[a]) =>
    return some ("\\sigma(" ++ (← form st 9 a) ++ "[p := \\bigcirc\\bot])")
  | (`PLLND.F0.FreeHAn.pvar, #[i]) => return some ("p_{" ++ (← generic st 0 i) ++ "}")
  | (`PLLND.F0.FreeHAn.base, #[m]) => return some ("\\sigma^{" ++ (← generic st 0 m) ++ "}\\bot")
  | (`PLLND.F0.Pair.b2, #[]) => return some "\\sigma^{2}\\bot"
  | (`PLLND.F0.Base3.b3, #[]) => return some "\\sigma^{3}\\bot"
  | (`PLLND.F0.FreeHAn.FreeHAnAbove, #[b, n]) =>
    return some (wrap 5 ("H_{" ++ (← generic st 0 n) ++ "} \\hookrightarrow [" ++ (← form st 0 b) ++ ", \\top]"))
  | (`PLLND.F0.FreeHAn.FreeHAωAbove, #[b]) =>
    return some (wrap 5 ("H_{\\omega} \\hookrightarrow [" ++ (← form st 0 b) ++ ", \\top]"))
  | (`PLLND.F0.FreeIPL.FreeIPLInAboveT3, #[]) => return some (wrap 5 "H_{\\omega} \\hookrightarrow [t_{3}, \\top]")
  | (`PLLND.F0.Base3.gen, #[r]) => return some ("x_{" ++ (← generic st 0 r) ++ "}")
  | (`PLLND.F0.Base3.x3, #[a]) => return some ("x(" ++ (← generic st 0 a) ++ ")")
  | (`PLLND.F0.Base3.xω, #[a]) => return some ("x^{\\omega}(" ++ (← generic st 0 a) ++ ")")
  | (`PLLND.F0.Base3.phiK, #[k]) => return some ("\\varphi_{" ++ (← generic st 0 k) ++ "}")
  | (`PLLND.F0.Base3.sepC, #[r]) => return some ("c_{" ++ (← generic st 0 r) ++ "}")
  | (`PLLND.F0.FreeHAn.Yf, #[]) => return some "Y"
  | (`PLLND.F0.FreeHAn.x0, #[]) => return some "y_{0}"
  | (`PLLND.F0.FreeHAn.x1, #[]) => return some "y_{1}"
  | (`PLLND.F0.Pair.xs, #[a]) => return some ("y(" ++ (← generic st 0 a) ++ ")")
  | (`PLLND.F0.FreeHAn.ZL.relX, #[a]) =>
    return some ((← form st 9 a) ++ "[p := \\bigcirc Y,\\ \\bot := t_{3}]")
  -- the cells `Z_r`, their bottoms, the gadget `M(K)` and its worlds
  | (`PLLND.F0.FreeHAn.ZL.M, #[n]) => return some ("Z_{" ++ (← generic st 0 n) ++ "}")
  | (`PLLND.F0.Base3.Cell.bot, #[r]) => return some ("m_{" ++ (← generic st 0 r) ++ "}")
  | (`PLLND.F0.Base3.Gad.MK, #[K, D, _]) =>
    if D.consumeMData.getAppFn.isConstOf `PLLND.F0.Base3.Gad.Dp then
      return some ("\\mathcal{M}(" ++ (← generic st 0 K) ++ ")")
    return some ("\\mathcal{M}(" ++ (← generic st 0 K) ++ ", " ++ (← generic st 0 D) ++ ")")
  | (`PLLND.F0.Base3.Gad.Pt.w, #[_, k]) => return some ("w_{" ++ (← generic st 0 k) ++ "}")
  | (`PLLND.F0.Base3.Gad.Pt.kn, #[_]) => return some "m'_{0}"
  -- type counts and meet-embeddings
  | (`PLLND.F0.FreeHAn.TypeBound, #[b, K]) =>
    return some (wrap 5 ("k(" ++ (← form st 0 b) ++ ") \\le " ++ (← generic st 6 K)))
  | (`PLLND.F0.FreeHAn.Distinct, #[b, K]) =>
    return some (wrap 5 ("k(" ++ (← form st 0 b) ++ ") \\ge " ++ (← generic st 6 K)))
  | (`PLLND.F0.MeetCount.MeetEmb, #[n, f]) =>
    return some (wrap 5 ((← generic st 6 f) ++ "\\ \\text{is a meet-embedding of}\\ H_{" ++
      (← generic st 0 n) ++ "}"))
  | _ => return none

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
  -- the cases of the semantics paper, when its notation is in force
  if paperkit.notation.get (← getOptions) == "sem" then
    if let some s ← semCase? st p e then return s
  if paperkit.notation.get (← getOptions) == "f0" then
    if let some s ← f0Case? st p e then return s
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
      -- a variable the body does not use is written `_`
      let names ← xs.mapM fun x => do
        if b.containsFVar x.fvarId! then pure (ident (← x.fvarId!.getDecl).userName.toString)
        else pure "\\_"
      return wrap 0 s!"\\lambda {"\\ ".intercalate names.toList}.\\, {← generic st 0 b}"
  | _ =>
  match e.getAppFnArgs with
  -- judgements
  | (``PLLND.LaxND, #[Γ, a]) => return wrap 5 s!"{← ctx st Γ} \\vdash {← form st 1 a}"
  | (``PLLND.SemUI.Deriv, #[Γ, a]) => return wrap 5 s!"{← ctx st Γ} \\vdash {← form st 1 a}"
  | (``Nonempty, #[j]) =>
    if isJudgement j then generic st0 p j
    -- an order isomorphism exists: `A ≃o B` read as a relation
    else if j.consumeMData.isAppOfArity ``OrderIso 4 then generic st0 p j
    else return "\\mathsf{Nonempty}(" ++ (← generic st 0 j) ++ ")"
  | (``PLLND.SemUI.Interd, #[a, b]) => return wrap 5 s!"{← form st 1 a} \\dashv\\vdash {← form st 1 b}"
  | (``PLLND.Consequence, #[Γ, a]) => return wrap 5 s!"{← ctx st Γ} \\models {← form st 1 a}"
  | (`PLLND.F0.Covers, #[u, v]) => return wrap 5 s!"{← form st 1 u} \\lessdot {← form st 1 v}"
  | (``PLLND.ConstraintModel.force, #[m, w, a]) =>
    return wrap 5 s!"{← model st m},\\ {← world st w} \\Vdash {← form st 1 a}"
  | (`PLLND.RNEmbed.Skel.sat, #[s, a, w]) =>
    return wrap 5 s!"{← generic st 9 s},\\ {← generic st 9 w} \\Vdash {← form st 1 a}"
  | (`PLLND.RNEmbed.Skel.le, #[s, x, y]) =>
    let sub ← if s.consumeMData.isConstOf `PLLND.RNEmbed.ladder then pure "" else
      pure ("_{" ++ (← generic st 0 s) ++ "}")
    return wrap 5 ((← generic st 6 x) ++ " \\preceq" ++ sub ++ " " ++ (← generic st 6 y))
  | (`PLLND.F0.IsEdge, #[ms, y]) => return wrap 5 s!"{← generic st 6 y} \\in {← edges st ms}"
  -- variable-freeness: `x ∈ Fm₀`
  | (``Eq, #[_, a, b]) =>
    match a.consumeMData.getAppFnArgs with
    | (``PLLND.LaxInfinite.atomFree, #[x]) =>
      if b.consumeMData.isConstOf ``Bool.true then
        return wrap 5 ((← form st 1 x) ++ " \\in \\mathrm{Fm}_0")
      else return wrap 5 ((← form st 1 x) ++ " \\notin \\mathrm{Fm}_0")
    | _ => return wrap 5 s!"{← generic st 6 a} = {← generic st 6 b}"
  -- the named formulas of the development
  | (`PLLND.RNEmbed.rnSub, #[n]) => return "t_{" ++ (← generic st 0 n) ++ "}"
  | (`PLLND.RNEmbed.rn, #[n]) => return "r_{" ++ (← generic st 0 n) ++ "}"
  | (`PLLND.RNEmbed.gap, #[k]) => return "g_{" ++ (← generic st 0 k) ++ "}"
  | (`PLLND.RNEmbed.chainF, #[k]) => return wrap 4 ("\\bigcirc t_{" ++ (← oddIndex st k) ++ "}")
  | (`PLLND.RNEmbed.Wit, #[b]) => return "W_{" ++ (← generic st 0 b) ++ "}"
  | (`PLLND.RNEmbed.embed, #[a]) =>
    -- `embed (rnP k).1` is the substituted rung `t_{2k+1}` (`rnSub` by definition)
    match rungProj? a with
    | Option.some (k, true) => return "t_{" ++ (← oddIndex st k) ++ "}"
    | Option.some (k, false) => return "t_{" ++ (← evenIndex st k) ++ "}"
    | Option.none => return (← form st 9 a) ++ "[p := \\bigcirc\\bot]"
  | (``Prod.fst, #[_, _, pr]) | (``Prod.snd, #[_, _, pr]) =>
    let proj := if e.isAppOfArity ``Prod.fst 3 then "\\pi_1" else "\\pi_2"
    match (if st.raw then Option.none else rungProj? e) with
    | Option.some (k, true) => return "r_{" ++ (← oddIndex st k) ++ "}"
    | Option.some (k, false) => return "r_{" ++ (← evenIndex st k) ++ "}"
    | Option.none => return proj ++ "(" ++ (← generic st 0 pr) ++ ")"
  -- `wip/f0T6.lean` and `wip/f0SelfSim.lean`: relativisation, `⊥ ↦ a`, the A-translation
  | (`PLLND.F0.T6.rel, #[a]) => return "\\mathrm{rel}(" ++ (← form st 0 a) ++ ")"
  | (`PLLND.F0.T6.xc, #[k]) => return "x_{" ++ (← generic st 0 k) ++ "}"
  | (`PLLND.F0.Sig.sig, #[a]) => return "\\sigma(" ++ (← form st 0 a) ++ ")"
  | (`PLLND.F0.Sig.sigN, #[n, a]) =>
    return "\\sigma^{" ++ (← generic st 0 n) ++ "}(" ++ (← form st 0 a) ++ ")"
  | (`PLLND.F0.Sig.subBot, #[a, b]) =>
    return (← form st 9 b) ++ "[\\bot := " ++ (← form st 1 a) ++ "]"
  | (`PLLND.F0.Sig.aTr, #[a, b]) => return (← form st 9 b) ++ "^{" ++ (← form st 0 a) ++ "}"
  -- subframe models, and the extension by two top worlds
  | (``PLLND.SubframeModel.force, #[m, w, a]) =>
    return wrap 5 s!"{← generic st 9 m},\\ {← generic st 9 w} \\Vdash {← form st 1 a}"
  | (`PLLND.F0.Sig.ext, #[m]) => return "\\widehat{" ++ (← generic st 9 m) ++ "}"
  | (`PLLND.F0.Sig.XW.orig, #[_, x]) => generic st p x
  | (`PLLND.F0.Sig.XW.nT, #[_]) => pure "n_{T}"
  | (`PLLND.F0.Sig.XW.eT, #[_]) => pure "e_{T}"
  | (`PLLND.F0.Sig.isTopX, #[_, w]) => return wrap 5 ((← generic st 6 w) ++ " \\in \\{n_{T}, e_{T}\\}")
  | (``PLLND.SemUI.bigAnd, #[l]) => bigOp st p "\\bigwedge" l
  | (``PLLND.bigOr, #[l]) => bigOp st p "\\bigvee" l
  | (`PLLND.RNEmbed.ladder, #[]) => pure "\\mathcal{L}"
  -- lattice polynomials, the dyadic construction and the rationals
  | (`PLLND.F0.LPoly.den, #[q]) => return "[\\![ " ++ (← generic st 0 q) ++ " ]\\!]"
  | (`PLLND.F0.LPoly.eval, #[σ, q]) => return (← generic st 9 σ) ++ "(" ++ (← generic st 0 q) ++ ")"
  | (`PLLND.F0.LPoly.vars, #[q]) => return "\\mathrm{var}(" ++ (← generic st 0 q) ++ ")"
  | (`PLLND.F0.LPoly.var, #[n]) =>
    -- the variable of index `idx n m` is `x_{n,m}`, as `idx n m` itself
    match n.consumeMData.getAppFnArgs with
    | (`PLLND.F0.idx, #[_, _]) => generic st p n
    | _ => return "x_{" ++ (← generic st 0 n) ++ "}"
  | (`PLLND.F0.F, #[n, m]) => return "F_{" ++ (← generic st 0 n) ++ "}(" ++ (← generic st 0 m) ++ ")"
  | (`PLLND.F0.thr, #[c, n]) => return "\\theta_{" ++ (← generic st 0 c) ++ "," ++ (← generic st 0 n) ++ "}"
  | (`PLLND.F0.thr, #[c, n, i]) =>
    return "\\theta_{" ++ (← generic st 0 c) ++ "," ++ (← generic st 0 n) ++ "}(" ++ (← generic st 0 i) ++ ")"
  | (`PLLND.F0.Dy.formula, #[d]) => return "f(" ++ (← generic st 0 d) ++ ")"
  | (`PLLND.F0.Dy.lt, #[d, d']) => return wrap 5 s!"{← generic st 6 d} < {← generic st 6 d'}"
  | (`PLLND.F0.Dy.mk, #[n, x, _]) =>
    -- m/2^0 is printed m
    if natLit? x == some 0 then generic st p n
    else if natLit? x == some 1 then return wrap 7 ((← generic st 7 n) ++ "/2")
    else return wrap 7 ((← generic st 7 n) ++ "/2^{" ++ (← generic st 0 x) ++ "}")
  | (`PLLND.F0.ratFormula, #[q]) => return "f_{\\mathbb{Q}}(" ++ (← generic st 0 q) ++ ")"
  -- Minkowski's question-mark function (`wip/f0Minkowski.lean`)
  | (`PLLND.F0.ratFormulaCF, #[q]) => return "f'(" ++ (← generic st 0 q) ++ ")"
  | (`PLLND.F0.Mink.mink, #[q]) => return "\\mathord{?}(" ++ (← generic st 0 q) ++ ")"
  | (`PLLND.F0.Mink.qmP, #[a, b]) =>
    return "\\mathord{?}(" ++ (← generic st 7 a) ++ "/" ++ (← generic st 8 b) ++ ")"
  -- `sq`, not `σ`: `σ` is the map of the self-similarity section
  | (`PLLND.F0.Mink.sq, #[q]) => return "\\mathit{sq}(" ++ (← generic st 0 q) ++ ")"
  | (`PLLND.F0.Mink.eqv, #[a, b]) => return wrap 5 s!"{← generic st 6 a} \\equiv {← generic st 6 b}"
  | (`PLLND.F0.Mink.rq, #[n, d, _, _]) => return wrap 7 ((← generic st 7 n) ++ "/" ++ (← generic st 8 d))
  | (`PLLND.F0.levels, #[t]) => return "\\mathrm{lev}(" ++ (← generic st 0 t) ++ ")"
  | (`PLLND.F0.root, #[t]) => return "\\mathrm{root}(" ++ (← generic st 0 t) ++ ")"
  | (``Decidable.decide, #[q, _]) => return "[" ++ (← generic st 0 q) ++ "]"
  -- the bodies of the definitions (v0.4): conditionals, Boolean tests, sets
  | (``ite, #[_, c, _, a, b]) =>
    return wrap 0 ((← generic st 1 a) ++ " \\;\\text{if}\\; " ++ (← generic st 1 c) ++
      ",\\; \\text{else}\\; " ++ (← generic st 0 b))
  | (``Bool.and, #[_, _]) | (``Bool.or, #[_, _]) | (``Bool.not, #[_])
  | (``List.all, #[_, _, _]) | (``List.any, #[_, _, _]) => boolProp st p e
  | (``Nat.succ, #[a]) => return wrap 6 ((← generic st 6 a) ++ " + 1")
  | (``HMod.hMod, #[_, _, _, _, a, b]) => return wrap 7 ((← generic st 7 a) ++ " \\bmod " ++ (← generic st 8 b))
  | (``Nat.log2, #[a]) => return "\\lfloor \\log_2 " ++ (← generic st 9 a) ++ " \\rfloor"
  | (``List.foldr, #[_, _, f, z, l]) =>
    if f.consumeMData.isAppOfArity ``Max.max 2 && natLit? z == some 0 then
      return "\\max(\\{0\\} \\cup " ++ (← generic st 6 l) ++ ")"
    else return "\\mathit{foldr}(" ++ (← generic st 0 f) ++ ", " ++ (← generic st 0 z) ++ ", " ++
      (← generic st 0 l) ++ ")"
  | (``setOf, #[_, f]) =>
    lambdaTelescope f fun xs b => do
      let x ← xs.mapM fun x => do pure (ident (← x.fvarId!.getDecl).userName.toString)
      return "\\{" ++ ",\\ ".intercalate x.toList ++ " \\mid " ++ (← generic st 0 b) ++ "\\}"
  | (``Subtype, #[ty, f]) =>
    lambdaTelescope f fun xs b => do
      let x ← xs.mapM fun x => do pure (ident (← x.fvarId!.getDecl).userName.toString)
      return "\\{" ++ ",\\ ".intercalate x.toList ++ " \\in " ++ (← generic st 6 ty) ++ " \\mid " ++
        (← generic st 0 b) ++ "\\}"
  | (``OrderIso, #[a, b, _, _]) => return wrap 5 ((← generic st 6 a) ++ " \\simeq_{o} " ++ (← generic st 6 b))
  | (``Option, #[a]) => return "\\mathsf{Option}\\," ++ (← generic st 9 a)
  -- the principal filter `[a, ⊤]`, a set used as a type, and the class `⟦t₃⟧`
  -- (`wip/f0NotIso.lean`), written by its representative as elsewhere
  | (``Set.Ici, #[_, _, a]) => return "[" ++ (← generic st 0 a) ++ ", \\top]"
  | (``Set.Elem, #[_, s]) => generic st0 p s
  | (`PLLND.F0.NotIso.T3, #[]) => pure "t_{3}"
  | (`PLLND.F0.NotIso.cls, #[φ, _]) => form st p φ
  | (``Set, #[a]) => return "\\mathsf{Set}\\," ++ (← generic st 9 a)
  -- lattice polynomials (`wip/f0Dyadic.lean`): `⊓`, `⊔`, and their constants
  | (`PLLND.F0.LPoly.bot, #[]) => pure "\\bot"
  | (`PLLND.F0.LPoly.top, #[]) => pure "\\top"
  -- (a nested meet or join is bracketed on either side, as for formulas)
  | (`PLLND.F0.LPoly.and, #[a, b]) => return wrap 3 ((← generic st 4 a) ++ " \\sqcap " ++ (← generic st 4 b))
  | (`PLLND.F0.LPoly.or, #[a, b]) => return wrap 2 ((← generic st 4 a) ++ " \\sqcup " ++ (← generic st 4 b))
  | (``Prod, #[a, b]) => return wrap 7 ((← generic st 8 a) ++ " \\times " ++ (← generic st 8 b))
  -- a bundled map applied to an argument (Mathlib's `⇑f x`): `f(x)`
  | (``DFunLike.coe, #[_, _, _, _, f, x]) => return s!"{← funHead st f}({← generic st 0 x})"
  -- the order of F0 as an algebra, and its MacNeille completion
  | (``PLLND.RNClass, #[]) => pure "F_0"
  | (`F0Nuclear.circNucleus, #[]) | (`MacNeille.dmNucleus, #[_, _, _])
  | (`MacNeille.JoinDenseHeytingEmbedding.extNucleus, #[_, _, _, _, _, _])
  | (`MacNeille.JoinDenseHeytingEmbedding.leastExt, #[_, _, _, _, _, _]) => funHead st e
  | (`DedekindCut, #[a, _]) => return "\\mathrm{DM}(" ++ (← generic st 0 a) ++ ")"
  | (`DedekindCut.principal, #[_, _, a]) => return "{\\downarrow}" ++ (← generic st 9 a)
  | (`DedekindCut.left, #[_, _, x]) => return "\\mathrm{L}(" ++ (← generic st 0 x) ++ ")"
  | (`DedekindCut.right, #[_, _, x]) => return "\\mathrm{U}(" ++ (← generic st 0 x) ++ ")"
  | (`F0Nuclear.himp, #[a, b]) => return wrap 6 s!"{← generic st 7 a} \\Rightarrow {← generic st 7 b}"
  | (`F0Nuclear.box, #[a]) => return "\\bigcirc " ++ (← generic st 9 a)
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
  | (`PLLND.F0.half, #[n]) =>
    if natLit? n == some 1 then return wrap 7 "1/2"
    else return wrap 7 ("1/2^{" ++ (← generic st 0 n) ++ "}")
  | (`PLLND.F0.idx, #[n, m]) => return "x_{" ++ (← generic st 0 n) ++ "," ++ (← generic st 0 m) ++ "}"
  | (`PLLND.F0.copyF, #[p, q, k, d]) =>
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
      | (``OrderIso, #[a, b, _, _]) =>
        return wrap 5 ((← generic st 6 a) ++ " \\not\\simeq_{o} " ++ (← generic st 6 b))
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
      -- in the semantics paper `∃ _ : FinDec M, P` is `FinDec(M) and P`
      if paperkit.notation.get (← getOptions) == "sem" && xs.size == 1 then
        let ty ← inferType xs[0]!
        if isConditionClass ty then
          return wrap 3 ((← generic st 4 ty) ++ metaAnd ++ (← generic st 3 b))
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
  | (``HDiv.hDiv, #[ty, _, _, _, a, b]) =>
    -- division of naturals rounds down
    if ty.consumeMData.isConstOf ``Nat then
      return "\\lfloor " ++ (← generic st 7 a) ++ " / " ++ (← generic st 8 b) ++ " \\rfloor"
    return wrap 7 s!"{← generic st 7 a} / {← generic st 8 b}"
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
      let env ← getEnv
      -- a named constant: an atom's name (`pv := "p"`) or a dyadic (`mid := 1/2`)
      if args.isEmpty then
        if let some (.defnInfo dv) := env.find? f then
          if let some s := strLit? dv.value then return ident s
          if dv.value.consumeMData.isAppOfArity `PLLND.F0.Dy.mk 3 then return ← generic st0 p dv.value
      -- a structure instance: its data fields
      if let some (.ctorInfo cv) := env.find? f then
        if isStructure env cv.induct then return ← structInst st e
      -- the projection to a parent structure is not written
      if let some info := env.getProjectionFnInfo? f then
        if let some (.ctorInfo cv) := env.find? info.ctorName then
          if let some fld := (getStructureFields env cv.induct)[info.i]? then
            if (isSubobjectField? env cv.induct fld).isSome && args.size == info.numParams + 1 then
              return ← generic st0 p args[info.numParams]!
      let args ← explicitArgs (mkConst f e.getAppFn.constLevels!) args
      -- proofs are not printed
      let args ← args.filterM fun a => do return !(← isProof a)
      let isType := match env.find? f with
        | Option.some (.inductInfo _) => true
        | _ => false
      let head := (if isType then "\\mathsf{" else "\\mathit{") ++ esc (lastName f) ++ "}"
      if args.isEmpty then pure head
      else return head ++ "(" ++ ", ".intercalate (← args.toList.mapM (argument st)) ++ ")"

/-- An argument: a function constant, partially applied, is written as a
`λ` when that shows its notation (`box` as `λx. ◯x`), else by name. -/
partial def argument (st : St) (a : Expr) : MetaM String := do
  let a := a.consumeMData
  let plain ← generic st 0 a
  let .const f _ := a.getAppFn | return plain
  let ty ← whnf (← inferType a)
  unless ty.isForall do return plain
  if (← isProp ty) || (← isProof a) then return plain
  let expanded ← generic st 0 (← etaNamed a)
  if expanded.contains ("\\mathit{" ++ esc (lastName f) ++ "}") then return plain
  return expanded

/-- A structure instance `⟨f₁ = v₁, …⟩`: its data fields, the fields of a
parent structure spliced in; proofs and instances are left out. -/
partial def structInst (st : St) (e : Expr) : MetaM String := do
  let fields ← structFields st e
  return "\\langle " ++ ",\\ ".intercalate fields.toList ++ " \\rangle"

/-- The printed data fields of a structure instance. -/
partial def structFields (st : St) (e : Expr) : MetaM (Array String) := do
  let env ← getEnv
  let .const c _ := e.getAppFn | return #[← generic st 0 e]
  let some (.ctorInfo cv) := env.find? c | return #[← generic st 0 e]
  let S := cv.induct
  let names := getStructureFields env S
  let vals := e.getAppArgs.extract cv.numParams e.getAppNumArgs
  let mut out := #[]
  for i in [0:names.size] do
    let some v := vals[i]? | continue
    if ← isProof v then continue
    -- a parent structure given by its constructor: its fields, spliced in
    if (isSubobjectField? env S names[i]!).isSome then
      let v' ← whnfR v
      if v'.getAppFn.isConst && (env.find? v'.getAppFn.constName!).any (·.isCtor) then
        out := out ++ (← structFields st v')
        continue
    let vty ← inferType v
    if (← isClass? vty).isSome then continue
    out := out.push ("\\mathit{" ++ esc (lastName names[i]!) ++ "} = " ++ (← argument st v))
  return out

/-- A Boolean test read as a proposition: `&&`, `||`, `!` are "and", "or",
`¬`; `List.all`, `List.any` are bounded quantifiers; `atomFree x` is
`x ∈ Fm₀`; any other test `b` is read as `b = true`. -/
partial def boolProp (st : St) (p : Nat) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  let wrap (q : Nat) (s : String) := if q < p then paren s else s
  match e.getAppFnArgs with
  | (``Bool.true, _) => pure "\\mathsf{True}"
  | (``Bool.false, _) => pure "\\mathsf{False}"
  -- `&&` and `||` are associative: a chain is written without brackets
  | (``Bool.and, #[a, b]) => return wrap 3 ((← boolProp st 3 a) ++ metaAnd ++ (← boolProp st 3 b))
  | (``Bool.or, #[a, b]) => return wrap 2 ((← boolProp st 2 a) ++ metaOr ++ (← boolProp st 2 b))
  | (``Bool.not, #[a]) =>
    match a.consumeMData.getAppFnArgs with
    | (``PLLND.LaxInfinite.atomFree, #[x]) => return wrap 5 ((← form st 4 x) ++ " \\notin \\mathrm{Fm}_0")
    | _ => return wrap 4 ("\\lnot " ++ (← boolProp st 5 a))
  | (``Decidable.decide, #[q, _]) => generic st p q
  | (``ite, #[_, c, _, a, b]) =>
    return wrap 0 ((← boolProp st 1 a) ++ " \\;\\text{if}\\; " ++ (← generic st 1 c) ++
      ",\\; \\text{else}\\; " ++ (← boolProp st 0 b))
  | (``PLLND.LaxInfinite.atomFree, #[x]) => return wrap 5 ((← form st 4 x) ++ " \\in \\mathrm{Fm}_0")
  | (``List.all, #[_, l, f]) => boundedQ st p "\\forall" l f
  | (``List.any, #[_, l, f]) => boundedQ st p "\\exists" l f
  | _ => generic st p e

/-- `List.all l f`, `List.any l f`: `∀ x ∈ l. f x`, `∃ x ∈ l. f x`, and
`∀ x < n` over `List.range n`. -/
partial def boundedQ (st : St) (p : Nat) (q : String) (l f : Expr) : MetaM String := do
  let wrap (q : Nat) (s : String) := if q < p then paren s else s
  let f := f.consumeMData
  let f ← if f.isLambda then pure f else etaNamed f
  lambdaTelescope f fun xs b => do
    let x := ident (← xs[0]!.fvarId!.getDecl).userName.toString
    let dom ← match l.consumeMData.getAppFnArgs with
      | (``List.range, #[n]) => pure (x ++ " < " ++ (← generic st 6 n))
      | _ => pure (x ++ " \\in " ++ (← generic st 6 l))
    return wrap 0 (q ++ "\\, " ++ dom ++ ".\\; " ++ (← boolProp st 0 b))

/-- A derivation type `Γ ⊢ A` (`LaxND Γ A`), as a binder: a premise. -/
partial def isJudgement (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``PLLND.LaxND

/-- `∀`-binders: variables are quantified, propositions and derivations become
premises, instance arguments vanish, `x` followed by `x ∈ C` is `x ∈ C`. -/
partial def quant (st0 : St) (p : Nat) (e : Expr) : MetaM String :=
  forallTelescope e fun xs body => do
    let st := {st0 with nested := true, schematic := false}
    let mut vars : Array String := #[]
    let mut prems : Array String := #[]
    let mut skip : Option FVarId := none
    -- the last binder, when it is a proposition (for `P → False` as `¬P`)
    let mut lastProp : Option Expr := none
    for i in [0:xs.size] do
      let x := xs[i]!
      if skip == some x.fvarId! then continue
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then
        -- a condition on a model (`Finite`, `FinDec`) is a premise in the semantics paper
        if paperkit.notation.get (← getOptions) == "sem" && isConditionClass d.type then
          prems := prems.push (← generic st 3 d.type)
        continue
      let ty := d.type
      -- an order isomorphism `f : A ≃o B` used nowhere after is the premise `A ≃o B`
      let mut unused := !body.containsFVar x.fvarId!
      for j in [i+1:xs.size] do
        if (← xs[j]!.fvarId!.getDecl).type.containsFVar x.fvarId! then unused := false
      if (← isProp ty) || isJudgement ty || (ty.consumeMData.isAppOfArity ``OrderIso 4 && unused) then
        prems := prems.push (← generic st 3 ty)
        lastProp := if i + 1 == xs.size && (← isProp ty) then some ty else none
      else
        let nm := ident d.userName.toString
        -- a bounded variable: the next binder is the hypothesis `x ∈ C`
        let mut done := false
        -- (not in a rule schema, which writes no binders: `x ∈ C` stays a premise)
        if h : i + 1 < xs.size ∧ !st0.schematic then
          let hy ← (xs[i + 1]'h.1).fvarId!.getDecl
          if let (``Membership.mem, #[_, _, _, coll, y]) := hy.type.consumeMData.getAppFnArgs then
            if y.consumeMData == x then
              vars := vars.push (nm ++ " \\in " ++ (← generic st 6 coll))
              skip := some (xs[i + 1]'h.1).fvarId!
              done := true
        if !done then vars := vars.push nm
    let binder := if vars.isEmpty || st0.schematic then "" else
      "\\forall\\, " ++ ",\\ ".intercalate vars.toList ++ ".\\; "
    let isIff := body.consumeMData.isAppOfArity ``Iff 2
    let mut concl ← generic st (if prems.isEmpty || !isIff then 0 else 2) body
    -- in the semantics paper a last premise `P` before `False` is the conclusion `¬P`
    if paperkit.notation.get (← getOptions) == "sem" && body.consumeMData.isConstOf ``False then
      if let some ty := lastProp then
        prems := prems.pop
        concl ← generic st 0 (mkNot ty)
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

/-! ### Definitions and types that have no single defining equation (v0.4) -/

/-- The names of the `∀`-binders of `ty` that are written in the source. -/
partial def binderNames (ty : Expr) : List String :=
  match ty with
  | .forallE nm _ b _ => (if nm.hasMacroScopes then [] else [nm.toString]) ++ binderNames b
  | _ => []

/-- `∀`-binders as local variables, renamed for print (`varName`): a `String`
variable, the name of an atom, is `q` (Lean's equation lemmas name it after
the field, `constantName`), and a variable named by a macro is given a name
by its type. -/
partial def atomTelescope {α : Type} (ty : Expr) (xs : Array Expr)
    (k : Array Expr → Expr → MetaM α) (used : List String := binderNames ty) : MetaM α := do
  match ty with
  | .forallE nm d b bi =>
    let rename := nm.hasMacroScopes || (d.isConstOf ``String && nm.toString.length > 2)
    let nm := if rename then varName d used else nm
    withLocalDecl nm bi d fun x =>
      atomTelescope (b.instantiate1 x) (xs.push x) k (nm.toString :: used)
  | _ => k xs ty

/-- Each item but the last followed by `;`. -/
def punctuate (items : List String) : List String :=
  match items.reverse with
  | [] => []
  | last :: rest => (rest.reverse.map (· ++ ";")) ++ [last]

/-- One case `lhs = rhs` of a definition: `lhs := rhs`, or `lhs :⟺ rhs` for a
proposition, and for a Boolean test read as a proposition (`boolProp`). -/
def eqnLine (st rhsSt : St) (lhs rhs : Expr) : MetaM String := do
  let ty ← whnf (← inferType lhs)
  if ty.isConstOf ``Bool then
    return ← match rhs.consumeMData.getAppFnArgs with
    | (``Bool.true, _) => boolProp st 0 lhs
    | (``Bool.false, _) => boolProp st 0 (mkApp (mkConst ``Bool.not) lhs)
    | _ => return (← boolProp st 0 lhs) ++ " \\mathrel{:\\Longleftrightarrow} " ++ (← boolProp rhsSt 0 rhs)
  if ty.isProp then
    return (← generic st 0 lhs) ++ " \\mathrel{:\\Longleftrightarrow} " ++ (← generic rhsSt 0 rhs)
  return (← generic st 0 lhs) ++ " \\mathrel{:=} " ++ (← generic rhsSt 0 rhs)

/-- Whether a definition is defined by recursion (structural or well-founded). -/
def isRecursiveDef (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo dv) := env.find? n | return false
  return (dv.value.find? fun s => match s with
    | .const c _ => isAuxRecursor env c || Lean.Meta.isMatcherCore env c || isRecCore env c ||
        c == ``WellFounded.fix
    | _ => false).isSome

/-- A definition, as one or more items to set on one line each:
* by recursion: its equation lemmas, one per case;
* a value chosen by `Classical.choice`: its type;
* structure-valued: `lhs : T := ⟨fields⟩`;
* otherwise `lhs := rhs`, a function-valued definition applied to fresh
  arguments first (`σ := subBot t₃` is `σ(φ) := φ[⊥ := t₃]`). -/
def defChunks (n : Name) : MetaM (List String) := do
  let env ← getEnv
  let some (.defnInfo dv) := env.find? n | return []
  let st : St := {flat := true}
  -- in the equations of `rn` the rung notation would be circular
  let rhsSt : St := {flat := true, raw := n == `PLLND.RNEmbed.rn}
  if ← isRecursiveDef n then
    let some eqs ← getEqnsFor? n | return []
    let lines ← eqs.toList.mapM fun eqn => do
      let t := (← getConstInfo eqn).type
      atomTelescope t #[] fun _ body => do
        let some (_, l, r) := body.consumeMData.eq? | generic st 0 body
        eqnLine st rhsSt l r
    return punctuate lines
  let value ← zetaReduce dv.value
  lambdaTelescope value fun xs body => do
    let lhs0 := mkAppN (mkConst n (dv.levelParams.map mkLevelParam)) xs
    atomTelescope (← inferType lhs0) #[] fun ys _ => do
      let lhs := mkAppN lhs0 ys
      let rhs := (mkAppN body ys).headBeta
      let ty ← whnf (← inferType lhs)
      let ls ← generic st 0 lhs
      -- in the semantics paper a decision procedure is printed by its type
      if paperkit.notation.get (← getOptions) == "sem" then
        let h := (← instantiateMVars (← inferType lhs)).getAppFn
        if h.isConstOf ``Decidable || h.isConstOf ``PSum || h.isConstOf ``Sum then
          return [ls ++ " :\\; " ++ (← generic st 0 (← inferType lhs))]
      if rhs.consumeMData.isAppOfArity ``Classical.choice 2 then
        return [ls ++ " : " ++ (← generic st 0 (← inferType lhs)) ++
          ",\\ \\text{chosen by}\\ \\mathsf{Classical.choice}"]
      if ty.isProp then
        let rs ← generic rhsSt 0 rhs
        -- `Deriv Γ φ := Nonempty (Γ ⊢ φ)`: both sides print `Γ ⊢ φ`
        let rs ← if rs != ls then pure rs else
          match rhs.consumeMData.getAppFnArgs with
          | (``Nonempty, #[j]) => pure ("\\mathsf{Nonempty}(" ++ (← generic rhsSt 0 j) ++ ")")
          | _ => pure rs
        return [ls ++ " \\mathrel{:\\Longleftrightarrow} " ++ rs]
      if ty.isConstOf ``Bool then
        return [(← boolProp st 0 lhs) ++ " \\mathrel{:\\Longleftrightarrow} " ++ (← boolProp rhsSt 0 rhs)]
      let tyHead := (← instantiateMVars (← inferType lhs)).getAppFn
      if tyHead.isConst && isStructure env tyHead.constName! then
        let T ← generic st 0 (← inferType lhs)
        return [ls ++ " : " ++ T ++ " \\mathrel{:=} " ++ (← argument rhsSt rhs)]
      return [ls ++ " \\mathrel{:=} " ++ (← argument rhsSt rhs)]

/-- An inductive type: a structure by its fields (a propositional structure as
the conjunction of its fields), a derivation type (an indexed family) by its
rules, any other type by the grammar of its constructors. -/
def typeChunks (n : Name) : MetaM (List String) := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? n | return []
  let st : St := {flat := true}
  let lvls := iv.levelParams.map mkLevelParam
  if isStructure env n then
    let some ctor := iv.ctors.head? | return []
    return ← forallTelescope (← getConstInfo ctor).type fun xs _ => do
      let params := xs.extract 0 iv.numParams
      let fields := xs.extract iv.numParams xs.size
      let self := mkAppN (mkConst n lvls) params
      let lhs ← generic st 0 self
      let mut data : Array String := #[]
      let mut propTys : Array Expr := #[]
      for f in fields do
        let d ← f.fvarId!.getDecl
        if ← isProp d.type then propTys := propTys.push d.type
        else data := data.push (ident d.userName.toString ++ " : " ++ (← generic st 0 d.type))
      -- bracketed when joined by "and", not when listed
      let isP ← isProp self
      let props ← propTys.mapM (generic st (if isP then 3 else 0))
      if isP then
        let ps := props.toList
        return match ps.reverse with
          | [] => [lhs]
          | last :: rest =>
            match rest.reverse with
            | [] => [lhs ++ " \\mathrel{:\\Longleftrightarrow} " ++ last]
            | first :: mid =>
              [lhs ++ " \\mathrel{:\\Longleftrightarrow} " ++ first ++ metaAnd.trimAsciiEnd.copy] ++
                (mid.map (· ++ metaAnd.trimAsciiEnd.copy)) ++ [last]
      -- `S := {(d₁ : T₁, …) | P₁; …}`: the data fields, then the conditions
      let tuple := lhs ++ " \\mathrel{:=} \\{(" ++ ",\\ ".intercalate data.toList ++ ")"
      if props.isEmpty then return [tuple ++ "\\}"]
      let conds := punctuate props.toList
      return [tuple ++ " \\mid"] ++ conds.dropLast ++ [conds.getLast! ++ "\\}"]
  if iv.numIndices > 0 then
    -- the rules: premises above, conclusion below, written `P₁ ⟹ … ⟹ C`
    let rules ← iv.ctors.mapM fun c => do
      quant {flat := true, schematic := true} 0 (← getConstInfo c).type
    return punctuate rules
  let alts ← iv.ctors.mapM fun c => do
    forallTelescope (← getConstInfo c).type fun xs _ => do
      generic st 0 (mkAppN (mkConst c lvls) xs)
  let lhs ← generic st 0 (mkConst n lvls)
  return match alts with
    | [] => [lhs]
    | a :: rest => (lhs ++ " ::= " ++ a) :: rest.map ("\\mid " ++ ·)

/-- The items of `n` for the tables: a statement, a defining equation, or the
cases of a definition or type (`defChunks`, `typeChunks`); never empty for a
definition or a type. -/
def stmtItems (n : Name) : MetaM (List String) := do
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  let judgement ← forallTelescope ci.type fun _ b => pure (isJudgement b)
  if (← isProp ci.type) || judgement then return [← generic {flat := true} 0 ci.type]
  match ci with
  | .defnInfo _ =>
    match ← defEquation? n (flat := true) with
    | Option.some s => return [s]
    | Option.none => defChunks n
  | .inductInfo _ => typeChunks n
  | _ => return []

/-- The statement of `n` as TeX, or `none` when there is nothing to print. -/
def stmtOf (n : Name) : MetaM (Option String) := do
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  let judgement ← forallTelescope ci.type fun _ b => pure (isJudgement b)
  unless (← isProp ci.type) || judgement do
    if let some s ← defEquation? n then return some s
    let items ← stmtItems n
    return if items.isEmpty then none else some (rows items)
  let s ← generic {} 0 ci.type
  if visLen s > rowMeasure && !s.startsWith "\\begin{aligned}" then
    return some (rows (breakRow s))
  return some s

/-- The statement of `n` on one line (the tables of supporting declarations),
as items set one after another, a line break allowed between them. -/
def stmtFlat (n : Name) : MetaM (List String) := stmtItems n

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

end PaperKit.Math
