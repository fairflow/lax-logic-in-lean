/-
`{leanDecl Full.Name}`: a declaration in compact form, for reading and for
print (Matthew, 2026-10-15).  It replaces Verso's `{docstring}`, which prints
every signature twice (once wrapped at 40 columns), with every implicit and
instance binder, and every inherited field of a structure.

What is printed:

* the signature ONCE, at full width, with only the explicit binders, as a
  paper states a result: `theorem sound (h : Γ ⊢ A) : Γ ⊨ A`.  The implicit
  ones (`{Γ : List Form} {A : Form}`) are the paper's free letters; the
  source link leads to the full statement;
* for an inductive, each constructor the same way; constructors of at most
  40 characters stand two to a line in aligned columns, longer ones keep
  their own lines;
* for a structure, its own fields only (not those it inherits), in binder
  form `(f : T)` after `where`;
* everything filled to the line (`width`), breaking only where needed and
  preferably at a top-level connective (v0.7);
* the docstring, rendered as Verso renders it, only with `+doc`;
* the source link (`{srcLink}`), so it need not be written separately.

Names are printed under the `open` declarations of the document file that
uses the block, as the rest of the paper is.
-/
import Lean
import Lean.DocString.Syntax
import VersoManual
import CLPPaper.Src

open Lean Meta Elab
open Lean.Doc.Syntax
open Verso Doc Elab Genre Manual ArgParse
open Verso.Output Html

namespace CLPPaper

/-- A binder as (name, printed type). -/
def binderText (x : Expr) : MetaM (String × Format) := do
  let d ← x.fvarId!.getDecl
  let n := if d.userName.hasMacroScopes || d.userName.isAnonymous then "_"
    else toString d.userName.eraseMacroScopes
  pure (n, ← ppExpr d.type)

/-- Adjacent binders of the same type share one group: `(A B : Form)`. -/
def groupBinders (bs : Array (String × Format)) : Array Format := Id.run do
  let mut out : Array (Array String × Format) := #[]
  for (n, ty) in bs do
    match out.back? with
    | Option.some (ns, ty') =>
      if ty'.pretty == ty.pretty then out := out.pop.push (ns.push n, ty)
      else out := out.push (#[n], ty)
    | Option.none => out := out.push (#[n], ty)
  out.map fun (ns, ty) => .paren (.text (String.intercalate " " ns.toList ++ " :") ++ .line ++ ty)

/-- The number of leading binders of `ty` to open: those with a name the
user wrote.  A plain arrow `A → B` has a hygienic name and stays in the body. -/
def namedPrefix : Expr → Nat
  | .forallE n _ b _ => if n.hasMacroScopes || n.isAnonymous then 0 else namedPrefix b + 1
  | .mdata _ e => namedPrefix e
  | _ => 0

/-- `binders : body` of a type, keeping only the explicit named binders.
With `skip`, the first `skip` binders are opened but not printed (a
structure projection's parameters and `self`). -/
def compactType (ty : Expr) (skip : Nat := 0) : MetaM (Array Format × Format) := do
  let n := if skip > 0 then skip else namedPrefix ty
  forallBoundedTelescope ty (some n) fun xs body => do
    let mut bs := #[]
    for x in xs, i in [0:xs.size] do
      if i < skip then continue
      if (← x.fvarId!.getDecl).binderInfo.isExplicit then
        bs := bs.push (← binderText x)
    pure (groupBinders bs, ← ppExpr body)

/-- The measure: signatures are filled to `width` columns (print has no
horizontal scroll), continuation lines indented by four. -/
def width : Nat := 88

/-! ### Filling

Lean's formatter breaks a group all or nothing and nests every arrow one step
deeper, so a statement that does not fit breaks at every `→`, in a staircase.
Here a statement is first cut at its top-level connectives (`chunks`), and
the pieces are filled: a line breaks only before a piece that does not fit on
it.  A piece keeps Lean's own notation and, if it is longer than a line,
Lean's own layout (Matthew, 2026-10-16: compact displays). -/

/-- The flat width of a piece. -/
def flatLen (f : Format) : Nat := (f.pretty 100000).length

/-- The leading binders of `e` that the body depends on. -/
def depPrefix : Expr → Nat
  | .forallE _ _ b _ => if b.hasLooseBVar 0 then depPrefix b + 1 else 0
  | .mdata _ e => depPrefix e
  | _ => 0

/-- `∀` binders as Lean writes them, adjacent ones of one type and kind grouped. -/
def forallBinders (xs : Array Expr) : MetaM Format := do
  let mut out : Array (Array String × Format × BinderInfo) := #[]
  for x in xs do
    let d ← x.fvarId!.getDecl
    let (n, ty) ← binderText x
    match out.back? with
    | Option.some (ns, ty', bi) =>
      if ty'.pretty == ty.pretty && bi == d.binderInfo then out := out.pop.push (ns.push n, ty, bi)
      else out := out.push (#[n], ty, d.binderInfo)
    | Option.none => out := out.push (#[n], ty, d.binderInfo)
  let one := fun ((ns, ty, bi) : Array String × Format × BinderInfo) =>
    let (l, r) := match bi with
      | .implicit => ("{", "}") | .strictImplicit => ("⦃", "⦄") | .instImplicit => ("[", "]")
      | _ => ("(", ")")
    let a : Format := .text (l ++ String.intercalate " " ns.toList ++ " : ")
    let z : Format := .text r
    Format.group (a ++ ty ++ z)
  pure (Format.joinSep (out.toList.map one) " ")

/-- Lean's printing of `e` on one line. -/
def flatPP (e : Expr) : MetaM String := do pure ((← ppExpr e).pretty 100000)

/-- Brackets around a sequence of pieces. -/
def wrap (cs : Array Format) : Array Format :=
  if cs.isEmpty then cs else
  let lp : Format := .text "("
  let rp : Format := .text ")"
  let cs := cs.modify 0 (lp ++ ·)
  cs.modify (cs.size - 1) (· ++ rp)

/-- A proposition cut into the pieces between which a line may break: the
operands of `→`, `↔`, `∨` and `∧` (each followed by its connective), and the
binders of a `∀`, `∃` or `¬∃` too long for one line.  Each piece keeps Lean's
own layout and notation; a piece that fits on a line is never broken.  An
operand is bracketed exactly when Lean brackets it in the whole statement
(`(Γ ⊢ A) ∧ (Δ ⊢ B)`, `(A ∧ ∀ x, P) → Q`), so the pieces read as Lean's
printing of the statement does. -/
partial def chunks (e : Expr) : MetaM (Array Format) := do
  let e := e.consumeMData
  let bin (a b : Expr) (op : String) : MetaM (Array Format) := do
    let w ← flatPP e
    let wl := w.startsWith ("(" ++ (← flatPP a) ++ ")")
    let wr := w.endsWith ("(" ++ (← flatPP b) ++ ")")
    let l ← chunks a
    let l := if wl then wrap l else l
    let r ← chunks b
    let r := if wr then wrap r else r
    let opF : Format := .text (" " ++ op)
    return l.modify (l.size - 1) (· ++ opF) ++ r
  match e with
  | .forallE _ d b _ =>
    if !b.hasLooseBVar 0 && (← isProp d) && (← isProp e) then
      return ← bin d (b.lowerLooseBVars 1 1) "→"
    let whole ← ppExpr e
    let n := depPrefix e
    if n == 0 || flatLen whole ≤ width - 12 || !(← isProp e) then return #[whole]
    forallBoundedTelescope e (some n) fun xs body => do
      let fa : Format := .text "∀ "
      let cm : Format := .text ","
      return #[fa ++ (← forallBinders xs) ++ cm] ++ (← chunks body)
  | _ =>
    if e.isAppOfArity ``Iff 2 then return ← bin e.appFn!.appArg! e.appArg! "↔"
    if e.isAppOfArity ``Or 2 then return ← bin e.appFn!.appArg! e.appArg! "∨"
    if e.isAppOfArity ``And 2 then return ← bin e.appFn!.appArg! e.appArg! "∧"
    if e.isAppOfArity ``Exists 2 then
      let whole ← ppExpr e
      if flatLen whole ≤ width - 12 then return #[whole]
      return ← openEx e #[]
    -- `¬∃ x, P` too long for a line: `¬∃ x,` then the body
    if e.isAppOfArity ``Not 1 then
      let whole ← ppExpr e
      let a := e.appArg!
      if flatLen whole ≤ width - 12 || !a.consumeMData.isAppOfArity ``Exists 2 then
        return #[whole]
      if whole.pretty 100000 != "¬" ++ (← flatPP a) then return #[whole]
      let c ← chunks a
      let neg : Format := .text "¬"
      return c.modify 0 (neg ++ ·)
    return #[← ppExpr e]
where

  /-- `∃ x y,` then the body. -/
  openEx (e : Expr) (names : Array String) : MetaM (Array Format) := do
    let e := e.consumeMData
    let head : Format := .text ("∃ " ++ String.intercalate " " names.toList ++ ",")
    if e.isAppOfArity ``Exists 2 then
      match e.appArg!.consumeMData with
      | .lam n ty b bi =>
        withLocalDecl n bi ty fun x => do
          let nm := toString (← x.fvarId!.getDecl).userName.eraseMacroScopes
          openEx (b.instantiate1 x) (names.push nm)
      | _ => return (if names.isEmpty then #[] else #[head]) ++ #[← ppExpr e]
    else
      return #[head] ++ (← chunks e)

/-- `binders : body` of a type, keeping only the explicit named binders, the
body cut into pieces. -/
def compactPieces (ty : Expr) : MetaM (Array Format × Array Format) := do
  forallBoundedTelescope ty (some (namedPrefix ty)) fun xs body => do
    let mut bs := #[]
    for x in xs do
      if (← x.fvarId!.getDecl).binderInfo.isExplicit then
        bs := bs.push (← binderText x)
    pure (groupBinders bs, ← chunks body)

def render (f : Format) (indent : Nat) : String :=
  let pad := "".pushn ' ' indent
  String.intercalate "\n" ((f.pretty (width - indent)).splitOn "\n" |>.map (pad ++ ·))

/-- `head binders : body suffix tail…`, filled at `width` columns with a
hanging indent of four: a line breaks only before a binder, a piece of the
body or a field that does not fit on it. -/
def sig (head : String) (bs : Array Format) (body : Array Format) (indent : Nat := 0)
    (suffix := "") (tail : Array Format := #[]) : String :=
  let bodyF : Format :=
    if body.isEmpty then .text suffix
    else .text " :" ++ Format.join (body.toList.map (.line ++ ·)) ++ .text suffix
  render (.fill (.nest 4 (.text head ++ Format.join (bs.toList.map (.line ++ ·)) ++ bodyF ++
    Format.join (tail.toList.map (.line ++ ·))))) indent

/-- Two consecutive constructors of at most 40 characters share a line, the
second starting at a fixed column, so that short constructors stand in two
aligned columns; longer ones keep their own lines. -/
def pack (cs : Array String) (indent : Nat := 2) : Array String := Id.run do
  let pad := "".pushn ' ' indent
  let short (c : String) := !c.contains '\n' && c.trimAsciiStart.copy.length ≤ 40
  let mut out : Array String := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if i + 1 < cs.size && short c && short cs[i+1]! then
      let a := c.trimAsciiStart.copy
      let b := cs[i+1]!.trimAsciiStart.copy
      out := out.push (pad ++ a.pushn ' ' (42 - a.length) ++ b)
      i := i + 2
    else
      out := out.push c
      i := i + 1
  return out

/-- The compact text of a declaration. -/
def compactDecl (n : Name) : MetaM String := do
  let env ← getEnv
  let ci ← getConstInfo n
  let short := toString (← unresolveNameGlobal n)
  match ci with
  | .inductInfo ii =>
    if isStructure env n then
      let (bs, body) ← compactPieces ci.type
      let parents := (getStructureParentInfo env n).map (·.structName)
      let ext ← if parents.isEmpty then pure "" else do
        let ps ← parents.mapM fun p => return toString (← unresolveNameGlobal p)
        pure (" extends " ++ String.intercalate ", " ps.toList)
      -- the own fields in binder form `(f : T)`, filled after `where`
      let mut fs : Array (Array String × String × Format) := #[]
      for f in getStructureFields env n do
        if (isSubobjectField? env n f).isSome then continue
        let Option.some proj := getProjFnForField? env n f | continue
        let (_, fty) ← compactType (← getConstInfo proj).type (skip := ii.numParams + 1)
        -- a field's type mentions the other fields as `self.f`; printed `f`
        let flatTy := (fty.pretty 100000).replace "self." ""
        match fs.back? with
        | Option.some (ns, t, g) =>
          if t == flatTy then fs := fs.pop.push (ns.push (toString f), t, g)
          else fs := fs.push (#[toString f], flatTy, fty)
        | Option.none => fs := fs.push (#[toString f], flatTy, fty)
      -- a field that fits on a line is one piece; a longer one keeps Lean's layout
      let fields : Array Format := fs.map fun (ns, t, g) =>
        let names := String.intercalate " " ns.toList
        let one := "(" ++ names ++ " : " ++ t ++ ")"
        let oneF : Format := .text one
        let nm : Format := .text (names ++ " :")
        if one.length + 4 ≤ width then oneF
        else Format.paren (nm ++ Format.line ++ g)
      -- `: Type` is the default and is left out
      let body := if body.map (·.pretty) == #["Type"] then #[] else body
      let s := sig s!"structure {short}" bs body (suffix := ext ++ " where") (tail := fields)
      pure (s.replace "self." "")
    else
      let (bs, body) ← compactPieces ci.type
      let mut cs := #[]
      for c in ii.ctors do
        let (cbs, cbody) ← compactPieces (← getConstInfo c).type
        cs := cs.push (sig s!"| {c.componentsRev.head!}" cbs cbody (indent := 2))
      let head := sig s!"inductive {short}" bs body (suffix := " where")
      pure (String.intercalate "\n" (#[head] ++ pack cs).toList)
  | .thmInfo _ =>
    let (bs, body) ← compactPieces ci.type
    pure (sig s!"theorem {short}" bs body)
  | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
    let (bs, body) ← compactPieces ci.type
    pure (sig s!"def {short}" bs body)
  | _ =>
    let (bs, body) ← compactPieces ci.type
    pure (sig short bs body)

/-- The opening of the signature's TeX environment: an fvextra `Verbatim`
that breaks long lines (at spaces, and anywhere if it must), at footnote size,
with a thin rule on the left in the colour of Verso's docstring boxes.  A
short signature (`samepage`) is never split across pages.  `bgcolorboxoverlap=0pt`
is needed for that: by default fvextra puts a `\vspace{-0.25pt}` after every
line, and a page may break at that glue whatever the line penalties say. -/
def verbatimOpen (samepage : Bool) : String :=
  "\\begin{Verbatim}[fontsize=\\footnotesize,breaklines=true,breakanywhere=true," ++
  "breaksymbolleft={},breakindent=1.5em,frame=leftline,framerule=0.6pt,framesep=5pt," ++
  (if samepage then "samepage=true," else "") ++ "bgcolorboxoverlap=0pt," ++
  -- no list skip above and below: the block's own spacing is set in `toTeX`
  "listparameters={\\setlength{\\topsep}{0pt}\\setlength{\\partopsep}{0pt}}," ++
  -- symbols in the monospaced font where it has them (`\leanSymbolfont`,
  -- defined by `{texSetup}`), so that the constructor columns align
  "formatcom={\\let\\versoSymbolFont\\symbolfont\\let\\symbolfont\\leanSymbolfont}," ++
  "rulecolor=\\color{bordercolor},xleftmargin=2pt]\n"

block_extension Block.leanDecl where
  traverse _ _ _ := pure none
  toTeX := some <| fun _ goB _ _ content => do
    -- the signature as a breakable fvextra Verbatim at footnote size, with a
    -- rule on the left; docstring paragraphs and the source link below it, small
    let mut parts : Array Verso.Output.TeX := #[]
    for b in content, i in [0:content.size] do
      match b with
      | .code s =>
        let short := (s.splitOn "\n").length ≤ 12
        parts := parts.push (.raw (verbatimOpen short ++ s ++ "\n\\end{Verbatim}\n"))
      | b =>
        -- the last block is the source link: set flush right, close under the code,
        -- and never separated from it by a page break
        let pre := if i + 1 == content.size then "\\nopagebreak{\\footnotesize\\raggedleft "
          else "{\\footnotesize\\noindent "
        parts := parts.push (.seq #[.raw pre, ← goB b, .raw "\\par}"])
    -- `\@endparpenalty` 10000: no page break straight after the Verbatim
    pure <| .seq #[.raw ("\\par\\vspace{3pt}\\begingroup\\setlength{\\parskip}{1pt}" ++
        "\\csname @endparpenalty\\endcsname=10000 "), .seq parts,
      .raw "\\endgroup\\par\\smallskip "]
  toHtml := some <| fun _ goB _ _ content => do
    pure {{ <div class="lean-decl">{{← content.mapM goB}}</div> }}
  extraCss := [r#"
.lean-decl { border-left: 3px solid #c8d3e0; padding: 0.1em 0 0.1em 0.8em; margin: 0.4em 0 1.2em 0; color: #333; }
.lean-decl pre { font-size: 78%; margin: 0.2em 0; white-space: pre-wrap; overflow-wrap: anywhere; }
.lean-decl p { margin: 0.2em 0; font-size: 82%; }
@media print {
  .lean-decl { break-inside: avoid; border-left-color: #999; }
  .lean-decl pre { font-size: 75%; }
  nav, .toc, #toc, .toc-frame, .header-title-wrapper, .search-wrapper, .permalink-widget { display: none !important; }
  main, .content-wrapper, .with-toc { margin: 0 !important; padding: 0 !important; max-width: none !important; }
  a { color: inherit; text-decoration: none; }
}
"#]

structure LeanDeclConfig where
  name : Ident × Name
  /-- show the declaration's docstring under the signature (off by default:
  the paper says in prose what the result is) -/
  doc : Bool := false

instance : FromArgs LeanDeclConfig DocElabM :=
  ⟨LeanDeclConfig.mk <$> .positional `name .documentableName <*> .flag `doc false⟩

@[block_command]
def leanDecl : BlockCommandOf LeanDeclConfig
  | ⟨(x, name), showDoc⟩ => do
    let text ← (compactDecl name : MetaM String)
    let found ← findDocString? (← getEnv) name
    let docs ← match (if showDoc then found else Option.none) with
      | Option.none => pure #[]
      | Option.some d =>
        let Option.some ast := MD4Lean.parse d | throwErrorAt x "Failed to parse docstring as Markdown"
        ast.blocks.mapM (blockFromMarkdownWithLean [name])
    let src ← srcLink.srcLinkFor name
    let code ← ``(Verso.Doc.Block.code $(quote text))
    let para ← ``(Verso.Doc.Block.para #[$src])
    let parts := #[code] ++ docs ++ #[para]
    ``(Verso.Doc.Block.other Block.leanDecl #[$parts,*])

end CLPPaper
