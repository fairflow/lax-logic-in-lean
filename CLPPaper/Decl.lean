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
* for an inductive, each constructor the same way, one per line;
* for a structure, its own fields only (not those it inherits);
* the docstring, rendered as Verso renders it;
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

/-- `head binders : body`, broken by Lean's formatter at `width` columns,
continuation lines indented by four (print has no horizontal scroll). -/
def width : Nat := 88

def joinSig (head : String) (bs : Array Format) (body : Format) (indent : Nat := 0)
    (suffix := "") : String :=
  let f : Format := .fill (.nest 4 (.text head ++
    Format.join (bs.toList.map (.line ++ ·)) ++ .text " :" ++ .line ++ body ++ .text suffix))
  let pad := "".pushn ' ' indent
  String.intercalate "\n" ((f.pretty (width - indent)).splitOn "\n" |>.map (pad ++ ·))

/-- The compact text of a declaration. -/
def compactDecl (n : Name) : MetaM String := do
  let env ← getEnv
  let ci ← getConstInfo n
  let short := toString (← unresolveNameGlobal n)
  match ci with
  | .inductInfo ii =>
    if isStructure env n then
      let (bs, body) ← compactType ci.type
      let parents := (getStructureParentInfo env n).map (·.structName)
      let ext ← if parents.isEmpty then pure "" else do
        let ps ← parents.mapM fun p => return toString (← unresolveNameGlobal p)
        pure (" extends " ++ String.intercalate ", " ps.toList)
      let mut lines := #[joinSig s!"structure {short}" bs body (suffix := ext ++ " where")]
      for f in getStructureFields env n do
        if (isSubobjectField? env n f).isSome then continue
        let Option.some proj := getProjFnForField? env n f | continue
        let (_, fty) ← compactType (← getConstInfo proj).type (skip := ii.numParams + 1)
        lines := lines.push ((joinSig s!"{f}" #[] fty (indent := 2)).replace "self." "")
      pure (String.intercalate "\n" lines.toList)
    else
      let (bs, body) ← compactType ci.type
      let mut lines := #[joinSig s!"inductive {short}" bs body (suffix := " where")]
      for c in ii.ctors do
        let (cbs, cbody) ← compactType (← getConstInfo c).type
        lines := lines.push (joinSig s!"| {c.componentsRev.head!}" cbs cbody (indent := 2))
      pure (String.intercalate "\n" lines.toList)
  | .thmInfo _ =>
    let (bs, body) ← compactType ci.type
    pure (joinSig s!"theorem {short}" bs body)
  | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
    let (bs, body) ← compactType ci.type
    pure (joinSig s!"def {short}" bs body)
  | _ =>
    let (bs, body) ← compactType ci.type
    pure (joinSig short bs body)

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
    pure <| .seq #[.raw ("\\par\\smallskip\\begingroup\\setlength{\\parskip}{1pt}" ++
        "\\csname @endparpenalty\\endcsname=10000 "), .seq parts,
      .raw "\\endgroup\\par\\medskip "]
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
