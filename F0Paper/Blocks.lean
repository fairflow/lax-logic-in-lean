/-
The presentation blocks of the F0 paper (v0.3, 2026-10-23; v0.4, 2026-10-24):

* `{leanStmt Name}`: the checked Lean statement of a declaration, beneath its
  displayed formula.  It is Lean's pretty-printing of the compiled declaration
  (`ppSignature`, under the document's `open` lines), with its source link.
  PDF: one small line; HTML: a collapsed panel that opens on click.
* `{lemmaTable n₁ n₂ …}`: the supporting declarations of a section, one row
  each: name, the formula on one line (`F0Paper.Math.stmtFlat`), source link.
  A row whose formula prints as empty is an error (v0.4: thirty-six rows of
  v0.3 printed nothing, among them every recursive definition).
* `:::f0table (widths := "…")`: a table written as Verso's list of lists, set
  with paragraph columns of the given fractions of the line.
* `{axiomsOf}`n₁ n₂``: the axioms the named declarations depend on, computed
  by `collectAxioms` when the document is built (the at-a-glance table).
* `{listElems}`L`` and `{listSize}`L``: a list of formulas of the
  development as a set, and its length (the downset table).
* `:::f0Figure "name"`: a generated figure with its caption.  The figure is
  `docs/f0-paper-figures/name.svg` (inlined in the HTML, enlarged by 8/5) and
  `name.pdf` (included in the PDF at its natural size, so that its labels
  print at the 10 pt they are set in; v0.4), written by
  `scripts/f0-figures.py` from data that Lean computed
  (`tools/F0/FigureData.lean`).
* The Lean statement line is `\footnotesize` in the PDF and 90% in the HTML
  (v0.4; v0.3 had `\scriptsize` and 80%).
-/
import Lean
import Lean.DocString.Syntax
import VersoManual
import CLPPaper.Src
import F0Paper.Math

open Lean Meta Elab
open Lean.Doc.Syntax
open Verso Doc Elab Genre Manual ArgParse
open Verso.Output Html

namespace F0Paper.Blocks

/-- TeX-escape running text (Verso's own escape covers `\ { } ^` only). -/
def texEsc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '\\' => "\\textbackslash{}" | '{' => "\\{" | '}' => "\\}" | '_' => "\\_"
      | '#' => "\\#" | '%' => "\\%" | '&' => "\\&" | '$' => "\\$"
      | '^' => "\\^{}" | '~' => "\\~{}"
      | c => c.toString

/-- A name in a narrow column: may break after `.` and `_`. -/
def texName (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '.' => ".\\allowbreak{}"
      | '_' => "\\_\\allowbreak{}"
      | c => texEsc c.toString

/-- (path, line, short label `file:line`) of a declaration. -/
def srcInfo (n : Name) : TermElabM (String × Nat × String) := do
  let env ← getEnv
  let modName : Name := match env.getModuleIdxFor? n with
    | Option.some i => env.header.moduleNames[i.toNat]!
    | Option.none => env.mainModule
  let path := (modName.toString.replace "." "/") ++ ".lean"
  let line := ((← findDeclarationRanges? n).map (·.selectionRange.pos.line)).getD 1
  let file := (modName.componentsRev.head?.map toString).getD path
  pure (path, line, s!"{file}:{line}")

/-- The URL of `path:line` at the commit the document is rendered from, read
from `F0_SRC_REPO` and `F0_SRC_SHA` (set by `scripts/f0-paper.sh`) when the
output is written: a `git` process per declaration took seconds inside Lean. -/
def srcUrl (path : String) (line : Nat) : IO String := do
  let repo := (← IO.getEnv "F0_SRC_REPO").getD "https://github.com/fairflow/lax-logic-in-lean"
  let sha := (← IO.getEnv "F0_SRC_SHA").getD "main"
  pure s!"{repo}/blob/{sha}/{path}#L{line}"

/-- A URL inside a TeX macro argument: `#` escaped. -/
def texUrl (u : String) : String := u.replace "#" "\\#"

/-- The name as the document writes it (under its `open` lines). -/
def shortName (n : Name) : TermElabM String := do
  pure (toString (← unresolveNameGlobal n))

/-! ## The Lean statement beneath a display -/

/-- (one-line signature, signature at 90 columns, label, path, line) -/
abbrev LeanStmtData := String × String × String × String × Nat

block_extension Block.f0Lean where
  traverse _ _ _ := pure none
  toTeX := some <| fun _ _ _ data _ => do
    match FromJson.fromJson? (α := LeanStmtData) data with
    | .error e => do reportError s!"leanStmt: bad data: {e}"; pure .empty
    | .ok (flat, _, label, path, line) =>
      let url ← (srcUrl path line : IO String)
      pure <| .raw ("\\par\\nopagebreak\\vspace{-2pt}{\\footnotesize\\raggedright\\noindent" ++
        "\\texttt{" ++ texEsc flat ++ "}\\hfill\\mbox{\\oldhref{" ++ texUrl url ++ "}{\\texttt{" ++
        texEsc label ++ "}}}\\par}\\medskip ")
  toHtml := some <| fun _ _ _ data _ => do
    match FromJson.fromJson? (α := LeanStmtData) data with
    | .error e => do reportError s!"leanStmt: bad data: {e}"; pure .empty
    | .ok (_, wide, label, path, line) =>
      let url ← (srcUrl path line : IO String)
      pure {{ <details class="f0-lean"><summary>"Lean statement · "<a href={{url}}><code>{{label}}</code></a></summary><pre>{{wide}}</pre></details> }}
  extraCss := [r#"
.f0-lean { margin: -0.4em 0 1em 0; font-size: 90%; color: #555; }
.f0-lean summary { cursor: pointer; }
.f0-lean summary a { text-decoration: none; }
.f0-lean pre { font-size: 95%; margin: 0.3em 0 0.3em 1em; white-space: pre-wrap; overflow-wrap: anywhere; }
"#]

structure NameConfig where
  name : Ident × Name

instance : FromArgs NameConfig DocElabM :=
  ⟨NameConfig.mk <$> .positional `name .documentableName⟩

/-- The checked Lean statement of a declaration, with its source link. -/
@[block_command]
def leanStmt : BlockCommandOf NameConfig
  | ⟨(_, n)⟩ => do
    let sig ← (PrettyPrinter.ppSignature n : MetaM FormatWithInfos)
    -- the declaration's name as the document writes it (its `open` lines)
    let full := n.toString
    let short ← shortName n
    let fix (s : String) : String :=
      if s.startsWith full then short ++ (s.drop full.length).toString else s
    let flat := fix (" ".intercalate ((sig.fmt.pretty 100000).splitOn "\n" |>.map (·.trimAscii.copy)))
    let wide := fix (sig.fmt.pretty 90)
    let (path, line, label) ← srcInfo n
    let d : LeanStmtData := (flat, wide, label, path, line)
    let js := (ToJson.toJson d).compress
    `(Verso.Doc.Block.other {Block.f0Lean with data := (Json.parse $(quote js)).toOption.getD Json.null} #[])

/-! ## The table of supporting declarations -/

/-- (name, the formula as items set one after another, label, path, line)
per row: a definition by cases has an item per case, a line break allowed
between items (`F0Paper.Math.stmtFlat`). -/
abbrev LemmaRow := String × List String × String × String × Nat

block_extension Block.f0Lemmas where
  traverse _ _ _ := pure none
  toTeX := some <| fun _ _ _ data _ => do
    match FromJson.fromJson? (α := Array LemmaRow) data with
    | .error e => do reportError s!"lemmaTable: bad data: {e}"; pure .empty
    | .ok rows =>
      let mut body := ""
      for (nm, f, label, path, line) in rows do
        let url ← (srcUrl path line : IO String)
        body := body ++ "\\texttt{" ++ texName nm ++ "} & " ++
          -- items apart by a stretchable space, where a line may break
          "\\hskip 0.7em plus 0.4em\\relax ".intercalate (f.map fun s => "$" ++ s ++ "$") ++
          " & \\oldhref{" ++ texUrl url ++ "}{\\texttt{" ++ texName label ++ "}}\\\\\n"
      pure <| .raw ("\\par\\begingroup\\footnotesize\\setlength{\\LTpre}{4pt}\\setlength{\\LTpost}{4pt}" ++
        "\\def\\arraystretch{1.2}" ++
        "\\begin{longtable}{@{}>{\\raggedright\\arraybackslash}p{0.25\\linewidth}" ++
        ">{\\raggedright\\arraybackslash}p{0.57\\linewidth}>{\\raggedleft\\arraybackslash}p{0.14\\linewidth}@{}}\n" ++
        "\\hline\n" ++ body ++ "\\hline\n\\end{longtable}\\endgroup\\par ")
  toHtml := some <| fun _ _ _ data _ => do
    match FromJson.fromJson? (α := Array LemmaRow) data with
    | .error e => do reportError s!"lemmaTable: bad data: {e}"; pure .empty
    | .ok rows =>
      let mut trs : Array Html := #[]
      for (nm, f, label, path, line) in rows do
        let url ← (srcUrl path line : IO String)
        let mut cells : Array Html := #[]
        for s in f do
          cells := cells.push {{ <code class="math inline">{{s}}</code> }}
          cells := cells.push (Html.text true " ")
        trs := trs.push {{ <tr><td><code>{{nm}}</code></td><td>{{cells}}</td><td><a href={{url}}><code>{{label}}</code></a></td></tr> }}
      pure {{ <table class="f0-lemmas"><tbody>{{trs}}</tbody></table> }}
  extraCss := [r#"
table.f0-lemmas { border-collapse: collapse; font-size: 85%; margin: 0.6em 0 1.2em 0; width: 100%; }
table.f0-lemmas td { border-top: 1px solid #ddd; padding: 0.2em 0.5em; vertical-align: top; }
table.f0-lemmas td:first-child { white-space: nowrap; }
table.f0-lemmas td:last-child { text-align: right; white-space: nowrap; }
table.f0-lemmas a { text-decoration: none; }
table.f0-lemmas td code.math { margin-right: 0.6em; }
"#]

structure NamesConfig where
  names : List (Ident × Name)

instance : FromArgs NamesConfig DocElabM :=
  ⟨NamesConfig.mk <$> .many (.positional `name .documentableName)⟩

/-- Supporting declarations, one row each. -/
@[block_command]
def lemmaTable : BlockCommandOf NamesConfig
  | ⟨names⟩ => do
    let mut rows : Array LemmaRow := #[]
    for (_, n) in names do
      let f ← (F0Paper.Math.stmtFlat n : MetaM (List String))
      if f.isEmpty || f.any (·.trimAscii.isEmpty) then
        throwError "lemmaTable: {n} prints as empty"
      let (path, line, label) ← srcInfo n
      rows := rows.push (← shortName n, f, label, path, line)
    let js := (ToJson.toJson rows).compress
    `(Verso.Doc.Block.other {Block.f0Lemmas with data := (Json.parse $(quote js)).toOption.getD Json.null} #[])

/-! ## Tables with paragraph columns -/

block_extension Block.f0Table (widths : List String) where
  data := ToJson.toJson widths
  traverse _ _ _ := pure none
  toTeX := some <| fun _ goB _ data blocks => do
    match FromJson.fromJson? (α := List String) data with
    | .error e => do reportError s!"f0table: bad data: {e}"; pure .empty
    | .ok widths =>
      let n := widths.length
      let spec := String.join (widths.map fun w =>
        ">{\\raggedright\\arraybackslash}p{" ++ w ++ "\\linewidth}")
      let #[.ul items] := blocks | do reportError "f0table: malformed"; pure .empty
      let mut out : Array Verso.Output.TeX := #[]
      let mut i := 0
      for it in items do
        let cell ← it.contents.mapM goB
        out := out.push (.seq cell)
        i := i + 1
        out := out.push (.raw (if i % n == 0 then
          (if i == n then "\\\\\\hline\n\\endhead\n" else "\\\\\n") else " & "))
      pure <| .seq (#[.raw ("\\par\\begingroup\\footnotesize\\setlength{\\parskip}{0pt}\\def\\arraystretch{1.2}" ++
          "\\begin{longtable}{@{}" ++ spec ++ "@{}}\n\\hline\n")] ++ out ++
        #[.raw "\\hline\n\\end{longtable}\\endgroup\\par "])
  toHtml := some <| fun _ goB _ data blocks => do
    match FromJson.fromJson? (α := List String) data with
    | .error e => do reportError s!"f0table: bad data: {e}"; pure .empty
    | .ok widths =>
      let n := widths.length
      let #[.ul items] := blocks | do reportError "f0table: malformed"; pure .empty
      let mut rowsOut : Array Html := #[]
      let mut cur : Array Html := #[]
      let mut i := 0
      for it in items do
        let cell ← it.contents.mapM goB
        cur := cur.push (if i < n then {{ <th>{{cell}}</th> }} else {{ <td>{{cell}}</td> }})
        i := i + 1
        if i % n == 0 then
          rowsOut := rowsOut.push {{ <tr>{{cur}}</tr> }}
          cur := #[]
      pure {{ <table class="f0-table"><tbody>{{rowsOut}}</tbody></table> }}
  extraCss := [r#"
table.f0-table { border-collapse: collapse; font-size: 90%; margin: 0.8em 0 1.2em 0; }
table.f0-table th, table.f0-table td { border-top: 1px solid #ccc; padding: 0.25em 0.6em; vertical-align: top; text-align: left; }
table.f0-table td p, table.f0-table th p { margin: 0; }
"#]

structure TableCfg where
  widths : String

instance : FromArgs TableCfg DocElabM :=
  ⟨TableCfg.mk <$> .named `widths .string false⟩

/-- A table as a list of rows, each a list of cells; the first row is the
header.  `widths` gives the column widths as fractions of the line. -/
@[directive]
def f0table : DirectiveExpanderOf TableCfg
  | cfg, contents => do
    let #[oneBlock] := contents
      | throwError "Expected a single unordered list"
    let `(block|ul{$items*}) := oneBlock
      | throwErrorAt oneBlock "Expected a single unordered list"
    let getLi : Syntax → DocElabM (TSyntaxArray `block) := fun
      | `(list_item| * $content* ) => pure content
      | other => throwErrorAt other "Expected list item"
    let preRows ← items.mapM getLi
    let rows ← preRows.mapM fun blks => do
      let #[oneInRow] := blks.filter (·.raw.isOfKind ``Lean.Doc.Syntax.ul)
        | throwError "Each row should have exactly one list in it"
      let `(block|ul{ $cellItems*}) := oneInRow
        | throwErrorAt oneInRow "Each row should have exactly one list in it"
      cellItems.mapM getLi
    let widths := (cfg.widths.splitOn " ").filter (· ≠ "")
    if rows.any (·.size != widths.length) then
      throwErrorAt oneBlock s!"Expected {widths.length} cells in every row"
    let blocks : Array (Syntax.TSepArray `term ",") ← rows.flatten.mapM (·.mapM Verso.Doc.Elab.elabBlock)
    ``(Verso.Doc.Block.other (Block.f0Table $(quote widths)) #[Verso.Doc.Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])

/-! ## Computed cells -/

structure RoleCfg where
  ok : Unit := ()

instance {m : Type → Type} [Monad m] : FromArgs RoleCfg m := ⟨(fun _ => {}) <$> .done⟩

/-- The axioms of the named declarations (space-separated), by `collectAxioms`. -/
@[role]
def axiomsOf : RoleExpanderOf RoleCfg
  | _, #[arg] => do
    let `(inline|code( $s:str )) := arg
      | throwErrorAt arg "Expected a code literal with declaration names"
    let mut axs : Array Name := #[]
    for w in (s.getString.splitOn " ").filter (· ≠ "") do
      let identStx := mkIdentFrom arg w.toName (canonical := true)
      let n ← realizeGlobalConstNoOverloadWithInfo identStx
      for a in ← collectAxioms n do
        unless axs.contains a do axs := axs.push a
    let order := [``propext, ``Classical.choice, ``Quot.sound]
    let sorted := order.filter axs.contains ++ (axs.toList.filter (!order.contains ·))
    let t := if sorted.isEmpty then "none" else ", ".intercalate (sorted.map toString)
    `(Verso.Doc.Inline.text $(quote t))
  | _, _ => throwError "Expected exactly one code literal"

/-- A list of formulas of the development, printed as the set it lists. -/
@[role]
def listElems : RoleExpanderOf RoleCfg
  | _, #[arg] => do
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected a code literal with the list's name"
    let identStx := mkIdentFrom arg name.getString.toName (canonical := true)
    let n ← realizeGlobalConstNoOverloadWithInfo identStx
    let tex ← (F0Paper.Math.generic {} 0 (mkConst n) : MetaM String)
    `(Verso.Doc.Inline.math .inline $(quote tex))
  | _, _ => throwError "Expected exactly one code literal"

/-- The length of a list literal of the development. -/
@[role]
def listSize : RoleExpanderOf RoleCfg
  | _, #[arg] => do
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected a code literal with the list's name"
    let identStx := mkIdentFrom arg name.getString.toName (canonical := true)
    let n ← realizeGlobalConstNoOverloadWithInfo identStx
    let some (.defnInfo dv) := (← getEnv).find? n | throwErrorAt arg "not a definition"
    let some l := F0Paper.Math.listLit? dv.value | throwErrorAt arg "not a list literal"
    `(Verso.Doc.Inline.text $(quote (toString l.length)))
  | _, _ => throwError "Expected exactly one code literal"

/-! ## Generated figures -/

/-- Where `scripts/f0-figures.py` writes the figures (gitignored). -/
def figDir : String := "docs/f0-paper-figures"

/-- Scale the integer `width="…"` and `height="…"` of the opening `<svg …>`
tag (the first occurrence of each) by `num/den`; its `viewBox` keeps the
drawing.  The figures are drawn with labels at the PDF's text size, 10 pt,
smaller than a browser's body text, so the HTML enlarges them by 8/5. -/
def scaleSvg (svg : String) (num den : Nat) : String := Id.run do
  let mut s := svg
  for attr in ["width", "height"] do
    let key := " " ++ attr ++ "=\""
    match s.splitOn key with
    | pre :: post :: more =>
      let digits := String.ofList (post.toList.takeWhile Char.isDigit)
      let after := String.ofList (post.toList.drop digits.length)
      if let some v := digits.toNat? then
        s := pre ++ key ++ toString (v * num / den) ++ key.intercalate (after :: more)
    | _ => pure ()
  return s

block_extension Block.f0Figure (name : String) where
  data := ToJson.toJson name
  traverse _ _ _ := pure none
  toTeX := some <| fun _ goB _ data blocks => do
    match FromJson.fromJson? (α := String) data with
    | .error e => do reportError s!"f0Figure: bad data: {e}"; pure .empty
    | .ok name =>
      let cwd ← (IO.currentDir : IO System.FilePath)
      let dir := (cwd / figDir).toString
      let caption ← blocks.mapM goB
      -- at its natural size, so that the labels print at the size they are set
      -- in (`scripts/f0-figures.py` keeps every figure within the text block)
      pure <| .seq (#[.raw ("\\par\\begin{center}{\\graphicspath{{" ++ dir ++ "/}}" ++
          "\\includegraphics{" ++ name ++ ".pdf}}\\end{center}" ++
          "\\vspace{-6pt}{\\small ")] ++ caption ++ #[.raw "\\par}\\medskip "])
  toHtml := some <| fun _ goB _ data blocks => do
    match FromJson.fromJson? (α := String) data with
    | .error e => do reportError s!"f0Figure: bad data: {e}"; pure .empty
    | .ok name =>
      let path : System.FilePath := figDir / (name ++ ".svg")
      let svg ← (IO.FS.readFile path : IO String)
      -- the SVG element only (graphviz writes an XML prologue and a doctype first)
      let svg := match svg.splitOn "<svg" with
        | _ :: rest => "<svg" ++ "<svg".intercalate rest
        | [] => svg
      let svg := scaleSvg svg 8 5
      let caption ← blocks.mapM goB
      pure {{ <figure class="f0-fig">{{Html.text false svg}}<figcaption>{{caption}}</figcaption></figure> }}
  extraCss := [r#"
figure.f0-fig { margin: 1em 0; text-align: center; }
figure.f0-fig svg { max-width: 100%; height: auto; }
figure.f0-fig figcaption { text-align: left; font-size: 90%; }
"#]

structure FigCfg where
  name : String

instance : FromArgs FigCfg DocElabM :=
  ⟨FigCfg.mk <$> .positional `name .string⟩

/-- A generated figure, with its caption as the directive's contents. -/
@[directive]
def f0Figure : DirectiveExpanderOf FigCfg
  | cfg, contents => do
    let blocks ← contents.mapM Verso.Doc.Elab.elabBlock
    ``(Verso.Doc.Block.other (Block.f0Figure $(quote cfg.name)) #[$blocks,*])

end F0Paper.Blocks
