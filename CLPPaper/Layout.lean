/-
Layout devices for the CLP paper (2026-10-15).

* `:::wtable (widths := "0.3 0.7") +header` — a table whose cells wrap.  Verso's
  own `table` directive sets every column `l` in TeX, so a long cell runs off
  the page; here each column is a `p{…}` column of the given fraction of the
  text width, and the HTML is an ordinary table with the same proportions.
  The body is Verso's table syntax: one outer list item per row, each holding
  a list of cells.
* `{texSetup}` — raw TeX for the print layout, emitted once at the start of
  the document and nothing in HTML: no blank recto pages, chapters run on,
  smaller chapter titles.
-/
import Lean
import VersoManual

open Lean Elab
open Lean.Doc.Syntax
open Verso Doc Elab Genre Manual ArgParse
open Verso.Output Html

namespace CLPPaper

/-! ## Wrapping tables -/

structure WTableConfig where
  widths : Option String := none
  header : Bool := false

instance : FromArgs WTableConfig DocElabM :=
  ⟨WTableConfig.mk <$> .named `widths .string true <*> .flag `header false⟩

/-- `"0.3 0.7"` as fractions; equal shares when absent or malformed. -/
def parseWidths (n : Nat) (s : Option String) : Array Float := Id.run do
  let fallback := Array.replicate n (1.0 / n.toFloat)
  let some s := s | return fallback
  let ws := (s.splitOn " ").filter (· ≠ "") |>.toArray
  if ws.size != n then return fallback
  let mut out := #[]
  for w in ws do
    match w.splitOn "." with
    | ["0", frac] =>
      let d := frac.toNat!.toFloat / (10.0 ^ frac.length.toFloat)
      out := out.push d
    | [i] => out := out.push i.toNat!.toFloat
    | _ => return fallback
  return out

/-- A fraction as `0.ddd`. -/
def fmtFrac (f : Float) : String :=
  let k := (f * 1000.0).round.toUInt64.toNat
  let s := toString k
  "0." ++ "".pushn (Char.ofNat 48) (3 - s.length) ++ s

block_extension Block.wtable (columns : Nat) (header : Bool) (widths : Array Float) where
  data := ToJson.toJson (columns, header, widths.map fmtFrac)
  traverse _ _ _ := pure none
  toTeX := some <| fun _ goB _ data blocks => do
    match FromJson.fromJson? data (α := Nat × Bool × Array String) with
    | .error e => do reportError s!"wtable: bad data {e}"; pure .empty
    | .ok (columns, header, ws) =>
      let #[.ul items] := blocks | do reportError "wtable: malformed"; pure .empty
      let spec := String.join (ws.toList.map fun w =>
        ">{\\raggedright\\arraybackslash}p{\\dimexpr " ++ w ++ "\\linewidth-2\\tabcolsep\\relax}")
      let mut rows : Array TeX := #[]
      let mut i := 0
      let mut cur : Array TeX := #[]
      for it in items do
        let cell ← it.contents.mapM goB
        let cellTeX := TeX.seq (cell.toList.intersperse (.raw "\\par ") |>.toArray)
        let cellTeX := if header && rows.size == 0 then TeX.seq #[.raw "\\bfseries ", cellTeX] else cellTeX
        cur := cur.push cellTeX
        i := i + 1
        if i % columns == 0 then
          let sep := if header && rows.size == 0 then "\\tabularnewline\\hline\n" else "\\tabularnewline[2pt]\n"
          rows := rows.push (.seq ((cur.toList.intersperse (.raw " & ")).toArray.push (.raw sep)))
          cur := #[]
      pure <| .seq #[.raw "\n\\par\\medskip\\noindent{\\small\\renewcommand{\\arraystretch}{1.1}%\n",
        .raw ("\\begin{tabular}{@{}" ++ spec ++ "@{}}\\hline\n"), .seq rows,
        .raw "\\hline\n\\end{tabular}}\\par\\medskip\n"]
  toHtml := some <| fun _ goB _ data blocks => do
    match FromJson.fromJson? data (α := Nat × Bool × Array String) with
    | .error _ => pure .empty
    | .ok (columns, header, ws) =>
      let #[.ul items] := blocks | pure .empty
      let mut rows : Array Html := #[]
      let mut cur : Array Html := #[]
      let mut i := 0
      for it in items do
        let cell ← it.contents.mapM goB
        let isHead := header && rows.size == 0
        cur := cur.push (Html.tag (if isHead then "th" else "td") #[] (.seq cell))
        i := i + 1
        if i % columns == 0 then
          let row := Html.tag "tr" #[] (.seq cur)
          rows := rows.push (if isHead then Html.tag "thead" #[] row else row)
          cur := #[]
      let cols : Array Html := ws.map fun w =>
        Html.tag "col" #[("style", "width:" ++ toString ((w.drop 2).toString.toNat! / 10) ++ "%")] .empty
      pure (Html.tag "table" #[("class", "wtable")] (.seq #[Html.tag "colgroup" #[] (.seq cols), .seq rows]))
  extraCss := [r#"
table.wtable { border-collapse: collapse; width: 100%; margin: 0.8em 0 1.2em 0; font-size: 92%; }
table.wtable th, table.wtable td { text-align: left; vertical-align: top; padding: 0.3em 0.6em; border-bottom: 1px solid #ddd; }
table.wtable thead th { border-bottom: 2px solid #999; border-top: 2px solid #999; }
table.wtable td p, table.wtable th p { margin: 0; }
"#]

@[directive]
def wtable : DirectiveExpanderOf WTableConfig
  | cfg, contents => do
    let #[oneBlock] := contents
      | throwError "Expected a single unordered list"
    let `(block|ul{$items*}) := oneBlock
      | throwErrorAt oneBlock "Expected a single unordered list"
    let preRows ← items.mapM getLi
    let rows ← preRows.mapM fun blks => do
      let #[oneInRow] := blks.filter (·.raw.isOfKind ``Lean.Doc.Syntax.ul)
        | throwError "Each row should have exactly one list in it"
      let `(block|ul{ $cellItems*}) := oneInRow
        | throwErrorAt oneInRow "Each row should have exactly one list in it"
      cellItems.mapM getLi
    if h : rows.size = 0 then
      throwErrorAt oneBlock "Expected at least one row"
    else
      let columns := rows[0].size
      if rows.any (·.size != columns) then
        throwErrorAt oneBlock s!"Expected all rows to have the same number of columns, got {rows.map (·.size)}"
      let ws := parseWidths columns cfg.widths
      let flattened := rows.flatten
      let blocks : Array (Syntax.TSepArray `term ",") ← flattened.mapM (·.mapM Verso.Doc.Elab.elabBlock)
      ``(Verso.Doc.Block.other (Block.wtable $(quote columns) $(quote cfg.header) $(quote ws))
          #[Verso.Doc.Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])
where
  getLi : Syntax → DocElabM (TSyntaxArray `block)
    | `(list_item| * $content* ) => pure content
    | other => throwErrorAt other "Expected list item"

/-! ## Print layout -/

/-- Raw TeX for the print layout (memoir): no blank recto pages, chapters run
on, smaller chapter and section titles, a little paragraph spacing. -/
def texSetupText : String :=
  "\\markboth{}{}\\openany\\let\\cleardoublepage\\clearpage\\settocdepth{chapter}" ++
  "\\renewcommand*{\\clearforchapter}{\\par\\bigskip}" ++
  "\\renewcommand*{\\chaptitlefont}{\\sffamily\\LARGE\\bfseries}" ++
  "\\renewcommand*{\\chapnumfont}{\\chaptitlefont}" ++
  "\\setlength{\\beforechapskip}{0pt}\\setlength{\\afterchapskip}{1.2\\baselineskip}" ++
  "\\setsecheadstyle{\\sffamily\\bfseries\\large}" ++
  "\\setbeforesecskip{-2.2ex plus -0.6ex minus -0.2ex}" ++
  "\\setaftersecskip{1.0ex plus 0.2ex}" ++
  "\\setlength{\\parskip}{0.25\\baselineskip plus 1pt}" ++
  "\\tightlists\\emergencystretch=2em\n"

block_extension Block.texSetup where
  traverse _ _ _ := pure none
  toTeX := some <| fun _ _ _ _ _ => pure (.raw texSetupText)
  toHtml := some <| fun _ _ _ _ _ => pure .empty

structure NoArgs where
  ok : Unit := ()

instance {m : Type → Type} [Monad m] : FromArgs NoArgs m := ⟨(fun _ => {}) <$> .done⟩

@[block_command]
def texSetup : BlockCommandOf NoArgs
  | _ => ``(Verso.Doc.Block.other Block.texSetup #[])

end CLPPaper
