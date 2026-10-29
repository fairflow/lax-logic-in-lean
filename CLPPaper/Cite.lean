/-
Citations for the CLP paper, author–year, read from the repository's master
bibliography `docs/references.bib` when the document is built (v0.9).

* `{cite}`Key`` — textual: “Jaffar and Lassez (1987)”.
* `{pcite}`Key1 Key2`` — parenthetical: “(Jaffar and Lassez 1987; Lloyd 1987)”.
* `{references}` — a block command: the list of every work cited in the
  modules this one imports, sorted by author and year, each entry formatted
  from its BibTeX fields, with its DOI linked.

A key that is not in `docs/references.bib` stops the build, and the list of
references is exactly the set of keys cited, so the paper cannot cite what the
master file lacks, nor list what it does not cite.  Verso's own
`VersoManual.Bibliography` was not used: it has no book or technical-report
entry type, and it sets each reference as a marginal note rather than in a
list of references.  Citations are plain text, not links (a link to an anchor
on another page would break in the per-section HTML).
-/
import Lean
import VersoManual

open Lean Elab
open Lean.Doc.Syntax
open Verso Doc Elab Genre Manual ArgParse
open Verso.Output Html

namespace CLPPaper.Cite

/-! ## Reading BibTeX -/

structure Entry where
  type : String
  key : String
  fields : List (String × String)
  deriving Inhabited, Repr

def Entry.get (e : Entry) (f : String) : Option String := e.fields.lookup f

/-- The text up to the brace closing the one just opened, and what follows it. -/
partial def takeBalanced : List Char → Nat → List Char → List Char × List Char
  | [], _, acc => (acc.reverse, [])
  | '{' :: r, d, acc => takeBalanced r (d + 1) ('{' :: acc)
  | '}' :: r, 0, acc => (acc.reverse, r)
  | '}' :: r, d + 1, acc => takeBalanced r d ('}' :: acc)
  | c :: r, d, acc => takeBalanced r d (c :: acc)

/-- Collapse runs of white space to one space and trim. -/
def squash (cs : List Char) : String :=
  let words := (String.ofList (cs.map fun c => if c.isWhitespace then ' ' else c)).splitOn " "
  " ".intercalate (words.filter (· ≠ ""))

partial def parseFields : List Char → List (String × String) → List (String × String)
  | cs, acc =>
    let cs := cs.dropWhile (fun c => c.isWhitespace || c == ',')
    let (name, r) := cs.span (fun c => c.isAlphanum || c == '_' || c == '-')
    if name.isEmpty then acc.reverse else
    match r.dropWhile Char.isWhitespace with
    | '=' :: r =>
      let r := r.dropWhile Char.isWhitespace
      let (v, rest) := match r with
        | '{' :: r => takeBalanced r 0 []
        | '"' :: r => let (v, rest) := r.span (· != '"'); (v, rest.drop 1)
        | r => r.span (fun c => c != ',' && c != '}' && !c.isWhitespace)
      parseFields rest ((String.ofList name |>.toLower, squash v) :: acc)
    | _ => acc.reverse

/-- The entries of a BibTeX file: each starts with `@` at the start of a line. -/
partial def scan : List Char → Bool → List Entry → List Entry
  | [], _, acc => acc.reverse
  | c :: r, lineStart, acc =>
    if lineStart && c == '@' then
      let (ty, r1) := r.span (· != '{')
      match r1 with
      | '{' :: r2 =>
        let (content, rest) := takeBalanced r2 0 []
        let (key, r3) := content.span (· != ',')
        scan rest false (⟨(String.ofList ty).toLower, squash key, parseFields (r3.drop 1) []⟩ :: acc)
      | _ => scan r1 false acc
    else scan r (c == '\n' || (lineStart && (c == ' ' || c == '\t'))) acc

/-- The master bibliography, relative to the repository root (where the
document is built). -/
def bibPath : System.FilePath := "docs/references.bib"

initialize bibCache : IO.Ref (Option (List Entry)) ← IO.mkRef none

def entries : IO (List Entry) := do
  if let some es := ← bibCache.get then return es
  let es := scan (← IO.FS.readFile bibPath).toList true []
  bibCache.set (some es)
  return es

def lookupKey (key : String) : IO (Option Entry) := do
  return (← entries).find? (·.key == key)

/-! ## From BibTeX's TeX to Unicode -/

def accentTable : List (Char × List (Char × Char)) :=
  [('\'', [('a','á'),('e','é'),('i','í'),('o','ó'),('u','ú'),('y','ý'),('A','Á'),('E','É'),('I','Í'),
           ('O','Ó'),('U','Ú'),('c','ć'),('n','ń'),('s','ś'),('z','ź'),('C','Ć'),('S','Ś'),('Z','Ź')]),
   ('`', [('a','à'),('e','è'),('i','ì'),('o','ò'),('u','ù'),('A','À'),('E','È'),('O','Ò')]),
   ('"', [('a','ä'),('e','ë'),('i','ï'),('o','ö'),('u','ü'),('y','ÿ'),('A','Ä'),('E','Ë'),('O','Ö'),('U','Ü')]),
   ('^', [('a','â'),('e','ê'),('i','î'),('o','ô'),('u','û'),('A','Â'),('E','Ê'),('O','Ô')]),
   ('~', [('a','ã'),('n','ñ'),('o','õ'),('A','Ã'),('N','Ñ'),('O','Õ')]),
   ('c', [('c','ç'),('C','Ç'),('s','ş'),('S','Ş')]),
   ('v', [('c','č'),('s','š'),('z','ž'),('r','ř'),('e','ě'),('C','Č'),('S','Š'),('Z','Ž'),('R','Ř')])]

def accent (a x : Char) : Char :=
  ((accentTable.lookup a).bind (·.lookup x)).getD x

/-- The argument of an accent command: `{x}`, `\i`, or the next letter. -/
def accArg : List Char → Option (Char × List Char)
  | '{' :: '\\' :: 'i' :: '}' :: r => some ('i', r)
  | '{' :: x :: '}' :: r => some (x, r)
  | '\\' :: 'i' :: r => some ('i', r)
  | ' ' :: x :: r => some (x, r)
  | x :: r => some (x, r)
  | [] => none

partial def detexL : List Char → List Char
  | [] => []
  | '\\' :: a :: r =>
    if "'`\"^~".toList.contains a then
      match accArg r with
      | some (x, r') => accent a x :: detexL r'
      | Option.none => detexL r
    else
      let (w, r') := (a :: r).span Char.isAlpha
      let word := String.ofList w
      if w.isEmpty then a :: detexL r            -- \& \% \_ \{ ...
      else if word == "c" || word == "v" then
        match accArg r' with
        | some (x, r'') => accent w.head! x :: detexL r''
        | Option.none => detexL r'
      else
        let out := match word with
          | "o" => "ø" | "O" => "Ø" | "ss" => "ß" | "aa" => "å" | "AA" => "Å"
          | "l" => "ł" | "L" => "Ł" | "i" => "ı" | "ae" => "æ" | _ => ""
        out.toList ++ detexL (r'.dropWhile (· == ' '))
  | '{' :: r => detexL r
  | '}' :: r => detexL r
  | '-' :: '-' :: '-' :: r => '—' :: detexL r
  | '-' :: '-' :: r => '–' :: detexL r
  | '~' :: r => ' ' :: detexL r
  | '$' :: r => detexL r
  | c :: r => c :: detexL r

def detex (s : String) : String := String.ofList (detexL s.toList)

/-! ## Names and labels -/

/-- `(surname, given names)` of each author; a braced name is corporate. -/
def authorsOf (s : String) : List (String × String) :=
  (s.splitOn " and ").map fun n =>
    let n := n.trimAscii.copy
    if n.startsWith "{" && n.endsWith "}" then (detex n, "")
    else match n.splitOn "," with
      | last :: rest@(_ :: _) => (detex last.trimAscii.copy, detex (", ".intercalate rest).trimAscii.copy)
      | _ =>
        let ws := (detex n).splitOn " " |>.filter (· ≠ "")
        match ws.reverse with
        | last :: given => (last, " ".intercalate given.reverse)
        | [] => (n, "")

def andList (xs : List String) : String :=
  match xs.reverse with
  | [] => ""
  | [x] => x
  | x :: rest => ", ".intercalate rest.reverse ++ " and " ++ x

def Entry.authorsOrEditors (e : Entry) : List (String × String) :=
  authorsOf ((e.get "author").getD ((e.get "editor").getD "Anonymous"))

def Entry.year (e : Entry) : String := (e.get "year").getD "n.d."

/-- “Jaffar and Lassez”, “Jaffar et al.”. -/
def Entry.label (e : Entry) : String :=
  match e.authorsOrEditors.map (·.1) with
  | [a] => a
  | [a, b] => a ++ " and " ++ b
  | a :: _ => a ++ " et al."
  | [] => "Anonymous"

/-! ## Citations -/

/-- The keys cited in a module, kept in its `.olean`. -/
initialize citedExt : SimplePersistentEnvExtension String (Array String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun a k => a.push k
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

structure CiteConfig where
  ok : Unit := ()

instance {m : Type → Type} [Monad m] : FromArgs CiteConfig m := ⟨(fun _ => {}) <$> .done⟩

def citeEntries (arg : Syntax) : DocElabM (List Entry) := do
  let `(inline|code( $keys:str )) := arg
    | throwErrorAt arg "Expected a code literal with one or more BibTeX keys"
  let ks := (keys.getString.splitOn " ").flatMap (·.splitOn ",") |>.filter (· ≠ "")
  ks.mapM fun k => do
    let some e ← (lookupKey k : IO _) | throwErrorAt arg s!"{k} is not in {bibPath}"
    modifyEnv (citedExt.addEntry · k)
    return e

/-- Textual citation: “Jaffar and Lassez (1987)”. -/
@[role]
def cite : RoleExpanderOf CiteConfig
  | _, #[arg] => do
    let es ← citeEntries arg
    let s := "; ".intercalate (es.map fun e => s!"{e.label} ({e.year})")
    ``(Verso.Doc.Inline.text $(quote s))
  | _, _ => throwError "Expected exactly one code literal"

/-- Parenthetical citation: “(Jaffar and Lassez 1987; Lloyd 1987)”. -/
@[role]
def pcite : RoleExpanderOf CiteConfig
  | _, #[arg] => do
    let es ← citeEntries arg
    let s := "(" ++ "; ".intercalate (es.map fun e => s!"{e.label} {e.year}") ++ ")"
    ``(Verso.Doc.Inline.text $(quote s))
  | _, _ => throwError "Expected exactly one code literal"

/-! ## The list of references -/

/- An external link (a DOI): `\oldhref` in TeX (Verso's `\href` becomes a
footnote), breakable after each `/`; an ordinary link in HTML. -/
inline_extension Inline.extLink where
  traverse _ _ _ := pure none
  toTeX := some <| fun _ _ data _ => do
    match FromJson.fromJson? (α := String × String) data with
    | .error e => do reportError s!"extLink: bad data: {e}"; pure .empty
    | .ok (url, txt) =>
      let comps := txt.splitOn "/"
      let txtTeX : Array TeX := comps.tail.foldl
        (fun acc s => acc ++ #[.raw "/\\allowbreak{}", .text s]) #[.text comps.head!]
      pure <| .seq (#[.raw "\\oldhref{", .raw url, .raw "}{\\texttt{"] ++ txtTeX ++ #[.raw "}}"])
  toHtml := some <| fun _ _ data _ => do
    match FromJson.fromJson? (α := String × String) data with
    | .error e => do reportError s!"extLink: bad data: {e}"; pure .empty
    | .ok (url, txt) => pure {{ <a href={{url}}><code>{{txt}}</code></a> }}

/-- The pieces of one reference: plain text, emphasised text, a DOI, or a URL
(a master's thesis without a DOI, 2026-10-29). -/
inductive Piece where
  | t (s : String)
  | em (s : String)
  | doi (d : String)
  | url (u : String)

def fmtName (n : String × String) : String := if n.2.isEmpty then n.1 else n.1 ++ ", " ++ n.2

def endDot (s : String) : String := if s.endsWith "." || s.endsWith "?" then s else s ++ "."

/-- One reference, author–year, by entry type. -/
def Entry.pieces (e : Entry) : List Piece := Id.run do
  let g (f : String) := (e.get f).map detex
  let who := andList (e.authorsOrEditors.map fmtName) ++
    (if (e.get "author").isNone && (e.get "editor").isSome then " (eds)" else "")
  let mut ps : List Piece := [.t s!"{who} ({e.year}). "]
  let title := (g "title").getD "(untitled)"
  let pages := (g "pages").map (fun p => s!"pp. {p}")
  let series := match g "series", g "volume" with
    | some s, some v => some s!"{s} {v}"
    | some s, Option.none => some s
    | _, _ => none
  let joinC (xs : List (Option String)) := ", ".intercalate (xs.filterMap id)
  match e.type with
  | "article" =>
    ps := ps ++ [.t (endDot title ++ " "), .em ((g "journal").getD "")]
    let vol := (g "volume").getD ""
    let num := ((g "number").map (s!"({·})")).getD ""
    let rest := joinC [if vol.isEmpty then none else some (vol ++ num), pages]
    ps := ps ++ [.t (if rest.isEmpty then ". " else ", " ++ rest ++ ". ")]
  | "book" =>
    ps := ps ++ [.em (endDot title), .t (" " ++ joinC [(g "edition").map (· ++ " edition"), series, g "publisher"] ++ ". ")]
  | "techreport" =>
    ps := ps ++ [.t (endDot title ++ " Technical report " ++ joinC [g "number", g "institution"] ++ ". ")]
  | "phdthesis" =>
    ps := ps ++ [.em (endDot title), .t (" PhD thesis, " ++ joinC [g "school"] ++ ". ")]
  | "mastersthesis" =>
    -- the F0 paper v0.7 (Melzer2020); its URL is linked when it has no DOI
    ps := ps ++ [.em (endDot title), .t (" " ++ ((g "type").getD "Master's thesis") ++ ", " ++
      joinC [g "school"] ++ ". ")]
    if (e.get "doi").isNone then
      if let some u := e.get "url" then ps := ps ++ [.url u]
  | "misc" | "unpublished" =>
    let arx := (e.get "eprint").map (s!"arXiv:{·}")
    let rest := joinC [arx, g "howpublished", g "publisher"]
    ps := ps ++ [.t (endDot title ++ (if rest.isEmpty then " " else " " ++ rest ++ ". "))]
  | _ =>  -- inproceedings, incollection, inbook
    let venue := (g "booktitle").getD ((g "journal").getD "")
    ps := ps ++ [.t (endDot title ++ " In "), .em venue,
      .t ((let r := joinC [series, pages, g "publisher"]; if r.isEmpty then ". " else ", " ++ r ++ ". "))]
  if let some d := e.get "doi" then ps := ps ++ [.doi d]
  return ps

def Piece.toTerm : Piece → MacroM Term
  | .t s => ``(Verso.Doc.Inline.text $(quote s))
  | .em s => ``(Verso.Doc.Inline.emph #[Verso.Doc.Inline.text $(quote s)])
  | .doi d =>
    let url := "https://doi.org/" ++ d
    `(Verso.Doc.Inline.other {CLPPaper.Cite.Inline.extLink with data := Lean.ToJson.toJson (($(quote url), $(quote ("doi:" ++ d))) : String × String)} #[])
  | .url u =>
    let txt := if u.startsWith "https://" then (u.drop 8).toString
      else if u.startsWith "http://" then (u.drop 7).toString else u
    `(Verso.Doc.Inline.other {CLPPaper.Cite.Inline.extLink with data := Lean.ToJson.toJson (($(quote u), $(quote txt)) : String × String)} #[])

block_extension Block.refList where
  traverse _ _ _ := pure none
  toTeX := some <| fun _ goB _ _ blocks => do
    let items ← blocks.mapM goB
    pure <| .seq (#[.raw "\n\\par\\begingroup\\small\\raggedright\\setlength{\\parindent}{0pt}\\setlength{\\parskip}{3pt}\\everypar{\\hangindent=1.5em\\hangafter=1}\n"] ++
      items.map (fun i => TeX.seq #[i, .raw "\\par\n"]) ++ #[.raw "\\endgroup\n"])
  toHtml := some <| fun _ goB _ _ blocks => do
    pure (Html.tag "div" #[("class", "references")] (.seq (← blocks.mapM goB)))
  extraCss := [".references p { padding-left: 1.5em; text-indent: -1.5em; margin: 0.35em 0; }"]

structure NoArgs where
  ok : Unit := ()

instance {m : Type → Type} [Monad m] : FromArgs NoArgs m := ⟨(fun _ => {}) <$> .done⟩

/-- Every work cited in the imported modules, sorted by the authors' surnames
(a sole author before the same author with others), then year and key. -/
@[block_command]
def references : BlockCommandOf NoArgs
  | _ => do
    let keys := (citedExt.getState (← getEnv)).toList.eraseDups
    let es ← keys.mapM fun k => do
      let some e ← (lookupKey k : IO _) | throwError s!"{k} is not in {bibPath}"
      return e
    let sortKey (e : Entry) :=
      ("\x01".intercalate (e.authorsOrEditors.map (·.1)) ++ "\x00" ++ e.year ++ "\x00" ++ e.key).toLower
    let es := (es.toArray.qsort (fun a b => sortKey a < sortKey b)).toList
    let paras ← es.mapM fun e => do
      let inls ← liftMacroM (e.pieces.mapM Piece.toTerm)
      ``(Verso.Doc.Block.para #[$(inls.toArray),*])
    ``(Verso.Doc.Block.other Block.refList #[$(paras.toArray),*])

end CLPPaper.Cite
