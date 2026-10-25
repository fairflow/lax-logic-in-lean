/-
The running header of a paper (Matthew, 2026-10-25): its number, a short
memorable name, the version and the build date,

    III:F0Lattice 0.5 · 25 Oct 2026

and, in small type in the title block, the build stamp of `CLPPaper/Src.lean`
(`Version 0.5 · branch@sha · built …`), which until v0.4.1 of the F0 paper and
v0.2 of the semantics paper was the running header.  A paper declares its
number and name in one place, the first line of its `Paper.lean`:

    {paperStamp (number := "III") (name := "F0Lattice")}`F0Paper/VERSION`

TeX: the role defines `\versoRunningHead` and `\versoBuildStamp` and prints
nothing; `scripts/verso-tex-pdf.sh` copies both definitions into the preamble,
sets the running head in every page header and the stamp as the date line of
the title page.  HTML: the running head, and the stamp beneath it in small
type.  (The CLP paper keeps `{buildStamp}`, whose stamp is its header.)
-/
import Lean
import VersoManual
import CLPPaper.Src

open Lean Elab
open Lean.Doc.Syntax
open Verso Doc Elab Genre Manual ArgParse
open Verso.Output Html

namespace PaperKit.Stamp

/-- The build date as `25 Oct 2026`, English month names whatever the locale. -/
def buildDate : IO String := do
  let o ← IO.Process.output {cmd := "date", args := #["+%d %b %Y"], env := #[("LC_ALL", some "C")]}
  let s := o.stdout.trimAscii.copy
  pure (if s.startsWith "0" then (s.drop 1).copy else s)

/-- (running head, build stamp) -/
abbrev StampData := String × String

inline_extension Inline.paperStamp where
  traverse _ _ _ := pure none
  toTeX := some <| fun _ _ data _ => do
    match FromJson.fromJson? (α := StampData) data with
    | .error e => do reportError s!"paperStamp: bad data: {e}"; pure .empty
    | .ok (head, stamp) =>
      pure <| .seq #[.raw "\\gdef\\versoRunningHead{", .text head, .raw "}",
        .raw "\\gdef\\versoBuildStamp{", .text stamp, .raw "}"]
  toHtml := some <| fun _ _ data _ => do
    match FromJson.fromJson? (α := StampData) data with
    | .error e => do reportError s!"paperStamp: bad data: {e}"; pure .empty
    | .ok (head, stamp) =>
      pure {{ <span class="paper-head">{{head}}</span><span class="paper-stamp">{{stamp}}</span> }}
  extraCss := [r#"
.paper-head { display: block; font-family: sans-serif; font-size: 100%; color: #333; }
.paper-stamp { display: block; font-family: sans-serif; font-size: 75%; color: #777; }
"#]

structure StampConfig where
  number : String
  name : String

instance : FromArgs StampConfig DocElabM :=
  ⟨StampConfig.mk <$> .named `number .string false <*> .named `name .string false⟩

/-- `{paperStamp (number := "III") (name := "F0Lattice")}`F0Paper/VERSION``: the
running head `III:F0Lattice 0.5 · 25 Oct 2026` from the arguments, the version
file and the clock, and the build stamp from `CLPPaper.buildStampText`, all
read at document build time. -/
@[role]
def paperStamp : RoleExpanderOf StampConfig
  | cfg, #[arg] => do
    let `(inline|code( $file:str )) := arg
      | throwErrorAt arg "Expected a code literal with the version file's path"
    let version := (← IO.FS.readFile file.getString).trimAscii.copy
    let date ← buildDate
    let head := s!"{cfg.number}:{cfg.name} {version} · {date}"
    let stamp ← CLPPaper.buildStampText file.getString
    `(Verso.Doc.Inline.other {Inline.paperStamp with data := ToJson.toJson (($(quote head), $(quote stamp)) : StampData)}
        #[Verso.Doc.Inline.text $(quote head)])
  | _, _ => throwError "Expected exactly one code literal"

end PaperKit.Stamp
