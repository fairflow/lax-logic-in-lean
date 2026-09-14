/-
A source link for a declaration: `{srcLink}`Full.Name`` renders
`LaxLogic/QLL/BodyCirc.lean:528` linked to that line of the file in the
repository on GitHub at the commit the document was built from.  HTML and
TeX (the TeX uses `\oldhref`, the unmodified `\href` that Verso's template
keeps before turning `\href` into a footnote).

Part of the verso-paper workflow (docs/verso-paper-workflow.md): the Lean
statement is *included* by `{docstring}` and *linked* by this role.
-/
import Lean
import Lean.DocString.Syntax
import VersoManual

open Lean Elab
open Lean.Doc.Syntax
open Verso Doc Elab Genre Manual ArgParse
open Verso.Output Html

namespace CLPPaper

/-- (repository-relative path, line, URL) -/
abbrev SrcLoc := String × Nat × String

inline_extension Inline.srcLink where
  traverse _ _ _ := pure none
  toTeX := some <| fun _ _ data _ => do
    match FromJson.fromJson? (α := SrcLoc) data with
    | .error e => do reportError s!"srcLink: bad data: {e}"; pure .empty
    | .ok (path, line, url) =>
      pure <| .seq #[.raw "{\\small ", .raw "\\oldhref{", .raw url, .raw "}{\\texttt{",
        .text s!"{path}:{line}", .raw "}}}"]
  toHtml := some <| fun _ _ data _ => do
    match FromJson.fromJson? (α := SrcLoc) data with
    | .error e => do reportError s!"srcLink: bad data: {e}"; pure .empty
    | .ok (path, line, url) =>
      pure {{ <span class="src-link"><a href={{url}} title="the declaration in the repository">
        <code>{{path}}":"{{toString line}}</code></a></span> }}
  extraCss := [".src-link { font-size: 85%; opacity: 0.8; } .src-link a { text-decoration: none; }"]

structure SrcLinkConfig where
  ok : Unit := ()

instance {m : Type → Type} [Monad m] : FromArgs SrcLinkConfig m := ⟨(fun _ => {}) <$> .done⟩

/-- `git rev-parse HEAD` and the origin URL, read at document build time. -/
def gitInfo : IO (String × String) := do
  let sha ← IO.Process.output {cmd := "git", args := #["rev-parse", "HEAD"]}
  let url ← IO.Process.output {cmd := "git", args := #["remote", "get-url", "origin"]}
  let repo := url.stdout.trimAscii.copy
  let repo := if repo.endsWith ".git" then (repo.dropEnd 4).copy else repo
  let repo := if repo.startsWith "git@github.com:" then
    "https://github.com/" ++ (repo.drop "git@github.com:".length).copy else repo
  pure (sha.stdout.trimAscii.copy, repo)

@[role]
def srcLink : RoleExpanderOf SrcLinkConfig
  | _, #[arg] => do
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected a code literal with the declaration name"
    let identStx := mkIdentFrom arg name.getString.toName (canonical := true)
    let n ← realizeGlobalConstNoOverloadWithInfo identStx
    let env ← getEnv
    let modName : Name := match env.getModuleIdxFor? n with
      | Option.some i => env.header.moduleNames[i.toNat]!
      | Option.none => env.mainModule
    let path := (modName.toString.replace "." "/") ++ ".lean"
    let line := ((← findDeclarationRanges? n).map (·.selectionRange.pos.line)).getD 1
    let (sha, repo) ← gitInfo
    let url := s!"{repo}/blob/{sha}/{path}#L{line}"
    `(Verso.Doc.Inline.other {Inline.srcLink with data := ToJson.toJson (($(quote path), $(quote line), $(quote url)) : SrcLoc)}
        #[Verso.Doc.Inline.code $(quote s!"{path}:{line}")])
  | _, _ => throwError "Expected exactly one code literal"

/-! ## The build stamp

`{buildStamp}`CLPPaper/VERSION`` renders "Version 0.3 · lax-obligations@0e190ea
· built 2026-09-14 17:05 BST" from the version file (hand-bumped for every
delivered draft), `git` (branch, short hash, `+` if the tree is dirty) and the
clock, all read at document build time.  Humans recognise version numbers,
machines need the hash; every generated document carries both. -/

def git (args : Array String) : IO String := do
  let o ← IO.Process.output {cmd := "git", args}
  pure o.stdout.trimAscii.copy

def buildStampText (versionFile : String) : IO String := do
  let version := (← IO.FS.readFile versionFile).trimAscii.copy
  let branch ← git #["rev-parse", "--abbrev-ref", "HEAD"]
  let hash ← git #["rev-parse", "--short", "HEAD"]
  let dirty := if (← git #["status", "--porcelain"]).isEmpty then "" else "+"
  let now ← IO.Process.output {cmd := "date", args := #["+%Y-%m-%d %H:%M %Z"]}
  pure s!"Version {version} · {branch}@{hash}{dirty} · built {now.stdout.trimAscii.copy}"

inline_extension Inline.buildStamp where
  traverse _ _ _ := pure none
  toTeX := some <| fun _ _ data _ => do
    match FromJson.fromJson? (α := String) data with
    | .error e => do reportError s!"buildStamp: bad data: {e}"; pure .empty
    | .ok t => pure <| .seq #[.raw "\\textsf{", .text t, .raw "}\\par"]
  toHtml := some <| fun _ _ data _ => do
    match FromJson.fromJson? (α := String) data with
    | .error e => do reportError s!"buildStamp: bad data: {e}"; pure .empty
    | .ok t => pure {{ <span class="build-stamp">{{t}}</span> }}
  extraCss := [".build-stamp { font-family: sans-serif; font-size: 90%; color: #555; }"]

@[role]
def buildStamp : RoleExpanderOf SrcLinkConfig
  | _, #[arg] => do
    let `(inline|code( $file:str )) := arg
      | throwErrorAt arg "Expected a code literal with the version file's path"
    let t ← buildStampText file.getString
    `(Verso.Doc.Inline.other {Inline.buildStamp with data := ToJson.toJson $(quote t)}
        #[Verso.Doc.Inline.text $(quote t)])
  | _, _ => throwError "Expected exactly one code literal"

end CLPPaper
