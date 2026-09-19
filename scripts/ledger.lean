/-
The proof-status ledger: for every declaration of the named modules, its kind,
its axiom set, and the two taints that matter here (`sorryAx`, and the
`native_decide` triple).

    lake env lean --run scripts/ledger.lean <modules-file> <out.jsonl>

`<modules-file>` holds one module name per line (`LaxLogic.PLL.ND.NDCore`), and
every one of them must already be built — this reads `.olean`s, it does not
elaborate.  Output is one JSON object per line, sorted by module then
declaration, so `git diff` on it is readable and `scripts/check-ledger.sh` can
compare two runs with `diff`.

Only `Lean.collectAxioms` is trusted for the axiom set (CLAUDE.md rule 1: it is
the only sound oracle; `#print axioms` is the same function).
-/
import Lean

open Lean

namespace Ledger

/-- The fixed axioms that mark a proof as compiler-trusting rather than
kernel-checked. -/
def nativeAxioms : Array Name :=
  #[``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- Is this axiom a `native_decide` trust?  Under Lean 4.31 a `native_decide`
call does NOT cite `Lean.ofReduceBool` directly: it mints a fresh axiom of its
own, named after the declaration, e.g.

    BeliefLax.chain4_card._native.native_decide.ax_1_1

so a check against the three fixed names alone silently passes such a proof.
Both forms count. -/
def nativeAxiom? (a : Name) : Bool :=
  nativeAxioms.contains a || (a.toString.splitOn "native_decide").length > 1

/-- A declaration's kind, as one short tag. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

/-- Escape a string for JSON.  Declaration names can contain `"`, `\` and
unicode; unicode is emitted as UTF-8, which `json.loads` accepts. -/
def esc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | c    => if c.toNat < 0x20 then
                  let ds := String.ofList (Nat.toDigits 16 c.toNat)
                  "\\u" ++ "".pushn '0' (4 - ds.length) ++ ds
                else c.toString

/-- One ledger row. -/
structure Row where
  module  : Name
  decl    : Name
  kind    : String
  axioms  : Array Name
  sorried : Bool
  native  : Bool
  priv    : Bool := false
  deriving Inhabited

def Row.toJson (r : Row) : String :=
  let axs := String.intercalate "," (r.axioms.toList.map fun a => "\"" ++ esc a.toString ++ "\"")
  "{\"module\":\"" ++ esc r.module.toString ++
  "\",\"decl\":\"" ++ esc r.decl.toString ++
  "\",\"kind\":\"" ++ r.kind ++
  "\",\"sorry\":" ++ (if r.sorried then "true" else "false") ++
  ",\"native\":" ++ (if r.native then "true" else "false") ++
  (if r.priv then ",\"private\":true" else "") ++
  ",\"axioms\":[" ++ axs ++ "]}"

/-- `Name.lt` on the pair, so the file is deterministic. -/
def Row.lt (a b : Row) : Bool :=
  if a.module == b.module then Name.lt a.decl b.decl else Name.lt a.module b.module

/-- Is ANY component of `n` one Lean generates from another declaration's name?
`Name.isInternalDetail` asks that of the LAST component and then falls back to
`isInternalOrNum` on the prefix, which answers `false` for
`f.match_1.splitter`: `splitter` is not a generated form and no component of
`f.match_1` starts with `_`.  Used only on the private branch of `skip?`. -/
def generatedName? : Name → Bool
  | .anonymous   => false
  | m@(.str p _) => m.isInternalDetail || generatedName? p
  | m@(.num p _) => m.isInternalDetail || generatedName? p

/-- Declarations we never report.  `Audit.isNoise` (`Meta/Sweep.lean`) defines
what "every declaration of the estate" means for the sweep gate; the ledger is
deliberately STRICTER, adding `isInternalDetail`, because Lean's generated
equation and matcher lemmas (`f.eq_3`, `f.match_1`) carry no content of their
own — they inherit their definition's axioms — and would swamp every count.
The sweep still checks them; nothing is exempted from the gate by this.

A PRIVATE NAME IS TESTED UNDER ITS USER NAME, and this matters.  Lean mangles
`private theorem foo` in module `M` to `_private.M.0.foo`
(`Lean/PrivateName.lean`, `mkPrivateNameCore`), and two of the five tests then
fire on it for reasons that have nothing to do with the declaration:
`isInternal` matches because the component `_private` starts with `_`, and
`isInternalDetail` matches because the `.num _ 0` component returns `true`
outright.  Testing the mangled name therefore dropped every `private`
declaration in the repository — counted from source inside
`docs/ledger-modules.txt` alone, 366 declarations, 225 of them theorems, in 73
modules, none of which the gate could see.  That is against this docstring's
own stated rationale: a `private theorem` is hand-written mathematics with its
own proof and its own axiom set, not a generated lemma inheriting one.  Found
from the other end by `docs/dangling-triage-2026-09-18.md` §4c, where seven
prose citations dangled for no other reason.

The public branch is left EXACTLY as it was, and the asymmetry is deliberate.
Un-mangling also exposes the generated children of private parents, and Lean
emits a matcher's splitter `private`: testing the user name alone admitted 706
`f.match_1.splitter` rows, which are the very class the paragraph above
excludes.  The private branch therefore tests every component, not just the
last — `isInternalDetail` tests the last component and then falls back to
`isInternalOrNum` on the prefix, which is `false` for `f.match_1.splitter`.
Applying the stronger test to public names too would be right by the same
reasoning, and would drop 111 recorded `f.match_N.congr_eq_M` rows; that is the
elaborator-plumbing question already open for Matthew in
`docs/proof-simplification-plan-2026-09-16.md` §"For Matthew", so this change
does not answer it. -/
def skip? (n : Name) : Bool :=
  if isPrivateName n then
    let u := privateToUserName n
    u.isInternal
      || generatedName? u
      || u.isImplementationDetail
      || (`_example).isPrefixOf u
      || n.hasMacroScopes
  else
    n.isInternal
      || n.isInternalDetail
      || n.isImplementationDetail
      || (`_example).isPrefixOf n
      || n.hasMacroScopes

end Ledger

open Ledger in
/-- The rows for the named modules.  Enumeration is module-indexed, as in
`Audit.estateConsts` (`Meta/Sweep.lean`): walking `env.constants` instead would
walk the whole import closure, Mathlib included. -/
def rowsFor (mods : Array Name) : CoreM (Array Row) := do
  let env ← getEnv
  let wanted : Std.HashSet Name := mods.foldl (·.insert ·) {}
  let mut rows : Array Row := #[]
  for i in [0 : env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    unless wanted.contains modName do continue
    let some data := env.header.moduleData[i]? | continue
    for n in data.constNames do
      if skip? n then continue
      let some ci := env.find? n | continue
      let axs ← collectAxioms n
      let sorried := axs.contains ``sorryAx
      let native := axs.any nativeAxiom?
      -- A private declaration is recorded under the name the PROSE cites, not
      -- under its `_private.M.0.…` mangling, with the flag to say which it is.
      rows := rows.push { module := modName, decl := privateToUserName n,
                          kind := kindOf ci, axioms := axs, sorried, native,
                          priv := isPrivateName n }
  return rows.qsort Row.lt

open Ledger in
/-- `scripts/ledger-diff.py` keys on `(module, decl)` in a dict, so two rows
sharing a key would silently overwrite one another and the survivor's axioms
would then read as drift.  Un-mangling private names makes that possible for
the first time: a module may hold both `private theorem foo` and `theorem foo`.
Report it rather than let it surface later as a phantom change. -/
def duplicateKeys (rows : Array Row) : Array (Name × Name) := Id.run do
  let mut dups := #[]
  for i in [1 : rows.size] do
    let a := rows[i - 1]!
    let b := rows[i]!
    if a.module == b.module && a.decl == b.decl then
      dups := dups.push (a.module, a.decl)
  return dups

open Ledger in
def main (args : List String) : IO UInt32 := do
  let [modsFile, outFile] := args
    | IO.eprintln "usage: ledger.lean <modules-file> <out.jsonl>"; return 1
  let mods := (← IO.FS.lines modsFile).filterMap fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then none else some l.toName
  IO.eprintln s!"ledger: importing {mods.size} modules"
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024)
  let ctx : Core.Context := { fileName := "<ledger>", fileMap := default }
  let (rows, _) ← (rowsFor mods).toIO ctx { env := env }
  IO.eprintln s!"ledger: {rows.size} declarations reported"
  let nPriv := rows.filter (·.priv) |>.size
  if nPriv != 0 then
    IO.eprintln s!"ledger: {nPriv} of them `private`, recorded under the user name"
  for (m, d) in duplicateKeys rows do
    IO.eprintln s!"ledger: WARNING duplicate key {m}::{d} — the diff keys on this pair"
  let h ← IO.FS.Handle.mk outFile .write
  for r in rows do
    h.putStrLn r.toJson
  return 0
