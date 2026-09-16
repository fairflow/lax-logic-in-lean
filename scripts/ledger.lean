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
  deriving Inhabited

def Row.toJson (r : Row) : String :=
  let axs := String.intercalate "," (r.axioms.toList.map fun a => "\"" ++ esc a.toString ++ "\"")
  "{\"module\":\"" ++ esc r.module.toString ++
  "\",\"decl\":\"" ++ esc r.decl.toString ++
  "\",\"kind\":\"" ++ r.kind ++
  "\",\"sorry\":" ++ (if r.sorried then "true" else "false") ++
  ",\"native\":" ++ (if r.native then "true" else "false") ++
  ",\"axioms\":[" ++ axs ++ "]}"

/-- `Name.lt` on the pair, so the file is deterministic. -/
def Row.lt (a b : Row) : Bool :=
  if a.module == b.module then Name.lt a.decl b.decl else Name.lt a.module b.module

/-- Declarations we never report.  `Audit.isNoise` (`Meta/Sweep.lean`) defines
what "every declaration of the estate" means for the sweep gate; the ledger is
deliberately STRICTER, adding `isInternalDetail`, because Lean's generated
equation and matcher lemmas (`f.eq_3`, `f.match_1`) carry no content of their
own — they inherit their definition's axioms — and would swamp every count.
The sweep still checks them; nothing is exempted from the gate by this. -/
def skip? (n : Name) : Bool :=
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
      rows := rows.push { module := modName, decl := n, kind := kindOf ci,
                          axioms := axs, sorried, native }
  return rows.qsort Row.lt

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
  let h ← IO.FS.Handle.mk outFile .write
  for r in rows do
    h.putStrLn r.toJson
  return 0
