/-
# Axiom auditing: where does an axiom actually enter?

`#print axioms` says *whether* a declaration depends on `Classical.choice`.
It does not say *why*, and finding out by hand is slow: the FRJ campaign
spent most of a day locating four sources, three of which turned out to
be tools rather than mathematics (Mathlib's `Finset` operations at
definition level, the `tauto` tactic, and — least expected — `simp`).

This module answers the "why".

* `#choice_path f` — the shortest dependency chain from `f` down to
  `Classical.choice`. Read it from the top: the first name you do not
  own is where your code hands the axiom off to the library.
* `#choice_sources f` — the direct dependencies of `f` that are tainted,
  i.e. which sub-lemma to attack next.
* `#axiom_path ax f` — the same, for any axiom (`sorryAx`, `propext`, …).
* `#axiom_pin f` — emit the `#guard_msgs`-wrapped `#print axioms` block
  for pasting into an audit module, so pins are generated rather than
  retyped.

Zero imports beyond `Lean`: this must be usable from any module of any
project without dragging Mathlib in.
-/
import Lean

open Lean Elab Command

namespace Audit

/-- The constants a declaration mentions, in its type and its value. -/
def declDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci => ci.getUsedConstantsAsSet.toArray

/-- Does `n` depend on the axiom `ax`?  Uses `collectAxioms`, which is
the same oracle `#print axioms` uses — the only sound one. -/
def dependsOn (ax : Name) (n : Name) : CommandElabM Bool := do
  let axs ← collectAxioms n
  return axs.contains ax

/-- Breadth-first search for the shortest chain from `start` to `ax`,
traversing only tainted constants.

Pruning by taintedness is sound *and* is what makes this fast: if `d`
does not depend on `ax`, no path through `d` can reach it, so the whole
subtree is skipped. -/
partial def searchPath (ax : Name) (queue : Array (Name × List Name))
    (visited : NameSet) : CommandElabM (Option (List Name)) := do
  if queue.isEmpty then return none
  let (n, path) := queue[0]!
  if n == ax then return some path.reverse
  let env ← getEnv
  let mut q := queue.extract 1 queue.size
  let mut vis := visited
  for d in declDeps env n do
    unless vis.contains d do
      vis := vis.insert d
      if ← dependsOn ax d then
        q := q.push (d, d :: path)
  searchPath ax q vis

/-- The chain from `n` to `ax`, if there is one. -/
def axiomPath (ax : Name) (n : Name) : CommandElabM (Option (List Name)) := do
  if !(← dependsOn ax n) then return none
  searchPath ax #[(n, [n])] (NameSet.empty.insert n)

/-- The direct dependencies of `n` that are themselves tainted. -/
def taintedDeps (ax : Name) (n : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for d in declDeps env n do
    if d != n then
      if ← dependsOn ax d then out := out.push d
  return out.qsort Name.lt

private def resolve (id : Syntax) : CommandElabM Name := do
  let cs ← liftCoreM <| realizeGlobalConstWithInfos id
  match cs with
  | [n] => return n
  | n :: _ => return n
  | [] => throwError "unknown constant"

/-- Which module a constant was declared in; `none` means the current
file.  This is what tells you, at a glance, where your own code stops and
the library begins. -/
def originOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | none => "«this file»"
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => toString m
      | none => "?"

private def reportPath (ax n : Name) : CommandElabM Unit := do
  match ← axiomPath ax n with
  | none => logInfo m!"'{n}' does not depend on '{ax}'"
  | some path =>
      let env ← getEnv
      let mut msg := m!"'{n}' reaches '{ax}' by:"
      for (c, i) in path.zipIdx do
        msg := msg ++ m!"\n  {i}. {MessageData.ofConstName c}    [{originOf env c}]"
      msg := msg ++ m!"\n\nRead the modules: where they stop being yours is where the "
        ++ m!"axiom enters from the library."
      logInfo msg

/-- `#axiom_path Classical.choice foo` — the shortest chain from `foo` to
the given axiom. -/
syntax (name := axiomPathCmd) "#axiom_path " ident ident : command

@[command_elab axiomPathCmd] def elabAxiomPath : CommandElab
  | `(#axiom_path $ax $id) => do
      reportPath (← resolve ax) (← resolve id)
  | _ => throwUnsupportedSyntax

/-- `#choice_path foo` — the shortest chain from `foo` to
`Classical.choice`. -/
syntax (name := choicePathCmd) "#choice_path " ident : command

@[command_elab choicePathCmd] def elabChoicePath : CommandElab
  | `(#choice_path $id) => do
      reportPath ``Classical.choice (← resolve id)
  | _ => throwUnsupportedSyntax

/-- `#choice_sources foo` — the direct dependencies of `foo` that carry
`Classical.choice`.  Attack these, then re-run. -/
syntax (name := choiceSourcesCmd) "#choice_sources " ident : command

@[command_elab choiceSourcesCmd] def elabChoiceSources : CommandElab
  | `(#choice_sources $id) => do
      let n ← resolve id
      if !(← dependsOn ``Classical.choice n) then
        logInfo m!"'{n}' is choice-free"
      else
        let ds ← taintedDeps ``Classical.choice n
        if ds.isEmpty then
          logInfo m!"'{n}' uses 'Classical.choice' directly (no tainted dependency)"
        else
          let mut msg := m!"'{n}' is tainted through {ds.size} direct dependencies:"
          for d in ds do
            msg := msg ++ m!"\n  {MessageData.ofConstName d}"
          logInfo msg
  | _ => throwUnsupportedSyntax

/-- `#axiom_pin foo` — emit the `#guard_msgs` block that pins `foo`'s
axioms, ready to paste into an audit module.  Generated, never retyped:
a transcription slip in a pin is a silent hole in the mandate. -/
syntax (name := axiomPinCmd) "#axiom_pin " ident : command

@[command_elab axiomPinCmd] def elabAxiomPin : CommandElab
  | `(#axiom_pin $id) => do
      let n ← resolve id
      let axs ← collectAxioms n
      let body :=
        if axs.isEmpty then
          s!"'{n}' does not depend on any axioms"
        else
          let names := (axs.qsort Name.lt).toList.map toString
          s!"'{n}' depends on axioms: [{String.intercalate ", " names}]"
      logInfo m!"/-- info: {body} -/\n#guard_msgs in\n#print axioms {n}"
  | _ => throwUnsupportedSyntax

/-! ## Choice-free search

`#print axioms` audits a lemma you already chose; the recurring loss is
upstream of that — REACHING for a library lemma that smuggles
`Classical.choice` into an otherwise clean def, and finding out only at
pin time (`List.eq_nil_iff_forall_not_mem` was the 2026-09-01 instance).
`#cf_search` answers "give me the choice-free one" directly. -/

/-- Every pattern occurs in `s` (empty patterns match nothing). -/
private def matchesAll (pats : List String) (s : String) : Bool :=
  pats.all (fun p => !p.isEmpty && (s.splitOn p).length > 1)

/-- `#cf_search "pat1" "pat2" …` — every environment constant whose full
name contains all the patterns AND whose axiom closure avoids
`Classical.choice`, each with its module of origin.  Tainted matches are
counted in the header, never silently dropped; an overflow past the
display cap is reported as a count. -/
syntax (name := cfSearchCmd) "#cf_search " str+ : command

@[command_elab cfSearchCmd] def elabCfSearch : CommandElab
  | `(#cf_search $pats*) => do
      let ps := pats.toList.map (·.getString)
      let env ← getEnv
      let mut cands := #[]
      for (n, _) in env.constants.toList do
        unless n.isInternal do
          if matchesAll ps n.toString then
            cands := cands.push n
      let sorted := cands.qsort Name.lt
      let mut clean := #[]
      let mut tainted : Nat := 0
      for n in sorted do
        if ← dependsOn ``Classical.choice n then
          tainted := tainted + 1
        else
          clean := clean.push n
      let cap := 40
      let shown := clean.extract 0 cap
      let mut msg :=
        m!"{clean.size} choice-free matches ({tainted} tainted suppressed):"
      for n in shown do
        msg := msg ++ m!"\n  {MessageData.ofConstName n}    [{originOf env n}]"
      if clean.size > cap then
        msg := msg ++ m!"\n  … {clean.size - cap} more not shown"
      logInfo msg
  | _ => throwUnsupportedSyntax

end Audit
