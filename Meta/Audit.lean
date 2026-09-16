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

/-! ## Bounded pins: declare what is ACCEPTABLE, not what is used

`#guard_msgs in #print axioms f` compares a rendered *string*, so it fails
in both directions.  A declaration that gets CLEANER breaks its own pin —
on 2026-09-04 that was eight of the ten stale pins in `wip/`, every one of
them an improvement nobody had recorded.  Exact match also dates badly:
the pin has to be rewritten whenever a proof is retuned, whether or not
anything of interest changed.

`#axioms_within` states an upper bound instead.  The declared axioms are
the ones that would be ACCEPTABLE; they need not all be used, and using
fewer is never a failure.  The check fires only when an axiom appears that
was not declared — the direction that actually carries information.

    #axioms_within foo [propext, Quot.sound]

`sorryAx` gets no special case.  A file built against a harness that
legitimately carries sorries writes them into the bound:

    #axioms_within partial_result [propext, sorryAx]

which is explicit at the site, greppable across the tree, and needs no
directory convention to interpret.

What a bound cannot do is police a declaration that carries no bound at
all: bounds are opt-in, so silence is not evidence.  Enforcing "no
`sorryAx` anywhere in this estate" therefore needs a sweep over every
declaration in a named library, independent of whether anyone wrote a
pin.  That sweep is NOT BUILT as of 2026-09-04; until it is, a
sorry-free claim about a whole library rests on `lake build` plus the
bounds that happen to exist, which is weaker than it sounds. -/

/-- `#axioms_within foo [propext, Quot.sound]` — succeeds iff every axiom
`foo` actually depends on appears in the declared list.  Unused declared
axioms are fine: the list is a permission, not a transcript. -/
syntax (name := axiomsWithinCmd) "#axioms_within " ident "[" ident,* "]" : command

@[command_elab axiomsWithinCmd] def elabAxiomsWithin : CommandElab
  | `(#axioms_within $id [$axs,*]) => do
      let n ← resolve id
      let allowed ← axs.getElems.mapM resolve
      let actual ← collectAxioms n
      let extra := actual.filter (fun a => !allowed.contains a)
      unless extra.isEmpty do
        let names := (extra.qsort Name.lt).toList.map toString
        let decl := (allowed.qsort Name.lt).toList.map toString
        throwError m!"'{n}' depends on {String.intercalate ", " names}, \
which the bound does not allow.\n  declared: [{String.intercalate ", " decl}]\n\
  Locate the entry with:  #axiom_path {names.headD "propext"} {n}"
  | _ => throwUnsupportedSyntax

/-- `#axioms_within_pin foo` — emit the `#axioms_within` line for `foo`'s
CURRENT axioms, ready to paste.  Generated, never retyped.  Widen the
emitted list by hand if a bound looser than today's fact is wanted. -/
syntax (name := axiomsWithinPinCmd) "#axioms_within_pin " ident : command

@[command_elab axiomsWithinPinCmd] def elabAxiomsWithinPin : CommandElab
  | `(#axioms_within_pin $id) => do
      let n ← resolve id
      let axs ← collectAxioms n
      let names := (axs.qsort Name.lt).toList.map toString
      logInfo m!"#axioms_within {n} [{String.intercalate ", " names}]"
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
