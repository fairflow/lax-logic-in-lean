/-
# Estate-level axiom sweep

`#axioms_within` (`Meta/Audit.lean`) bounds ONE declaration, and it is
opt-in.  That is its limit: a declaration carrying no bound is not
checked, so the absence of an alarm is not evidence.  Omitting the guard
is exactly how a `sorry` travels unnoticed, and it is why "everything in
this library is sorry-free" cannot be established by pins, however many
of them there are.

This module sweeps an ESTATE: every declaration of every module named,
whether or not anyone wrote a bound.

    #axiom_sweep [LaxLogic, FRJ] allowing [propext, Classical.choice, Quot.sound]

Membership is by MODULE NAME PREFIX, which is the same thing the
`lakefile.toml` globs already declare — not by directory convention, and
not by where a file happens to sit on disk.  A module is in the estate
because a library lists it, and the sweep is told which libraries it is
auditing.

The sweep reads `env.header.moduleData`, so it visits only the modules
named; it does not scan the whole environment.  `collectAxioms` is the
oracle throughout, the same one `#print axioms` uses.

What the sweep does NOT check: that a statement says anything.  A vacuous
theorem passes every axiom test there is.
-/
import Lean

open Lean Elab Command

namespace Audit

/-- Declarations Lean generates for its own bookkeeping.  They are not
mathematical content and would swamp the report. -/
private def isNoise (n : Name) : Bool :=
  n.isInternal
    || n.isImplementationDetail
    || (`_example).isPrefixOf n

/-- Every constant declared by a module whose name has one of `prefixes`
as a prefix, paired with the module it came from. -/
def estateConsts (env : Environment) (prefixes : Array Name) :
    Array (Name × Name) := Id.run do
  let mut out := #[]
  for i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if prefixes.any (fun p => p.isPrefixOf m) then
      match env.header.moduleData[i]? with
      | none => pure ()
      | some data =>
          for n in data.constNames do
            unless isNoise n do
              out := out.push (n, m)
  return out

/-- `#axiom_sweep [L₁, …] allowing [a₁, …]` — check EVERY declaration of
every module under one of the listed prefixes against the allowance.

Fails the build listing each declaration that escapes it, so this belongs
in a module that the estate's own lake target builds.

An `except` list names modules held OUT of the estate by hand.  It is
recorded debt, not a silencer: each entry is one line in a file under
review, it says which module is not meeting the bar, and every OTHER
declaration in the estate is still swept.  Widening `allowing` to cover a
known violation would instead disable the check for everything, which is
how a gate stops meaning anything. -/
syntax (name := axiomSweepCmd)
  "#axiom_sweep " "[" ident,* "]"
  (" except " "[" ident,* "]")?
  " allowing " "[" ident,* "]" : command

private def resolveIdent (id : Syntax) : CommandElabM Name := do
  match ← liftCoreM <| realizeGlobalConstWithInfos id with
  | n :: _ => return n
  | [] => throwError "unknown constant"

@[command_elab axiomSweepCmd] def elabAxiomSweep : CommandElab
  | `(#axiom_sweep [$mods,*] $[except [$exc,*]]? allowing [$axs,*]) => do
      let env ← getEnv
      let prefixes := mods.getElems.map (fun m => m.getId)
      -- Module names, NOT constants: resolved by `getId`, never by
      -- `realizeGlobalConstWithInfos`, which would fail on a module.
      let excluded : Array Name := match exc with
        | some e => e.getElems.map (fun m => m.getId)
        | none => #[]
      let allowed ← axs.getElems.mapM resolveIdent
      let all := estateConsts env prefixes
      if all.isEmpty then
        throwError "sweep matched no modules; prefixes were \
{prefixes.toList.map toString}.  Is the estate imported by this file?"
      let targets := all.filter (fun (_, m) => !excluded.contains m)
      let held := all.size - targets.size
      unless excluded.isEmpty do
        logInfo m!"axiom sweep: {held} declarations held out by `except` \
({excluded.size} modules: {String.intercalate ", " (excluded.toList.map toString)})"
      let mut bad : Array (Name × Name × List String) := #[]
      for (n, m) in targets do
        let actual ← collectAxioms n
        let extra := actual.filter (fun a => !allowed.contains a)
        unless extra.isEmpty do
          bad := bad.push (n, m, (extra.qsort Name.lt).toList.map toString)
      if bad.isEmpty then
        logInfo m!"axiom sweep: {targets.size} declarations, all within \
[{String.intercalate ", " ((allowed.qsort Name.lt).toList.map toString)}]"
      else
        let mut msg := m!"axiom sweep: {bad.size} of {targets.size} \
declarations escape the allowance \
[{String.intercalate ", " ((allowed.qsort Name.lt).toList.map toString)}]:"
        for (n, m, extra) in bad.extract 0 (min bad.size 40) do
          msg := msg ++ m!"\n  {n}  [{m}]  → {String.intercalate ", " extra}"
        if bad.size > 40 then
          msg := msg ++ m!"\n  … and {bad.size - 40} more"
        throwError msg
  | _ => throwUnsupportedSyntax

end Audit
