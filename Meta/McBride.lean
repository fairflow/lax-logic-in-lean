/-
# The McBride test, mechanised: `#mcbride`

**The rule** (McBride's "no green slime", as this repo's briefs state it —
`docs/frj-lax-handoff.md` §4.1, `docs/frj-lax-plan.md` §3.1): *every index
in a constructor's RETURN TYPE is a variable or a constructor form.*  A
computed term in a return-type index — `nf G (…)`, `rm (gAt G) F`,
`joinCtxAt …`, `St₁ ++ St₂` — is green slime: unification cannot invert
it, so every consumer of the family fights the kernel, case statements
must respell the computed term verbatim, and one paper-level proof case
multiplies into per-constructor clones.  The FRJ campaign measured the
bill: a 1,981-line soundness file, six ~130-line clone cases, for a
theorem the paper proves in one induction.

The plan called this test "checkable mechanically before any proof is
attempted".  It was never mechanised, and the constraint was then lost at
a documented decision point (see the `constraint-supersession-check`
skill).  This module is the mechanisation, in the house idiom of
`Meta/Audit.lean`: commands whose output is `#guard_msgs`-pinnable, so
the verdict is a standing BUILD-TIME gate, not prose.

* `#mcbride I₁ I₂ …` — report, per inductive family, which constructors
  fail the test and through which function heads.  Never errors; pin the
  output with `#guard_msgs` to freeze the current state (including a
  deliberately-slimy state, so any *new* slime is a build failure).
* `#mcbride! I₁ I₂ …` — the gate form: ERROR if any listed family has a
  slimy constructor.  For families that are meant to be clean from line
  one.
* `#mcbride_pin I₁ …` — emit the ready-to-paste `#guard_msgs` block, the
  `#axiom_pin` pattern: pins are generated, never retyped.

**What exactly is checked.**  For each constructor, the conclusion of its
type is the family applied to parameters and indices.  Parameters (the
first `numParams` arguments, uniform by construction) are exempt.  Each
INDEX expression is walked along its application spine:

* allowed heads: a telescope variable (applied or not — a variable head
  is a flex pattern, not a computed term), a CONSTRUCTOR of any inductive
  (its arguments are checked recursively — `.imp A B` and `.chain Z` are
  fine, `.circ (nf G l)` is not), an inductive TYPE, a sort, a literal;
* everything else — a `def`, a projection, a recursor, a matcher, a
  lambda-headed application — is slime.  The OUTERMOST offending head is
  reported and the subterm is not entered further: `rm (gAt G) F` reports
  `FRJ.rm`, which is how a human names the defect.

Hypotheses are deliberately NOT checked: the whole point of the
re-presentation discipline is that computation moves out of the indices
and INTO hypotheses (`hΓ : Γ ≐ joinCtxAt …`), where it may be arbitrary.

**Status: DRAFT, not yet elaborated** — written in a session without a
Lean toolchain.  Deliberately not imported from `Meta.lean`, so
`lake build Meta` is unaffected until it is wired.  First session with a
toolchain: elaborate this file, fix what the compiler objects to, add
`import Meta.McBride` to `Meta.lean`, then run `#mcbride_pin FRJ.FRJr
FRJ.FRJi` and paste the pins into `FRJ/Audit.lean`.  Expected first
verdict, from reading `FRJ/Calculus.lean` (the run is the authority, not
this comment): the nine join/axiom constructors of `FRJr` fail (`axR`
through `rm`; the six joins through their `joinCtx…`; `joinCirc`/
`joinCircP` through `joinCtxOr…`), and `axI`/`orI`/`impInI`/`axIC` of
`FRJi` fail (`nf`, `++`, `vacZoneA`); the `∧`/`⊃∈`/`◯∈`/`⊃∉`/`◯∉`
constructors pass.

Zero imports beyond `Lean`, as `Meta/Audit.lean`: usable from any module
of any project.
-/
import Lean

open Lean Elab Command Meta

namespace McBride

/-- The slimy heads of an index expression: the outermost non-variable,
non-constructor heads along the application spine.  Empty iff the
expression is a variable or a constructor form all the way down. -/
partial def slimeHeads (e : Expr) : MetaM (Array Name) := do
  let e := e.consumeMData
  match e.getAppFn with
  | .const n _ =>
      match (← getEnv).find? n with
      | some (.ctorInfo _) | some (.inductInfo _) =>
          let mut out := #[]
          for a in e.getAppArgs do
            out := out ++ (← slimeHeads a)
          return out
      | _ => return #[n]
  | .fvar _  => return #[]
  | .bvar _  => return #[]
  | .sort _  => return #[]
  | .mvar _  => return #[]
  | .lit _   => return #[]
  | _        => return #[`«non-atomic-head»]

/-- The failing indices of one constructor: `(position, offending heads)`
with positions 0-based among the INDICES (parameters exempt), heads
deduplicated in traversal order. -/
def checkCtor (numParams : Nat) (ctor : Name) :
    MetaM (Array (Nat × Array Name)) := do
  let ci ← getConstInfoCtor ctor
  forallTelescopeReducing ci.type fun _ concl => do
    let args := concl.getAppArgs
    let idxArgs := args.extract numParams args.size
    let mut out := #[]
    let mut pos := 0
    for a in idxArgs do
      let hs ← slimeHeads a
      let dedup := hs.foldl
        (fun acc n => if acc.contains n then acc else acc.push n) #[]
      unless dedup.isEmpty do
        out := out.push (pos, dedup)
      pos := pos + 1
    return out

/-- The full report for one inductive family, as a `String` so that the
same text serves `logInfo`, the error of `#mcbride!`, and the generated
pin verbatim.  Deterministic: constructors in declaration order, indices
in position order, heads in traversal order. -/
def reportFor (n : Name) : CommandElabM (Bool × String) := do
  liftTermElabM do
    let indVal ← getConstInfoInduct n
    let mut lines : Array String := #[]
    let mut nBad := 0
    for c in indVal.ctors do
      let bad ← checkCtor indVal.numParams c
      unless bad.isEmpty do
        nBad := nBad + 1
        let short := toString (c.updatePrefix Name.anonymous)
        for (i, hs) in bad do
          let heads := ", ".intercalate (hs.toList.map toString)
          lines := lines.push s!"  {short} : index {i} ← {heads}"
    if nBad == 0 then
      return (true,
        s!"'{n}' : all {indVal.ctors.length} constructors pass the McBride test")
    else
      let head :=
        s!"'{n}' : {nBad} of {indVal.ctors.length} constructors FAIL the McBride test"
      return (false, "\n".intercalate (head :: lines.toList))

private def resolve (id : Syntax) : CommandElabM Name := do
  let cs ← liftCoreM <| realizeGlobalConstWithInfos id
  match cs with
  | [n] => return n
  | n :: _ => return n
  | [] => throwError "unknown constant"

/-- `#mcbride I₁ I₂ …` — report the McBride test for each listed
inductive family.  Pin the output with `#guard_msgs` to make the current
state a build-time invariant. -/
syntax (name := mcbrideCmd) "#mcbride " ident+ : command

@[command_elab mcbrideCmd] def elabMcbride : CommandElab
  | `(#mcbride $ids*) => do
      for id in ids do
        let n ← resolve id
        let (_, report) ← reportFor n
        logInfo report
  | _ => throwUnsupportedSyntax

/-- `#mcbride! I₁ I₂ …` — the gate form: a slimy constructor in any
listed family is an ERROR.  Put this next to a family that must be clean
from line one; no pin text to maintain. -/
syntax (name := mcbrideBangCmd) "#mcbride! " ident+ : command

@[command_elab mcbrideBangCmd] def elabMcbrideBang : CommandElab
  | `(#mcbride! $ids*) => do
      let mut failures : Array String := #[]
      for id in ids do
        let n ← resolve id
        let (clean, report) ← reportFor n
        if clean then logInfo report
        else failures := failures.push report
      unless failures.isEmpty do
        throwError "\n\n".intercalate failures.toList
  | _ => throwUnsupportedSyntax

/-- `#mcbride_pin I₁ I₂ …` — emit the `#guard_msgs`-wrapped `#mcbride`
block for each family, ready to paste into an audit module.  Generated,
never retyped: a transcription slip in a pin is a silent hole in the
gate. -/
syntax (name := mcbridePinCmd) "#mcbride_pin " ident+ : command

@[command_elab mcbridePinCmd] def elabMcbridePin : CommandElab
  | `(#mcbride_pin $ids*) => do
      for id in ids do
        let n ← resolve id
        let (_, report) ← reportFor n
        logInfo s!"/-- info: {report} -/\n#guard_msgs in\n#mcbride {n}"
  | _ => throwUnsupportedSyntax

end McBride
