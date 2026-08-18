/-
# Green slime: computed indices in constructor return types

McBride's rule for indexed inductive families: in a constructor's
**return type**, every index should be a variable, or a constructor
applied to variables — never a *function* applied to anything. A
function application in that position ("green slime") is not invertible,
so `cases`, `injection` and dependent pattern matching cannot decompose
it. Every proof over the family then has to transport across an equation
the unifier refuses to solve.

The damage is not unsoundness — a slimed development can still be
kernel-checked. The damage is that the *statements* bend to fit what can
be case-analysed: normalisation gets welded into the indices so the
computed forms come out syntactically equal, and the judgment silently
stops being the one the source defines. That is a fidelity failure, and
it is invisible from a green build.

`#deslime J` reports, for each constructor of `J`, which indices of its
conclusion are computed and which function heads compute them.

Inert (clean): free variables, sorts, literals, constructor applications
and type formers, recursively — and `Nat` offsets (`n + 1`), which the
unifier inverts natively, so height-indexed families are not slimed. Everything else is reported, named by the
head symbol that does the computing — including a schematic function
applied to an argument (`Δs i`), which is equally uninvertible.

Premises are NOT examined. Computation in a premise (`LaxND (φ :: Γ) ψ`)
is harmless and normal; only the return type matters.

This command reports; it does not fail a build. FRJ carries slime today,
and a check that broke the build would leave the repo unbuildable.
-/
import Lean

open Lean Elab Command Meta

namespace Audit

/-- `none` = inert; `some h` = computed, with `h` the offending head. -/
private partial def slimeIn (e : Expr) : MetaM (Option Name) := do
  -- `Nat` offsets are the standard exception: `n + 1` is definitionally
  -- `Nat.succ n`, and the unifier inverts it natively, so a height-indexed
  -- family is NOT slimed. Classify the base instead.
  if let some (base, k) ← isOffset? e then
    if k > 0 then return ← slimeIn base
  match e with
  | .mdata _ b => slimeIn b
  | .fvar _ | .bvar _ | .sort _ | .lit _ | .mvar _ => return none
  | .proj s _ _ => return some s
  | .lam .. | .forallE .. | .letE .. => return none
  | _ =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ =>
        match ← getConstInfo c with
        | .ctorInfo _ | .inductInfo _ =>
            -- a constructor, or a type former: inert in itself, but its
            -- arguments may still compute
            for a in args do
              if let some bad ← slimeIn a then return some bad
            return none
        | _ => return some c
    | .fvar id =>
        -- a bare schematic variable is fine; applied to anything it is not
        if args.isEmpty then return none else return some (← id.getUserName)
    | _ => return some `«?»

private structure Report where
  ctor : Name
  bad  : Array (Nat × String × Name)   -- index position, printed form, head

/-- Examine one constructor's conclusion. -/
private def inspect (numParams : Nat) (ctor : Name) : MetaM Report := do
  let ci ← getConstInfo ctor
  forallTelescope ci.type fun _ body => do
    let idxs := body.getAppArgs.extract numParams body.getAppArgs.size
    let mut bad : Array (Nat × String × Name) := #[]
    for i in [0 : idxs.size] do
      let e := idxs[i]!
      if let some head ← slimeIn e then
        bad := bad.push (i + 1, (← ppExpr e).pretty, head)
    return { ctor := ctor, bad := bad }

/-- `#deslime J …` — report computed indices in the return types of the
constructors of each inductive family `J`. -/
syntax (name := deslimeCmd) "#deslime " ident+ : command

@[command_elab deslimeCmd] def elabDeslime : CommandElab
  | `(#deslime $ids*) => do
      for id in ids do
        let cs ← liftCoreM <| realizeGlobalConstWithInfos id
        let n := cs.head!
        liftTermElabM do
          withTheReader Core.Context
              (fun ctx => { ctx with currNamespace := n.getPrefix }) do
            let iv ← getConstInfoInduct n
            let mut reports : Array Report := #[]
            for c in iv.ctors do
              reports := reports.push (← inspect iv.numParams c)
            let slimed := reports.filter (fun r => !r.bad.isEmpty)
            let clean := reports.filter (fun r => r.bad.isEmpty)
            let mut out :=
              s!"{n} — {iv.numIndices} indices, {reports.size} constructors, "
                ++ s!"{slimed.size} carrying green slime"
            for r in slimed do
              out := out ++ s!"\n\n  {r.ctor.getString!}"
              for (i, printed, head) in r.bad do
                out := out ++ s!"\n    index {i}  {printed}\n              ↳ computed by  {head}"
            unless clean.isEmpty do
              out := out ++ "\n\n  clean: "
                ++ String.intercalate ", " (clean.toList.map (·.ctor.getString!))
            if slimed.isEmpty then logInfo out else logWarning out
  | _ => throwUnsupportedSyntax

end Audit
