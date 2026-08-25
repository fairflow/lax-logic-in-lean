/-
# Rendering a judgment as inference figures

An indexed inductive family *is* a rule table, but it does not read like
one: the premises, the side conditions and the schematic variables are
all just binders, in whatever order the constructor happened to be
written. Checking it against a paper's figure means reading Lean syntax
and holding the correspondence in your head — which is exactly where
transcription errors survive.

`#rules J` prints `J`'s constructors as inference figures: premises over
a line, conclusion under it, side conditions listed after `if`. That can
be compared with the source line by line, and it can be shown to a human
before anything is proved about it.

The classification is by type, not by name:

* a binder whose type ends in an application of the family (possibly
  under `∀`, as the join rules' premises do) is a **premise**;
* any other binder that is a `Prop` is a **side condition**;
* an explicit binder that is neither is **data the rule names**;
* implicit data binders are the schematic variables, and are left
  implicit, as in a paper's figure.
-/
import Lean

open Lean Elab Command Meta

namespace Audit

/-- Strip `∀`s and report the head constant, so that a premise stated as
`∀ j, J … ` is recognised as a premise of `J`. -/
private def headAfterBinders (e : Expr) : MetaM (Option Name) :=
  forallTelescopeReducing e fun _ body => return body.getAppFn.constName?

private structure Slot where
  kind : String        -- "premise" | "side" | "data"
  text : String

/-- Classify one binder of a constructor. -/
private def classify (family : List Name) (x : Expr) : MetaM (Option Slot) := do
  let t ← inferType x
  let bi := (← x.fvarId!.getDecl).binderInfo
  let pretty := (← ppExpr t).pretty
  match ← headAfterBinders t with
  | some h =>
      if family.contains h then
        return some { kind := "premise", text := pretty }
      else if ← isProp t then
        return some { kind := "side", text := pretty }
      else if bi.isExplicit then
        return some { kind := "data", text := s!"{← ppExpr x} : {pretty}" }
      else
        return none
  | none =>
      if ← isProp t then
        return some { kind := "side", text := pretty }
      else if bi.isExplicit then
        return some { kind := "data", text := s!"{← ppExpr x} : {pretty}" }
      else
        return none

/-- Render one constructor as a figure. -/
private def figure (family : List Name) (ctor : Name) : MetaM String := do
  let ci ← getConstInfo ctor
  forallTelescope ci.type fun xs body => do
    let mut premises : Array String := #[]
    let mut sides : Array String := #[]
    let mut data : Array String := #[]
    for x in xs do
      match ← classify family x with
      | some s =>
          if s.kind == "premise" then premises := premises.push s.text
          else if s.kind == "side" then sides := sides.push s.text
          else data := data.push s.text
      | none => pure ()
    let concl := (← ppExpr body).pretty
    -- premises on one line if they fit, else one per line
    let premLine := String.intercalate "      " premises.toList
    let premBlock :=
      if premises.isEmpty then ""
      else if premLine.length ≤ 100 then "    " ++ premLine ++ "\n"
      else String.join (premises.toList.map (fun p => "    " ++ p ++ "\n"))
    -- the bar spans whatever is actually printed above it
    let premWidth :=
      if premises.isEmpty then 0
      else if premLine.length ≤ 100 then premLine.length
      else premises.foldl (fun w p => max w p.length) 0
    let width := min 100 (max concl.length premWidth)
    let bar := "    " ++ String.ofList (List.replicate (width + 2) '─') ++ "\n"
    let mut out := s!"\n{ctor.getString!}\n{premBlock}{bar}    {concl}\n"
    unless data.isEmpty do
      out := out ++ "    for  " ++ String.intercalate ",  " data.toList ++ "\n"
    unless sides.isEmpty do
      out := out ++ "    if   " ++ String.intercalate "\n         " sides.toList ++ "\n"
    return out

/-- `#rules J` — print the constructors of the inductive family `J` as
inference figures, for comparison against the source the rules were
transcribed from. -/
syntax (name := rulesCmd) "#rules " ident : command

@[command_elab rulesCmd] def elabRules : CommandElab
  | `(#rules $id) => do
      let cs ← liftCoreM <| realizeGlobalConstWithInfos id
      let n := cs.head!
      liftTermElabM do
        -- print inside the judgment's own namespace, so the figures read
        -- the way the source does rather than fully qualified
        withTheReader Core.Context
            (fun ctx => { ctx with currNamespace := n.getPrefix }) do
          let iv ← getConstInfoInduct n
          let mut out := s!"{n} — {iv.ctors.length} rules"
          for c in iv.ctors do
            out := out ++ (← figure iv.all c)
          logInfo out
  | _ => throwUnsupportedSyntax

end Audit
