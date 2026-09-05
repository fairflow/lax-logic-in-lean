/-
# `postpone` — a hole that records a debt instead of asserting the goal

Lean's `sorry` elaborates to `sorryAx`, which inhabits the goal outright. A
declaration containing one therefore *asserts* its statement on no evidence, and
`#print axioms` reports only that something is missing, not what.

`postpone` closes a goal differently. It reverts the local context into the
target, records the resulting closed proposition as an **obligation**, and
discharges the goal from a hypothesis. The enclosing `postponing theorem` then
abstracts those hypotheses into the statement, so what gets added to the
environment is

    theorem foo : foo.obligation1 → … → foo.obligationN → <the intended goal>

which is a complete, `sorry`-free theorem about a weaker statement. Its axioms
are whatever the *finished* parts of the proof used; the holes contribute none.

Discharging the obligations recovers the intended theorem:

    theorem foo' : <the intended goal> := foo proof1 … proofN

and obligations compose: a `postponing theorem` built from holed theorems in
other modules accumulates their obligations alongside its own, which is
`LaxLogic.Obligation.Debt.and` and `Debt.imp` doing the work.

## Usage

```lean
postponing theorem split (n : Nat) : n + 0 = n ∧ n * 1 = n := by
  refine ⟨?_, ?_⟩
  · rfl
  · postpone

#obligations          -- human-readable report
#obligations_json     -- one JSON object per declaration, for tooling
```

## Known limits of this first cut

* `postpone` reverts the **whole** local context. That is the safe choice — a
  hypothesis absent from the goal may still be needed to prove it — but it makes
  obligations larger than necessary. Simplifying them is not done here.
* Obligations are deduplicated by syntactic equality only, so two goals equal up
  to definitional unfolding produce two constants.
* The command re-implements only what it needs of `theorem`: a doc comment,
  binders, a type and a body. Attributes, `private`/`protected`, mutual blocks
  and the equation compiler are not supported.
* `Prop` goals are the intended use. A hole standing for *data* rather than a
  proof would make the obligation computational, which is a different design.
-/

import LaxLogic.Obligation.Ledger
import LaxLogic.Obligation.Modality

namespace LaxLogic.Obligation

open Lean Meta Elab Command Term Tactic

/-- The part of the local context the goal actually reaches: the free variables
of the target, closed under "its type mentions something already reachable".

Reverting only these keeps an obligation legible. The closure is what makes it
correct in practice: a hypothesis constraining a variable the goal mentions is
itself reachable, so `ht : ta + D₁ ≤ t₁` survives when the goal mentions `t₁`,
dragging `ta` and `D₁` in with it, while a dozen unrelated hypotheses about
other signals do not.

Dropping an unreachable hypothesis yields a *stronger* obligation, so the
theorem `obligation → goal` is true either way; only provability is at stake,
and a hypothesis the goal cannot see could not have been used to prove it. -/
private def reachable (g : MVarId) (keep : Array FVarId) : MetaM (Array FVarId) :=
  g.withContext do
    let lctx ← getLCtx
    let tgt ← instantiateMVars (← g.getType)
    let mut rel : FVarIdSet := {}
    for f in (collectFVars {} tgt).fvarIds do
      if !keep.contains f then rel := rel.insert f
    let mut changed := true
    while changed do
      changed := false
      for d in lctx do
        if d.isImplementationDetail || keep.contains d.fvarId then continue
        let fs := (collectFVars {} (← instantiateMVars d.type)).fvarIds
        if rel.contains d.fvarId || fs.any (fun f => rel.contains f) then
          if !rel.contains d.fvarId then
            rel := rel.insert d.fvarId; changed := true
          for f in fs do
            if !keep.contains f && !rel.contains f then
              rel := rel.insert f; changed := true
    let mut out : Array FVarId := #[]
    for d in lctx do
      if !d.isImplementationDetail && !keep.contains d.fvarId && rel.contains d.fvarId then
        out := out.push d.fvarId
    return out

/-- Every local not among the declaration's binders: the safe fallback. -/
private def allLocals (g : MVarId) (keep : Array FVarId) : MetaM (Array FVarId) :=
  g.withContext do
    let mut out : Array FVarId := #[]
    for d in ← getLCtx do
      if !d.isImplementationDetail && !keep.contains d.fvarId then
        out := out.push d.fvarId
    return out

/-- Record the current goal as an obligation and close it.

The whole local context is reverted into the target first, so the recorded
proposition is closed and can be stated on its own. The goal is then discharged
by a fresh metavariable living in the *empty* local context, which
`postponing theorem` later replaces by a hypothesis of the finished statement.

This adds no axiom. A declaration whose only holes are `postpone`s reports the
axioms of its finished parts and nothing else. -/
syntax (name := postponeTac) "postpone" : tactic

/-- The whole of `postpone`, on an explicit goal and without touching the goal
list. Factored out so that `lax_apply` can postpone the obligation goals left
by applying a holed theorem, through the *same* code path — a second
implementation would be a second thing to keep correct. -/
def postponeCore (g : MVarId) : MetaM Unit := do
  let keep := (← binderFVars.get).filterMap (fun e => e.fvarId?)
  -- Revert what the goal reaches, never the declaration's own binders: the
  -- obligation is a statement about THESE parameters, not about all of them.
  let rel ← reachable g keep
  let (_, gRel) ← g.revert rel
  let tyRel ← instantiateMVars (← gRel.getType)
  let stray (e : Expr) : Array FVarId :=
    (collectFVars {} e).fvarIds.filter (fun f => !keep.contains f)
  let (g', ty) ←
    if (stray tyRel).isEmpty then pure (gRel, tyRel)
    else do
      let (_, gAll) ← g.revert (← allLocals g keep)
      pure (gAll, ← instantiateMVars (← gAll.getType))
  if !(stray ty).isEmpty then
    throwError "postpone: the goal still mentions local hypotheses after \
      reverting; this is a bug in postpone, please report the goal"
  -- A non-`Prop` goal would produce an ill-typed obligation definition, which
  -- the kernel rejects -- whereupon `addDecl`'s `addAsAxiom` fallback adds the
  -- obligation AS AN AXIOM and the failure becomes invisible. Refuse first.
  unless ← isProp ty do
    throwError "postpone: the goal is not a proposition, so it cannot be \
      recorded as an obligation. A hole standing for data rather than a proof \
      is outside this library's scope.\n  goal after reverting: {ty}"
  let m ← withLCtx {} {} (mkFreshExprMVar ty (kind := .natural) (userName := `obligation))
  g'.assign m
  inFlight.modify (·.push m.mvarId!)

@[tactic postponeTac]
def elabPostpone : Tactic := fun _ => do
  postponeCore (← getMainGoal)
  replaceMainGoal []

/-! ## `lax_apply` — borrowing a holed theorem

`postpone` opens a debt. `lax_apply` **transfers** one: it applies a theorem
that was itself built with `postponing theorem`, and re-postpones whichever of
the resulting goals are that theorem's own obligations, so they land in the
current declaration's ledger instead of having to be discharged on the spot.

This is what makes the mechanism modular. Without it, using a holed lemma means
proving its constraint immediately, which defeats the purpose: the whole point
of abstracting a constraint is to go on reasoning while it is outstanding. With
it, a proof can be assembled from holed components and the finished statement
carries the accumulated debt — which is Mendler's monoid law
`weak (c ++ d) φ = weak c (weak d φ)` (`Mendler.weak_append`) as an operation
rather than a theorem.

Goals that are *not* registered obligations are left for the caller, exactly as
`apply` leaves them. -/

/-- Every obligation constant currently known, including imported ones. -/
private def obligationNames : MetaM NameSet := do
  let mut s : NameSet := {}
  for o in owedEntries (← getEnv) do
    for e in o.obligations do
      s := s.insert e.name
  return s

/-- Apply a theorem, postponing its obligations into the current ledger.

`lax_apply h` behaves as `apply h`, except that any resulting goal whose head is
an obligation constant of some `postponing theorem` is recorded by `postpone`
rather than returned. The remaining goals — the lemma's ordinary hypotheses —
are left to prove. -/
syntax (name := laxApplyTac) "lax_apply" ppSpace term : tactic

@[tactic laxApplyTac]
def elabLaxApply : Tactic := fun stx => do
  match stx with
  | `(tactic| lax_apply $t:term) => do
      let obs ← obligationNames
      let g ← getMainGoal
      let e ← g.withContext do
        let e ← Term.elabTerm t none
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
      let gs ← g.apply e
      let mut rest : List MVarId := []
      let mut borrowed := 0
      for g' in gs do
        if ← g'.isAssigned then continue
        let ty ← instantiateMVars (← g'.getType)
        match ty.getAppFn.constName? with
        | some n =>
            if obs.contains n then
              postponeCore g'
              borrowed := borrowed + 1
            else
              rest := g' :: rest
        | none => rest := g' :: rest
      if borrowed == 0 then
        logWarning "lax_apply: no obligation was borrowed; this is plain `apply`. \
          Was the lemma built with `postponing theorem`?"
      replaceMainGoal rest.reverse
  | _ => throwUnsupportedSyntax

/-- Deduplicate obligation types by syntactic equality, returning the distinct
types and, for each original position, the index of its representative. -/
private def dedup (tys : Array Expr) : Array Expr × Array Nat := Id.run do
  let mut uniq : Array Expr := #[]
  let mut idx : Array Nat := #[]
  for t in tys do
    match uniq.findIdx? (· == t) with
    | some j => idx := idx.push j
    | none   => idx := idx.push uniq.size; uniq := uniq.push t
  return (uniq, idx)

/-- Add `name : Prop := ty` as a reducible definition, so that anything proving
`ty` also proves `name` without an explicit unfolding step. -/
private def addObligationDef (name : Name) (bfvars : Array Expr) (ty : Expr) :
    TermElabM Unit := do
  let value ← instantiateMVars (← Term.levelMVarToParam (← mkLambdaFVars bfvars ty))
  let dtype ← instantiateMVars
    (← Term.levelMVarToParam (← mkForallFVars bfvars (.sort .zero)))
  let ps := (collectLevelParams (collectLevelParams {} dtype) value).params
  addDecl (.defnDecl {
    name, levelParams := ps.toList, type := dtype, value
    hints := .abbrev, safety := .safe })
  setReducibleAttribute name

/-- Declare a theorem whose unproved goals are recorded as obligations rather
than asserted.

Each `postpone` in the body contributes one hypothesis to the front of the
resulting statement, named `<decl>.obligation<i>` and added as a reducible
`Prop`-valued definition so it can be stated and proved elsewhere. -/
syntax (name := postponingDecl)
  (docComment)? "postponing " "theorem " ident (ppSpace bracketedBinder)*
    " : " term " := " term : command

@[command_elab postponingDecl]
def elabPostponing : CommandElab := fun stx => do
  match stx with
  | `(command| $[$doc?:docComment]? postponing theorem $nm:ident
        $bs:bracketedBinder* : $tyStx:term := $bodyStx:term) => do
    let declName := (← getCurrNamespace) ++ nm.getId
    let entries ← liftTermElabM do
      inFlight.set #[]
      Term.elabBinders bs fun bfvars => do
        binderFVars.set bfvars
        let type ← Term.elabType tyStx
        let val ← Term.elabTermEnsuringType bodyStx type
        Term.synthesizeSyntheticMVarsNoPostponing
        let ms ← inFlight.get
        let rawTys ← ms.mapM fun m => do instantiateMVars (← m.getType)
        let (uniq, idx) := dedup rawTys
        -- Name and declare each distinct obligation before it is referred to.
        let names := uniq.mapIdx fun i _ =>
          declName ++ Name.mkSimple s!"obligation{i + 1}"
        for n in names, t in uniq do
          addObligationDef n bfvars t
        let obTys ← names.mapM fun n => do
          let info ← getConstInfo n
          pure (mkAppN (Lean.mkConst n (info.levelParams.map mkLevelParam)) bfvars)
        let decls : Array (Name × (Array Expr → TermElabM Expr)) :=
          names.mapIdx fun i _ =>
            (Name.mkSimple s!"obl{i + 1}", fun _ => pure obTys[i]!)
        withLocalDeclsD decls fun hs => do
          -- Each hole is discharged by the hypothesis for its representative.
          for m in ms, j in idx do
            m.assign hs[j]!
          let val ← instantiateMVars val
          let value ← mkLambdaFVars bfvars (← mkLambdaFVars hs val)
          let newType ← mkForallFVars bfvars (← mkForallFVars hs type)
          -- Unassigned LEVEL metavariables make `addDecl` fail, and its
          -- `addAsAxiom` fallback then re-adds the declaration AS AN AXIOM,
          -- silently. Pinning them to parameters is not optional.
          let newType ← instantiateMVars (← Term.levelMVarToParam newType)
          let value ← instantiateMVars (← Term.levelMVarToParam value)
          let ps := (collectLevelParams (collectLevelParams {} newType) value).params
          -- Refuse to hand the kernel a non-proposition. It would reject the
          -- declaration, and `addDecl`'s `addAsAxiom` fallback would then add
          -- the name AS AN AXIOM -- observed, and the reason this check exists.
          unless ← isProp newType do
            throwError "postponing theorem: the finished statement is not a \
              proposition, so it cannot be added as a theorem.\n  {newType}"
          addDecl (.thmDecl {
            name := declName, levelParams := ps.toList, type := newType, value })
          Term.applyAttributes declName #[]
          -- Store the obligation ABSTRACTED over the binders: the raw type has
          -- the binders free, and printing it outside their scope shows
          -- `_fvar.28` rather than `sa`.
          let absTys ← uniq.mapM fun t => mkLambdaFVars bfvars t
          let entries := names.mapIdx fun i n => ({ name := n, type := absTys[i]! } : Entry)
          return entries
    modifyEnv (obligationExt.addEntry · { decl := declName, obligations := entries })
    if let some doc := doc? then
      liftTermElabM <| Lean.addDocStringCore declName (← getDocStringText doc)
    if entries.isEmpty then
      logInfo m!"{declName} : owes nothing"
    else
      logInfo m!"{declName} owes {entries.size}: \
        {entries.toList.map (·.name)}"
  | _ => throwUnsupportedSyntax

/-- Report every outstanding obligation in the current environment, including
those inherited through `import`. -/
elab "#obligations" : command => do
  let st := owedEntries (← getEnv)
  if st.isEmpty then
    logInfo "no obligations recorded"
    return
  let mut total := 0
  for o in st do
    total := total + o.obligations.size
    let lines ← liftTermElabM <| o.obligations.mapM fun e => do
      pure m!"    {e.name} : {← ppExpr e.type}"
    logInfo m!"{o.decl} owes {o.obligations.size}:\n{MessageData.joinSep lines.toList "\n"}"
  logInfo m!"total outstanding: {total} across {st.size} declaration(s)"

/-- The same report as machine-readable JSON, one object per declaration.

This is the hook for an automated proving loop: the obligations are the goals to
attack, they are named constants so a proof can be stated against them, and the
count is a progress measure that a binary sorry-or-not cannot provide. -/
elab "#obligations_json" : command => do
  let st := owedEntries (← getEnv)
  for o in st do
    let obs ← liftTermElabM <| o.obligations.mapM fun e => do
      pure <| Json.mkObj [
        ("name", Json.str e.name.toString),
        ("type", Json.str (toString (← ppExpr e.type)))]
    logInfo (Json.mkObj [
      ("decl", Json.str o.decl.toString),
      ("count", Json.num o.obligations.size),
      ("obligations", Json.arr obs)]).compress

end LaxLogic.Obligation
