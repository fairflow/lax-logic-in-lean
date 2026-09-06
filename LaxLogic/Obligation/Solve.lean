/-
# Computing the reduced constraints: a `(max, +)` solver

`reduce_obligation` *proves* `obligation ↔ n·δ ≤ T`, but somebody has to write
`n·δ ≤ T` down. That is the last place a human or an agent was still inserting
the answer, and it is the place where a mistake would go unnoticed: a wrong
right-hand side that happens to be equivalent is silently accepted, and a wrong
one that is not equivalent merely fails to compile, having wasted the step.

This module computes it instead.

## The normal form

Every constraint synthesised by this library has the shape

    ∀ z, A ≤ z → e ≤ z

with `e` built from atoms by `+` and `max` — the two operations of
`Timing.lean`'s table, and no others, because those are the only two the
modality's rules introduce. Over that signature:

* `∀ z, A ≤ z → e ≤ z`  reduces to  `e ≤ A`  (the paper's (8) → (9));
* `+` distributes over `max`: `max a b + c = max (a+c) (b+c)`, so every
  expression normalises to a **max of sums**;
* `max` splits on the left of `≤`: `max e₁ e₂ ≤ A ↔ e₁ ≤ A ∧ e₂ ≤ A`.

So the solved form of any such constraint is a **conjunction of linear
inequalities** — which is what static timing analysis actually wants, one
inequality per path. `max T tp + δsum ≤ Tclk` becomes

    T + δsum ≤ Tclk  ∧  tp + δsum ≤ Tclk

naming the two paths separately.

## Why the normaliser need not be verified

It is a *search* device, in the sense this repository already uses for proof and
countermodel discovery: it proposes the right-hand side, and `omega` certifies
the resulting `↔` against the kernel. A bug in the normaliser cannot produce an
unsound theorem; it can only produce one `omega` refuses to prove, which is a
build failure. Nothing here is trusted.

## What is automated, and what is not

`solve_obligations d` emits, for a declaration `d` built by
`postponing theorem`:

* `d.obligationᵢ_solved : ∀ binders, d.obligationᵢ … ↔ <computed>` for each
  obligation, including the ones `lax_apply` borrowed from other modules;
* `d_debt : ∀ binders, Debt (⋀ᵢ <computed>) <d's conclusion>` — the `C ⊃ φ`
  form, with `C` the whole computed constraint set.

Nothing is written by hand. An obligation whose shape is outside the fragment is
reported and left alone; it still appears in the `Debt` fold, unreduced, so the
statement stays true and the gap is visible rather than silent.
-/

import LaxLogic.Obligation.Postpone
import LaxLogic.Obligation.Timing

namespace LaxLogic.Obligation.Solve

open Lean Meta Elab Command Term
open LaxLogic.Obligation

/-! ## The normal form -/

/-- A sum: a multiset of atoms plus a constant. The `max`-free part of a
`(max, +)` expression. -/
structure Summand where
  /-- The non-literal factors, in source order. -/
  atoms : Array Expr
  /-- The accumulated literal. -/
  const : Nat
  deriving Inhabited

/-- Combine two summands: `(as, c) + (bs, d) = (as ++ bs, c + d)`. -/
def Summand.add (a b : Summand) : Summand :=
  { atoms := a.atoms ++ b.atoms, const := a.const + b.const }

/-- Rebuild a summand as an expression: `a₁ + ⋯ + aₙ + c`, dropping a zero
constant unless there is nothing else. -/
def Summand.toExpr (s : Summand) : MetaM Expr := do
  let lit := mkNatLit s.const
  if s.atoms.isEmpty then return lit
  let mut e := s.atoms[0]!
  for a in s.atoms[1:] do
    e ← mkAppM ``HAdd.hAdd #[e, a]
  if s.const == 0 then return e
  mkAppM ``HAdd.hAdd #[e, lit]

/-- Normalise a `(max, +)` expression to a **max of sums**.

`+` distributes over `max`, so the result is the cross product of the operands'
normal forms; `max` is their union; a literal is a constant summand; anything
else is an opaque atom. Unrecognised structure is therefore safe — it becomes an
atom, and the worst that happens is a coarser constraint that `omega` may not
certify. -/
partial def normMP (e₀ : Expr) : MetaM (Array Summand) := do
  -- `whnfCore` reduces projections and beta/iota redexes without unfolding
  -- definitions, so `(a, b).snd` becomes `b` while `k * δ` is left alone.
  let e ← whnfCore e₀
  if let some n := e.nat? then
    return #[{ atoms := #[], const := n }]
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let as ← normMP a
      let bs ← normMP b
      let mut out : Array Summand := #[]
      for x in as do
        for y in bs do
          out := out.push (x.add y)
      return out
  | (``Max.max, #[_, _, a, b]) => return (← normMP a) ++ (← normMP b)
  | (``Nat.max, #[a, b])       => return (← normMP a) ++ (← normMP b)
  -- Projection *functions* need delta, which `whnfCore` will not do; the two
  -- that occur here are worth handling by hand rather than opening the door to
  -- unfolding arithmetic and printing `Nat.mul k δ` back at the reader.
  | (``Prod.fst, #[_, _, p]) =>
      match p.getAppFnArgs with
      | (``Prod.mk, #[_, _, x, _]) => normMP x
      | _ => return #[{ atoms := #[e], const := 0 }]
  | (``Prod.snd, #[_, _, p]) =>
      match p.getAppFnArgs with
      | (``Prod.mk, #[_, _, _, y]) => normMP y
      | _ => return #[{ atoms := #[e], const := 0 }]
  | _ => return #[{ atoms := #[e], const := 0 }]

/-- Match `a ≤ b` at any type, returning the two sides. -/
def matchLe? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``LE.le, #[_, _, a, b]) => some (a, b)
  | _ => none

/-- Right-nested conjunction of a non-empty array; `True` if empty. -/
def mkConj (cs : Array Expr) : MetaM Expr := do
  if cs.isEmpty then return mkConst ``True
  let mut e := cs.back!
  for c in cs.pop.reverse do
    e ← mkAppM ``And #[c, e]
  return e

/-- The solved form of one obligation, or `none` if it is outside the fragment.

Expects `∀ z, A ≤ z → e ≤ z` (after reducible unfolding, which is what turns
`from_ e z` into `e ≤ z`), and returns `⋀ sᵢ ≤ A` over the normal form of `e`.
Duplicate paths are removed. -/
def solvedForm (ty : Expr) : MetaM (Option Expr) := do
  forallTelescopeReducing ty fun xs body => do
    unless xs.size == 2 do return none
    let z := xs[0]!
    let h := xs[1]!
    let hty ← whnfR (← inferType h)
    let some (a, z') := matchLe? hty | return none
    let a ← whnfCore a
    let a ← match a.getAppFnArgs with
      | (``Prod.fst, #[_, _, p]) =>
          match p.getAppFnArgs with
          | (``Prod.mk, #[_, _, x, _]) => pure x
          | _ => pure a
      | (``Prod.snd, #[_, _, p]) =>
          match p.getAppFnArgs with
          | (``Prod.mk, #[_, _, _, y]) => pure y
          | _ => pure a
      | _ => pure a
    unless z' == z do return none
    let body ← whnfR body
    let some (lhs, z'') := matchLe? body | return none
    unless z'' == z do return none
    -- `A` and the left-hand side must not mention the bound time.
    let zid := z.fvarId!
    if a.hasAnyFVar (· == zid) || lhs.hasAnyFVar (· == zid) then return none
    let sums ← normMP lhs
    let mut cs : Array Expr := #[]
    for s in sums do
      let se ← s.toExpr
      let c ← mkAppM ``LE.le #[se, a]
      unless cs.any (· == c) do cs := cs.push c
    return some (← mkConj cs)

/-! ## The command -/

/-- The tactic that certifies a computed right-hand side. Uniform in the arity
of the conjunction, because `omega` handles conjunctions of linear constraints
directly: the forward branch instantiates the universal at its own bound, and
the backward branch reintroduces it. -/
private def certifyStx : MetaM Term := `(term|
  by
    intros
    constructor <;> intro h <;>
      first
        | (have h₂ := h _ (Nat.le_refl _)
           try simp only [LaxLogic.Obligation.Timing.from_] at h₂
           try simp only [LaxLogic.Obligation.Timing.from_]
           omega)
        | (intro z hz
           try simp only [LaxLogic.Obligation.Timing.from_]
           omega))

/-- Add `name : stmt`, proving it with the certifying tactic.

The statement is delaborated and handed to the ordinary `theorem` elaborator
rather than assembled with `addDecl`. That is deliberate: `addDecl` falls back
to `addAsAxiom` when a declaration it is given does not check — for instance
when a tactic leaves an unassigned universe metavariable — and the failure is
then invisible. Going through `theorem` cannot silently axiomatise anything, and
`checkAdded` below confirms what landed. -/
private def addCertified (name : Name) (stmt : Expr) : CommandElabM Unit := do
  let stmtStx ← liftTermElabM <|
    withOptions (fun o => o.setBool `pp.fullNames true) <| PrettyPrinter.delab stmt
  let id := mkIdent (`_root_ ++ name)
  elabCommand (← `(command| theorem $id : $stmtStx := $(← liftTermElabM certifyStx)))

/-- Confirm that what was added is a theorem and not an axiom. The mechanism
must not be able to introduce one; this is where that is checked rather than
assumed. -/
private def checkAdded (name : Name) : CommandElabM Unit := do
  match (← getEnv).find? name with
  | some (.thmInfo _) => pure ()
  | some (.axiomInfo _) =>
      throwError "solve_obligations: {name} was added as an AXIOM, not a theorem"
  | some _ => throwError "solve_obligations: {name} is not a theorem"
  | none => throwError "solve_obligations: {name} was not added"

/-- Compute and record the reduced form of every obligation of a declaration
built with `postponing theorem`, and the `Debt` fold over them.

    solve_obligations pipeline_meets_clock

emits `pipeline_meets_clock.obligationᵢ_solved` for each `i`, and
`pipeline_meets_clock_debt`. -/
syntax (name := solveObligationsCmd) "solve_obligations" ident : command

/-- Solve and fold the obligations of `declName`. The command and the
`postponing theorem` hook both call this. -/
def solveFor (declName : Name) : CommandElabM Unit := do
      let env ← getEnv
      let some owed := (owedEntries env).find? (·.decl == declName)
        | throwError "solve_obligations: {declName} is not in the obligation \
            ledger; was it built with `postponing theorem`?"
      let mut solvedNames : Array (Name × Option Expr) := #[]
      let mut nBinders := 0
      for e in owed.obligations do
        let sName := e.name.appendAfter "_solved"
        -- `e.type` is `fun binders => ty`.
        let r ← liftTermElabM <| lambdaTelescope e.type fun bs ty => do
          match ← solvedForm ty with
          | none => pure (bs.size, none)
          | some rhs => do
              let info ← getConstInfo e.name
              let ob := mkAppN (mkConst e.name (info.levelParams.map mkLevelParam)) bs
              let stmt ← mkForallFVars bs (← mkAppM ``Iff #[ob, rhs])
              pure (bs.size, some (stmt, ← mkLambdaFVars bs rhs))
        nBinders := r.1
        let r := r.2
        match r with
        | none =>
            logWarning m!"solve_obligations: {e.name} is outside the \
              (max, +) fragment; left unreduced"
            solvedNames := solvedNames.push (sName, none)
        | some (stmt, rhsAbs) =>
            addCertified sName stmt
            checkAdded sName
            solvedNames := solvedNames.push (sName, some rhsAbs)
      -- The `Debt` fold.
      liftTermElabM do
        let info ← getConstInfo declName
        let n := owed.obligations.size
        -- Bounded: the declaration's conclusion may itself be a `∀`, and an
        -- unbounded telescope would swallow it (the latch's does).
        forallBoundedTelescope info.type (some (nBinders + n)) fun xs goal => do
          let bs := xs.extract 0 nBinders
          let hs := xs.extract nBinders xs.size
          let mut cs : Array Expr := #[]
          for i in [0 : n] do
            match solvedNames[i]!.2 with
            | some rhsAbs => cs := cs.push (← instantiateLambda rhsAbs bs)
            | none        => cs := cs.push (← inferType hs[i]!)
          let conj ← mkConj cs
          let dName := declName.appendAfter "_debt"
          let stmt ← mkForallFVars bs (← mkAppM ``Debt #[conj, goal])
          -- Proof: intro the conjunction, project, transport through each
          -- `_solved` equivalence, apply the declaration.
          let val ← withLocalDeclD `hc conj fun hc => do
            let mut args : Array Expr := #[]
            let mut rest := hc
            for i in [0 : n] do
              let comp ← if i + 1 == n then pure rest else mkAppM ``And.left #[rest]
              if i + 1 != n then
                rest ← mkAppM ``And.right #[rest]
              match solvedNames[i]!.2 with
              | none => args := args.push comp
              | some _ =>
                  let sInfo ← getConstInfo solvedNames[i]!.1
                  let iff := mkAppN (mkConst solvedNames[i]!.1
                    (sInfo.levelParams.map mkLevelParam)) bs
                  args := args.push (← mkAppM ``Iff.mpr #[iff, comp])
            let body := mkAppN (mkConst declName (info.levelParams.map mkLevelParam))
              (bs ++ args)
            mkLambdaFVars bs (← mkLambdaFVars #[hc] body)
          let stmt ← instantiateMVars (← Term.levelMVarToParam stmt)
          let val ← instantiateMVars (← Term.levelMVarToParam val)
          let ps := (collectLevelParams (collectLevelParams {} stmt) val).params
          addDecl (.thmDecl {
            name := dName, levelParams := ps.toList, type := stmt, value := val })
          logInfo m!"solve_obligations {declName}: {n} solved, folded into {dName}"
      checkAdded (declName.appendAfter "_debt")

@[command_elab solveObligationsCmd]
def elabSolveObligations : CommandElab := fun stx => do
  match stx with
  | `(command| solve_obligations $nm:ident) => do
      let some declName ← liftTermElabM (do
          let cs ← realizeGlobalConst nm
          pure cs.head?) | throwError "solve_obligations: unknown declaration"
      solveFor declName
  | _ => throwUnsupportedSyntax

/-- Register the solver with `postponing theorem`: from here on, a declaration
that records obligations gets its reduced forms and its `Debt` fold in the same
step, with nothing for the author to write. -/
initialize solverHook.set (some solveFor)

end LaxLogic.Obligation.Solve
