/-
# Solving the constraint, at the moment it is recorded

`reduce_obligation` *proves* `obligation ↔ n·δ ≤ T`, but somebody has to write
`n·δ ≤ T` down, and doing it afterwards leaves the recorded obligation holding
the raw goal. This module removes both problems: the reduction is **computed**,
and it happens **as `postpone` records the obligation**, so what the ledger
holds, what `#obligations` prints, and what the finished statement quantifies
over is the solved constraint.

## The fragment, and why the reduction is forced

Every constraint this library synthesises has the shape

    ∀ z, A ≤ z → e ≤ z

with `e` built from atoms by `+` and `max` — those two and no others, because
`meet` and `image` are the only combinators the modality's rules introduce, and
on lower bounds they are exactly `max` and `+`. Over that signature the
reduction is forced, and it is three rewrites:

* `oblIff` — the quantifier goes by instantiating at its own bound. This is the
  paper's equation (8) to equation (9) step, the one it justifies with "given
  such reasoning is built into constraint reductions".
* `distrR`, `distrL` — `+` distributes over `max`, so `e` normalises to a max of
  sums.
* `Nat.max_le` — `max` splits on the left of `≤`.

So the solved form is a **conjunction of linear inequalities**, one per timing
path, which is what static timing analysis wants and is finer than what a person
writing the right-hand side by hand usually bothers with: `max T tp + δsum ≤
Tclk` becomes `T + δsum ≤ Tclk ∧ tp + δsum ≤ Tclk`, naming the two paths.

## How the right-hand side is computed

Not by a normaliser. The goal `ty ↔ ?rhs` is stated with a **metavariable** on
the right, `simp only` rewrites the left with the lemmas above, and `Iff.rfl`
assigns `?rhs` to whatever came out. Nothing states the answer, and there is no
unverified component to trust: the lemmas are theorems, so the equivalence is
kernel-checked by construction.

Two things the earlier version got wrong and this one does not. It used `omega`
as the certifier, and `omega` normalises `max` by a classical case split, so
every constraint arising from a parallel join carried `Classical.choice`; the
three lemmas here are `[propext]` at worst. And it ran after the declaration was
added, so the obligation constant kept the raw form; this runs at `postpone`.

The two passes are not cosmetic: `simp` rewrites innermost-first, so splitting
the `max` first would destroy the pattern `oblIff` matches.

## What is still emitted afterwards

`solve_obligations d`, and the `postponing theorem` hook, add
`d_debt : ∀ binders, Debt (⋀ᵢ obligationᵢ) <d's conclusion>` — the `C ⊃ φ` form
over the whole constraint set, which discharges at a model with one `omega`.

An obligation outside the fragment is left alone; it still appears in the fold,
so the statement stays true and the gap is visible rather than silent. The
latch's internal memory constraint is the standing example.
-/

import LaxLogic.Obligation.Postpone
import LaxLogic.Obligation.Timing

namespace LaxLogic.Obligation.Solve

open Lean Meta Elab Command Term
open LaxLogic.Obligation

/-- Right-nested conjunction of a non-empty array; `True` if empty. -/
def mkConj (cs : Array Expr) : MetaM Expr := do
  if cs.isEmpty then return mkConst ``True
  let mut e := cs.back!
  for c in cs.pop.reverse do
    e ← mkAppM ``And #[c, e]
  return e

/-! ## The reduction, as rewrite rules

Three lemmas, and they are the whole solver.  Each is `[propext]` at worst, so
a constraint reduced by them carries no `Classical.choice` — which the previous
route, `omega`, could not manage, because it normalises `max` by a classical
case split. -/

/-- **The paper's (8) → (9)**: a constraint universally quantified over a time,
with a lower bound as its hypothesis, is equivalent to the bound instantiated at
itself.  Depends on no axioms. -/
theorem oblIff (A e : Nat) : (∀ z, A ≤ z → e ≤ z) ↔ e ≤ A :=
  ⟨fun h => h A (Nat.le_refl A), fun h _ hz => Nat.le_trans h hz⟩

/-- `+` distributes over `max` on the right. -/
theorem distrR (a b c : Nat) : max a b + c = max (a + c) (b + c) := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.add_le_add_right h c)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.add_le_add_right h c)]

/-- And on the left. -/
theorem distrL (a b c : Nat) : c + max a b = max (c + a) (c + b) := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.add_le_add_left h c)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.add_le_add_left h c)]

/-- Compute the solved form of a constraint **into a metavariable**, together
with the equivalence that certifies it.

Nothing states the right-hand side.  The goal `ty ↔ ?rhs` is rewritten by the
three lemmas above — first the quantifier step, then the distribution and the
`max` split, which must be a second pass because `simp` rewrites innermost-first
and would otherwise destroy the pattern `oblIff` matches — and `Iff.rfl` then
assigns `?rhs` to whatever came out.

`none` means the shape is outside the fragment and nothing was reduced. -/
def reduceIff (ty : Expr) : TermElabM (Option (Expr × Expr)) := do
  let rhs ← mkFreshExprMVar (mkSort .zero)
  let goal ← mkAppM ``Iff #[ty, rhs]
  let tac ← `(term|
    by
      try simp only [LaxLogic.Obligation.Timing.from_, LaxLogic.Obligation.Solve.oblIff]
      try simp only [LaxLogic.Obligation.Solve.distrR, LaxLogic.Obligation.Solve.distrL,
        Nat.max_le]
      exact Iff.rfl)
  let prf ←
    try
      let e ← Term.elabTermEnsuringType tac goal
      Term.synthesizeSyntheticMVarsNoPostponing
      pure (some e)
    catch _ => pure none
  match prf with
  | none => return none
  | some prf =>
      let solved ← instantiateMVars rhs
      -- Nothing was achieved, or the hole survived: treat as out of fragment.
      if solved.hasExprMVar || solved == (← instantiateMVars ty) then return none
      return some (solved, ← instantiateMVars prf)

/-- The reducer `postpone` calls as it records: the solved proposition, and a
proof that it implies the goal. -/
def reduceAtRecord (ty : Expr) : TermElabM (Option (Expr × Expr)) := do
  match ← reduceIff ty with
  | none => return none
  | some (solved, iff) => return some (solved, ← mkAppM ``Iff.mpr #[iff])

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

/-- Fold a declaration's obligations into the single implication `C ⊃ φ`.

The obligations are already in solved form — `postpone` reduced each as it
recorded it — so there is nothing left to compute here. What this adds is the
fold: `d_debt : ∀ binders, Debt (⋀ᵢ obligationᵢ) <d's conclusion>`, which is the
form a reader wants and the form that discharges at a constraint model with one
call to `omega`. -/
def solveFor (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some owed := (owedEntries env).find? (·.decl == declName)
    | throwError "solve_obligations: {declName} is not in the obligation \
        ledger; was it built with `postponing theorem`?"
  let n := owed.obligations.size
  if n == 0 then return
  let nBinders ← liftTermElabM <|
    lambdaTelescope owed.obligations[0]!.type fun bs _ => pure bs.size
  liftTermElabM do
    let info ← getConstInfo declName
    -- Bounded: the declaration's conclusion may itself be a `∀`, and an
    -- unbounded telescope would swallow it (the latch's does).
    forallBoundedTelescope info.type (some (nBinders + n)) fun xs goal => do
      let bs := xs.extract 0 nBinders
      let hs := xs.extract nBinders xs.size
      let cs ← hs.mapM (fun h => inferType h)
      let conj ← mkConj cs
      let dName := declName.appendAfter "_debt"
      let stmt ← mkForallFVars bs (← mkAppM ``Debt #[conj, goal])
      let val ← withLocalDeclD `hc conj fun hc => do
        let mut args : Array Expr := #[]
        let mut rest := hc
        for i in [0 : n] do
          let comp ← if i + 1 == n then pure rest else mkAppM ``And.left #[rest]
          if i + 1 != n then
            rest ← mkAppM ``And.right #[rest]
          args := args.push comp
        let body := mkAppN (mkConst declName (info.levelParams.map mkLevelParam))
          (bs ++ args)
        mkLambdaFVars bs (← mkLambdaFVars #[hc] body)
      let stmt ← instantiateMVars (← Term.levelMVarToParam stmt)
      let val ← instantiateMVars (← Term.levelMVarToParam val)
      let ps := (collectLevelParams (collectLevelParams {} stmt) val).params
      addDecl (.thmDecl {
        name := dName, levelParams := ps.toList, type := stmt, value := val })
      logInfo m!"{declName}: {n} obligation(s) folded into {dName}"
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

/-- And register the reducer, so that what `postpone` records is the **solved**
constraint rather than the raw goal. This is the difference between solving as
an afterthought and solving at the point the obligation comes into existence:
with it, unfolding an obligation gives the solved form, `#obligations` prints
it, and the `Debt` fold is over it. -/
initialize reducerHook.set (some reduceAtRecord)

end LaxLogic.Obligation.Solve
