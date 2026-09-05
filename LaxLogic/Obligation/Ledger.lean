/-
# The obligation ledger

A persistent environment extension recording, for each declaration built with
`postponing theorem`, the obligations it still owes.

This lives in its own module for a mundane reason: `initialize` cannot be
consumed in the module that declares it, so the tactic and command in
`LaxLogic.Obligation.Postpone` need the extension to have been set up already.

The ledger survives `import`, which is the property that makes the mechanism
usable across a development rather than within a single file: a theorem in one
module can be built from holed theorems in another, and `#obligations` reports
the whole accumulated debt.
-/

import Lean

namespace LaxLogic.Obligation

open Lean

/-- One recorded obligation: the generated `Prop`-valued constant standing for
it, and its statement. The constant is what makes the obligation addressable —
it can be stated, searched for, and proved in a later module. -/
structure Entry where
  /-- The generated obligation constant, for example `foo.obligation1`. -/
  name : Name
  /-- Its statement: a closed proposition, the goal at the hole with the whole
  local context reverted into it. -/
  type : Expr
  deriving Inhabited

/-- What one declaration owes. -/
structure Owed where
  /-- The declaration built by `postponing theorem`. -/
  decl : Name
  /-- Its obligations, in the order the holes were encountered, after
  deduplication of syntactically identical ones. -/
  obligations : Array Entry
  deriving Inhabited

/-- The ledger. Local entries are appended; imported ones are concatenated, so
the state seen by `#obligations` is the whole transitive debt of everything
currently imported. -/
initialize obligationExt :
    SimplePersistentEnvExtension Owed (Array Owed) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => s.push e
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Obligations recorded by `postpone` during elaboration of the declaration
currently being processed. Cleared at the start of each `postponing theorem`. -/
initialize inFlight : IO.Ref (Array MVarId) ← IO.mkRef #[]

/-- The declaration's own binders, which `postpone` must NOT revert.

An obligation that re-quantified them would be a statement about *all*
parameters rather than the ones at hand, and no assumption about the actual
parameters could discharge it. Obligations are therefore predicates over the
binders, applied to them in the finished statement. -/
initialize binderFVars : IO.Ref (Array Expr) ← IO.mkRef #[]

/-- Every declaration that owes something, in declaration order. -/
def owedEntries (env : Environment) : Array Owed :=
  obligationExt.getState env

end LaxLogic.Obligation
