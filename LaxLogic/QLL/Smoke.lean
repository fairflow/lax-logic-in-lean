/-
# `LaxLogic.QLL.Smoke` — can the rules be applied at all?

Not mathematics, and not a test bench.  These cells check that the *encoding*
composes: that the freshness side conditions are satisfiable, that opening a
binder lines up with the premise a rule asks for, and that the two independent
de Bruijn spaces do not collide.  A rule can elaborate perfectly and still be
unusable, which is what this catches.

They are written by hand because there is no searcher yet.  Once `Check` and
`Search` exist these are superseded: the same statements become "the searcher
produced a term and the checker accepted it", and no derivation in this
development should be built by hand again.

Each freshness goal is discharged by `show` followed by `decide`.  The `show`
is not decoration: it exposes the reduced side condition, and `decide` cannot
evaluate a goal that still mentions free variables.
-/
import LaxLogic.QLL.Deriv

namespace LaxLogic.QLL.Smoke

open Form Pf

/-- `⊢ λz.z : M ⊃ M`.  Exercises `impI`'s freshness and proof-variable opening
against `var`'s lookup. -/
theorem identity (M : Form) : Derivable [] (lam (bvar 0)) (imp M M) := by
  refine Derivable.impI "z" ⟨?_, ?_⟩ ?_
  · show "z" ∉ ([] : List String); decide
  · show "z" ∉ ([] : List String); decide
  · exact Derivable.var (List.Mem.head _)

/-- `⊢ val_Q(*) : ◯_Q ⊤`, for either modality — the rule is `Q`-parametric, so
one derivation serves both. -/
theorem val_top (q : Q) : Derivable [] (val q star) (circ q top) :=
  Derivable.circI Derivable.topI

/-- `⊢ ⟨λz.z | x⟩ : ∀x. P(x) ⊃ P(x)`.  The point of this one is the binder
interaction: `allI` opens an *individual* while `impI` opens a *proof*
variable, and neither may disturb the other's indices. -/
theorem forall_identity : Derivable []
    (gen (lam (bvar 0)))
    (forall_ (imp (pred "P" [Tm.bvar 0]) (pred "P" [Tm.bvar 0]))) := by
  refine Derivable.allI "x" ⟨?_, ?_, ?_⟩ ?_
  · show "x" ∉ ([] : List String); decide
  · show "x" ∉ ([] : List String); decide
  · show "x" ∉ ([] : List String); decide
  · refine Derivable.impI "z" ⟨?_, ?_⟩ ?_
    · show "z" ∉ ([] : List String); decide
    · show "z" ∉ ([] : List String); decide
    · exact Derivable.var (List.Mem.head _)

/-- `p : ◯_Q M ⊢ let_Q z ⇐ p in val_Q(z) : ◯_Q M` — the monad's left unit, as a
shape check on `circE`.  `M` must be supplied explicitly: `circE`'s `M` occurs
only in its premises, so the conclusion does not determine it. -/
theorem left_unit (q : Q) (M : Form) :
    Derivable [(fvar "p", circ q M)] (letQ q (fvar "p") (val q (bvar 0))) (circ q M) := by
  refine Derivable.circE (M := M) "z" ⟨?_, ?_⟩ ?_ ?_
  · show "z" ∉ ["p"]; decide
  · show "z" ∉ ([] : List String); decide
  · exact Derivable.var (List.Mem.head _)
  · exact Derivable.circI (Derivable.var (List.Mem.head _))

/-! ### Axiom pins

`decide` and the explicit `List.Mem.head` keep every cell free of
`Classical.choice` and `Quot.sound`; `propext` remains, from the decidability
instances `decide` evaluates.  An earlier version discharged these goals with
`simp`, which cost all three axioms. -/

/-- info: 'LaxLogic.QLL.Smoke.identity' depends on axioms: [propext] -/
#guard_msgs in #print axioms identity

/-- info: 'LaxLogic.QLL.Smoke.val_top' does not depend on any axioms -/
#guard_msgs in #print axioms val_top

/-- info: 'LaxLogic.QLL.Smoke.forall_identity' depends on axioms: [propext] -/
#guard_msgs in #print axioms forall_identity

/-- info: 'LaxLogic.QLL.Smoke.left_unit' depends on axioms: [propext] -/
#guard_msgs in #print axioms left_unit

end LaxLogic.QLL.Smoke
