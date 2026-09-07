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
import LaxLogic.QLL.Surface

namespace LaxLogic.QLL.Smoke

open Form Pf LaxLogic.QLL.Surface

/-- `⊢ λz.z : A ⊃ A`.  Exercises `impI`'s freshness and proof-variable opening
against `var`'s lookup. -/
def identity (A : Form) : Derives (lam (bvar 0)) [] (imp A A) := by
  refine Derives.impI "z" ⟨?_, ?_⟩ ?_
  · show "z" ∉ ([] : List String); decide
  · show "z" ∉ ([] : List String); decide
  · exact Derives.var (List.Mem.head _)

/-- `⊢ val_Q(*) : ◯_Q ⊤`, for either modality — the rule is `Q`-parametric, so
one derivation serves both. -/
def val_top (q : Q) : Derives (val q star) [] (circ q top) :=
  Derives.circI Derives.topI

/-- `⊢ ⟨λz.z | x⟩ : ∀x. P(x) ⊃ P(x)`.  The point of this one is the binder
interaction: `allI` opens an *individual* while `impI` opens a *proof*
variable, and neither may disturb the other's indices. -/
def forall_identity : Derives (gen (lam (bvar 0))) [] qf[∀x. P(x) ⊃ P(x)] := by
  refine Derives.allI "x" ⟨?_, ?_, ?_⟩ ?_
  · show "x" ∉ ([] : List String); decide
  · show "x" ∉ ([] : List String); decide
  · show "x" ∉ ([] : List String); decide
  · refine Derives.impI "z" ⟨?_, ?_⟩ ?_
    -- the goal here is `fvP` applied to an unreduced `openI`, so `simp` has no
    -- rewrite to make; `decide` evaluates through it
    · exact by decide
    · exact by decide
    · exact Derives.var (List.Mem.head _)

/-- `p : ◯_Q A ⊢ let_Q z ⇐ p in val_Q(z) : ◯_Q A` — the monad's left unit, as a
shape check on `circE`.  `A` must be supplied explicitly: `circE`'s `A` occurs
only in its premises, so the conclusion does not determine it. -/
def left_unit (q : Q) (A : Form) :
    Derives (letQ q (fvar "p") (val q (bvar 0))) [(fvar "p", circ q A)] (circ q A) := by
  refine Derives.circE (A := A) "z" ⟨?_, ?_⟩ ?_ ?_
  · show "z" ∉ ["p"]; decide
  · show "z" ∉ ([] : List String); decide
  · exact Derives.var (List.Mem.head _)
  · exact Derives.circI (Derives.var (List.Mem.head _))

/-! ### The `Prop` view comes for free

`Nonempty` collapses a derivation to the proposition that one exists.  Nothing
is proved here beyond `Nonempty.intro`; the point is that both views are
available from the single family. -/

example (A : Form) : Derivable (lam (bvar 0)) [] (imp A A) := ⟨identity A⟩

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
