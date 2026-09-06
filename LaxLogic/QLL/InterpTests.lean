/-
# `LaxLogic.QLL.InterpTests` — `◯∀` and `◯∃` are genuinely two modalities

Fig. 5 gives them **the same rules**: its side condition reads only "if `Q = ∀`
or `Q = ∃`", so `val∀ *` and `val∃ *` are derived by one rule schema, and the
checker accepts both (`CertifyTests.lean`).  Nothing in the proof system tells
them apart.

Fig. 4 does.  This file exhibits one model and two constraints for which

    (φ : ◯∃P) holds and (φ : ◯∀P) fails,
    (ψ : ◯∀P) holds and (ψ : ◯∃P) fails,

so neither modality implies the other, and the subscript in Fig. 6 is carrying
content after all.  Both cells are `Prop`s proved by term, not by `decide`, so
there is nothing to trust in the harness.

## The model

One individual, and `Bool` as the type of constraints witnessing an atom.  `P`
is witnessed by `true` and not by `false`; that single asymmetry is all the
separation needs.
-/
import LaxLogic.QLL.Interp
import LaxLogic.QLL.Judgement

namespace LaxLogic.QLL.InterpTests

open LaxLogic.QLL LaxLogic.QLL.Surface

/-- One individual; atoms witnessed by `Bool`, and `P` holds of `true` only. -/
def 𝔅 : Model where
  D    := Unit
  C    := Bool
  fn   := fun _ _ => ()
  atom := fun _ _ c => c = true
  d₀   := ()
  c₀   := false

/-- The only valuation there is. -/
def ρ : String → 𝔅.D := fun _ => ()

/-! ## Fig. 3 computes the constraint types

`|P| = Bool`, and a `◯` layer turns a type into a predicate on it — a
*constraint*, in the report's sense: the set of witnesses it admits. -/

example : Val 𝔅 qf[P] = Bool := rfl
example : Val 𝔅 qf[⊥] = Unit := rfl
example : Val 𝔅 qf[◯∀ P] = (Bool → Prop) := rfl
example : Val 𝔅 qf[◯∃ P] = (Bool → Prop) := rfl
example : Val 𝔅 qf[∀a. P] = (Unit → Bool) := rfl
example : Val 𝔅 qf[∃a. P] = (Unit × Bool) := rfl

/-! ## The two separating constraints

`φ` admits every witness; `ψ` admits none. -/

/-- The constraint that admits everything. -/
def φ : Val 𝔅 qf[◯∀ P] := fun _ => True

/-- The unsatisfiable constraint. -/
def ψ : Val 𝔅 qf[◯∀ P] := fun _ => False

/-! ## `◯∃` without `◯∀`

`φ` admits `true`, which does witness `P` — so *some* admitted witness refines
`P`.  It also admits `false`, which does not — so not *every* one does. -/

example : Sat 𝔅 [] ρ qf[◯∃ P] φ := ⟨true, trivial, rfl⟩

example : ¬ Sat 𝔅 [] ρ qf[◯∀ P] φ := by
  intro h; exact Bool.noConfusion (h false trivial)

/-! ## `◯∀` without `◯∃`

The unsatisfiable constraint satisfies `◯∀` vacuously and can never satisfy
`◯∃`.  This is the direction that makes `◯∀` a *weakening* modality: it is
the reading under which "the constraint is contradictory" counts as success. -/

example : Sat 𝔅 [] ρ qf[◯∀ P] ψ := by
  intro _ hz; exact hz.elim

example : ¬ Sat 𝔅 [] ρ qf[◯∃ P] ψ := by
  intro h; exact h.elim fun _ hz => hz.1

/-! ## What Fig. 5 says about the same two formulas

Identical shape, identical rule, both accepted — the contrast with the two
refutations above is the whole point. -/

example : qj[⊢ val∀ * : ◯∀ ⊤] := ⟨.circI .topI⟩
example : qj[⊢ val∃ * : ◯∃ ⊤] := ⟨.circI .topI⟩

/-! ## The non-modal clauses, for coverage

Every arm of Fig. 4 exercised at least once. -/

example : Sat 𝔅 [] ρ qf[⊤] () := trivial
example : ¬ Sat 𝔅 [] ρ qf[⊥] () := id
example : Sat 𝔅 [] ρ qf[P ∧ P] (true, true) := ⟨rfl, rfl⟩
example : Sat 𝔅 [] ρ qf[P ∨ P] (.inl true) := rfl
example : Sat 𝔅 [] ρ qf[P ⊃ P] id := fun _ h => h
example : Sat 𝔅 [] ρ qf[∀a. P] (fun _ => true) := fun _ => rfl
example : Sat 𝔅 [] ρ qf[∃a. P] ((), true) := rfl

/-! ## Terms are interpreted, not substituted

A bound individual is looked up in the environment; a free one in `ρ`.  With a
one-element domain the values are forced, so this only checks that the
recursion reaches the arguments at all. -/

example : Sat 𝔅 [] ρ qf[∀a. Q(a, x, f(a))] (fun _ => true) := fun _ => rfl

end LaxLogic.QLL.InterpTests
