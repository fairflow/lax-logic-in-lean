/-
# Constraint extraction on the repository's own calculus

Everything so far has been at the meta level: `Debt` and `◯∀` are Lean
propositions, and `postpone` records Lean goals. This module connects that to
the object logic — `LaxND`, the natural deduction system of `PLLNDCore.lean`
that this development's results are stated in.

The claim is small and the proof is a structural induction: **`Debt C` is a
sound interpretation of `◯` for PLL natural deduction.** Read `◯φ` as "φ modulo
the outstanding constraint C" and every rule of `LaxND` goes through, so a
derivation of `◯φ` yields, for *every* constraint `C`, a proof of `Debt C ⟦φ⟧`.
The two lax rules are exactly the two `Debt` combinators:

| `LaxND` rule | becomes |
| --- | --- |
| `laxIntro : Γ ⊢ φ → Γ ⊢ ◯φ` | `Debt.ret` |
| `laxElim : Γ ⊢ ◯φ → φ::Γ ⊢ ◯ψ → Γ ⊢ ◯ψ` | bind at a fixed constraint |

## Where this sits relative to the two existing readings

`PLLConstraints.lean` already interprets `◯φ` as `M × ⟦φ⟧` for a writer monad
over `(M, op, e)`, so that *evaluating a proof term is constraint extraction*.
That is the **◯∃** side of Fig. 4: the constraint is carried *alongside* a
witness, proof-relevantly, and instantiating `(ℕ, +, 0)` or `(ℕ, max, 0)` gives
sequential and parallel delay.

This module is the **◯∀** side: the constraint is what the claim is weakened
*by*. Both are constraint extraction; they are the paper's two modalities, and
having both in the repository means a derivation can be read either way.

## The boundary, stated

The interpretation here uses **one** constraint `C` for every occurrence of `◯`.
That is the simplest sound model, and it collapses iterated modalities —
`Debt C (Debt C A)` is equivalent to `Debt C A`. Letting the constraint vary
with the occurrence is what Mendler's `(Ω*, [], @)` and F&M's standard contexts
do; in this repository that is `StdCtx` and `subC` in
`PLLCtxCompleteness.lean`, whose Theorem 6 is the completeness statement for
exactly that richer model. So this file is the easy half of the bridge, and the
`StdCtx` connection is the part still to build.
-/

import LaxLogic.PLLNDCore
import LaxLogic.Obligation.Mendler

namespace LaxLogic.Obligation.PLLBridge

open PLLFormula PLLND

/-- The **`◯∀` interpretation** of PLL formulas at a fixed constraint `C` and a
valuation `v` of atoms. Every clause is the ordinary one except the modality,
which is `Debt C`. -/
def interp (C : Prop) (v : String → Prop) : PLLFormula → Prop
  | .prop a => v a
  | .falsePLL => False
  | .and φ ψ => interp C v φ ∧ interp C v ψ
  | .or φ ψ => interp C v φ ∨ interp C v ψ
  | .ifThen φ ψ => interp C v φ → interp C v ψ
  | .somehow φ => Debt C (interp C v φ)

@[simp] theorem interp_somehow (C : Prop) (v : String → Prop) (φ : PLLFormula) :
    interp C v (.somehow φ) = Debt C (interp C v φ) := rfl

/-- A context holds when all of its formulas do. -/
def interpCtx (C : Prop) (v : String → Prop) : List PLLFormula → Prop
  | [] => True
  | φ :: Γ => interp C v φ ∧ interpCtx C v Γ

theorem interpCtx.lookup {C : Prop} {v : String → Prop} :
    ∀ {Γ : List PLLFormula} {φ : PLLFormula},
      interpCtx C v Γ → φ ∈ Γ → interp C v φ
  | _ :: _, _, ⟨hφ, _⟩, .head _ => hφ
  | _ :: Γ, _, ⟨_, hΓ⟩, .tail _ h => interpCtx.lookup (Γ := Γ) hΓ h

/-- **Soundness: `Debt C` interprets `◯`.**

Every rule of `LaxND` is validated. The modal cases are the two `Debt`
combinators and nothing else, which is the content of the claim: reading `◯` as
an outstanding proof obligation is not an analogy but a model. -/
theorem sound {Γ : List PLLFormula} {φ : PLLFormula}
    (C : Prop) (v : String → Prop) (p : LaxND Γ φ) :
    interpCtx C v Γ → interp C v φ := by
  induction p with
  | iden h => exact fun ρ => interpCtx.lookup ρ h
  | falsoElim _ _ ih => exact fun ρ => (ih ρ).elim
  | impIntro _ ih => exact fun ρ a => ih ⟨a, ρ⟩
  | impElim _ _ ih₁ ih₂ => exact fun ρ => (ih₁ ρ) (ih₂ ρ)
  | andIntro _ _ ih₁ ih₂ => exact fun ρ => ⟨ih₁ ρ, ih₂ ρ⟩
  | andElim1 _ ih => exact fun ρ => (ih ρ).1
  | andElim2 _ ih => exact fun ρ => (ih ρ).2
  | orIntro1 _ ih => exact fun ρ => Or.inl (ih ρ)
  | orIntro2 _ ih => exact fun ρ => Or.inr (ih ρ)
  | orElim _ _ _ ih₀ ih₁ ih₂ =>
      exact fun ρ => (ih₀ ρ).elim (fun a => ih₁ ⟨a, ρ⟩) (fun b => ih₂ ⟨b, ρ⟩)
  -- `◯I` is `Debt.ret`: a finished proof owes nothing, so it owes `C`.
  | laxIntro _ ih => exact fun ρ => Debt.ret (ih ρ) C
  -- `◯E` is bind at a fixed constraint: discharge once, use twice.
  | laxElim _ _ ih₁ ih₂ => exact fun ρ c => ih₂ ⟨ih₁ ρ c, ρ⟩ c

/-- **What a `LaxND` derivation of `◯φ` gives you**: for every constraint `C`,
a proof of `φ` modulo `C`. This is constraint extraction on the object logic,
stated in the obligation library's own vocabulary. -/
theorem debt_of_lax {φ : PLLFormula} (C : Prop) (v : String → Prop)
    (p : LaxND [] (.somehow φ)) : Debt C (interp C v φ) :=
  sound C v p trivial

/-- The single-constraint model collapses iterated modalities. Recorded rather
than hidden: it is the precise sense in which this bridge is the easy half. -/
theorem interp_somehow_idem (C : Prop) (v : String → Prop) (φ : PLLFormula) :
    interp C v (.somehow (.somehow φ)) ↔ interp C v (.somehow φ) :=
  ⟨fun h c => h c c, fun h c _ => h c⟩

/-! ### `◯◯M` and `◯M`: equi-inhabited, but not the same term

`interp_somehow_idem` says the two are equivalent *as propositions*. In `Prop`
that is the end of the matter: `propext` turns the equivalence into an equality
of propositions, and Lean's definitional proof irrelevance then makes any two
proofs of it equal, so nothing distinguishes `◯◯M` from `◯M`.

**Above `Prop` it should not collapse, and does not.** Under the writer reading
of `PLLConstraints.lean`, `◯φ` is `M × ⟦φ⟧`, so `◯◯φ` is `M × (M × ⟦φ⟧)` — a
genuinely different type. The multiplication that takes one to the other is a
real computation, `(c, (d, a)) ↦ (op c d, a)`, and it is **not injective**: how
the constraint was apportioned between the two modalities is destroyed. For the
timing reading that apportionment is the point — `◯◯` records two delays and
the multiplication is the deliberate act of adding them, so `1 then 2` and
`3 then 0` are different proofs with the same total. -/

/-- The monad multiplication of the writer reading: combine the two constraints
of an iterated modality. -/
def writerMul {M A : Type} (op : M → M → M) : M × (M × A) → M × A :=
  fun p => (op p.1 p.2.1, p.2.2)

/-- **The collapse loses information.** Two distinct proofs of `◯◯φ` with the
same image under the multiplication — so above `Prop`, `◯◯` is strictly more
informative than `◯`, and the equivalence of `interp_somehow_idem` is available
only because `Prop` is proof-irrelevant. -/
theorem writerMul_not_injective :
    ((1, (2, ())) : Nat × (Nat × Unit)) ≠ (3, (0, ())) ∧
      writerMul (· + ·) ((1, (2, ())) : Nat × (Nat × Unit))
        = writerMul (· + ·) ((3, (0, ())) : Nat × (Nat × Unit)) :=
  ⟨by decide, rfl⟩

/-- With `C := True` the interpretation is the ordinary one: `◯` disappears.
The degenerate end of the model, and a sanity check that `Debt` is not adding
strength. -/
theorem interp_true (v : String → Prop) (φ : PLLFormula) :
    interp True v (.somehow φ) ↔ interp True v φ :=
  ⟨fun h => h trivial, fun h _ => h⟩

/-- With `C := False` everything modal is vacuous — the object-logic form of
`Debt.vacuous`, and of Matthew's gloss: if the constraint is not true, the
belief says nothing. -/
theorem interp_false (v : String → Prop) (φ : PLLFormula) :
    interp False v (.somehow φ) :=
  fun h => h.elim

/-! ## Gates

Soundness of the interpretation rests on nothing: not `propext`, not
`Quot.sound`. Reading `◯` as an outstanding obligation is a model of PLL
natural deduction in the base logic, with no assumptions at all. -/

/-- info: 'LaxLogic.Obligation.PLLBridge.sound' does not depend on any axioms -/
#guard_msgs in
#print axioms sound

/-- info: 'LaxLogic.Obligation.PLLBridge.debt_of_lax' does not depend on any axioms -/
#guard_msgs in
#print axioms debt_of_lax

end LaxLogic.Obligation.PLLBridge
