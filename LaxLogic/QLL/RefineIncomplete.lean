/-
# `LaxLogic.QLL.RefineIncomplete` — refinement is not complete, and here is why

`Interp.lean` interprets a formula as a *type of constraints* and `Refines` as
a proposition of Lean's own logic.  That is a shallow embedding, which is why
the report's headline result is conservativity over HOL rather than
completeness — and it is not a gap waiting to be filled.  The ambient logic is
strictly stronger than the object logic, and any argument available in it
counts as a refinement whether or not the calculus can reproduce it.

The witness below is the **Constant Domain** entailment

    ∀x. (A ∨ B(x))  ⊢  A ∨ ∀x. B(x)      (`x` not free in `A`)

which is *refinement-valid* and *not derivable*:

* valid, because to refine the conclusion it is enough to ask whether some
  individual takes the left disjunct — a classical case split, available in
  Lean and used below through `by_cases` and `Exists.choose`;
* underivable, by `CompleteTests.cd_not_prv`, which refutes it in a two-state
  Kripke model with different domains — the same fact that forced the domains
  of the canonical model to increase.

So the two semantics separate on a formula, and the separation is exactly the
strength of the ambient logic.  Completeness of a refinement semantics is a
reasonable goal only against a *fixed* object logic from the literature, not
against Lean.
-/
import LaxLogic.QLL.Interp
import LaxLogic.QLL.CompleteTests

namespace LaxLogic.QLL.RefineIncomplete

open LaxLogic.QLL LaxLogic.QLL.CompleteTests

/-- The Constant Domain entailment refines, in every model.

`FA` is `A` with no argument, so its refinement does not consult the
environment and the entailment is the genuine constant-domain shape. -/
theorem cd_refines {𝔐 : Model} (ρ : String → 𝔐.D)
    (f : Val 𝔐 (.forall_ (.or FA FB)))
    (hf : Refines 𝔐 [] ρ (.forall_ (.or FA FB)) f) :
    ∃ q, Refines 𝔐 [] ρ (.or FA (.forall_ FB)) q := by
  classical
  by_cases h : ∃ (d : 𝔐.D) (c : 𝔐.C), f d = .inl c
  · obtain ⟨d, c, hd⟩ := h
    refine ⟨.inl c, ?_⟩
    have hfd := hf d
    rw [hd] at hfd
    exact hfd
  · push_neg at h
    have h' : ∀ d : 𝔐.D, ∃ c : 𝔐.C, f d = .inr c := by
      intro d
      rcases hfd : f d with c | c
      · exact absurd hfd (h d c)
      · exact ⟨c, rfl⟩
    refine ⟨.inr (fun d => (h' d).choose), ?_⟩
    intro d
    have hfd := hf d
    rw [(h' d).choose_spec] at hfd
    exact hfd

/-- **Refinement is not complete.**  A formula the refinement semantics
validates in every model, and the calculus does not prove. -/
theorem refinement_not_complete :
    (∀ (𝔐 : Model) (ρ : String → 𝔐.D) (f : Val 𝔐 (.forall_ (.or FA FB))),
        Refines 𝔐 [] ρ (.forall_ (.or FA FB)) f →
        ∃ q, Refines 𝔐 [] ρ (.or FA (.forall_ FB)) q)
      ∧ ¬ Prv [.forall_ (.or FA FB)] (.or FA (.forall_ FB)) :=
  ⟨fun _ ρ f hf => cd_refines ρ f hf, cd_not_prv⟩

/-- info: 'LaxLogic.QLL.RefineIncomplete.refinement_not_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refinement_not_complete

end LaxLogic.QLL.RefineIncomplete
