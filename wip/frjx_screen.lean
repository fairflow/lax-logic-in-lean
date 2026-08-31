/-
# FRJX — Stage-1 screening

Countermodels and refutations found while writing the plan.  A `sorry`ed
lemma ASSERTS its statement, so every plan statement is screened before it
is banked.  This file holds what the screen found.
-/
import wip.gbu_search_circ

namespace FRJ.Gbu.X

open FRJ FRJ.Gbu

/-- `D` is *lift-closed*: a regular row may be re-read as an irregular row
over any retained `Ĝ`-context inside `Cl(Γ)`.  This is `(Lift)`. -/
def LiftClosed (G : Form) (D : FSeq → Prop) : Prop :=
  ∀ (Γ Θ : List Form) (C : Form), D (.reg Γ C) →
    (∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) → D (.irr [] Θ C)

/-! ## The repair cannot be a property of a database over FRJV

The first plan draft made `(Lift)` a closure condition on the database and
kept `Saturated G D`.  That is CONTRADICTORY, and the witness is the cell
the whole campaign is about.

`Saturated G D` carries `IsDatabase G D : ∀ s, D s → FDerivable G s`, so
every member must be FRJV-derivable.  Saturation forces a regular row for
`Gcc = ◯(◯p ⊃ p)` (`provableV_Gcc`); lift-closure then forces the irregular
row `∅ ; ∅ → Gcc`; and `no_irregular_circ_imp_self` says no such FRJV
disproof exists.

So `(Lift)` must extend the DERIVABILITY relation, not merely the database:
a campaign that keeps `Saturated` unchanged has an unsatisfiable hypothesis
and asserts nothing — the `CleanReg` failure again, one level up. -/

theorem not_saturated_liftClosed :
    ¬ ∃ D : FSeq → Prop, Saturated Gcc D ∧ LiftClosed Gcc D := by
  rintro ⟨D, hsat, hlift⟩
  obtain ⟨t, Γ, hd⟩ := provableV_Gcc
  obtain ⟨s', hs'mem, hsub⟩ := hsat.2 (.reg Γ Gcc) ⟨t, hd⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, _⟩ =>
      have hirr : D (.irr [] [] Gcc) :=
        hlift Γ' [] Gcc hs'mem (fun X hX => absurd hX List.not_mem_nil)
      obtain ⟨d⟩ := hsat.1 _ hirr
      exact FRJ.V.WCounter.no_irregular_circ_imp_self d

/-- info: 'FRJ.Gbu.X.not_saturated_liftClosed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_saturated_liftClosed

end FRJ.Gbu.X
