/-
# `(R^bar)` — the proposed irregular rule, and its soundness

`wip/gbu_search_circ.lean` (§2026-08-31c) shows that the irregular
duality FAILS at `◯(◯Z ⊃ Z)`: `FRJV(G)` has no irregular DISPROOF of it
(`no_irregular_circ_imp_self`), and `Gbu◯(G)` cannot prove `∅ →g
◯(◯p ⊃ p)` either — nor may it, since `soundIC` would then make the
formula valid and `GccWitness` refutes it.

The gap is on the FRJV side.  A REGULAR disproof of `◯(◯p ⊃ p)` exists
(`provableV_Gcc`, obtained by the barren `⋈^◯` join), but no rule turns
a regular disproof into an irregular one.  The proposed rule does:

        Γ ⇒ C          Θ ⊆ Ĝ,   Θ ⊆ Cl(Γ)
    ─────────────────────────────────────────  (R^bar)
                   ∅ ; Θ → C

This file states and proves its soundness clause — the case that would
be added to `lemma39I` — WITHOUT touching `FRJ/CalculusV.lean`.  Nothing
here changes the calculus; it is the certificate to review before any
rule is added.
-/
import FRJ.SoundV

namespace FRJ.V.RBar

open FRJ Form

/-! ## The obligation

`lemma39I` reads an irregular disproof `Σ ; Θ → C` not as a model but as
a SCHEMA: in every premodel `P`, at every infallible world `w` whose
label lies in `Cl(Σ ++ Θ)`, with the disproof's regular components
grafted above `w`, and with `w ⊩ Σ ∩ sfm C`, the world `w` refutes `C`.

    lemma39I (d : FRJVi G Σ Θ C) (P) (hP : ClosedLbl P) (w) :
      ¬ P.fal w →
      (∀ X ∈ P.lbl w, Clo (Σ ++ Θ) X) →
      (∀ i : RegIdx d, RootAbove P hP w (preI d i) (preI_closed d i)) →
      (P.toKripke hP).forces w (cap Σ (sfm C)) →
      ¬ (P.toKripke hP).force w C

`(R^bar)` designates ONE regular component, the premise `d` itself, so
its clause is the statement below with `RootAbove P hP w (preR d)` in
place of the component quantifier. -/

/-- **`(R^bar)` is sound.**  The clause `lemma39I` would have to prove
for the new constructor, discharged from monotonicity of forcing alone.

The component's root `v` sits ABOVE `w`, and `v` refutes `C` by Lemma
3.9(i) for the regular judgment; forcing is monotone, so `w` refutes `C`
too.  Neither the infallibility of `w`, nor the label bound, nor the
`Σ`-forcing hypothesis is used — which is why the rule carries no
tag condition, no `Υ` condition and no cleanliness condition. -/
theorem rbar_lemma39I {G : Form} {t : Tag} {Γ Θ : List Form} {C : Form}
    (d : FRJVr G t Γ C)
    (_hΘ : ∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G)
    (P : PreModel) (hP : ClosedLbl P) (w : P.W)
    (_hfal : ¬ P.fal w)
    (_hlbl : ∀ X ∈ P.lbl w, Clo ([] ++ Θ) X)
    (hcomp : RootAbove P hP w (preR d) (preR_closed d))
    (_hst : (P.toKripke hP).forces w (cap [] (sfm C))) :
    ¬ (P.toKripke hP).force w C := by
  intro hC
  obtain ⟨v, hwv, hiff⟩ := hcomp
  exact (lemma39R d).2 ((hiff C).mp ((P.toKripke hP).force_mono hwv hC))

/-- info: 'FRJ.V.RBar.rbar_lemma39I' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rbar_lemma39I

/-! ## What the side conditions are for

`Θ ⊆ Cl(Γ)` and `Θ ⊆ Ĝ` are NOT used above.  They are the CONSUMER's
interface: a join that grafts this component above its own new root must
establish `RootAbove`, and it can do so only when the new root's label
is contained in `Cl(Γ)`.  Since the join's root label is built from the
premises' zones, `Θ ⊆ Cl(Γ)` is exactly what makes that containment go
through — and it is verbatim the condition

    hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G

that `⊃∉` (`impNotIn`) and `◯∉` (`circNotIn`) already carry.  So
`(R^bar)` presents the SAME interface to the joins as the two rules that
already supply regular components; no join needs a new side condition.

## Which rules it replaces

* **`⊃∉` becomes redundant.**  Its premises are `d : Γ ⇒ B`,
  `Clo Γ A`, `hTh`, and `¬ Cl(Θ) ∋ A`.  From the first two, `⊃∈`
  (`impIn`) gives `Γ ⇒ A ⊃ B` with no side condition at all, and
  `(R^bar)` then gives `∅ ; Θ → A ⊃ B`.  So `⊃∉` is `(R^bar)` composed
  with `⊃∈`, plus a side condition `¬ Cl(Θ) ∋ A` that `(R^bar)` does not
  need.  Adding `(R^bar)` lets `⊃∉` be deleted.

* **`◯∉` is NOT redundant**, and this is the whole point.  Its premise
  is a regular disproof of `Z`, not of `◯Z`: it climbs the modality,
  and `(R^bar)` does not.  `(R^bar)` reaches `∅ ; Θ → ◯Z` only from a
  regular disproof of `◯Z` — which `◯∈` supplies under the SAME clean
  tag that `◯∉` demands, but which the barren `⋈^◯` join supplies with
  NO tag condition.  That is exactly the missing route: `◯(◯p ⊃ p)` has
  a regular disproof by `⋈^◯` (`GccWitness`) and none by `◯∈`, so
  `(R^bar)` yields the irregular disproof that `◯∉` cannot.

So the proposal is: ADD `(R^bar)`, DELETE `⊃∉`, KEEP `◯∉`.

## What it also delivers

Two invertibility clauses of Lemma 9 that the search needed and could
not have, both now immediate, because `(R^bar)` makes every regularly
disprovable sequent irregularly disprovable over any `Ĝ`-context inside
`Cl(Γ)`:

* `(∨-inv)`  `D ▷ (Ω ⇒g C₁)` and `D ▷ (Ω ⇒g C₂)`  ⟹  `D ▷ (Ω ⇒g C₁ ∨ C₂)`
  — via `⋈^∨` on the two `(R^bar)` premises.
* `(★)`      `D ▷ (Ω ⇒g Z)`  ⟹  `D ▷ (Ω ⇒g ◯Z)` on a critical `Ω`
  — via `(R^bar)` then `gbuSuccCirc`.

## What still has to be checked before implementing

1. Every `match` over `FRJVi` gains a case: `transportVi`, `preI`,
   `RegIdx`, `preI_closed`, `lemma39I`, the decision procedures and the
   searchers.  Mechanical, but it touches the mutual recursion.
2. `RegIdx` for the new constructor is `Unit` and `preI` is `preR d`.
   The mutual induction `lemma39R`/`lemma39I` must still terminate:
   `(R^bar)` makes an irregular disproof strictly larger than its
   regular premise, so the structural order is unchanged.
3. TERMINATION OF SEARCH is the real risk, not soundness.  `(R^bar)`
   makes `EvalI` at least as strong as `EvalR` over `Ĝ`-contexts, so the
   `∨` and `◯` branches of the search will take the join route far more
   often; the `Wg` measure must be re-checked against the new traffic.
-/

end FRJ.V.RBar
