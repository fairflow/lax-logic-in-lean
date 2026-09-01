/-
# FRJX — shared definitions, and Stage-1 screening

Countermodels and refutations found while writing the plan.  A `sorry`ed
lemma ASSERTS its statement, so every plan statement is screened before it
is banked.  This file holds what the screen found.
-/
import wip.gbu_search_circ

namespace FRJ.Gbu.X

open FRJ FRJ.Gbu

private def pvx : Form := .atom "p"

/-- Derivability extended by `(Lift)`.  The new clause produces `.irr` rows
only, which is why §1.1 below is available. -/
inductive LiftClosure (G : Form) : FSeq → Prop
  | base {s : FSeq} : FDerivable G s → LiftClosure G s
  | lift {Γ Θ : List Form} {C : Form} :
      LiftClosure G (.reg Γ C) →
      (∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) →
      LiftClosure G (.irr [] Θ C)

/-- `Saturated`, with the base derivability relation a parameter. -/
def SaturatedOver (Base D : FSeq → Prop) : Prop :=
  (∀ s, D s → Base s) ∧ ∀ s, Base s → ∃ s', D s' ∧ Subsumes s s'

/-- Soundness of the database, regular rows only.  This is the only
soundness the completeness theorem consumes: it is what turns `PLL G` into
`¬ D ▷ (∅ ⇒g G)`. -/
def RegSound (D : FSeq → Prop) : Prop :=
  ∀ (Γ : List Form) (C : Form), D (.reg Γ C) →
    ∃ K : Kripke, (∀ X ∈ Γ, K.force K.root X) ∧ ¬ K.force K.root C


/-- The first draft's database-level reading of `(Lift)`, kept because the
refutation below is about it. -/
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


/-! ## X14 is REFUTED

`(X14)` asserted that at a critical context whose implication has an
undisproved, `◯`-carrying, oversized antecedent, `Ω →g ◯Z` is derivable.
It carries no hypothesis that `◯Z` is ENTAILED by `Ω`, and that is fatal:
the search only ever reaches such a node holding `¬ D ▷ (Ω ⇒g ◯Z)`, which
(soundness plus completeness of the database) means `Ω ⊨ ◯Z`.  Without it
the statement is simply too strong.

The witness is the `omegaNI` cell of `wip/gbu_circ.lean` §11 with the
antecedent made modal, which is what `hsz` needs and what `omegaNI`'s own
`A = p` does not give:

    G = p ⊃ ((◯p ⊃ p) ⊃ (r ∨ ◯r)),   Ω = { p , ◯p ⊃ p },   A = ◯p,  Z = r

`A = ◯p` carries a `◯` and `|◯p| = |◯r|`, so `hsz` holds; `Ω ⊨ ◯p` (the
unit on `p ∈ Ω`), so `A` is undisproved; and `Ω ⊭ ◯r`, so `Ω →g ◯r` is not
derivable — by `soundIC` on the model `⋈`-free `◯∈` over `Ax^R` extracts. -/

private def rvx : Form := .atom "r"

/-- `G = p ⊃ ((◯p ⊃ p) ⊃ (r ∨ ◯r))`. -/
def Gx : Form :=
  .imp pvx (.imp (.imp (.circ pvx) pvx) (.or rvx (.circ rvx)))

/-- `Ω = { p , ◯p ⊃ p }` — critical: atoms and implications only. -/
def omegaX : List Form := [pvx, .imp (.circ pvx) pvx]

theorem omegaX_critical : ∀ X ∈ omegaX, X ∈ gAt Gx ++ gImp Gx := by decide

theorem circr_goal : Form.circ rvx ∈ sfR Gx := by decide

/-- `hsz`: the antecedent `◯p` carries a `◯` and is not smaller than `◯r`. -/
theorem hsz_holds :
    ¬ ((Form.circ pvx).hasCirc = false ∨
        (Form.circ pvx).size < (Form.circ rvx).size) := by decide

/-- The context of the disproof closes `Ω`: `p` is in it, and `◯p ⊃ p` is
`Clo`-derived from `p` by the `imp` clause. -/
theorem clo_omegaX : ∀ X ∈ omegaX, Clo (rm (gAt Gx) rvx) X := by
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .base (by decide)
  · rcases List.mem_cons.mp hX' with rfl | hX''
    · exact .imp (.base (by decide))
    · exact absurd hX'' List.not_mem_nil

/-- `Ω ⊭ ◯r`: the model is extracted from `◯∈` over `Ax^R`, not built by
hand.  Hence `Ω →g ◯r` is NOT derivable in `Gbu◯(Gx)`, by `soundIC`. -/
theorem not_gbuIC_omegaX : ¬ Nonempty (GbuIC Gx omegaX (.circ rvx)) := by
  rintro ⟨d⟩
  obtain ⟨K, a, hf, hnf⟩ :=
    frjv_countermodel
      (FRJVr.circIn (FRJVr.axR rvx (by decide) (by decide) (CtxEq.refl _))
        (Or.inl rfl) circr_goal)
  exact hnf (soundIC d a (fun X hX => clo_forces hf (clo_omegaX X hX)))

/-- info: 'FRJ.Gbu.X.not_gbuIC_omegaX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_gbuIC_omegaX


/-! ### The remaining hypotheses, and the refutation

`hnA` says the antecedent `◯p` is not irregularly disproved.  It is not:
`p ∈ Ω`, so `Ω ⊨ ◯p` by the unit, and neither an FRJV irregular disproof
nor a `(Lift)`ed regular one can exist over a context that forces it. -/

/-- `(Lift)` adds no REGULAR rows — its conclusion is always `.irr`.  This
is `(X1)` of the plan; proved here because the screen needs it. -/
theorem liftClosure_reg {G : Form} {Γ : List Form} {C : Form}
    (h : LiftClosure G (.reg Γ C)) : FDerivable G (.reg Γ C) := by
  cases h with
  | base h => exact h

/-- `Subsumes` is reflexive, so the closure is saturated over itself. -/
theorem subsumes_refl : ∀ s : FSeq, Subsumes s s
  | .reg _ _ => ⟨rfl, fun {_} h => h⟩
  | .regC _ _ => ⟨rfl, fun {_} h => h⟩
  | .irr _ _ _ => ⟨rfl, CtxEq.refl _, fun {_} h => h⟩

theorem saturatedOver_self (G : Form) :
    SaturatedOver (LiftClosure G) (LiftClosure G) :=
  ⟨fun _ h => h, fun s hs => ⟨s, hs, subsumes_refl s⟩⟩

/-- `Ω ⊨ ◯p`, by the unit on `p ∈ Ω`. -/
theorem omegaX_valid {K : Kripke} {a : K.W} (h : K.forces a omegaX) :
    K.force a (.circ pvx) :=
  fun b hb => ⟨b, K.rm_refl b, K.force_mono hb (h pvx List.mem_cons_self)⟩

/-- Hence the antecedent is undisproved, over the LIFTED derivability too:
the `base` case is the FRJV argument, and a `(Lift)`ed row would carry a
regular disproof of `◯p` whose model root forces `Ω`. -/
theorem not_evalI_omegaX_ante :
    ¬ EvalI (LiftClosure Gx) omegaX (.circ pvx) := by
  rintro ⟨St, Th, hmem, hSt, hΩ⟩
  cases hmem with
  | base hb =>
      refine not_evalI_circ_of_valid' (G := Gx) (saturated_fderivable Gx).1
        (by decide) (fun _ _ h => omegaX_valid h) ?_ ⟨St, Th, hb, hSt, hΩ⟩
      intro ats hz hsub
      have hp := List.mem_filter.mp (hsub pvx List.mem_cons_self)
      rw [show classForce ats pvx = true from hp.2] at hz
      exact Bool.noConfusion hz
  | lift hreg hΘ =>
      obtain ⟨t, ⟨d⟩⟩ := liftClosure_reg hreg
      obtain ⟨K, a, hf, hnf⟩ := frjv_countermodel d
      refine hnf (omegaX_valid (fun X hX => ?_))
      have h := hΩ hX
      rw [List.nil_append] at h
      exact clo_forces hf (hΘ X h).1

/-- **(X14) IS REFUTED.**  Every hypothesis holds at `Gx`, `Ω = {p, ◯p ⊃ p}`,
`A = ◯p`, `B = p`, `Z = r`, and the conclusion fails.

The defect is in the statement, not the calculus: `(X14)` never says the
goal is ENTAILED.  The search reaches such a node only while holding
`¬ D ▷ (Ω ⇒g ◯Z)`, and that hypothesis is exactly what is missing. -/
theorem not_X14 :
    ¬ (∀ (G : Form) (D : FSeq → Prop), SaturatedOver (LiftClosure G) D →
        ∀ (Ω : List Form) (A B Z : Form),
          (∀ X ∈ Ω, X ∈ gAt G ++ gImp G) → Form.imp A B ∈ Ω →
          Form.circ Z ∈ sfR G → ¬ EvalI D Ω A →
          ¬ (A.hasCirc = false ∨ A.size < (Form.circ Z).size) →
          Nonempty (GbuIC G Ω (.circ Z))) := by
  intro h
  exact not_gbuIC_omegaX
    (h Gx (LiftClosure Gx) (saturatedOver_self Gx) omegaX
      (.circ pvx) pvx rvx omegaX_critical
      (List.mem_cons_of_mem _ List.mem_cons_self) circr_goal
      not_evalI_omegaX_ante hsz_holds)

/-- info: 'FRJ.Gbu.X.not_X14' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_X14

end FRJ.Gbu.X
