/-
BiLax (a) — THE INTERNALISATION THEOREM.

This is what co-implication is *for*, and what rounds 1–2 failed to
use: `⤙` turns the FAILURE of an entailment — a ∀-over-models
statement — into the SATISFIABILITY of a single formula.

    A ⊢ B   ⟺   ⊢ ¬(A ⤙ B)          (co-residuation at C := ⊥)
    A ⊬ B   ⟺   A ⤙ B is satisfiable

Non-entailment stops being "no proof exists" (the absence of an
object) and becomes "this formula has a model" (the presence of one) —
the precondition for a POSITIVE calculus of disproof.  What syntactic
object witnesses the ∃ is the next question (a rejection calculus);
this file establishes that the reduction itself is EXACT, in both
directions, for PLL.

**A design finding, and the reason this file works over plain
`ConstraintModel`s.**  Co-implication needs NO new frame conditions:
its persistence uses only `Ri`-transitivity (`cforce_hered`).  All the
retrospective machinery of `BiModel` — `Rc`, `square_c`, `counit_c`,
`serial_c` — is needed for the co-lax MODALITY `◯∃`, not for `⤙`.  So
the internalisation lives over PLL's own semantics.

**A refuted attempt, recorded** (keep the corpse).  A first version
proved the completeness direction by adjoining a fallible top world to
any constraint model, to satisfy `serial_c`.  That is UNSOUND for
forcing: a fallible top `Rm`-reachable from every world makes `◯φ`
true *everywhere* (take the top as the witness), so the extension does
not preserve the forward fragment.  The same phenomenon as everywhere
else here — fallibility trivialises the future.
-/
import BiLax.Syntax
import LaxLogic.PLLCompleteness

namespace BiLax

open PLLND

/-- Forcing for the `◯∃`-free bi-lax language over a PLAIN constraint
model: PLL's clauses plus the backward-looking `⤙`.  (`◯∃` gets the
empty clause — it is not in this fragment, and `cforce` is never
applied to a `◯∃`-formula here.) -/
def cforce (C : ConstraintModel) : C.W → BiForm → Prop
  | w, .prop a => w ∈ C.V a
  | w, .bot => w ∈ C.F
  | w, .and A B => cforce C w A ∧ cforce C w B
  | w, .or A B => cforce C w A ∨ cforce C w B
  | w, .imp A B => ∀ v, C.Ri w v → cforce C v A → cforce C v B
  | w, .coimp A B => ∃ v, C.Ri v w ∧ cforce C v A ∧ ¬ cforce C v B
  | w, .lax A => ∀ v, C.Ri w v → ∃ u, C.Rm v u ∧ cforce C u A
  | _, .colax _ => False

/-- **Co-implication is persistent over ANY constraint model** — the
only law it uses is transitivity of `Ri`.  No `Rc`, no `square_c`. -/
theorem cforce_hered (C : ConstraintModel) {A : BiForm} :
    ∀ {w v : C.W}, C.Ri w v → cforce C w A → cforce C v A := by
  induction A with
  | prop a => exact fun h hw => C.hered_V h hw
  | bot => exact fun h hw => C.hered_F h hw
  | and A B ihA ihB => exact fun h hw => ⟨ihA h hw.1, ihB h hw.2⟩
  | or A B ihA ihB =>
      exact fun h hw =>
        hw.elim (fun x => .inl (ihA h x)) (fun x => .inr (ihB h x))
  | imp A B ihA ihB => exact fun h hw u hvu hu => hw u (C.trans_i h hvu) hu
  | coimp A B ihA ihB =>
      rintro w v h ⟨u, huw, hA, hnB⟩
      exact ⟨u, C.trans_i huw h, hA, hnB⟩
  | lax A ih => exact fun h hw u hvu => hw u (C.trans_i h hvu)
  | colax A ih => exact fun _ hw => absurd hw not_false

/-- On embedded PLL formulas, `cforce` is PLL forcing. -/
theorem cforce_emb (C : ConstraintModel) (φ : PLLFormula) :
    ∀ w : C.W, cforce C w (emb φ) ↔ C.force w φ := by
  induction φ with
  | prop a => exact fun w => Iff.rfl
  | falsePLL => exact fun w => Iff.rfl
  | and φ ψ ihφ ihψ => exact fun w => and_congr (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ => exact fun w => or_congr (ihφ w) (ihψ w)
  | ifThen φ ψ ihφ ihψ =>
      intro w
      constructor
      · intro h v hv hφ
        exact (ihψ v).mp (h v hv ((ihφ v).mpr hφ))
      · intro h v hv hφ
        exact (ihψ v).mpr (h v hv ((ihφ v).mp hφ))
  | somehow φ ih =>
      intro w
      constructor
      · intro h v hv
        obtain ⟨u, hu, hφ⟩ := h v hv
        exact ⟨u, hu, (ih u).mp hφ⟩
      · intro h v hv
        obtain ⟨u, hu, hφ⟩ := h v hv
        exact ⟨u, hu, (ih u).mpr hφ⟩

/-- Satisfiability of a co-implication over the PLL model class. -/
def CoimpSat (A B : BiForm) : Prop :=
  ∃ (C : ConstraintModel) (w : C.W), cforce C w (A ⤙ B)

/-- **THE INTERNALISATION THEOREM, semantic form**: `A ⤙ B` is
satisfiable exactly when `A` fails to entail `B`. -/
theorem coimp_sat_iff_not_entail (A B : BiForm) :
    CoimpSat A B ↔
      ¬ (∀ (C : ConstraintModel) (w : C.W), cforce C w A → cforce C w B) := by
  constructor
  · rintro ⟨C, w, v, hvw, hA, hnB⟩ hc
    exact hnB (hc C v hA)
  · intro h
    classical
    by_contra hns
    refine h (fun C w hA => ?_)
    by_contra hnB
    exact hns ⟨C, w, w, C.refl_i w, hA, hnB⟩

/-- **THE INTERNALISATION, for PLL**: non-derivability of `φ ⊢ ψ` is
EQUIVALENT to satisfiability of the single formula `emb φ ⤙ emb ψ`.

Left to right is PLL completeness (a countermodel exists and witnesses
the co-implication at its own world, by reflexivity of `Ri`); right to
left is PLL soundness. -/
theorem not_laxND_iff_coimp_sat (φ ψ : PLLFormula) :
    ¬ Nonempty (LaxND [φ] ψ) ↔ CoimpSat (emb φ) (emb ψ) := by
  classical
  constructor
  · intro h
    obtain ⟨C, w, hφ, hnψ⟩ : ∃ (C : ConstraintModel) (w : C.W),
        C.force w φ ∧ ¬ C.force w ψ := by
      by_contra hcon
      push_neg at hcon
      exact h (completeness (fun C w hΓ => hcon C w (hΓ φ (by simp))))
    exact ⟨C, w, w, C.refl_i w, (cforce_emb C φ w).mpr hφ,
      fun hc => hnψ ((cforce_emb C ψ w).mp hc)⟩
  · rintro ⟨C, w, v, hvw, hA, hnB⟩ ⟨p⟩
    refine hnB ((cforce_emb C _ v).mpr ?_)
    refine soundness p C v ?_
    intro χ hχ
    simp only [List.mem_singleton] at hχ
    subst hχ
    exact (cforce_emb C _ v).mp hA

/-- The `⊥`-form, which is what co-residuation actually gives:
`φ ⊢ ψ` iff `emb φ ⤙ emb ψ` is UNSATISFIABLE. -/
theorem laxND_iff_coimp_unsat (φ ψ : PLLFormula) :
    Nonempty (LaxND [φ] ψ) ↔ ¬ CoimpSat (emb φ) (emb ψ) := by
  classical
  constructor
  · intro hp hs
    exact ((not_laxND_iff_coimp_sat φ ψ).mpr hs) hp
  · intro hns
    by_contra hnp
    exact hns ((not_laxND_iff_coimp_sat φ ψ).mp hnp)

/-! ## Pins -/

/--
info: 'BiLax.coimp_sat_iff_not_entail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms coimp_sat_iff_not_entail

/--
info: 'BiLax.not_laxND_iff_coimp_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_laxND_iff_coimp_sat

end BiLax
