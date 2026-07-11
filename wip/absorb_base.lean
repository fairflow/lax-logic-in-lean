import LaxLogic.PLLG4UITrunc

/-!
# WIP: the absorption base, ambient-relative form

Hand-executing the pure `gamma_box_map` obligations showed every
boxed γ-position demanding an E-glue one budget below the band — an
infinite regress.  The resolution: the pure statement was stronger
than anything the adequacy landing needs.  The landing always holds
the ambient `E(Γ)`, and with ambient E:

* budget-mono (`E@b ⊢ E@(b-1)`, the easy direction) matches any
  lower guard;
* `box_guard_collapse` opens a guarded box against a ◯-goal;
* `laxL` re-imports ambient at every box crossing, so the inner value
  lands IN CONTEXT — exactly what the pigeonhole/splice shortcut
  consumes (`itp_budget_mono_le` from the repeated state's low value
  into the spliced target slot).

Crux statement (mutual, fuel-inducted; the E-half needs no extra
ambient because E is its own):

    STAB(b):  [E@(b-1)] ⊢ E@b   ∧   E@b, A@b(Γ,C) ⊢ A@(b-1)(Γ,C)

for `b` past the jump-state count.  The cascade lives in the A-half's
jump/γ disjuncts; everything else is the fuel induction.
-/

open PLLFormula

namespace PLLND

/-- Jump-state threshold (overcount). -/
def kcap (S : Finset PLLFormula) : Nat := 2 * S.card + 4

/-!
Case analysis, hand-executed 2026-07-11 (all against the actual
clause tables; the compiler adjudicates next):

E-half `[E@(b-1)] ⊢ E@b` — closes at the fuel level, every case:
* atoms/⊥: project.
* growth conjuncts: E-half fuel-IH at the grown context, composed
  through `andAll_elim`.
* jump conjuncts `(A@(b-1)(A_F) ⇢ E@b(B::Γ))`: impR, fire the
  source's jump conjunct after converting its antecedent by the
  A-half at the (b-1)-pair (IN CONTEXT: the impR antecedent plus the
  source E-value as ambient), then lift the consequent by the E-half
  fuel-IH at the grown context.
* γ conjuncts (the former barrier): impR introduces the target's box
  `◯(E@(b-1) ⇢ A@(b-1)(◯A_F))`; its guard EXACTLY matches the
  in-context source value `E@(b-1)`, so `box_guard_collapse` opens
  it; `laxL` on the result puts `A@(b-1)(◯A_F)` in context; `laxR` +
  impR rebuild the source's γ-antecedent, closing with the A-half at
  the (b-1)-pair.  No regress: ambient is re-imported at the
  crossing.

A-half `[E@b, A@b(Γ,C)] ⊢ A@(b-1)(Γ,C)` — orAll-elim on the source
value with E-ambient:
* goal decomposition: A-half fuel-IH (ambient stepped down by
  `itp_fuel_mono` + `itp_budget_mono`).
* growth disjuncts: impR-texture — introduce the target's guard,
  derive the source's by the E-half at the grown context, fire, then
  A-half at the grown context with the just-derived grown-E as
  ambient.
* SECOND components of jump/γ disjuncts (`A@b(B::Γ, C)`): unlock the
  grown ambient by firing the ambient E-value's own jump conjunct
  with the in-context first component (the adequacy case-map's
  `hfire` pattern), then A-half at the grown context.
* FIRST components of jump/γ disjuncts: the b-descent — THE CASCADE.
  Each jump/γ-first-component map is an A-half instance at the
  (b-1)-pair, whose own jump cases descend again: the descent chain
  carries jump goals (≤ kcap distinct) WITH their values in context
  (andL keeps them).  At a goal repeat: `itp_budget_mono_le` lifts
  the deep in-context value into the spliced (higher-budget) target
  slot.  Pigeonhole bounds the descent by kcap+1, which is what the
  threshold pays for; below it, jump-free target values make the map
  genuinely false.
* trunc: collapse via guard-match, laxL, orAll-elim, reuse the
  per-disjunct bundle (as in itp_sound's trunc case).

Lean plan: outer fuel induction (mutual halves as the ∧); the A-half
jump-first-components via an inner descent lemma carrying
`seen : List (PLLFormula × Nat)` (goal, budget-at-first-visit) with
their values as explicit context hypotheses; repeats close by
mono-splice, fresh states recurse with the budget slack decreasing;
`kcap S < b` supplies the room.
-/

/-- Ambient-relative budget stabilization, the crux of uniformity.
`b` ranges one past the threshold so that both `b` and `b-1` carry
every jump clause. -/
theorem itp_stab (p : String) (S : Finset PLLFormula) : ∀ (fuel : Nat)
    (b : Nat), kcap S < b →
    (∀ Γ, G4c [itpE p S fuel (b - 1) Γ] (itpE p S fuel b Γ)) ∧
    (∀ Γ C, G4c [itpE p S fuel b Γ, itpA p S fuel b Γ C]
      (itpA p S fuel (b - 1) Γ C)) := by
  sorry

/-- Consumption form for the adequacy landing: under the theorem's own
ambient `E`, the packaged-budget value feeds any lower slot above the
threshold. -/
theorem itp_stab_le (p : String) (S : Finset PLLFormula)
    {fuel b b' : Nat} (hk : kcap S < b') (hle : b' ≤ b) :
    (∀ Γ, G4c [itpE p S fuel b' Γ] (itpE p S fuel b Γ)) ∧
    (∀ Γ C, G4c [itpE p S fuel b Γ, itpA p S fuel b Γ C]
      (itpA p S fuel b' Γ C)) := by
  sorry

end PLLND
