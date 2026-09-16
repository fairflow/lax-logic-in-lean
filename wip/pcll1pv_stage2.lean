/-
STAGE 2, part (a): the confluent WITNESS-form m-clauses of the
agreement family — the σ-ping-pong (design pin:
docs/pcll-1pv-ui-plan.md §"Stage 2 design pin").

The general-PLL m-clauses are the standing sorries
(PLLSemUIChar.lean:322/327).  Under BOTH models mutually confluent the
witness form is provable: transfer `◯(charPos κ)` across the
agreement (bare possibility makes both intro and elim local), extract
the other side's witness; if it refutes `charNeg κ` we are matched
(`agree_of_char`); otherwise it forces some disjunct `D₀` that `κ`
does not — transfer `◯D₀` back, extract a K-side witness for it, and
merge with `κ` by directedness (iterated confluence).  `κ`'s forced
set strictly grows inside the finite representative list, so the loop
terminates; fallible escapes bounce `◯⊥`.

crank bookkeeping (`crank (somehow φ) = crank φ + 2`): the budget is
r+2 over the rank-r list; `◯D₀` costs ≤ r+2, `◯⊥` costs 2, and
`◯(charPos)` costs ≤ r+2 exactly when the filter is nonempty
(`bigAnd` is crank-free on cons); the empty-σ case needs no transfer —
the reflexive `Rm` witness serves.
-/
import LaxLogic.PLLSemUIChar
import LaxLogic.PLLFrames

namespace PLLND
namespace SemUI

open Classical

/-- Directedness of `Rₘ`-successors from mutual confluence: two rows
out of `w` have a common refinement that is a row of `w`, above the
first along `Rᵢ` (content persists) and above the second along `Rₘ`. -/
theorem confluent_directed {C : ConstraintModel} (hC : MutuallyConfluent C)
    {w a b : C.W} (ha : C.Rm w a) (hb : C.Rm w b) :
    ∃ c, C.Rm w c ∧ C.Ri a c ∧ C.Rm b c := by
  obtain ⟨c, hac, hbc⟩ := hC ha (C.sub_mi hb)
  exact ⟨c, C.trans_m hb hbc, hac, hbc⟩

/-- Pointwise `length_filter` monotonicity. -/
theorem lengthFilterMono {α : Type} {L : List α}
    {p q : α → Bool} (h : ∀ a ∈ L, q a = true → p a = true) :
    (L.filter q).length ≤ (L.filter p).length := by
  induction L with
  | nil => simp
  | cons x L ih =>
      have h' : ∀ a ∈ L, q a = true → p a = true :=
        fun a ha => h a (List.mem_cons_of_mem _ ha)
      cases hqx : q x with
      | true =>
          have hpx : p x = true := h x (List.mem_cons_self ..) hqx
          simp only [List.filter_cons, hqx, hpx]
          simpa using Nat.succ_le_succ (ih h')
      | false =>
          cases hpx : p x with
          | true =>
              simp only [List.filter_cons, hqx, hpx]
              exact Nat.le_succ_of_le (ih h')
          | false =>
              simp only [List.filter_cons, hqx, hpx]
              exact ih h'

/-- The termination helper: a filter by a pointwise-stronger predicate
that loses a witnessed member is strictly shorter. -/
theorem filter_length_lt {α : Type} (L : List α) (p q : α → Bool)
    (himp : ∀ a ∈ L, q a = true → p a = true)
    {a₀ : α} (ha₀ : a₀ ∈ L) (hp : p a₀ = true) (hq : q a₀ = false) :
    (L.filter q).length < (L.filter p).length := by
  induction L with
  | nil => cases ha₀
  | cons x L ih =>
      by_cases hx : x = a₀
      · subst hx
        simp only [List.filter_cons, hp, hq]
        have hle : (L.filter q).length ≤ (L.filter p).length :=
          lengthFilterMono (fun a ha => himp a (List.mem_cons_of_mem _ ha))
        simpa using Nat.lt_succ_of_le hle
      · have ha₀' : a₀ ∈ L := (List.mem_cons.mp ha₀).resolve_left
          (fun h => hx h.symm)
        have himp' : ∀ a ∈ L, q a = true → p a = true :=
          fun a ha => himp a (List.mem_cons_of_mem _ ha)
        have hlt := ih himp' ha₀'
        cases hqx : q x with
        | true =>
            have hpx : p x = true := himp x (List.mem_cons_self ..) hqx
            simp only [List.filter_cons, hqx, hpx]
            simpa using Nat.succ_lt_succ hlt
        | false =>
            cases hpx : p x with
            | true =>
                simp only [List.filter_cons, hqx, hpx]
                exact Nat.lt_succ_of_lt hlt
            | false =>
                simp only [List.filter_cons, hqx, hpx]
                exact hlt

/-- **The σ-ping-pong**: over mutually confluent models, a K-side row
witness of `ψ` can be grown (keeping `ψ`) until some M-side row
realises its character — or both sides go fallible.  Terminates
because the witness's forced set strictly grows in the finite list. -/
theorem confluent_char_match {M N : ConstraintModel}
    (hM : MutuallyConfluent M) (hN : MutuallyConfluent N)
    {V : Finset String} {r : Nat} {L : List PLLFormula}
    (hL : ∀ D ∈ L, crank D ≤ r ∧ ∀ a ∈ D.atoms, a ∈ V)
    {w : M.W} {w' : N.W}
    (h : ∀ χ : PLLFormula, crank χ ≤ r + 2 →
      (∀ a ∈ χ.atoms, a ∈ V) → (M.force w χ ↔ N.force w' χ))
    {ψ : PLLFormula} (κ : M.W) (hκ : M.Rm w κ) (hψ : M.force κ ψ) :
    ∃ κ' u', M.Rm w κ' ∧ M.Ri κ κ' ∧ M.force κ' ψ ∧ N.Rm w' u' ∧
      ((N.force u' (charPos M κ' L) ∧ ¬ N.force u' (charNeg M κ' L)) ∨
        (κ' ∈ M.F ∧ u' ∈ N.F)) := by
  classical
  -- extract an M-side-character-forcing N-row witness `u'`
  obtain ⟨u', hwu', hu'pos⟩ :
      ∃ u', N.Rm w' u' ∧ N.force u' (charPos M κ L) := by
    cases hfe : L.filter (fun D => decide (M.force κ D)) with
    | nil =>
        refine ⟨w', N.refl_m w', ?_⟩
        rw [charPos, hfe]
        exact (force_bigAnd_iff N w' []).mpr (fun D hD => absurd hD (by simp))
    | cons E l =>
        have hcp : crank (charPos M κ L) ≤ r := by
          rw [charPos]
          exact crank_bigAnd_le (by simp [hfe])
            (fun D hD => (hL D (List.mem_of_mem_filter hD)).1)
        have h1 : M.force w ((charPos M κ L).somehow) :=
          (force_somehow_iff_of_confluent hM).mpr
            ⟨κ, hκ, force_charPos M κ L⟩
        have h2 : N.force w' ((charPos M κ L).somehow) := by
          refine (h _ ?_ ?_).mp h1
          · show crank (charPos M κ L) + 2 ≤ r + 2
            omega
          · intro a ha
            exact atoms_charPos (fun D hD => (hL D hD).2) a ha
        exact (force_somehow_iff_of_confluent hN).mp h2
  by_cases hneg : N.force u' (charNeg M κ L)
  · rcases force_bigOr_cases hneg with ⟨D₀, hD₀mem, hD₀⟩ | hu'F
    · -- growth: κ absorbs D₀ through the back-transfer and directedness
      have hD₀L : D₀ ∈ L := List.mem_of_mem_filter hD₀mem
      have hD₀not : ¬ M.force κ D₀ :=
        of_decide_eq_true (List.mem_filter.mp hD₀mem).2
      have h2 : N.force w' (D₀.somehow) :=
        (force_somehow_iff_of_confluent hN).mpr ⟨u', hwu', hD₀⟩
      have h3 : M.force w (D₀.somehow) := by
        refine (h _ ?_ ?_).mpr h2
        · show crank D₀ + 2 ≤ r + 2
          have := (hL D₀ hD₀L).1
          omega
        · intro a ha
          exact (hL D₀ hD₀L).2 a ha
      obtain ⟨t, hwt, htD₀⟩ := (force_somehow_iff_of_confluent hM).mp h3
      obtain ⟨κ2, hwκ2, hκκ2, htκ2⟩ := confluent_directed hM hκ hwt
      have hψ2 : M.force κ2 ψ := M.force_hered hκκ2 hψ
      obtain ⟨κ', u', h1, h2, h3', h4, h5⟩ :=
        confluent_char_match hM hN hL h κ2 hwκ2 hψ2
      exact ⟨κ', u', h1, M.trans_i hκκ2 h2, h3', h4, h5⟩
    · -- the N-side witness is fallible: bounce ◯⊥ and go fallible too
      have h2 : N.force w' ((PLLFormula.falsePLL).somehow) :=
        (force_somehow_iff_of_confluent hN).mpr ⟨u', hwu', hu'F⟩
      have h3 : M.force w ((PLLFormula.falsePLL).somehow) := by
        refine (h _ ?_ ?_).mpr h2
        · show crank PLLFormula.falsePLL + 2 ≤ r + 2
          simp [crank]
        · intro a ha
          simp [PLLFormula.atoms] at ha
      obtain ⟨t, hwt, htF⟩ := (force_somehow_iff_of_confluent hM).mp h3
      obtain ⟨κ2, hwκ2, hκκ2, htκ2⟩ := confluent_directed hM hκ hwt
      exact ⟨κ2, u', hwκ2, hκκ2, M.force_hered hκκ2 hψ, hwu',
        .inr ⟨M.hered_F (M.sub_mi htκ2) htF, hu'F⟩⟩
  · exact ⟨κ, u', hκ, M.refl_i κ, hψ, hwu', .inl ⟨hu'pos, hneg⟩⟩
termination_by (L.filter (fun D => decide (¬ M.force κ D))).length
decreasing_by
  refine filter_length_lt L _ _ ?_ hD₀L (by simpa using hD₀not) ?_
  · intro D hD hq
    by_contra hp
    have hforce : M.force κ D := by
      by_contra hnf
      exact absurd (decide_eq_true hnf) (by simpa using hp)
    have : M.force κ2 D := M.force_hered hκκ2 hforce
    exact absurd (of_decide_eq_true hq) (fun hn => hn this)
  · have : M.force κ2 D₀ := M.force_hered (M.sub_mi htκ2) htD₀
    simpa using this

/-! ## Part (d): the witness m-clauses of the agreement family -/

/-- **The confluent K-side witness m-clause** (`mwit`-shaped): the
ping-pong's match, closed to full rank-2α agreement through the
representative list. -/
theorem agree_mwit {V : Finset String} {α : Nat}
    {M N : ConstraintModel} (hM : MutuallyConfluent M)
    (hN : MutuallyConfluent N) {w : M.W} {w' : N.W}
    (h : ∀ χ : PLLFormula, crank χ ≤ 2 * α + 2 →
      (∀ a ∈ χ.atoms, a ∈ V) → (M.force w χ ↔ N.force w' χ))
    {ψ : PLLFormula} (hex : ∃ κ, M.Rm w κ ∧ M.force κ ψ) :
    ∃ κ u', M.Rm w κ ∧ M.force κ ψ ∧ N.Rm w' u' ∧
      ((∀ χ : PLLFormula, crank χ ≤ 2 * α →
        (∀ a ∈ χ.atoms, a ∈ V) → (M.force κ χ ↔ N.force u' χ)) ∨
       (κ ∈ M.F ∧ u' ∈ N.F)) := by
  classical
  obtain ⟨L, hL, hrep⟩ := frag_reps_exist' V (2 * α)
  obtain ⟨κ₀, hκ₀, hψ₀⟩ := hex
  obtain ⟨κ, u', hκ, _hRi, hψκ, hu', hres⟩ :=
    confluent_char_match hM hN hL h κ₀ hκ₀ hψ₀
  rcases hres with ⟨hpos, hneg⟩ | hfal
  · refine ⟨κ, u', hκ, hψκ, hu', .inl ?_⟩
    intro χ hχc hχa
    obtain ⟨D, hD, h1, h2⟩ := hrep χ hχc hχa
    have hagree := agree_of_char hpos hneg D hD
    constructor
    · intro hf
      exact force_of_deriv h2 (hagree.mp (force_of_deriv h1 hf))
    · intro hf
      exact force_of_deriv h2 (hagree.mpr (force_of_deriv h1 hf))
  · exact ⟨κ, u', hκ, hψκ, hu', .inr hfal⟩

/-- **The confluent M-side witness m-clause** (`MWitM`-shaped), by
symmetry of the agreement. -/
theorem agree_mwitN {V : Finset String} {α : Nat}
    {M N : ConstraintModel} (hM : MutuallyConfluent M)
    (hN : MutuallyConfluent N) {w : M.W} {w' : N.W}
    (h : ∀ χ : PLLFormula, crank χ ≤ 2 * α + 2 →
      (∀ a ∈ χ.atoms, a ∈ V) → (M.force w χ ↔ N.force w' χ))
    {ψ : PLLFormula} (hex : ∃ u', N.Rm w' u' ∧ N.force u' ψ) :
    ∃ u' u, N.Rm w' u' ∧ N.force u' ψ ∧ M.Rm w u ∧
      ((∀ χ : PLLFormula, crank χ ≤ 2 * α →
        (∀ a ∈ χ.atoms, a ∈ V) → (M.force u χ ↔ N.force u' χ)) ∨
       (u ∈ M.F ∧ u' ∈ N.F)) := by
  obtain ⟨κ, u, hκ, hψκ, hu, hres⟩ :=
    agree_mwit hN hM (fun χ hc ha => (h χ hc ha).symm) hex
  rcases hres with hagree | ⟨hκF, huF⟩
  · exact ⟨κ, u, hκ, hψκ, hu, .inl (fun χ hc ha => (hagree χ hc ha).symm)⟩
  · exact ⟨κ, u, hκ, hψκ, hu, .inr ⟨huF, hκF⟩⟩

/-- **The ANCHORED M-side witness clause**: the output witness GROWS
from the given seed along `Rᵢ` (the ping-pong's directedness joins),
keeping the base `Rₘ`-anchor.  The corner recursion consumes exactly
this: `Rᵢ`-anchoring at the corner witness survives to the `Rᵢ b₂`
corner constraint while the `Rₘ` base-anchor serves `Rₘ c₂`. -/
theorem agree_mwitN_anchored {V : Finset String} {α : Nat}
    {M N : ConstraintModel} (hM : MutuallyConfluent M)
    (hN : MutuallyConfluent N) {w : M.W} {w' : N.W}
    (h : ∀ χ : PLLFormula, crank χ ≤ 2 * α + 2 →
      (∀ a ∈ χ.atoms, a ∈ V) → (M.force w χ ↔ N.force w' χ))
    {ψ : PLLFormula} (u'₀ : N.W) (hu'₀ : N.Rm w' u'₀)
    (hψ₀ : N.force u'₀ ψ) :
    ∃ u' u, N.Rm w' u' ∧ N.Ri u'₀ u' ∧ N.force u' ψ ∧ M.Rm w u ∧
      ((∀ χ : PLLFormula, crank χ ≤ 2 * α →
        (∀ a ∈ χ.atoms, a ∈ V) → (M.force u χ ↔ N.force u' χ)) ∨
       (u ∈ M.F ∧ u' ∈ N.F)) := by
  classical
  obtain ⟨L, hL, hrep⟩ := frag_reps_exist' V (2 * α)
  obtain ⟨u', u, hu', hRi, hψ', hu, hres⟩ :=
    confluent_char_match hN hM hL (fun χ hc ha => (h χ hc ha).symm)
      u'₀ hu'₀ hψ₀
  rcases hres with ⟨hpos, hneg⟩ | hfal
  · refine ⟨u', u, hu', hRi, hψ', hu, .inl ?_⟩
    intro χ hχc hχa
    obtain ⟨D, hD, h1, h2⟩ := hrep χ hχc hχa
    have hagree := agree_of_char hpos hneg D hD
    constructor
    · intro hf
      exact force_of_deriv h2 (hagree.mpr (force_of_deriv h1 hf))
    · intro hf
      exact force_of_deriv h2 (hagree.mp (force_of_deriv h1 hf))
  · exact ⟨u', u, hu', hRi, hψ', hu, .inr ⟨hfal.2, hfal.1⟩⟩

/-! ## Pins -/

/--
info: 'PLLND.SemUI.confluent_char_match' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms confluent_char_match

/--
info: 'PLLND.SemUI.agree_mwit' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms agree_mwit

/--
info: 'PLLND.SemUI.agree_mwitN' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms agree_mwitN

end SemUI
end PLLND
