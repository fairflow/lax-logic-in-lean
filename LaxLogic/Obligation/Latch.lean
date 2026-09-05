/-
# The RS latch: §3 of Fairtlough–Mendler–Cheng, reproduced

The paper's case study, and the real test of whether the shallow embedding
carries the method. A functional property of an RS latch is proved with no
reference to time, and the timing constraint under which it holds is
*synthesised* from the derivation rather than assumed.

The target is the paper's final result (its equation (9), refined back into the
base logic):

    (t_a + D₁ ≥ s_a + 2d₁ + d₂  ∧  D₂ + D₁ > 0)
      ⊃  ∀t ≥ s_a + d₁. ⦇⌐q_out⦈ (s_a + d₁, t)

with the two conjuncts having the meanings the paper gives them: the first is
the **external hold constraint** — `r_in` must stay high long enough for the
latch to reset — and the second is the **internal memory constraint**, that at
least one gate has non-zero inertia. Neither is put in by hand; both fall out of
the two side conditions of the induction step.

## What this file exercises

* `Interval`, and `During` as a `Refined Interval`. The refinement type here is
  `ℕ × ℕ`, so a constraint is a predicate on intervals.
* The paper's **interval induction**, whose abstract form is
  `P ⊃ (P ⊃ ◯∀P) ⊃ ◯∀P` — stated with the Fig. 4 combinators of
  `Connectives.lean` and proved. That statement is the coherence test for the
  whole library: if the combinators are right, unfolding it must give the
  concrete induction principle, and it does.
* The latch theory of Fig. 8, and the derivation.

## The one thing worth noticing about the timing algebra

Fig. 8's `θ₂` combines two intervals as
`((max s₁ s₂) + d₂, (min t₁ t₂) + D₂)`: **max on starts, min on ends**. That is
intersection of intervals, not the single lower bound of `Timing.lean`. The lax
`meet` is doing the same job in both — conjoin the demands — but what
conjunction *computes* depends on the constraint domain, which is exactly why
the modality is worth having separately from any one of its readings.
-/

import LaxLogic.Obligation.Connectives

namespace LaxLogic.Obligation.Latch

open LaxLogic.Obligation Refined

/-- Intervals, identified with pairs of endpoints as the paper does. -/
abbrev Interval := Nat × Nat

/-- `During r (s,t)` — the signal `r` holds throughout `[s,t]`. The paper
abbreviates this `⦇r⦈`. As a `Refined Interval` it is an abstract formula whose
refinement type is `ℕ × ℕ`. -/
def During (r : Nat → Prop) : Refined Interval :=
  fun st => ∀ u, st.1 ≤ u → u ≤ st.2 → r u

/-! ### The two closure properties interval induction needs -/

/-- `During` restricts to sub-intervals. -/
theorem During.restrict {r : Nat → Prop} {a b c : Nat}
    (h : During r (a, c)) (hb : b ≤ c) : During r (a, b) :=
  fun u hu hu' => h u hu (Nat.le_trans hu' hb)

/-- `During` is closed under union of overlapping intervals — the side condition
the paper states for the induction principle, `P(I) ∧ P(J) ⊃ P(I ∪ J)`. -/
theorem During.union {r : Nat → Prop} {a b c d : Nat}
    (h₁ : During r (a, b)) (h₂ : During r (c, d)) (hac : c ≤ b) :
    During r (a, d) := by
  intro u hu hu'
  by_cases h : u ≤ b
  · exact h₁ u hu h
  · exact h₂ u (Nat.le_trans hac (Nat.le_of_lt (Nat.lt_of_not_le h))) hu'

/-! ## Interval induction, in the paper's abstract form

`Prog R (b₁,b₂)` says `R` is *progressive*: every interval `(b₁,t₁)` extending
`(b₁,b₂)` is related by `R` to one strictly overlapping it on the right. -/

/-- Progressiveness, exactly as the paper defines it. -/
def Prog (R : Interval → Constraint Interval) (b : Interval) : Prop :=
  ∀ t₁, b.2 ≤ t₁ → ∃ s₂ t₂, b.1 ≤ s₂ ∧ s₂ ≤ t₁ ∧ t₁ < t₂ ∧ R (b.1, t₁) (s₂, t₂)

/-- The constraint term of the induction axiom, the paper's `Ind_P♯₁`:

    λ(b₁,b₂). λR. λ(s,t). s = b₁ ∧ b₁ ≤ t ∧ Prog R (b₁,b₂)

Its type is dictated by Fig. 3 and is checked by Lean here rather than
maintained by hand. -/
def indTerm (b : Interval) (R : Interval → Constraint Interval) :
    Constraint Interval :=
  fun st => st.1 = b.1 ∧ b.1 ≤ st.2 ∧ Prog R b

/-- The abstract formula of the induction axiom, the paper's `Ind_P♯₂`:

    P ⊃ (P ⊃ ◯∀P) ⊃ ◯∀P

built from the Fig. 4 combinators. Note that its refinement type,
`Interval → (Interval → Constraint Interval) → Constraint Interval`, is computed
by Lean from Fig. 3 and is exactly the type of `indTerm`. -/
def indForm (P : Refined Interval) :
    Refined (Interval → (Interval → Constraint Interval) → Constraint Interval) :=
  Refined.imp P (Refined.imp (Refined.imp P (boxAll P)) (boxAll P))

/-- What `indForm P indTerm` unfolds to. Stated separately because it is the
coherence check: the Fig. 4 combinators, applied to the paper's proof term, must
give back the paper's concrete induction principle, and this `rfl` says they
do. -/
theorem indForm_unfold (P : Refined Interval) :
    indForm P indTerm =
      ∀ b : Interval, P b →
        ∀ R : Interval → Constraint Interval,
          (∀ x, P x → ∀ y, R x y → P y) →
            ∀ st : Interval, (st.1 = b.1 ∧ b.1 ≤ st.2 ∧ Prog R b) → P st :=
  rfl

/-- **Interval induction is sound**, for any property closed under restriction
and under union of overlapping intervals.

This is the paper's `Ind_P♯`, and it is proved rather than assumed. -/
theorem ind_aux (P : Refined Interval)
    (restrict : ∀ {a b c}, P (a, c) → b ≤ c → P (a, b))
    (union : ∀ {a b c d}, P (a, b) → P (c, d) → c ≤ b → P (a, d))
    {b₁ b₂ : Nat} (hP0 : P (b₁, b₂))
    {R : Interval → Constraint Interval}
    (hR : ∀ x, P x → ∀ y, R x y → P y) (hprog : Prog R (b₁, b₂)) :
    ∀ t, b₁ ≤ t → P (b₁, t) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro hbt
    by_cases hle : t ≤ b₂
    · exact restrict hP0 hle
    · -- `t > b₂`, so the predecessor is still past the base interval
      have hgt : b₂ < t := Nat.lt_of_not_le hle
      have hpred : b₂ ≤ t - 1 := by omega
      have hlt : t - 1 < t := by omega
      obtain ⟨s₂, t₂, hs₂, hs₂t, ht₂, hRel⟩ := hprog (t - 1) hpred
      -- `b₁ ≤ t - 1` is not available from `b₁ ≤ t`; it comes from the
      -- progressiveness witness, which starts at or after `b₁`.
      have hb1 : b₁ ≤ t - 1 := Nat.le_trans hs₂ hs₂t
      have hIH : P (b₁, t - 1) := ih (t - 1) hlt hb1
      have hP2 : P (s₂, t₂) := hR (b₁, t - 1) hIH (s₂, t₂) hRel
      have hUnion : P (b₁, t₂) := union hIH hP2 hs₂t
      exact restrict hUnion (by omega)

theorem ind_sound (P : Refined Interval)
    (restrict : ∀ {a b c}, P (a, c) → b ≤ c → P (a, b))
    (union : ∀ {a b c d}, P (a, b) → P (c, d) → c ≤ b → P (a, d)) :
    indForm P indTerm := by
  rintro ⟨b₁, b₂⟩ hP0 R hR ⟨s, t⟩ ⟨hs, hbt, hprog⟩
  cases hs
  exact ind_aux P restrict union hP0 hR hprog t hbt

/-- `During` satisfies both closure conditions, so interval induction applies to
it. This is the paper's remark that `Ind_P♯` is sound for any `P` of the form
`⦇Q⦈`. -/
theorem ind_sound_During (r : Nat → Prop) : indForm (During r) indTerm :=
  ind_sound _ (fun h hb => During.restrict h hb) (fun h₁ h₂ hc => During.union h₁ h₂ hc)

/-! ## The latch

Fig. 7's RS latch, as Fig. 8's theory. Signals are predicates on time; `⦇⌐r⦈` is
`During` of the negation. The parameters are the two gates' delays `d₁, d₂` and
inertialities `D₁, D₂`, and the input window `[s_a, t_a]`. -/

/-- `Low r` is the paper's `⌐r`: the signal read as low. Signals here are
`Nat → Prop`, so this is Lean's intuitionistic `Not`; the development needs no
classical reasoning, and the axiom pins below show none is used. The paper's HOL
signals are `𝔹`-valued, where "low" is `r u = false`. -/
def Low (r : Nat → Prop) : Nat → Prop := fun u => ¬ r u

section Latch

variable (rin sin qout qbar : Nat → Prop)
variable (d₁ d₂ D₁ D₂ sa ta : Nat)

/-- `θ₁`: `r_in` high on `[s,t]` drives `q_out` low on `[s+d₁, t+D₁]`. -/
def Θ₁ : Prop :=
  ∀ s t, During rin (s, t) → During (Low qout) (s + d₁, t + D₁)

/-- `θ₂`: `s_in` low and `q_out` low, on overlapping windows, drive `q̄_out` high
on the **intersection** shifted by the second gate — `max` on starts, `min` on
ends. -/
def Θ₂ : Prop :=
  ∀ s₁ t₁ s₂ t₂, During (Low sin) (s₁, t₁) →
    During (Low qout) (s₂, t₂) →
      During qbar (max s₁ s₂ + d₂, min t₁ t₂ + D₂)

/-- `θ₃`: `q̄_out` high drives `q_out` low, through the first gate. -/
def Θ₃ : Prop :=
  ∀ s t, During qbar (s, t) → During (Low qout) (s + d₁, t + D₁)

/-- `θ_p1`: the input `r_in` is high on `[s_a, t_a]`. -/
def Θₚ₁ : Prop := During rin (sa, ta)

/-- `θ_p2`: the input `s_in` is low on `[s_a, ∞)`. -/
def Θₚ₂ : Prop := ∀ t, sa ≤ t → During (Low sin) (sa, t)

/-- **The step of the derivation.** From `q_out` low on `[x₁,x₂]` — with `x₁`
after the input arrives — `q_out` is low again on
`[x₁ + d₁ + d₂, x₂ + D₁ + D₂]`: round the feedback loop, through the second gate
and back through the first.

This is where `θ₂`'s `max`/`min` is discharged: `max s_a x₁ = x₁` because the
window starts after the input, and `min (max s_a x₂) x₂ = x₂` by construction. -/
theorem loop (h2 : Θ₂ sin qout qbar d₂ D₂) (h3 : Θ₃ qout qbar d₁ D₁)
    (hp2 : Θₚ₂ sin sa) {x₁ x₂ : Nat} (hx : sa ≤ x₁)
    (hq : During (Low qout) (x₁, x₂)) :
    During (Low qout) (x₁ + d₂ + d₁, x₂ + D₂ + D₁) := by
  have hs : During (Low sin) (sa, max sa x₂) := hp2 _ (Nat.le_max_left _ _)
  have hbar := h2 sa (max sa x₂) x₁ x₂ hs hq
  rw [Nat.max_eq_right hx, Nat.min_eq_right (Nat.le_max_right _ _)] at hbar
  exact h3 _ _ hbar

/-- **The paper's result.**

    (t_a + D₁ ≥ s_a + 2d₁ + d₂ ∧ D₂ + D₁ > 0)
      ⊃ ∀t ≥ s_a + d₁. ⦇⌐q_out⦈ (s_a + d₁, t)

The two hypotheses are the paper's two constraints, and they enter in exactly
the two places the paper says: `hold` is what makes the induction's step reach
far enough (`b₁ + d₁ + d₂ ≤ t₁` for every `t₁` past the base interval), and
`inertia` is what makes it a *strict* advance (`t₁ < t₂`). Neither is assumed
for its own sake; each is the side condition of one clause of `Prog`. -/
theorem latch_resets
    (h1 : Θ₁ rin qout d₁ D₁) (h2 : Θ₂ sin qout qbar d₂ D₂)
    (h3 : Θ₃ qout qbar d₁ D₁)
    (hp1 : Θₚ₁ rin sa ta) (hp2 : Θₚ₂ sin sa)
    (hold : sa + 2 * d₁ + d₂ ≤ ta + D₁) (inertia : 0 < D₂ + D₁) :
    ∀ t, sa + d₁ ≤ t → During (Low qout) (sa + d₁, t) := by
  -- the base interval: q_out is low on [s_a + d₁, t_a + D₁]
  have base : During (Low qout) (sa + d₁, ta + D₁) := h1 sa ta hp1
  -- the step relation: advance by (d₁ + d₂) on the left, (D₁ + D₂) on the right
  have hR : ∀ x : Interval, During (Low qout) x → ∀ y : Interval,
      (sa ≤ x.1 ∧ y.1 = x.1 + d₂ + d₁ ∧ y.2 = x.2 + D₂ + D₁) →
      During (Low qout) y := by
    rintro ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ ⟨hsa, rfl, rfl⟩
    exact loop sin qout qbar d₁ d₂ D₁ D₂ sa h2 h3 hp2 hsa hx
  -- progressiveness, and the two constraints that make it hold
  have hprog : Prog
      (fun x y => sa ≤ x.1 ∧ y.1 = x.1 + d₂ + d₁ ∧ y.2 = x.2 + D₂ + D₁)
      (sa + d₁, ta + D₁) := by
    intro t₁ ht₁
    exact ⟨sa + d₁ + d₂ + d₁, t₁ + D₂ + D₁,
      by omega, by omega, by omega, by omega, rfl, rfl⟩
  intro t ht
  exact ind_aux (During (Low qout))
    (fun h hb => During.restrict h hb) (fun h₁ h₂ hc => During.union h₁ h₂ hc)
    base hR hprog t ht

end Latch

end LaxLogic.Obligation.Latch
