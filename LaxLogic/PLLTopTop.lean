import LaxLogic.PLLReducibility
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Strong normalisation of the full reduction (Lindley–Stark ⊤⊤-lifting)

This file proves **strong normalisation of the full one-step reduction
`Step`** — β for every connective *and* `let`-assoc, interleaved freely —
for the PLL proof-term calculus: `SNt t` for every `t : Tm Γ φ`.

`PLLReducibility.lean` ends with machine-checked counterexamples showing
that `beta_sn` and `assoc_sn` do not compose: each fragment creates redexes
of the other (both orientations of Bachmair–Dershowitz quasi-commutation
fail), so a semantic method over the *full* relation is forced.  The method
is Lindley–Stark ⊤⊤-lifting (TLCA 2005), the biorthogonal upgrade of the
value-style `◯`-clause used for the β-fragment:

* a **continuation stack** `K : Kont Γ A B` is a list of `bind`-bodies;
  `K.plug t` wraps `t` in scrutinee position, innermost frame first;
* `K` is **reducible** (`KRed A K`, membership in `SRed A ⊤`) when
  `K[val s]` is SN for every reducible `s` — in any renaming extension;
* `SRed (◯A) t` holds when `K[t ρ]` is SN for every reducible stack `K`
  (membership in `SRed A ⊤⊤`).  The β-fragment's value clause is exactly
  the `K = []` shadow of this definition.

The mathematical heart is the **principal lemma**
`SN s → SN (K[u[s]]) → SN (K[bind (val s) u])`, whose assoc-interface case
produces a reduct with the *same* underlying SN witness but a *shorter*
stack; bare `Acc`-induction cannot recurse on an equal argument, so the
induction is over the lexicographic measure
`(Acc.rank of K[u[s]], |K|, Acc.rank of s)` using mathlib's ordinal rank
of accessibility (`Mathlib.SetTheory.Ordinal.Rank`).

Everything else is the Kripke–Tait skeleton of `PLLReducibility.lean`
re-run over `Step`: the reducibility candidates change only at `◯`, and
`bind` is no longer neutral (its scrutinee position participates in assoc),
matching the normal-form grammar of `PLLNormal.lean`.

The only prior mechanisation of ⊤⊤-lifting we know of is
Doczkal–Schwinghammer (Isabelle/HOL-Nominal, LFMTP 2009), for the calculus
without sums; this appears to be the first in Lean, and the first with
sums and an intrinsically-typed syntax.
-/

open PLLFormula

namespace PLLND

/-! ### SN for the full relation: basic kit

`SNt` is defined in `PLLTerms.lean`.  The congruence lemmas are
`Acc.of_inversion` at the evident step inversions, as in the β-fragment.
-/

theorem SNt.step {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ φ}
    (h : SNt t) (hs : Step t t') : SNt t' :=
  h.inv hs

theorem SNt.steps {Γ : List PLLFormula} {φ : PLLFormula} {t t' : Tm Γ φ}
    (hs : Steps t t') : SNt t → SNt t' := by
  induction hs with
  | refl _ => exact id
  | head h1 _ ih => exact fun h => ih (h.inv h1)

theorem SNt.abort {Γ : List PLLFormula} (φ : PLLFormula) {t : Tm Γ .falsePLL}
    (h : SNt t) : SNt (Tm.abort φ t) :=
  Acc.of_inversion (f := Tm.abort φ)
    (fun hy => by cases hy with | abortCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.lam {Γ : List PLLFormula} {φ ψ : PLLFormula} {b : Tm (φ :: Γ) ψ}
    (h : SNt b) : SNt (Tm.lam b) :=
  Acc.of_inversion (f := Tm.lam)
    (fun hy => by cases hy with | lamCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.inl {Γ : List PLLFormula} {φ ψ : PLLFormula} {a : Tm Γ φ}
    (h : SNt a) : SNt (Tm.inl (ψ := ψ) a) :=
  Acc.of_inversion (f := Tm.inl (ψ := ψ))
    (fun hy => by cases hy with | inlCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.inr {Γ : List PLLFormula} {φ ψ : PLLFormula} {a : Tm Γ ψ}
    (h : SNt a) : SNt (Tm.inr (φ := φ) a) :=
  Acc.of_inversion (f := Tm.inr (φ := φ))
    (fun hy => by cases hy with | inrCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.val {Γ : List PLLFormula} {φ : PLLFormula} {a : Tm Γ φ}
    (h : SNt a) : SNt (Tm.val a) :=
  Acc.of_inversion (f := Tm.val)
    (fun hy => by cases hy with | valCong h' => exact ⟨_, rfl, h'⟩) h

theorem SNt.pair {Γ : List PLLFormula} {φ ψ : PLLFormula}
    {a : Tm Γ φ} {b : Tm Γ ψ} (ha : SNt a) (hb : SNt b) :
    SNt (Tm.pair a b) :=
  Acc.of_inversion₂ (f := Tm.pair)
    (fun hy => by
      cases hy with
      | pairCong₁ h' => exact .inl ⟨_, rfl, h'⟩
      | pairCong₂ h' => exact .inr ⟨_, rfl, h'⟩) ha hb

/-! ### Multi-step utilities -/

theorem Steps.trans {Γ : List PLLFormula} {φ : PLLFormula}
    {a b c : Tm Γ φ} (h₁ : Steps a b) (h₂ : Steps b c) : Steps a c := by
  induction h₁ with
  | refl _ => exact h₂
  | head h _ ih => exact .head h (ih h₂)

/-- Congruence closure of `Steps` under any step-preserving map. -/
theorem Steps.cong {Γ Δ : List PLLFormula} {φ ψ : PLLFormula}
    {f : Tm Γ φ → Tm Δ ψ}
    (hf : ∀ {x y : Tm Γ φ}, Step x y → Step (f x) (f y))
    {a b : Tm Γ φ} (h : Steps a b) : Steps (f a) (f b) := by
  induction h with
  | refl _ => exact .refl _
  | head h1 _ ih => exact .head (hf h1) ih

/-! ### Full steps versus renaming and substitution

The β-cases are as in the β-fragment; the new assoc case needs the two
σ-algebra facts below (how `skip1` commutes with a lifted renaming or
substitution).
-/

theorem Tm.rename_lift_skip1 {Γ Δ : List PLLFormula} {A ψ χ : PLLFormula}
    (u : Tm (ψ :: Γ) χ) (ρ : Ren Γ Δ) :
    (u.rename (Ren.lift ρ)).rename (Ren.skip1 (φ := A))
      = (u.rename Ren.skip1).rename (Ren.lift (Ren.lift ρ)) := by
  rw [Tm.rename_rename, Tm.rename_rename]
  exact u.rename_congr (by lift_cases)

theorem Tm.subst_lift_skip1 {Γ Δ : List PLLFormula} {A ψ χ : PLLFormula}
    (u : Tm (ψ :: Γ) χ) (σ : Sub Γ Δ) :
    (u.rename (Ren.skip1 (φ := A))).subst (Sub.lift (Sub.lift σ))
      = (u.subst (Sub.lift σ)).rename Ren.skip1 := by
  rw [Tm.subst_rename, Tm.rename_subst]
  refine u.subst_congr ?_
  intro χ v
  cases v with
  | here => rfl
  | there w =>
      show ((σ w).weaken).weaken = ((σ w).weaken).rename Ren.skip1
      simp only [Tm.weaken]
      rw [Tm.rename_rename, Tm.rename_rename]
      exact (σ w).rename_congr (fun v => rfl)

/-- Full steps are preserved by renaming. -/
theorem Step.rename : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (ρ : Ren Γ Δ),
    Step t t' → Step (t.rename ρ) (t'.rename ρ) := by
  intro Γ Δ φ t t' ρ h
  induction h generalizing Δ <;>
    (try rw [Tm.subst1_rename]) <;>
    (try (simp only [Tm.rename]; rw [← Tm.rename_lift_skip1])) <;>
    mirror

/-- Full steps are preserved by substitution. -/
theorem Step.subst : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (σ : Sub Γ Δ),
    Step t t' → Step (t.subst σ) (t'.subst σ) := by
  intro Γ Δ φ t t' σ h
  induction h generalizing Δ <;>
    (try rw [Tm.subst1_subst]) <;>
    (try (simp only [Tm.subst]; rw [Tm.subst_lift_skip1])) <;>
    mirror

theorem Steps.rename {Γ Δ : List PLLFormula} {φ : PLLFormula}
    (ρ : Ren Γ Δ) {a b : Tm Γ φ} (h : Steps a b) :
    Steps (a.rename ρ) (b.rename ρ) :=
  Steps.cong (fun hs => Step.rename ρ hs) h

/-- **Reflection of full reduction under renaming**: every step of a
renamed term is the renaming of a step.  As for the β-fragment, but the
`bind` case now splits its scrutinee three ways (`val` / `bind` / other)
to expose the `let`-β and `let`-assoc head redexes. -/
theorem Step.rename_reflect : ∀ {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ), ∀ {Δ : List PLLFormula} (ρ : Ren Γ Δ) {y : Tm Δ φ},
    Step (t.rename ρ) y → ∃ t' : Tm Γ φ, Step t t' ∧ y = t'.rename ρ := by
  intro Γ φ t
  induction t with
  | var v =>
      intro Δ ρ y h
      cases h
  | abort φ t iht =>
      intro Δ ρ y h
      cases h with
      | abortCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨.abort φ t', .abortCong hs, rfl⟩
  | lam t iht =>
      intro Δ ρ y h
      cases h with
      | lamCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ.lift h'
          exact ⟨.lam t', .lamCong hs, rfl⟩
  | app t s iht ihs =>
      intro Δ ρ y h
      cases t
      case lam b₀ =>
          cases h with
          | beta _ _ => exact ⟨b₀.subst1 s, .beta b₀ s, (Tm.subst1_rename ..).symm⟩
          | appCong₁ h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .appCong₁ hs, rfl⟩
          | appCong₂ h' =>
              obtain ⟨s', hs, rfl⟩ := ihs ρ h'
              exact ⟨_, .appCong₂ hs, rfl⟩
      all_goals
        cases h with
        | appCong₁ h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .appCong₁ hs, rfl⟩
        | appCong₂ h' =>
            obtain ⟨s', hs, rfl⟩ := ihs ρ h'
            exact ⟨_, .appCong₂ hs, rfl⟩
  | pair t s iht ihs =>
      intro Δ ρ y h
      cases h with
      | pairCong₁ h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨_, .pairCong₁ hs, rfl⟩
      | pairCong₂ h' =>
          obtain ⟨s', hs, rfl⟩ := ihs ρ h'
          exact ⟨_, .pairCong₂ hs, rfl⟩
  | fst t iht =>
      intro Δ ρ y h
      cases t
      case pair a₀ b₀ =>
          cases h with
          | fstPair _ _ => exact ⟨a₀, .fstPair a₀ b₀, rfl⟩
          | fstCong h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .fstCong hs, rfl⟩
      all_goals
        cases h with
        | fstCong h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .fstCong hs, rfl⟩
  | snd t iht =>
      intro Δ ρ y h
      cases t
      case pair a₀ b₀ =>
          cases h with
          | sndPair _ _ => exact ⟨b₀, .sndPair a₀ b₀, rfl⟩
          | sndCong h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .sndCong hs, rfl⟩
      all_goals
        cases h with
        | sndCong h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .sndCong hs, rfl⟩
  | inl t iht =>
      intro Δ ρ y h
      cases h with
      | inlCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨_, .inlCong hs, rfl⟩
  | inr t iht =>
      intro Δ ρ y h
      cases h with
      | inrCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨_, .inrCong hs, rfl⟩
  | case t u₁ u₂ iht ih₁ ih₂ =>
      intro Δ ρ y h
      cases t
      case inl a₀ =>
          cases h with
          | caseInl _ _ _ =>
              exact ⟨u₁.subst1 a₀, .caseInl a₀ u₁ u₂, (Tm.subst1_rename ..).symm⟩
          | caseCong₀ h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .caseCong₀ hs, rfl⟩
          | caseCong₁ h' =>
              obtain ⟨u₁', hs, rfl⟩ := ih₁ ρ.lift h'
              exact ⟨_, .caseCong₁ hs, rfl⟩
          | caseCong₂ h' =>
              obtain ⟨u₂', hs, rfl⟩ := ih₂ ρ.lift h'
              exact ⟨_, .caseCong₂ hs, rfl⟩
      case inr a₀ =>
          cases h with
          | caseInr _ _ _ =>
              exact ⟨u₂.subst1 a₀, .caseInr a₀ u₁ u₂, (Tm.subst1_rename ..).symm⟩
          | caseCong₀ h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .caseCong₀ hs, rfl⟩
          | caseCong₁ h' =>
              obtain ⟨u₁', hs, rfl⟩ := ih₁ ρ.lift h'
              exact ⟨_, .caseCong₁ hs, rfl⟩
          | caseCong₂ h' =>
              obtain ⟨u₂', hs, rfl⟩ := ih₂ ρ.lift h'
              exact ⟨_, .caseCong₂ hs, rfl⟩
      all_goals
        cases h with
        | caseCong₀ h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .caseCong₀ hs, rfl⟩
        | caseCong₁ h' =>
            obtain ⟨u₁', hs, rfl⟩ := ih₁ ρ.lift h'
            exact ⟨_, .caseCong₁ hs, rfl⟩
        | caseCong₂ h' =>
            obtain ⟨u₂', hs, rfl⟩ := ih₂ ρ.lift h'
            exact ⟨_, .caseCong₂ hs, rfl⟩
  | val t iht =>
      intro Δ ρ y h
      cases h with
      | valCong h' =>
          obtain ⟨t', hs, rfl⟩ := iht ρ h'
          exact ⟨_, .valCong hs, rfl⟩
  | bind t u iht ihu =>
      intro Δ ρ y h
      cases t
      case val a₀ =>
          cases h with
          | bindVal _ _ =>
              exact ⟨u.subst1 a₀, .bindVal a₀ u, (Tm.subst1_rename ..).symm⟩
          | bindCong₁ h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .bindCong₁ hs, rfl⟩
          | bindCong₂ h' =>
              obtain ⟨u', hs, rfl⟩ := ihu ρ.lift h'
              exact ⟨_, .bindCong₂ hs, rfl⟩
      case bind s₀ t₀ =>
          cases h with
          | bindAssoc _ _ _ =>
              refine ⟨.bind s₀ (.bind t₀ (u.rename Ren.skip1)),
                .bindAssoc s₀ t₀ u, ?_⟩
              simp only [Tm.rename]
              rw [Tm.rename_lift_skip1]
          | bindCong₁ h' =>
              obtain ⟨t', hs, rfl⟩ := iht ρ h'
              exact ⟨_, .bindCong₁ hs, rfl⟩
          | bindCong₂ h' =>
              obtain ⟨u', hs, rfl⟩ := ihu ρ.lift h'
              exact ⟨_, .bindCong₂ hs, rfl⟩
      all_goals
        cases h with
        | bindCong₁ h' =>
            obtain ⟨t', hs, rfl⟩ := iht ρ h'
            exact ⟨_, .bindCong₁ hs, rfl⟩
        | bindCong₂ h' =>
            obtain ⟨u', hs, rfl⟩ := ihu ρ.lift h'
            exact ⟨_, .bindCong₂ hs, rfl⟩

/-- Multi-step reflection under renaming. -/
theorem Steps.rename_reflect {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ} {ρ : Ren Γ Δ} {z : Tm Δ φ}
    (h : Steps (t.rename ρ) z) :
    ∃ t₀ : Tm Γ φ, Steps t t₀ ∧ z = t₀.rename ρ := by
  generalize hx : t.rename ρ = x at h
  induction h generalizing t with
  | refl _ => exact ⟨t, .refl t, hx.symm⟩
  | head hs _ ih =>
      subst hx
      obtain ⟨t', hst, rfl⟩ := Step.rename_reflect _ ρ hs
      obtain ⟨t₀, hsteps, rfl⟩ := ih rfl
      exact ⟨t₀, .head hst hsteps, rfl⟩

/-- SN transfers forwards along renaming, by reflection. -/
theorem SNt.rename {Γ Δ : List PLLFormula} {φ : PLLFormula}
    {t : Tm Γ φ} (ρ : Ren Γ Δ) (h : SNt t) : SNt (t.rename ρ) :=
  Acc.of_inversion (f := fun t : Tm Γ φ => t.rename ρ)
    (fun hy => by
      obtain ⟨t', hs, heq⟩ := Step.rename_reflect _ ρ hy
      exact ⟨t', heq, hs⟩) h

/-! ### Pointwise multi-step substitution

A step in the substituend becomes finitely many steps (one per occurrence)
in the substituted term.
-/

/-- Pointwise multi-step relation between substitutions. -/
def SubSteps {Γ Δ : List PLLFormula} (σ τ : Sub Γ Δ) : Prop :=
  ∀ {ψ : PLLFormula} (v : Var Γ ψ), Steps (σ v) (τ v)

theorem SubSteps.lift {Γ Δ : List PLLFormula} {A : PLLFormula}
    {σ τ : Sub Γ Δ} (h : SubSteps σ τ) :
    SubSteps (Sub.lift (ψ := A) σ) (Sub.lift τ) := by
  intro ψ v
  cases v with
  | here => exact .refl _
  | there w => exact Steps.rename (fun v => .there v) (h w)

theorem Tm.subst_steps : ∀ {Γ Δ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) {σ τ : Sub Γ Δ}, SubSteps σ τ →
    Steps (t.subst σ) (t.subst τ)
  | _, _, _, .var v, _, _, h => h v
  | _, _, _, .abort φ t, _, _, h =>
      Steps.cong (fun hs => .abortCong hs) (t.subst_steps h)
  | _, _, _, .lam t, _, _, h =>
      Steps.cong (fun hs => .lamCong hs) (t.subst_steps h.lift)
  | _, _, _, .app t s, _, _, h =>
      (Steps.cong (fun hs => .appCong₁ hs) (t.subst_steps h)).trans
        (Steps.cong (fun hs => .appCong₂ hs) (s.subst_steps h))
  | _, _, _, .pair t s, _, _, h =>
      (Steps.cong (fun hs => .pairCong₁ hs) (t.subst_steps h)).trans
        (Steps.cong (fun hs => .pairCong₂ hs) (s.subst_steps h))
  | _, _, _, .fst t, _, _, h =>
      Steps.cong (fun hs => .fstCong hs) (t.subst_steps h)
  | _, _, _, .snd t, _, _, h =>
      Steps.cong (fun hs => .sndCong hs) (t.subst_steps h)
  | _, _, _, .inl t, _, _, h =>
      Steps.cong (fun hs => .inlCong hs) (t.subst_steps h)
  | _, _, _, .inr t, _, _, h =>
      Steps.cong (fun hs => .inrCong hs) (t.subst_steps h)
  | _, _, _, .case t u₁ u₂, _, _, h =>
      ((Steps.cong (fun hs => .caseCong₀ hs) (t.subst_steps h)).trans
        (Steps.cong (fun hs => .caseCong₁ hs) (u₁.subst_steps h.lift))).trans
        (Steps.cong (fun hs => .caseCong₂ hs) (u₂.subst_steps h.lift))
  | _, _, _, .val t, _, _, h =>
      Steps.cong (fun hs => .valCong hs) (t.subst_steps h)
  | _, _, _, .bind t u, _, _, h =>
      (Steps.cong (fun hs => .bindCong₁ hs) (t.subst_steps h)).trans
        (Steps.cong (fun hs => .bindCong₂ hs) (u.subst_steps h.lift))

/-- A step in the substituted value becomes multi-steps of the instance. -/
theorem Tm.subst1_steps_arg {Γ : List PLLFormula} {A φ : PLLFormula}
    (u : Tm (A :: Γ) φ) {s s' : Tm Γ A} (h : Step s s') :
    Steps (u.subst1 s) (u.subst1 s') := by
  refine u.subst_steps ?_
  intro ψ v
  cases v with
  | here => exact .head h (.refl _)
  | there w => exact .refl _

/-! ### Ordinal rank bookkeeping

`Acc.rank` is proof-irrelevant (any two `Acc` proofs of the same element
are equal), so ranks are effectively attached to terms; the two lemmas
below package the strict and non-strict decreases the principal lemma
needs.
-/

theorem rank_lt_of_step {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (h : SNt t) (h' : SNt t') (hs : Step t t') :
    Acc.rank h' < Acc.rank h := by
  rw [Subsingleton.elim h' (h.inv hs)]
  exact Acc.rank_lt_of_rel h hs

theorem rank_le_of_steps {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (hs : Steps t t') :
    ∀ (h : SNt t) (h' : SNt t'), Acc.rank h' ≤ Acc.rank h := by
  induction hs with
  | refl _ =>
      intro h h'
      rw [Subsingleton.elim h' h]
  | head h1 _ ih =>
      intro h h'
      exact (ih (h.inv h1) h').trans (le_of_lt (Acc.rank_lt_of_rel h h1))

/-! ### The lexicographic triple -/

/-- The measure order for the principal lemma:
`(rank of K[u[s]], stack size, rank of s)`, lexicographically. -/
def Lex₃ : Ordinal × ℕ × Ordinal → Ordinal × ℕ × Ordinal → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem lex₃_wf : WellFounded Lex₃ :=
  Ordinal.lt_wf.prod_lex (Nat.lt_wfRel.wf.prod_lex Ordinal.lt_wf)

theorem lex₃_of_lt {o₁ o₁' : Ordinal} {n n' : ℕ} {o₂ o₂' : Ordinal}
    (h : o₁' < o₁) : Lex₃ (o₁', n', o₂') (o₁, n, o₂) :=
  .left _ _ h

theorem lex₃_of_le_lt {o₁ o₁' : Ordinal} {n n' : ℕ} {o₂ o₂' : Ordinal}
    (h1 : o₁' ≤ o₁) (h2 : n' < n) : Lex₃ (o₁', n', o₂') (o₁, n, o₂) := by
  rcases lt_or_eq_of_le h1 with h | rfl
  · exact .left _ _ h
  · exact .right _ (.left _ _ h2)

theorem lex₃_of_le_eq_lt {o₁ o₁' : Ordinal} {n n' : ℕ} {o₂ o₂' : Ordinal}
    (h1 : o₁' ≤ o₁) (h2 : n' = n) (h3 : o₂' < o₂) :
    Lex₃ (o₁', n', o₂') (o₁, n, o₂) := by
  subst h2
  rcases lt_or_eq_of_le h1 with h | rfl
  · exact .left _ _ h
  · exact .right _ (.right _ h3)

theorem rank_eq_of_eq {Γ : List PLLFormula} {φ : PLLFormula}
    {t t' : Tm Γ φ} (heq : t = t') (h : SNt t) (h' : SNt t') :
    Acc.rank h = Acc.rank h' := by
  cases heq
  rw [Subsingleton.elim h h']

/-! ### Continuation stacks

`Kont Γ C A` is a stack of `bind`-bodies awaiting a scrutinee of type
`◯A` and producing a term of type `◯C`.  The *result* type `C` is a
parameter and the *hole* type `A` is the index — `nil`'s index is then a
bare variable (the `Eq.refl` shape), so matches iota-reduce and the
plugging equations below hold definitionally.  (The first draft indexed
both ends and `nil : Kont Γ A A` repeated an index — green slime, in this
project of all places.)
-/

/-- Continuation stacks with result type `◯C` and hole type `◯A`. -/
inductive Kont (Γ : List PLLFormula) (C : PLLFormula) : PLLFormula → Type
  | nil : Kont Γ C C
  | cons {A B : PLLFormula} (u : Tm (A :: Γ) (somehow B)) (K : Kont Γ C B) :
      Kont Γ C A

namespace Kont

/-- Plugging, innermost frame first: `(cons u K).plug t = K.plug (bind t u)`.
The parameters `Γ, C` stay out of the match columns so that the equations
hold by iota-reduction. -/
def plug {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ {A : PLLFormula}, Kont Γ C A → Tm Γ (somehow A) → Tm Γ (somehow C)
  | _, .nil, t => t
  | _, .cons u K, t => plug K (.bind t u)

/-- Number of frames. -/
def size {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ {A : PLLFormula}, Kont Γ C A → ℕ
  | _, .nil => 0
  | _, .cons _ K => size K + 1

/-- Framewise renaming (under the binder). -/
def rename {Γ Δ : List PLLFormula} {C : PLLFormula} (ρ : Ren Γ Δ) :
    ∀ {A : PLLFormula}, Kont Γ C A → Kont Δ C A
  | _, .nil => .nil
  | _, .cons u K => .cons (u.rename ρ.lift) (rename ρ K)

theorem rename_id {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ {A : PLLFormula} (K : Kont Γ C A), K.rename (fun {_} v => v) = K
  | _, .nil => rfl
  | _, .cons u K => by
      show Kont.cons (u.rename (Ren.lift fun {_} v => v))
        (K.rename fun {_} v => v) = _
      rw [show u.rename (Ren.lift fun {_} v => v) = u from
        (u.rename_congr (by lift_cases)).trans u.rename_id, rename_id K]

theorem rename_rename {Γ Δ Θ : List PLLFormula} {C : PLLFormula}
    (ρ : Ren Γ Δ) (ρ' : Ren Δ Θ) :
    ∀ {A : PLLFormula} (K : Kont Γ C A),
    (K.rename ρ).rename ρ' = K.rename (fun v => ρ' (ρ v))
  | _, .nil => rfl
  | _, .cons u K => by
      show Kont.cons ((u.rename ρ.lift).rename ρ'.lift) ((K.rename ρ).rename ρ')
        = Kont.cons (u.rename (Ren.lift fun v => ρ' (ρ v))) (K.rename _)
      rw [Tm.rename_rename, rename_rename ρ ρ' K,
        show u.rename (fun v => Ren.lift ρ' (Ren.lift ρ v))
            = u.rename (Ren.lift fun v => ρ' (ρ v)) from
          u.rename_congr (by lift_cases)]

/-- Scrutinee steps lift through the stack. -/
theorem plug_step {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ {A : PLLFormula} (K : Kont Γ C A) {t t' : Tm Γ (somehow A)},
    Step t t' → Step (K.plug t) (K.plug t')
  | _, .nil, _, _, h => h
  | _, .cons u K, _, _, h => plug_step K (.bindCong₁ h)

theorem plug_steps {Γ : List PLLFormula} {C A : PLLFormula}
    (K : Kont Γ C A) {t t' : Tm Γ (somehow A)}
    (h : Steps t t') : Steps (K.plug t) (K.plug t') :=
  Steps.cong (fun hs => K.plug_step hs) h

end Kont

/-- One-step reduction of a stack: the innermost frame steps, a deeper
part steps, or two adjacent frames merge by `let`-assoc. -/
inductive KStep : ∀ {Γ : List PLLFormula} {C A : PLLFormula},
    Kont Γ C A → Kont Γ C A → Prop
  | frame {Γ : List PLLFormula} {C A B : PLLFormula}
      {u u' : Tm (A :: Γ) (somehow B)} {K : Kont Γ C B} :
      Step u u' → KStep (.cons u K) (.cons u' K)
  | tail {Γ : List PLLFormula} {C A B : PLLFormula}
      {u : Tm (A :: Γ) (somehow B)} {K K' : Kont Γ C B} :
      KStep K K' → KStep (.cons u K) (.cons u K')
  | assocK {Γ : List PLLFormula} {C A B₁ B₂ : PLLFormula}
      (u₁ : Tm (A :: Γ) (somehow B₁)) (u₂ : Tm (B₁ :: Γ) (somehow B₂))
      (K : Kont Γ C B₂) :
      KStep (.cons u₁ (.cons u₂ K)) (.cons (.bind u₁ (u₂.rename Ren.skip1)) K)

/-- Stack steps are steps of any plugged term. -/
theorem KStep.plug_step : ∀ {Γ : List PLLFormula} {C A : PLLFormula}
    {K K' : Kont Γ C A}, KStep K K' →
    ∀ (t : Tm Γ (somehow A)), Step (K.plug t) (K'.plug t) := by
  intro Γ C A K K' h
  induction h with
  | frame h' => exact fun t => Kont.plug_step _ (.bindCong₂ h')
  | tail _ ih => exact fun t => ih (.bind t _)
  | assocK u₁ u₂ K => exact fun t => Kont.plug_step K (.bindAssoc t u₁ u₂)

/-- Stack steps are preserved by renaming. -/
theorem KStep.rename : ∀ {Γ Δ : List PLLFormula} {C A : PLLFormula}
    (ρ : Ren Γ Δ) {K K' : Kont Γ C A},
    KStep K K' → KStep (K.rename ρ) (K'.rename ρ) := by
  intro Γ Δ C A ρ K K' h
  induction h with
  | frame h' => exact .frame (Step.rename ρ.lift h')
  | tail _ ih => exact .tail ih
  | assocK u₁ u₂ K =>
      show KStep _ (Kont.cons ((Tm.bind u₁ (u₂.rename Ren.skip1)).rename ρ.lift)
        (K.rename ρ))
      simp only [Tm.rename]
      rw [← Tm.rename_lift_skip1]
      exact .assocK (u₁.rename ρ.lift) (u₂.rename ρ.lift) (K.rename ρ)

/-- **Classification of the steps of a plugged term**, for an arbitrary
scrutinee `X`: either `X` steps, or the stack steps, or `X`'s head
constructor meets the innermost frame (`let`-β or `let`-assoc at the
interface).  This is `cut_aux`'s `leftCommute` in continuation clothing;
the scrutinee is kept general precisely so the lemma can be reused for
neutral, `val`- and `bind`-headed `X` alike. -/
theorem plug_step_cases : ∀ {Γ : List PLLFormula} {C A : PLLFormula}
    (K : Kont Γ C A) (X : Tm Γ (somehow A)) {y : Tm Γ (somehow C)},
    Step (K.plug X) y →
    (∃ X', Step X X' ∧ y = K.plug X') ∨
    (∃ K', KStep K K' ∧ y = K'.plug X) ∨
    (∃ (s₀ : Tm Γ A) (B : PLLFormula) (u₀ : Tm (A :: Γ) (somehow B))
        (K₀ : Kont Γ C B), X = .val s₀ ∧ K = .cons u₀ K₀ ∧
        y = K₀.plug (u₀.subst1 s₀)) ∨
    (∃ (A₀ : PLLFormula) (t₀ : Tm Γ (somehow A₀))
        (t₁ : Tm (A₀ :: Γ) (somehow A)) (B : PLLFormula)
        (u₀ : Tm (A :: Γ) (somehow B)) (K₀ : Kont Γ C B),
        X = .bind t₀ t₁ ∧ K = .cons u₀ K₀ ∧
        y = K₀.plug (.bind t₀ (.bind t₁ (u₀.rename Ren.skip1)))) := by
  intro Γ C A K
  induction K with
  | nil =>
      intro X y h
      exact .inl ⟨y, h, rfl⟩
  | cons u₀ K₀ ih =>
      intro X y h
      rcases ih (.bind X u₀) h with
        ⟨Z', hZ, rfl⟩ | ⟨K', hK, rfl⟩ | ⟨s₀, B', w, K₁, hXeq, hKeq, rfl⟩ |
        ⟨A₀, t₀, t₁, B', w, K₁, hXeq, hKeq, rfl⟩
      · cases hZ with
        | bindVal s _ =>
            exact .inr (.inr (.inl ⟨s, _, u₀, K₀, rfl, rfl, rfl⟩))
        | bindAssoc s t _ =>
            exact .inr (.inr (.inr ⟨_, s, t, _, u₀, K₀, rfl, rfl, rfl⟩))
        | bindCong₁ h' =>
            exact .inl ⟨_, h', rfl⟩
        | bindCong₂ h' =>
            exact .inr (.inl ⟨.cons _ K₀, .frame h', rfl⟩)
      · exact .inr (.inl ⟨.cons u₀ K', .tail hK, rfl⟩)
      · exact Tm.noConfusion hXeq
      · cases hXeq
        subst hKeq
        exact .inr (.inl ⟨_, .assocK u₀ w K₁, rfl⟩)

/-! ### The interface σ-lemma and the principal lemma -/

/-- Renaming by `skip1` and then substituting under a lifted `cons`
collapses to the identity: the merged frame of an interface assoc, once
the `let`-β fires, is the original frame. -/
theorem Tm.rename_skip1_subst_lift {Γ : List PLLFormula} {A B χ : PLLFormula}
    (u₀ : Tm (B :: Γ) χ) (s : Tm Γ A) :
    (u₀.rename (Ren.skip1 (φ := A))).subst (Sub.lift (Sub.cons s Sub.ids)) = u₀ := by
  rw [Tm.subst_rename]
  exact (u₀.subst_congr (by lift_cases)).trans u₀.subst_ids

/-- Instantiating a merged frame is binding the instance against the
original frame. -/
theorem bind_subst1_merge {Γ : List PLLFormula} {A B C : PLLFormula}
    (u : Tm (A :: Γ) (somehow B)) (u₀ : Tm (B :: Γ) (somehow C)) (s : Tm Γ A) :
    (Tm.bind u (u₀.rename Ren.skip1)).subst1 s = Tm.bind (u.subst1 s) u₀ := by
  show Tm.bind (u.subst (Sub.cons s Sub.ids))
      ((u₀.rename Ren.skip1).subst (Sub.lift (Sub.cons s Sub.ids))) = _
  rw [Tm.rename_skip1_subst_lift]
  exact rfl

/-- **The principal lemma** (Lindley–Stark): a `let`-β redex in a stack
context is SN as soon as its contractum-in-context and its value part are.
Induction over `(rank (K.plug (u[s])), K.size, rank s)`: the
interface-assoc reduct keeps the first component — the underlying term is
literally unchanged — and shortens the stack, which is exactly the case
bare `Acc`-induction cannot handle and ordinal rank can. -/
theorem principal : ∀ {Γ : List PLLFormula} {A B C : PLLFormula}
    (s : Tm Γ A) (u : Tm (A :: Γ) (somehow B)) (K : Kont Γ C B),
    SNt s → SNt (K.plug (u.subst1 s)) →
    SNt (K.plug (.bind (.val s) u)) := by
  suffices H : ∀ (μ : Ordinal × ℕ × Ordinal) {Γ A B C}
      (s : Tm Γ A) (u : Tm (A :: Γ) (somehow B)) (K : Kont Γ C B)
      (hs : SNt s) (hKu : SNt (K.plug (u.subst1 s))),
      μ = (Acc.rank hKu, K.size, Acc.rank hs) →
      SNt (K.plug (.bind (.val s) u)) by
    intro Γ A B C s u K hs hKu
    exact H _ s u K hs hKu rfl
  intro μ
  induction μ using lex₃_wf.induction with
  | _ μ IH =>
    intro Γ A B C s u K hs hKu hμ
    subst hμ
    refine Acc.intro _ fun y hy => ?_
    rcases plug_step_cases K _ hy with
      ⟨X', hX, rfl⟩ | ⟨K', hK, rfl⟩ | ⟨s₀, B', u₀, K₀, hXeq, hKeq, rfl⟩ |
      ⟨A₀, t₀, t₁, B', u₀, K₀, hXeq, hKeq, rfl⟩
    · -- the redex part stepped
      cases hX with
      | bindVal _ _ =>
          exact hKu
      | bindCong₁ h' =>
          cases h' with
          | valCong h'' =>
              have hs' := hs.step h''
              have hsteps := Kont.plug_steps K (u.subst1_steps_arg h'')
              have hKu' := SNt.steps hsteps hKu
              exact IH _ (lex₃_of_le_eq_lt (rank_le_of_steps hsteps hKu hKu')
                rfl (rank_lt_of_step hs hs' h'')) _ u K hs' hKu' rfl
      | bindCong₂ h' =>
          have hstep := Kont.plug_step K (Step.subst (Sub.cons s Sub.ids) h')
          have hKu' := hKu.step hstep
          exact IH _ (lex₃_of_lt (rank_lt_of_step hKu hKu' hstep)) s _ K hs hKu' rfl
    · -- the stack stepped
      have hstep := KStep.plug_step hK (u.subst1 s)
      have hKu' := hKu.step hstep
      exact IH _ (lex₃_of_lt (rank_lt_of_step hKu hKu' hstep)) s u K' hs hKu' rfl
    · -- X = val s₀: impossible, X is a bind
      exact Tm.noConfusion hXeq
    · -- interface assoc: same contractum, shorter stack
      cases hXeq
      subst hKeq
      have heq : K₀.plug ((Tm.bind u (u₀.rename Ren.skip1)).subst1 s)
          = K₀.plug (Tm.bind (u.subst1 s) u₀) :=
        congrArg _ (bind_subst1_merge u u₀ s)
      have hKu' : SNt (K₀.plug ((Tm.bind u (u₀.rename Ren.skip1)).subst1 s)) :=
        heq ▸ hKu
      exact IH _ (lex₃_of_le_lt (rank_eq_of_eq heq hKu' hKu).le
        (Nat.lt_succ_self _)) s _ K₀ hs hKu' rfl

end PLLND
