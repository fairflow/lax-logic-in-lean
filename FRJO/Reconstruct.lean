/-
# FRJ◯ W5, the base case — `Reconstruction` at a solo countermodel

The lemma kit for `Reconstruction`, all PROVED: `sf` transitivity and
closure of the universe, closure soundness (`clB` ⟹ derivable, via
the searcher's own certificate), fallible-solo triviality.

STATUS NOTE (2026-08-16).  The solo case WAS proved against worldOK
v2 (commit `99868db`) — and doing so flushed out that v2 was UNSOUND:
its goal conjunct read the bounded searcher (`clB`), whose budget
failures admit semantically wrong `world` nodes, making W3b false.
worldOK v3 (structural membership conjuncts, shape-restricted goals)
repairs this, and invalidates the v2 proof: under v3, compound goals
must go through their own rules, so the solo case needs the inner
induction on the goal formula.

Both cases are now PROVED under v3, in `FRJO/Recon.lean`:
`FRJO.recon_solo` and `FRJO.recon_join`, assembled as `FRJO.recon`,
all pinned `[propext, Quot.sound]`.  `ReconstructionSolo` below is
discharged by `FRJO.reconstructionSolo`.

Separately, v3 turned out to be unsound for W3b as well, for a
DIFFERENT reason: it constrains the stable zone only by membership in
the universe, never by closure.  `FRJO/Screen.lean` refutes
`ExtractForces` at three certified cells and specifies (and checks)
the v4 repair.
-/
import FRJO.Complete

namespace FRJO

open PLLND PLLFormula Classical

/-! ## sf transitivity and closure of the universe -/

theorem sf_trans : ∀ (ρ ψ φ : PLLFormula), ψ ∈ sf φ → φ ∈ sf ρ → ψ ∈ sf ρ := by
  intro ρ
  induction ρ with
  | prop a => intro ψ φ hψ hφ; simp [sf] at hφ; subst hφ; simpa [sf] using hψ
  | falsePLL => intro ψ φ hψ hφ; simp [sf] at hφ; subst hφ; simpa [sf] using hψ
  | and α β ihα ihβ =>
      intro ψ φ hψ hφ
      simp only [sf, List.mem_cons, List.mem_append] at hφ ⊢
      rcases hφ with rfl | hφ | hφ
      · simp only [sf, List.mem_cons, List.mem_append] at hψ; exact hψ
      · exact Or.inr (Or.inl (ihα ψ φ hψ hφ))
      · exact Or.inr (Or.inr (ihβ ψ φ hψ hφ))
  | or α β ihα ihβ =>
      intro ψ φ hψ hφ
      simp only [sf, List.mem_cons, List.mem_append] at hφ ⊢
      rcases hφ with rfl | hφ | hφ
      · simp only [sf, List.mem_cons, List.mem_append] at hψ; exact hψ
      · exact Or.inr (Or.inl (ihα ψ φ hψ hφ))
      · exact Or.inr (Or.inr (ihβ ψ φ hψ hφ))
  | ifThen α β ihα ihβ =>
      intro ψ φ hψ hφ
      simp only [sf, List.mem_cons, List.mem_append] at hφ ⊢
      rcases hφ with rfl | hφ | hφ
      · simp only [sf, List.mem_cons, List.mem_append] at hψ; exact hψ
      · exact Or.inr (Or.inl (ihα ψ φ hψ hφ))
      · exact Or.inr (Or.inr (ihβ ψ φ hψ hφ))
  | somehow α ihα =>
      intro ψ φ hψ hφ
      simp only [sf, List.mem_cons] at hφ ⊢
      rcases hφ with rfl | hφ
      · simp only [sf, List.mem_cons] at hψ; exact hψ
      · exact Or.inr (ihα ψ φ hψ hφ)

theorem sfPlus_closed {G : Cell} {φ ψ : PLLFormula}
    (hφ : φ ∈ sfPlus G) (hψ : ψ ∈ sf φ) : ψ ∈ sfPlus G := by
  simp only [sfPlus, List.mem_eraseDups, List.mem_flatMap] at hφ ⊢
  obtain ⟨ρ, hρ, hm⟩ := hφ
  exact ⟨ρ, hρ, sf_trans ρ ψ φ hψ hm⟩

/-! ## The closure is sound -/

theorem clB_sound {G : Cell} {b : Nat} {Δ : List PLLFormula}
    {φ : PLLFormula} (h : φ ∈ clB G b Δ) : Nonempty (LaxND Δ φ) := by
  simp only [clB, List.mem_filter] at h
  obtain ⟨-, h⟩ := h
  cases hd : Search.decide { findBudget := some b, emitClosureCap := 0 } Δ φ with
  | proved t => exact Search.proved_sound t
  | refuted w => rw [hd] at h; simp at h
  | unknown => rw [hd] at h; simp at h

/-! ## Fallible solo worlds force everything -/

theorem solo_fal_forces {V₀ : String → Prop} {fal : Prop}
    {hfull : fal → ∀ a, V₀ a} (hf : fal) (φ : PLLFormula) :
    (Reject.solo V₀ fal hfull).force () φ := by
  induction φ with
  | prop a => exact hfull hf a
  | falsePLL => exact hf
  | and φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | or φ ψ ihφ _ => exact Or.inl ihφ
  | ifThen φ ψ _ ihψ => intro v _ _; cases v; exact ihψ
  | somehow φ ihφ => intro v _; cases v; exact ⟨(), True.intro, ihφ⟩

/-! ## The base case — PROVED, in `FRJO/Recon.lean` -/

/-- The solo half of `Reconstruction`: a sequent refuted at a
one-world countermodel has an FRJ◯ derivation.  PROVED as
`FRJO.reconstructionSolo` (`FRJO/Recon.lean`) exactly on this plan:
inner induction on the goal formula; `world` nodes at base shapes with
the zone `theory ∩ sfPlus`; `impIn` at ⊃ (the antecedent is forced at
the only world); `orR`/`andR` at compounds. -/
def ReconstructionSolo (b : Nat) : Prop :=
  ∀ (Γ : List PLLFormula) (C : PLLFormula)
    (V₀ : String → Prop) (fal : Prop) (hfull : fal → ∀ a, V₀ a),
    (∀ φ ∈ Γ, (Reject.solo V₀ fal hfull).force () φ) →
    ¬ (Reject.solo V₀ fal hfull).force () C →
    ∃ S : Reg ⟨Γ, C⟩, S.goal = C ∧ Γ ⊆ S.stable ∧
      Nonempty (FRJD ⟨Γ, C⟩ b S)

end FRJO
