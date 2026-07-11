import LaxLogic.PLLG4Space

/-!
# Craig interpolation for PLL (Maehara's method)

**Craig interpolation** for propositional lax logic, proved by Maehara's
method over the cut-free complete sequent calculus `SCh`/`SC` of
`PLLSequent.lean`.  Since the repo proves `SC` equivalent to natural
deduction (`cutElimination`, F&M Theorem 2.6) and hence to the Hilbert
system and the term calculus, interpolation for `SC`-derivability *is*
Craig interpolation for PLL.

Given a derivation of `Γ ⊢ C` and a splitting of the context into two
parts `Γ₁; Γ₂`, Maehara's induction produces an **interpolant** `I`:

  * `Γ₁ ⊢ I` and `I, Γ₂ ⊢ C`, and
  * every atom of `I` occurs both in `Γ₁` and in `Γ₂, C`.

Because the left rules of `SCh` are membership-style (the principal
formula stays in the context), the working notion of splitting is a
membership assignment `∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂` (`SCh.maehara`); the
packaged statements (`SC.maehara`, `craig_interpolation`,
`craig_implication`) specialise it to permutation/append splittings.

The interpolant construction is the textbook one on the intuitionistic
fragment — interpolants combine by `∧`/`∨`/`⊃` according to the side
carrying the principal formula, with the split *swapped* for the minor
premise of `⊃L` when the principal implication sits in `Γ₁`.  The two
lax rules add exactly one twist:

  * `◯R` and `◯L`-with-principal-in-`Γ₂` pass the premise interpolant
    through unchanged;
  * `◯L` with principal `◯A ∈ Γ₁` **boxes** the premise interpolant,
    `I ↦ ◯I`.  Boxing is forced: to derive `Γ₁ ⊢ I` one would have to
    open `◯A ∈ Γ₁` with `◯L`, and `◯L` fires only at a `◯`-shaped
    succedent.  `◯I` restores the discipline on both sides — `Γ₁ ⊢ ◯I`
    opens `◯A` under the now-boxed goal, and `◯I, Γ₂ ⊢ ◯B` opens `◯I`
    under the `◯`-shaped end-formula `◯B`.

This mirrors the `□`-case of Maehara interpolation for constructive
modal calculi; the single-succedent lax `◯` needs no bookkeeping
beyond it.
-/

open PLLFormula

namespace PLLND

/-! ### Atoms of a context -/

/-- The atoms occurring in a list of formulas. -/
def atomsList : List PLLFormula → Finset String
  | [] => ∅
  | φ :: Γ => φ.atoms ∪ atomsList Γ

@[simp] theorem atomsList_nil : atomsList [] = ∅ := rfl

@[simp] theorem atomsList_cons {φ : PLLFormula} {Γ : List PLLFormula} :
    atomsList (φ :: Γ) = φ.atoms ∪ atomsList Γ := rfl

/-- Atoms of a member are atoms of the list. -/
theorem atoms_subset_atomsList {φ : PLLFormula} {Γ : List PLLFormula}
    (h : φ ∈ Γ) : φ.atoms ⊆ atomsList Γ := by
  induction Γ with
  | nil => cases h
  | cons ψ Γ ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Finset.subset_union_left
      · exact subset_trans (ih h) Finset.subset_union_right

/-- Consing a formula whose atoms are already present adds no atoms. -/
theorem atomsList_cons_subset {X : PLLFormula} {Γ : List PLLFormula}
    (hX : X.atoms ⊆ atomsList Γ) : atomsList (X :: Γ) ⊆ atomsList Γ := by
  rw [atomsList_cons]
  exact Finset.union_subset hX (Finset.Subset.refl _)

/-! ### Atom bookkeeping: connective components and union monotonicity -/

private theorem atoms_and_left {A B : PLLFormula} :
    A.atoms ⊆ (A.and B).atoms := by
  rw [atoms_and]; exact Finset.subset_union_left

private theorem atoms_and_right {A B : PLLFormula} :
    B.atoms ⊆ (A.and B).atoms := by
  rw [atoms_and]; exact Finset.subset_union_right

private theorem atoms_or_left {A B : PLLFormula} :
    A.atoms ⊆ (A.or B).atoms := by
  rw [atoms_or]; exact Finset.subset_union_left

private theorem atoms_or_right {A B : PLLFormula} :
    B.atoms ⊆ (A.or B).atoms := by
  rw [atoms_or]; exact Finset.subset_union_right

private theorem atoms_imp_left {A B : PLLFormula} :
    A.atoms ⊆ (A.ifThen B).atoms := by
  rw [atoms_ifThen]; exact Finset.subset_union_left

private theorem atoms_imp_right {A B : PLLFormula} :
    B.atoms ⊆ (A.ifThen B).atoms := by
  rw [atoms_ifThen]; exact Finset.subset_union_right

private theorem atoms_lax {A : PLLFormula} :
    A.atoms ⊆ (A.somehow).atoms := by
  intro x hx
  rwa [atoms_somehow]

/-- Monotonicity of `⊆ _ ∪ _` in the right component. -/
private theorem sub_union_right_mono {s t u v : Finset String}
    (h : s ⊆ t ∪ u) (huv : u ⊆ v) : s ⊆ t ∪ v :=
  subset_trans h (Finset.union_subset_union (Finset.Subset.refl _) huv)

/-- Monotonicity of `⊆ _ ∪ _` in the left component. -/
private theorem sub_union_left_mono {s t t' u : Finset String}
    (h : s ⊆ t ∪ u) (htt' : t ⊆ t') : s ⊆ t' ∪ u :=
  subset_trans h (Finset.union_subset_union htt' (Finset.Subset.refl _))

/-! ### Splitting combinators

A *split* of `Γ` assigns each hypothesis to `Γ₁` or to `Γ₂`.  The three
combinators below are the only ways splits evolve during the induction:
a freshly introduced hypothesis joins the side of its principal
formula, and (for the minor premise of `⊃L` on the `Γ₁` side) the two
sides swap roles. -/

private theorem split_cons_left {φ : PLLFormula} {Γ Γ₁ Γ₂ : List PLLFormula}
    (H : ∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂) :
    ∀ ψ ∈ φ :: Γ, ψ ∈ φ :: Γ₁ ∨ ψ ∈ Γ₂ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact Or.inl (.head _)
  · rcases H _ hψ with h | h
    · exact Or.inl (.tail _ h)
    · exact Or.inr h

private theorem split_cons_right {φ : PLLFormula} {Γ Γ₁ Γ₂ : List PLLFormula}
    (H : ∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂) :
    ∀ ψ ∈ φ :: Γ, ψ ∈ Γ₁ ∨ ψ ∈ φ :: Γ₂ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact Or.inr (.head _)
  · rcases H _ hψ with h | h
    · exact Or.inl h
    · exact Or.inr (.tail _ h)

private theorem split_swap {Γ Γ₁ Γ₂ : List PLLFormula}
    (H : ∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂) :
    ∀ ψ ∈ Γ, ψ ∈ Γ₂ ∨ ψ ∈ Γ₁ :=
  fun ψ hψ => (H ψ hψ).symm

/-- `⊤` (definitionally `⊥ ⊃ ⊥`) is derivable in any context. -/
theorem SC.trueR {Γ : List PLLFormula} : SC Γ truePLL :=
  SC.impR (SC.botL (.head _))

/-! ### Maehara's lemma -/

/-- **Maehara's lemma** for the cut-free calculus, membership-split form:
from a derivation of `Γ ⊢ C` and an assignment of each hypothesis of `Γ`
to `Γ₁` or to `Γ₂`, an interpolant `I` with `Γ₁ ⊢ I`, `I, Γ₂ ⊢ C`, and
`I`'s atoms contained both in `Γ₁`'s and in `Γ₂, C`'s.

Interpolant construction, by the last rule and the side of its
principal formula (`Γ₁`-side / `Γ₂`-side):

| rule       | `Γ₁`-side              | `Γ₂`-side       |
|------------|------------------------|-----------------|
| `init`     | the atom itself        | `⊤`             |
| `botL`     | `⊥`                    | `⊤`             |
| `andR`     | `I₁ ∧ I₂`              | (same — right rule) |
| `andL`     | pass through           | pass through    |
| `orR1/2`   | pass through           | (right rule)    |
| `orL`      | `I₁ ∨ I₂`              | `I₁ ∧ I₂`       |
| `impR`     | pass through           | (right rule)    |
| `impL`     | `I₁ ⊃ I₂` (split swapped for the minor premise) | `I₁ ∧ I₂` |
| `laxR`     | pass through           | (right rule)    |
| `laxL`     | **`◯I`**               | pass through    |
-/
theorem SCh.maehara : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    SCh n Γ C → ∀ Γ₁ Γ₂ : List PLLFormula,
    (∀ ψ ∈ Γ, ψ ∈ Γ₁ ∨ ψ ∈ Γ₂) →
    ∃ I : PLLFormula,
      SC Γ₁ I ∧ SC (I :: Γ₂) C ∧
      I.atoms ⊆ atomsList Γ₁ ∧ I.atoms ⊆ atomsList Γ₂ ∪ C.atoms := by
  intro n Γ C d
  induction d with
  | @init n Γ a h =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · exact ⟨.prop a, SC.init h₁, SC.init (.head _),
          atoms_subset_atomsList h₁, Finset.subset_union_right⟩
      · refine ⟨truePLL, SC.trueR, SC.init (.tail _ h₂), ?_, ?_⟩ <;> simp
  | @botL n Γ C h =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · exact ⟨.falsePLL, SC.botL h₁, SC.botL (.head _), by simp, by simp⟩
      · refine ⟨truePLL, SC.trueR, SC.botL (.tail _ h₂), ?_, ?_⟩ <;> simp
  | @andR n Γ A B dA dB ihA ihB =>
      intro Γ₁ Γ₂ H
      obtain ⟨I₁, s₁, t₁, a₁, b₁⟩ := ihA Γ₁ Γ₂ H
      obtain ⟨I₂, s₂, t₂, a₂, b₂⟩ := ihB Γ₁ Γ₂ H
      refine ⟨I₁.and I₂, SC.andR s₁ s₂, ?_, ?_, ?_⟩
      · refine SC.andL (.head _) (SC.andR ?_ ?_)
        · exact t₁.rename (by
            intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
        · exact t₂.rename (by
            intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
      · simp only [atoms_and]
        exact Finset.union_subset a₁ a₂
      · simp only [atoms_and]
        exact Finset.union_subset
          (sub_union_right_mono b₁ Finset.subset_union_left)
          (sub_union_right_mono b₂ Finset.subset_union_right)
  | @andL n Γ A B C h d ih =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · -- principal `A ∧ B` assigned to `Γ₁`: pass through
        obtain ⟨I, s, t, a₁, a₂⟩ :=
          ih (A :: B :: Γ₁) Γ₂ (split_cons_left (split_cons_left H))
        have hA : A.atoms ⊆ atomsList Γ₁ :=
          subset_trans atoms_and_left (atoms_subset_atomsList h₁)
        have hB : B.atoms ⊆ atomsList Γ₁ :=
          subset_trans atoms_and_right (atoms_subset_atomsList h₁)
        have habs : atomsList (A :: B :: Γ₁) ⊆ atomsList Γ₁ := by
          simp only [atomsList_cons]
          exact Finset.union_subset hA
            (Finset.union_subset hB (Finset.Subset.refl _))
        exact ⟨I, SC.andL h₁ s, t, subset_trans a₁ habs, a₂⟩
      · -- principal `A ∧ B` assigned to `Γ₂`: pass through
        obtain ⟨I, s, t, a₁, a₂⟩ :=
          ih Γ₁ (A :: B :: Γ₂) (split_cons_right (split_cons_right H))
        have hA : A.atoms ⊆ atomsList Γ₂ :=
          subset_trans atoms_and_left (atoms_subset_atomsList h₂)
        have hB : B.atoms ⊆ atomsList Γ₂ :=
          subset_trans atoms_and_right (atoms_subset_atomsList h₂)
        have habs : atomsList (A :: B :: Γ₂) ⊆ atomsList Γ₂ := by
          simp only [atomsList_cons]
          exact Finset.union_subset hA
            (Finset.union_subset hB (Finset.Subset.refl _))
        refine ⟨I, s, ?_, a₁, sub_union_left_mono a₂ habs⟩
        refine SC.andL (.tail _ h₂) ?_
        exact t.rename (by
          intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
  | @orR1 n Γ A B d ih =>
      intro Γ₁ Γ₂ H
      obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ Γ₂ H
      exact ⟨I, s, SC.orR1 t, a₁, sub_union_right_mono a₂ atoms_or_left⟩
  | @orR2 n Γ A B d ih =>
      intro Γ₁ Γ₂ H
      obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ Γ₂ H
      exact ⟨I, s, SC.orR2 t, a₁, sub_union_right_mono a₂ atoms_or_right⟩
  | @orL n Γ A B C h d₁ d₂ ih₁ ih₂ =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · -- principal `A ∨ B` in `Γ₁`: interpolants combine with `∨`
        obtain ⟨I₁, s₁, t₁, a₁, b₁⟩ := ih₁ (A :: Γ₁) Γ₂ (split_cons_left H)
        obtain ⟨I₂, s₂, t₂, a₂, b₂⟩ := ih₂ (B :: Γ₁) Γ₂ (split_cons_left H)
        have hA : A.atoms ⊆ atomsList Γ₁ :=
          subset_trans atoms_or_left (atoms_subset_atomsList h₁)
        have hB : B.atoms ⊆ atomsList Γ₁ :=
          subset_trans atoms_or_right (atoms_subset_atomsList h₁)
        refine ⟨I₁.or I₂, SC.orL h₁ (SC.orR1 s₁) (SC.orR2 s₂), ?_, ?_, ?_⟩
        · refine SC.orL (.head _) ?_ ?_
          · exact t₁.rename (by
              intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
          · exact t₂.rename (by
              intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
        · simp only [atoms_or]
          exact Finset.union_subset
            (subset_trans a₁ (atomsList_cons_subset hA))
            (subset_trans a₂ (atomsList_cons_subset hB))
        · simp only [atoms_or]
          exact Finset.union_subset b₁ b₂
      · -- principal `A ∨ B` in `Γ₂`: interpolants combine with `∧`
        obtain ⟨I₁, s₁, t₁, a₁, b₁⟩ := ih₁ Γ₁ (A :: Γ₂) (split_cons_right H)
        obtain ⟨I₂, s₂, t₂, a₂, b₂⟩ := ih₂ Γ₁ (B :: Γ₂) (split_cons_right H)
        have hA : A.atoms ⊆ atomsList Γ₂ :=
          subset_trans atoms_or_left (atoms_subset_atomsList h₂)
        have hB : B.atoms ⊆ atomsList Γ₂ :=
          subset_trans atoms_or_right (atoms_subset_atomsList h₂)
        refine ⟨I₁.and I₂, SC.andR s₁ s₂, ?_, ?_, ?_⟩
        · refine SC.orL (.tail _ h₂) ?_ ?_
          · refine SC.andL (.tail _ (.head _)) ?_
            exact t₁.rename (by
              intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
          · refine SC.andL (.tail _ (.head _)) ?_
            exact t₂.rename (by
              intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
        · simp only [atoms_and]
          exact Finset.union_subset a₁ a₂
        · simp only [atoms_and]
          exact Finset.union_subset
            (sub_union_left_mono b₁ (atomsList_cons_subset hA))
            (sub_union_left_mono b₂ (atomsList_cons_subset hB))
  | @impR n Γ A B d ih =>
      intro Γ₁ Γ₂ H
      obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ (A :: Γ₂) (split_cons_right H)
      refine ⟨I, s, ?_, a₁, ?_⟩
      · refine SC.impR ?_
        exact t.rename (by
          intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
      · -- the discharged hypothesis `A` migrates from context to succedent
        intro x hx
        have hx' := a₂ hx
        simp only [atomsList_cons, Finset.mem_union, atoms_ifThen] at hx' ⊢
        tauto
  | @impL n Γ A B C h d₁ d₂ ih₁ ih₂ =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · -- principal `A ⊃ B` in `Γ₁`: `I₁ ⊃ I₂`, with the split *swapped*
        -- for the minor premise `Γ ⊢ A`
        obtain ⟨J, sJ, tJ, aJ, bJ⟩ := ih₁ Γ₂ Γ₁ (split_swap H)
        obtain ⟨K, sK, tK, aK, bK⟩ := ih₂ (B :: Γ₁) Γ₂ (split_cons_left H)
        have hA : A.atoms ⊆ atomsList Γ₁ :=
          subset_trans atoms_imp_left (atoms_subset_atomsList h₁)
        have hB : B.atoms ⊆ atomsList Γ₁ :=
          subset_trans atoms_imp_right (atoms_subset_atomsList h₁)
        refine ⟨J.ifThen K, ?_, ?_, ?_, ?_⟩
        · refine SC.impR (SC.impL (.tail _ h₁) tJ ?_)
          exact sK.rename (by
            intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
        · refine SC.impL (.head _) ?_ ?_
          · exact sJ.rename (fun ψ hψ => .tail _ hψ)
          · exact tK.rename (by
              intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
        · simp only [atoms_ifThen]
          refine Finset.union_subset ?_
            (subset_trans aK (atomsList_cons_subset hB))
          exact subset_trans bJ
            (Finset.union_subset (Finset.Subset.refl _) hA)
        · simp only [atoms_ifThen]
          exact Finset.union_subset
            (subset_trans aJ Finset.subset_union_left) bK
      · -- principal `A ⊃ B` in `Γ₂`: interpolants combine with `∧`
        obtain ⟨I₁, s₁, t₁, a₁, b₁⟩ := ih₁ Γ₁ Γ₂ H
        obtain ⟨I₂, s₂, t₂, a₂, b₂⟩ := ih₂ Γ₁ (B :: Γ₂) (split_cons_right H)
        have hA : A.atoms ⊆ atomsList Γ₂ :=
          subset_trans atoms_imp_left (atoms_subset_atomsList h₂)
        have hB : B.atoms ⊆ atomsList Γ₂ :=
          subset_trans atoms_imp_right (atoms_subset_atomsList h₂)
        refine ⟨I₁.and I₂, SC.andR s₁ s₂, ?_, ?_, ?_⟩
        · refine SC.andL (.head _) ?_
          refine SC.impL (.tail _ (.tail _ (.tail _ h₂))) ?_ ?_
          · exact t₁.rename (by
              intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
          · exact t₂.rename (by
              intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
        · simp only [atoms_and]
          exact Finset.union_subset a₁ a₂
        · simp only [atoms_and]
          refine Finset.union_subset ?_
            (sub_union_left_mono b₂ (atomsList_cons_subset hB))
          exact subset_trans
            (subset_trans b₁ (Finset.union_subset (Finset.Subset.refl _) hA))
            Finset.subset_union_left
  | @laxR n Γ A d ih =>
      intro Γ₁ Γ₂ H
      obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ Γ₂ H
      exact ⟨I, s, SC.laxR t, a₁, sub_union_right_mono a₂ atoms_lax⟩
  | @laxL n Γ A B h d ih =>
      intro Γ₁ Γ₂ H
      rcases H _ h with h₁ | h₂
      · -- principal `◯A` in `Γ₁`: **box** the premise interpolant.
        -- A bare pass-through fails: `Γ₁ ⊢ I` would need `◯L` on
        -- `◯A ∈ Γ₁`, which fires only at a `◯`-shaped succedent.
        obtain ⟨I, s, t, a₁, a₂⟩ := ih (A :: Γ₁) Γ₂ (split_cons_left H)
        have hA : A.atoms ⊆ atomsList Γ₁ :=
          subset_trans atoms_lax (atoms_subset_atomsList h₁)
        refine ⟨I.somehow, SC.laxL h₁ (SC.laxR s), ?_, ?_, ?_⟩
        · refine SC.laxL (.head _) ?_
          exact t.rename (by
            intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)
        · simp only [atoms_somehow]
          exact subset_trans a₁ (atomsList_cons_subset hA)
        · simpa only [atoms_somehow] using a₂
      · -- principal `◯A` in `Γ₂`: pass through
        obtain ⟨I, s, t, a₁, a₂⟩ := ih Γ₁ (A :: Γ₂) (split_cons_right H)
        have hA : A.atoms ⊆ atomsList Γ₂ :=
          subset_trans atoms_lax (atoms_subset_atomsList h₂)
        refine ⟨I, s, ?_, a₁, sub_union_left_mono a₂ (atomsList_cons_subset hA)⟩
        refine SC.laxL (.tail _ h₂) ?_
        exact t.rename (by
          intro ψ hψ; simp only [List.mem_cons] at hψ ⊢; tauto)

/-! ### Packaged statements -/

/-- **Maehara interpolation** for `SC`: every permutation-splitting of the
context of a derivable sequent has an interpolant over the shared atoms. -/
theorem SC.maehara {Γ : List PLLFormula} {C : PLLFormula} :
    SC Γ C → ∀ Γ₁ Γ₂ : List PLLFormula, Γ.Perm (Γ₁ ++ Γ₂) →
    ∃ I : PLLFormula,
      SC Γ₁ I ∧ SC (I :: Γ₂) C ∧
      I.atoms ⊆ atomsList Γ₁ ∩ (atomsList Γ₂ ∪ C.atoms) := by
  rintro ⟨n, d⟩ Γ₁ Γ₂ hp
  obtain ⟨I, s, t, a₁, a₂⟩ := d.maehara Γ₁ Γ₂
    (fun ψ hψ => List.mem_append.mp (hp.subset hψ))
  exact ⟨I, s, t, Finset.subset_inter a₁ a₂⟩

/-- **Craig interpolation for PLL**, sequent form: if `Γ₁ ++ Γ₂ ⊢ C` is
derivable then some interpolant `I` has `Γ₁ ⊢ I`, `I, Γ₂ ⊢ C`, and atoms
occurring both in `Γ₁` and in `Γ₂, C`. -/
theorem craig_interpolation {Γ₁ Γ₂ : List PLLFormula} {C : PLLFormula}
    (h : SC (Γ₁ ++ Γ₂) C) :
    ∃ I : PLLFormula,
      SC Γ₁ I ∧ SC (I :: Γ₂) C ∧
      I.atoms ⊆ atomsList Γ₁ ∩ (atomsList Γ₂ ∪ C.atoms) :=
  h.maehara Γ₁ Γ₂ (List.Perm.refl _)

/-- **Craig interpolation for PLL**, implication form: if `⊢ A ⊃ B` then
there is an interpolant `I` over the common atoms of `A` and `B` with
`⊢ A ⊃ I` and `⊢ I ⊃ B`. -/
theorem craig_implication {A B : PLLFormula} (h : SC [] (A.ifThen B)) :
    ∃ I : PLLFormula,
      SC [] (A.ifThen I) ∧ SC [] (I.ifThen B) ∧
      I.atoms ⊆ A.atoms ∩ B.atoms := by
  have hAB : SC [A] B := by
    have h' : SC [A] (A.ifThen B) := h.rename (by intro ψ hψ; cases hψ)
    exact SC.cut h' (SC.impL (.head _)
      (SC.iden A (.tail _ (.head _))) (SC.iden B (.head _)))
  obtain ⟨I, s, t, hI⟩ := hAB.maehara [A] [] (List.Perm.refl _)
  exact ⟨I, SC.impR s, SC.impR t, by simpa using hI⟩

/-! ### Axiom audit -/

/--
info: 'PLLND.SC.maehara' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SC.maehara

/--
info: 'PLLND.craig_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms craig_interpolation

/--
info: 'PLLND.craig_implication' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms craig_implication

end PLLND
