import LaxLogic.PLL.Semantics.Subframe
import LaxLogic.PLL.SemUI.SemUIFrag
import LaxLogic.PLL.SemUI.SemUIOFree

/-!
# Step 2 of the semantic route in the subframe semantics

Step 2 of the semantic route to uniform interpolation turns agreement on a
finite fragment into a layered bisimulation.  Over constraint models it is
REFUTED (`SemUI.layered_of_frag_agree_refuted`,
`SemUI.pair_escape_not_from_agreement`): the refuting cells force a partner
for a fallible world, or for an `Rm`-move into one.  Subframe models
(`LaxLogic/PLL/Semantics/Subframe.lean`) have no fallible worlds, and `◯` is
the universal modality over `≤ ∩ S`:

    x ⊩ ◯φ   ⟺   ∀ y ≥ x, y ∈ S → y ⊩ φ.

So the Hennessy–Milner character argument goes through.  Write `w ≡ᵣ w'` for
agreement on every formula of crank ≤ r over the finite atom set `V`
(`Agree`), and `w ⇄ₙ w'` for "linked at level n by some layered
bisimulation over `V`" (`LayeredBisim`: atoms, `≤`-forth/back and
`S`-forth/back, each step down one level).  This file PROVES

    w ≡_{3n+1} w'   ⟹   w ⇄ₙ w'   ⟹   w ≡ₙ w'

(`layered_of_agree`, `agree_of_layered`), and, first (rule 8), the ◯-free
instance, which is the textbook IPC statement:

    w ≡°_{n+1} w'   ⟹   w ⇄°ₙ w'   ⟹   w ≡°ₙ w'

with `≡°` agreement on ◯-free formulas and `⇄°` the bisimulation without the
`S`-clauses (`layeredI_of_agree`, `agreeI_of_layeredI`).

The characters.  Let `L` list representatives of the formulas of crank ≤ r
over `V` up to interderivability (`SemUI.frag_reps_exist'`).  For a world
`v`, put `θ⁺ := ⋀ {D ∈ L | v ⊩ D}` and `θ⁻ := ⋁ {D ∈ L | v ⊮ D}`.  Then

* `u ≤ v` gives `u ⊮ θ⁺ ↠ θ⁻`, of crank ≤ r + 1; a world `u'` refuting it has
  some `v' ≥ u'` with the same `L`-type as `v` (`≤`-forth);
* `u ≤ v ∈ S` gives `u ⊮ θ⁺ ↠ ◯θ⁻`, of crank ≤ r + 3; a world `u'` refuting
  it has some `v' ≥ u'` in `S` with the same `L`-type as `v` (`S`-forth; the
  `S`-point is reached through persistence of `θ⁺`).

The `S`-step costs three ranks, so level `n` is agreement at crank `3n + 1`
(the `+1` pays for `⋀ [] = ⊤`, of crank 1).  For the ◯-free instance the
representatives must be ◯-free: `eraseBox` replaces every `◯ψ` by `⊤`, and in
the model with `S` emptied (`noS`) each formula and its erasure are forced at
the same worlds, so an erased representative still represents
(`force_iff_eraseBox_of_interd`).

`S_clause_needed` is the designed cell for the `S`-clauses: two one-point
models, one point in `S` and one not, linked at every level by the
`≤`-bisimulation, separated by `◯⊥` (crank 2).

What this does not give: step 3 (amalgamation) in the subframe semantics,
and the semantic quantifiers over subframe models.  See
`docs/subframe-step2-2026-10-14.md`.
-/

open PLLFormula

namespace PLLND

namespace SemUI

/-! ## Erasing `◯` -/

/-- Replace every `◯`-subformula by `⊤`. -/
def eraseBox : PLLFormula → PLLFormula
  | .prop a => .prop a
  | .falsePLL => .falsePLL
  | .and φ ψ => .and (eraseBox φ) (eraseBox ψ)
  | .or φ ψ => .or (eraseBox φ) (eraseBox ψ)
  | .ifThen φ ψ => .ifThen (eraseBox φ) (eraseBox ψ)
  | .somehow _ => truePLL

theorem boxFree_eraseBox : ∀ φ : PLLFormula, boxFree (eraseBox φ) = true
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and φ ψ => by
      simp only [eraseBox, boxFree, Bool.and_eq_true]
      exact ⟨boxFree_eraseBox φ, boxFree_eraseBox ψ⟩
  | .or φ ψ => by
      simp only [eraseBox, boxFree, Bool.and_eq_true]
      exact ⟨boxFree_eraseBox φ, boxFree_eraseBox ψ⟩
  | .ifThen φ ψ => by
      simp only [eraseBox, boxFree, Bool.and_eq_true]
      exact ⟨boxFree_eraseBox φ, boxFree_eraseBox ψ⟩
  | .somehow _ => rfl

theorem crank_eraseBox_le : ∀ φ : PLLFormula, crank (eraseBox φ) ≤ crank φ
  | .prop _ => le_refl _
  | .falsePLL => le_refl _
  | .and φ ψ => by
      have h₁ := crank_eraseBox_le φ
      have h₂ := crank_eraseBox_le ψ
      simp only [eraseBox, crank]
      omega
  | .or φ ψ => by
      have h₁ := crank_eraseBox_le φ
      have h₂ := crank_eraseBox_le ψ
      simp only [eraseBox, crank]
      omega
  | .ifThen φ ψ => by
      have h₁ := crank_eraseBox_le φ
      have h₂ := crank_eraseBox_le ψ
      simp only [eraseBox, crank]
      omega
  | .somehow φ => by
      have h : crank (eraseBox (.somehow φ)) = 1 := rfl
      simp only [crank]
      omega

theorem mem_atoms_eraseBox {a : String} :
    ∀ {φ : PLLFormula}, a ∈ (eraseBox φ).atoms → a ∈ φ.atoms
  | .prop _, h => h
  | .falsePLL, h => h
  | .and φ ψ, h => by
      rcases mem_atoms_and.mp h with h' | h'
      exacts [mem_atoms_and.mpr (Or.inl (mem_atoms_eraseBox h')),
        mem_atoms_and.mpr (Or.inr (mem_atoms_eraseBox h'))]
  | .or φ ψ, h => by
      rcases mem_atoms_or.mp h with h' | h'
      exacts [mem_atoms_or.mpr (Or.inl (mem_atoms_eraseBox h')),
        mem_atoms_or.mpr (Or.inr (mem_atoms_eraseBox h'))]
  | .ifThen φ ψ, h => by
      rcases mem_atoms_ifThen.mp h with h' | h'
      exacts [mem_atoms_ifThen.mpr (Or.inl (mem_atoms_eraseBox h')),
        mem_atoms_ifThen.mpr (Or.inr (mem_atoms_eraseBox h'))]
  | .somehow _, h => by simp [eraseBox, truePLL] at h

theorem boxFree_bigAnd :
    ∀ {T : List PLLFormula}, (∀ D ∈ T, boxFree D = true) →
      boxFree (bigAnd T) = true
  | [], _ => rfl
  | [E], h => h E (.head _)
  | E :: F :: l, h => by
      simp only [bigAnd_cons₂, boxFree, Bool.and_eq_true]
      exact ⟨h E (.head _), boxFree_bigAnd fun D hD => h D (.tail _ hD)⟩

theorem boxFree_bigOr :
    ∀ {T : List PLLFormula}, (∀ D ∈ T, boxFree D = true) →
      boxFree (bigOr T) = true
  | [], _ => rfl
  | E :: l, h => by
      simp only [bigOr, boxFree, Bool.and_eq_true]
      exact ⟨h E (.head _), boxFree_bigOr fun D hD => h D (.tail _ hD)⟩

/-- A conjunction of formulas of crank ≤ r, for r ≥ 1, has crank ≤ r (the
empty conjunction is `⊤`, of crank 1). -/
theorem crank_bigAnd_le' {r : Nat} (hr : 1 ≤ r) {T : List PLLFormula}
    (h : ∀ D ∈ T, crank D ≤ r) : crank (bigAnd T) ≤ r := by
  rcases T with _ | ⟨E, T⟩
  · have h₁ : crank (bigAnd ([] : List PLLFormula)) = 1 := rfl
    omega
  · exact crank_bigAnd_le (List.cons_ne_nil _ _) h

end SemUI

namespace SubframeModel

open SemUI (crank bigAnd bigAnd_cons₂ boxFree eraseBox boxFree_eraseBox
  crank_bigAnd_le' crank_bigOr_le atoms_bigAnd atoms_bigOr boxFree_bigAnd
  boxFree_bigOr crank_eraseBox_le mem_atoms_eraseBox frag_reps_exist')

/-! ## Persistence, finite connectives, interderivable formulas -/

/-- **Persistence**: forcing is upward closed along `≤`. -/
theorem force_mono (M : SubframeModel) :
    ∀ (φ : PLLFormula) {u v : M.W}, M.le u v → M.force u φ → M.force v φ
  | .prop _, _, _, h, hu => M.hered h hu
  | .falsePLL, _, _, _, hu => hu
  | .and φ ψ, _, _, h, hu => by
      simp only [force] at hu ⊢
      exact ⟨force_mono M φ h hu.1, force_mono M ψ h hu.2⟩
  | .or φ ψ, _, _, h, hu => by
      simp only [force] at hu ⊢
      exact hu.elim (fun h' => Or.inl (force_mono M φ h h'))
        (fun h' => Or.inr (force_mono M ψ h h'))
  | .ifThen _ _, _, _, h, hu => by
      simp only [force] at hu ⊢
      exact fun w hvw hφ => hu w (M.trans h hvw) hφ
  | .somehow _, _, _, h, hu => by
      simp only [force] at hu ⊢
      exact fun w hvw hwS => hu w (M.trans h hvw) hwS

theorem force_bigAnd_iff (M : SubframeModel) (x : M.W) :
    ∀ T : List PLLFormula, M.force x (bigAnd T) ↔ ∀ D ∈ T, M.force x D
  | [] => by
      constructor
      · intro _ D hD
        exact absurd hD List.not_mem_nil
      · intro _ v _ h
        exact h
  | [E] => by simp
  | E :: F :: l => by
      rw [bigAnd_cons₂]
      show M.force x E ∧ M.force x (bigAnd (F :: l)) ↔ _
      rw [force_bigAnd_iff M x (F :: l)]
      simp

theorem force_bigOr_iff (M : SubframeModel) (x : M.W) :
    ∀ T : List PLLFormula, M.force x (bigOr T) ↔ ∃ D ∈ T, M.force x D
  | [] => by
      constructor
      · intro h
        exact h.elim
      · rintro ⟨D, hD, -⟩
        exact absurd hD List.not_mem_nil
  | E :: l => by
      show M.force x E ∨ M.force x (bigOr l) ↔ _
      rw [force_bigOr_iff M x l]
      simp

/-- Interderivable formulas are forced at the same worlds. -/
theorem force_iff_of_interd {φ D : PLLFormula} (h₁ : Nonempty ([φ] ⊢ D))
    (h₂ : Nonempty ([D] ⊢ φ)) (M : SubframeModel) (x : M.W) :
    M.force x φ ↔ M.force x D := by
  obtain ⟨d₁⟩ := h₁
  obtain ⟨d₂⟩ := h₂
  exact ⟨fun h => SubframeModel.soundness d₁ M x (by simpa using h),
    fun h => SubframeModel.soundness d₂ M x (by simpa using h)⟩

/-! ## Emptying `S` -/

/-- The same model with `S` emptied: every `◯`-formula holds everywhere. -/
def noS (M : SubframeModel) : SubframeModel := { M with S := ∅ }

/-- With `S` empty, a formula and its erasure are forced at the same worlds. -/
theorem noS_force_eraseBox (M : SubframeModel) :
    ∀ (φ : PLLFormula) (x : M.W), M.noS.force x φ ↔ M.noS.force x (eraseBox φ)
  | .prop _, _ => Iff.rfl
  | .falsePLL, _ => Iff.rfl
  | .and φ ψ, x => by
      show M.noS.force x φ ∧ M.noS.force x ψ ↔
        M.noS.force x (eraseBox φ) ∧ M.noS.force x (eraseBox ψ)
      exact and_congr (noS_force_eraseBox M φ x) (noS_force_eraseBox M ψ x)
  | .or φ ψ, x => by
      show M.noS.force x φ ∨ M.noS.force x ψ ↔
        M.noS.force x (eraseBox φ) ∨ M.noS.force x (eraseBox ψ)
      exact or_congr (noS_force_eraseBox M φ x) (noS_force_eraseBox M ψ x)
  | .ifThen φ ψ, x => by
      show (∀ v, M.le x v → M.noS.force v φ → M.noS.force v ψ) ↔
        (∀ v, M.le x v → M.noS.force v (eraseBox φ) →
          M.noS.force v (eraseBox ψ))
      exact forall_congr' fun v => imp_congr_right fun _ =>
        imp_congr (noS_force_eraseBox M φ v) (noS_force_eraseBox M ψ v)
  | .somehow φ, x => by
      show (∀ v, M.le x v → v ∈ (∅ : Set M.W) → M.noS.force v φ) ↔
        (∀ v, M.le x v → False → False)
      exact ⟨fun _ _ _ h => h, fun _ _ _ h => False.elim h⟩

/-- A ◯-free formula does not see `S`. -/
theorem force_noS_of_boxFree (M : SubframeModel) :
    ∀ (φ : PLLFormula), boxFree φ = true → ∀ x : M.W,
      (M.noS.force x φ ↔ M.force x φ)
  | .prop _, _, _ => Iff.rfl
  | .falsePLL, _, _ => Iff.rfl
  | .and φ ψ, h, x => by
      simp only [boxFree, Bool.and_eq_true] at h
      show M.noS.force x φ ∧ M.noS.force x ψ ↔ M.force x φ ∧ M.force x ψ
      exact and_congr (force_noS_of_boxFree M φ h.1 x)
        (force_noS_of_boxFree M ψ h.2 x)
  | .or φ ψ, h, x => by
      simp only [boxFree, Bool.and_eq_true] at h
      show M.noS.force x φ ∨ M.noS.force x ψ ↔ M.force x φ ∨ M.force x ψ
      exact or_congr (force_noS_of_boxFree M φ h.1 x)
        (force_noS_of_boxFree M ψ h.2 x)
  | .ifThen φ ψ, h, x => by
      simp only [boxFree, Bool.and_eq_true] at h
      show (∀ v, M.le x v → M.noS.force v φ → M.noS.force v ψ) ↔
        (∀ v, M.le x v → M.force v φ → M.force v ψ)
      exact forall_congr' fun v => imp_congr_right fun _ =>
        imp_congr (force_noS_of_boxFree M φ h.1 v)
          (force_noS_of_boxFree M ψ h.2 v)
  | .somehow _, h, _ => by simp [boxFree] at h

/-- An erased representative of a ◯-free formula still represents it. -/
theorem force_iff_eraseBox_of_interd {φ D : PLLFormula} (hφ : boxFree φ = true)
    (h₁ : Nonempty ([φ] ⊢ D)) (h₂ : Nonempty ([D] ⊢ φ))
    (M : SubframeModel) (x : M.W) :
    M.force x φ ↔ M.force x (eraseBox D) :=
  (force_noS_of_boxFree M φ hφ x).symm.trans
    ((force_iff_of_interd h₁ h₂ M.noS x).trans
      ((noS_force_eraseBox M D x).trans
        (force_noS_of_boxFree M _ (boxFree_eraseBox D) x)))

/-! ## Agreement -/

variable {M N : SubframeModel}

/-- `w ≡ᵣ w'`: agreement on every formula of crank ≤ r over `V`. -/
def Agree (M N : SubframeModel) (V : Finset String) (r : Nat)
    (w : M.W) (w' : N.W) : Prop :=
  ∀ φ : PLLFormula, crank φ ≤ r → (∀ a ∈ φ.atoms, a ∈ V) →
    (M.force w φ ↔ N.force w' φ)

/-- `w ≡°ᵣ w'`: agreement on every ◯-free formula of crank ≤ r over `V`. -/
def AgreeI (M N : SubframeModel) (V : Finset String) (r : Nat)
    (w : M.W) (w' : N.W) : Prop :=
  ∀ φ : PLLFormula, boxFree φ = true → crank φ ≤ r →
    (∀ a ∈ φ.atoms, a ∈ V) → (M.force w φ ↔ N.force w' φ)

theorem Agree.symm {V : Finset String} {r : Nat} {w : M.W} {w' : N.W}
    (h : Agree M N V r w w') : Agree N M V r w' w :=
  fun φ hc ha => (h φ hc ha).symm

theorem AgreeI.symm {V : Finset String} {r : Nat} {w : M.W} {w' : N.W}
    (h : AgreeI M N V r w w') : AgreeI N M V r w' w :=
  fun φ hb hc ha => (h φ hb hc ha).symm

theorem Agree.mono {V : Finset String} {r s : Nat} (hrs : r ≤ s)
    {w : M.W} {w' : N.W} (h : Agree M N V s w w') : Agree M N V r w w' :=
  fun φ hc ha => h φ (le_trans hc hrs) ha

theorem AgreeI.mono {V : Finset String} {r s : Nat} (hrs : r ≤ s)
    {w : M.W} {w' : N.W} (h : AgreeI M N V s w w') : AgreeI M N V r w w' :=
  fun φ hb hc ha => h φ hb (le_trans hc hrs) ha

/-- Agreement on a representative list is agreement on the fragment. -/
theorem agree_of_reps {V : Finset String} {r : Nat} {L : List PLLFormula}
    (hL : ∀ φ : PLLFormula, crank φ ≤ r → (∀ a ∈ φ.atoms, a ∈ V) →
      ∃ D ∈ L, Nonempty ([φ] ⊢ D) ∧ Nonempty ([D] ⊢ φ))
    {w : M.W} {w' : N.W} (h : ∀ D ∈ L, (M.force w D ↔ N.force w' D)) :
    Agree M N V r w w' := by
  intro φ hc ha
  obtain ⟨D, hD, h₁, h₂⟩ := hL φ hc ha
  exact (force_iff_of_interd h₁ h₂ M w).trans
    ((h D hD).trans (force_iff_of_interd h₁ h₂ N w').symm)

/-- The ◯-free form: agreement on the erased representatives. -/
theorem agreeI_of_reps {V : Finset String} {r : Nat} {L : List PLLFormula}
    (hL : ∀ φ : PLLFormula, crank φ ≤ r → (∀ a ∈ φ.atoms, a ∈ V) →
      ∃ D ∈ L, Nonempty ([φ] ⊢ D) ∧ Nonempty ([D] ⊢ φ))
    {w : M.W} {w' : N.W}
    (h : ∀ D ∈ L.map eraseBox, (M.force w D ↔ N.force w' D)) :
    AgreeI M N V r w w' := by
  intro φ hb hc ha
  obtain ⟨D, hD, h₁, h₂⟩ := hL φ hc ha
  exact (force_iff_eraseBox_of_interd hb h₁ h₂ M w).trans
    ((h _ (List.mem_map_of_mem hD)).trans
      (force_iff_eraseBox_of_interd hb h₁ h₂ N w').symm)

/-! ## Characters -/

open scoped Classical in
/-- The members of `L` forced at `v`. -/
noncomputable def posL (M : SubframeModel) (L : List PLLFormula) (v : M.W) :
    List PLLFormula :=
  L.filter fun D => decide (M.force v D)

open scoped Classical in
/-- The members of `L` not forced at `v`. -/
noncomputable def negL (M : SubframeModel) (L : List PLLFormula) (v : M.W) :
    List PLLFormula :=
  L.filter fun D => !decide (M.force v D)

theorem mem_posL {L : List PLLFormula} {v : M.W} {D : PLLFormula} :
    D ∈ posL M L v ↔ D ∈ L ∧ M.force v D := by
  simp [posL]

theorem mem_negL {L : List PLLFormula} {v : M.W} {D : PLLFormula} :
    D ∈ negL M L v ↔ D ∈ L ∧ ¬ M.force v D := by
  simp [negL]

/-- `θ⁺ ↠ θ⁻`, the `≤`-character of `v` over `L`. -/
noncomputable def charImp (M : SubframeModel) (L : List PLLFormula) (v : M.W) :
    PLLFormula :=
  (bigAnd (posL M L v)).ifThen (bigOr (negL M L v))

/-- `θ⁺ ↠ ◯θ⁻`, the `S`-character of `v` over `L`. -/
noncomputable def charBox (M : SubframeModel) (L : List PLLFormula) (v : M.W) :
    PLLFormula :=
  (bigAnd (posL M L v)).ifThen (bigOr (negL M L v)).somehow

theorem force_pos (M : SubframeModel) (L : List PLLFormula) (v : M.W) :
    M.force v (bigAnd (posL M L v)) :=
  (force_bigAnd_iff M v _).mpr fun _ hD => (mem_posL.mp hD).2

theorem not_force_neg (M : SubframeModel) (L : List PLLFormula) (v : M.W) :
    ¬ M.force v (bigOr (negL M L v)) := by
  intro h
  obtain ⟨D, hD, hf⟩ := (force_bigOr_iff M v _).mp h
  exact (mem_negL.mp hD).2 hf

theorem not_force_charImp {u v : M.W} (huv : M.le u v) (L : List PLLFormula) :
    ¬ M.force u (charImp M L v) := fun h =>
  not_force_neg M L v (h v huv (force_pos M L v))

theorem not_force_charBox {u v : M.W} (huv : M.le u v) (hvS : v ∈ M.S)
    (L : List PLLFormula) : ¬ M.force u (charBox M L v) := fun h =>
  not_force_neg M L v (h v huv (force_pos M L v) v (M.refl v) hvS)

/-- A world forcing `θ⁺` and refuting `θ⁻` has the `L`-type of `v`. -/
theorem agree_of_char {L : List PLLFormula} {v : M.W} {v' : N.W}
    (hp : N.force v' (bigAnd (posL M L v)))
    (hn : ¬ N.force v' (bigOr (negL M L v))) :
    ∀ D ∈ L, (M.force v D ↔ N.force v' D) := by
  intro D hD
  by_cases hv : M.force v D
  · exact ⟨fun _ => (force_bigAnd_iff N v' _).mp hp D (mem_posL.mpr ⟨hD, hv⟩),
      fun _ => hv⟩
  · exact ⟨fun h => absurd h hv, fun h =>
      absurd ((force_bigOr_iff N v' _).mpr ⟨D, mem_negL.mpr ⟨hD, hv⟩, h⟩) hn⟩

theorem exists_of_not_force_charImp {L : List PLLFormula} {v : M.W} {u' : N.W}
    (h : ¬ N.force u' (charImp M L v)) :
    ∃ v', N.le u' v' ∧ ∀ D ∈ L, (M.force v D ↔ N.force v' D) := by
  by_contra hne
  apply h
  show ∀ x, N.le u' x → N.force x (bigAnd (posL M L v)) →
    N.force x (bigOr (negL M L v))
  intro x hx hp
  by_contra hn
  exact hne ⟨x, hx, agree_of_char hp hn⟩

theorem exists_of_not_force_charBox {L : List PLLFormula} {v : M.W} {u' : N.W}
    (h : ¬ N.force u' (charBox M L v)) :
    ∃ v', N.le u' v' ∧ v' ∈ N.S ∧ ∀ D ∈ L, (M.force v D ↔ N.force v' D) := by
  by_contra hne
  apply h
  show ∀ x, N.le u' x → N.force x (bigAnd (posL M L v)) →
    ∀ y, N.le x y → y ∈ N.S → N.force y (bigOr (negL M L v))
  intro x hx hp y hy hyS
  by_contra hn
  exact hne ⟨y, N.trans hx hy, hyS, agree_of_char (force_mono N _ hy hp) hn⟩

theorem crank_charImp_le {L : List PLLFormula} {r : Nat} (hr : 1 ≤ r)
    (hL : ∀ D ∈ L, crank D ≤ r) (v : M.W) : crank (charImp M L v) ≤ r + 1 := by
  have h₁ : crank (bigAnd (posL M L v)) ≤ r :=
    crank_bigAnd_le' hr fun D hD => hL D (mem_posL.mp hD).1
  have h₂ : crank (bigOr (negL M L v)) ≤ r :=
    crank_bigOr_le fun D hD => hL D (mem_negL.mp hD).1
  simp only [charImp, crank]
  omega

theorem crank_charBox_le {L : List PLLFormula} {r : Nat} (hr : 1 ≤ r)
    (hL : ∀ D ∈ L, crank D ≤ r) (v : M.W) : crank (charBox M L v) ≤ r + 3 := by
  have h₁ : crank (bigAnd (posL M L v)) ≤ r :=
    crank_bigAnd_le' hr fun D hD => hL D (mem_posL.mp hD).1
  have h₂ : crank (bigOr (negL M L v)) ≤ r :=
    crank_bigOr_le fun D hD => hL D (mem_negL.mp hD).1
  simp only [charBox, crank]
  omega

theorem atoms_charImp {L : List PLLFormula} {Q : String → Prop}
    (hL : ∀ D ∈ L, ∀ a ∈ D.atoms, Q a) (v : M.W) :
    ∀ a ∈ (charImp M L v).atoms, Q a := by
  intro a ha
  rcases mem_atoms_ifThen.mp ha with h | h
  · exact atoms_bigAnd (fun D hD => hL D (mem_posL.mp hD).1) a h
  · exact atoms_bigOr (fun D hD => hL D (mem_negL.mp hD).1) a h

theorem atoms_charBox {L : List PLLFormula} {Q : String → Prop}
    (hL : ∀ D ∈ L, ∀ a ∈ D.atoms, Q a) (v : M.W) :
    ∀ a ∈ (charBox M L v).atoms, Q a := by
  intro a ha
  rcases mem_atoms_ifThen.mp ha with h | h
  · exact atoms_bigAnd (fun D hD => hL D (mem_posL.mp hD).1) a h
  · exact atoms_bigOr (fun D hD => hL D (mem_negL.mp hD).1) a h

theorem boxFree_charImp {L : List PLLFormula} (hL : ∀ D ∈ L, boxFree D = true)
    (v : M.W) : boxFree (charImp M L v) = true := by
  simp only [charImp, boxFree, Bool.and_eq_true]
  exact ⟨boxFree_bigAnd fun D hD => hL D (mem_posL.mp hD).1,
    boxFree_bigOr fun D hD => hL D (mem_negL.mp hD).1⟩

/-! ## The steps from agreement -/

/-- `≤`-forth from agreement. -/
theorem Agree.forth {V : Finset String} {r : Nat} (hr : 1 ≤ r)
    {u : M.W} {u' : N.W} (h : Agree M N V (r+1) u u') {v : M.W}
    (huv : M.le u v) : ∃ v', N.le u' v' ∧ Agree M N V r v v' := by
  obtain ⟨L, hLb, hL⟩ := frag_reps_exist' V r
  have hc := crank_charImp_le (M := M) hr (fun D hD => (hLb D hD).1) v
  have ha := atoms_charImp (M := M) (fun D hD => (hLb D hD).2) v
  have hN : ¬ N.force u' (charImp M L v) := fun hN' =>
    not_force_charImp huv L ((h _ hc ha).mpr hN')
  obtain ⟨v', hle, hag⟩ := exists_of_not_force_charImp hN
  exact ⟨v', hle, agree_of_reps hL hag⟩

/-- `≤`-back from agreement. -/
theorem Agree.back {V : Finset String} {r : Nat} (hr : 1 ≤ r)
    {u : M.W} {u' : N.W} (h : Agree M N V (r+1) u u') {v' : N.W}
    (hv : N.le u' v') : ∃ v, M.le u v ∧ Agree M N V r v v' := by
  obtain ⟨v, hle, hag⟩ := h.symm.forth hr hv
  exact ⟨v, hle, hag.symm⟩

/-- `S`-forth from agreement. -/
theorem Agree.sforth {V : Finset String} {r : Nat} (hr : 1 ≤ r)
    {u : M.W} {u' : N.W} (h : Agree M N V (r+3) u u') {v : M.W}
    (huv : M.le u v) (hvS : v ∈ M.S) :
    ∃ v', N.le u' v' ∧ v' ∈ N.S ∧ Agree M N V r v v' := by
  obtain ⟨L, hLb, hL⟩ := frag_reps_exist' V r
  have hc := crank_charBox_le (M := M) hr (fun D hD => (hLb D hD).1) v
  have ha := atoms_charBox (M := M) (fun D hD => (hLb D hD).2) v
  have hN : ¬ N.force u' (charBox M L v) := fun hN' =>
    not_force_charBox huv hvS L ((h _ hc ha).mpr hN')
  obtain ⟨v', hle, hS, hag⟩ := exists_of_not_force_charBox hN
  exact ⟨v', hle, hS, agree_of_reps hL hag⟩

/-- `S`-back from agreement. -/
theorem Agree.sback {V : Finset String} {r : Nat} (hr : 1 ≤ r)
    {u : M.W} {u' : N.W} (h : Agree M N V (r+3) u u') {v' : N.W}
    (hv : N.le u' v') (hvS : v' ∈ N.S) :
    ∃ v, M.le u v ∧ v ∈ M.S ∧ Agree M N V r v v' := by
  obtain ⟨v, hle, hS, hag⟩ := h.symm.sforth hr hv hvS
  exact ⟨v, hle, hS, hag.symm⟩

/-- Erased representatives keep the crank and atom bounds, and are ◯-free. -/
theorem erase_reps {V : Finset String} {r : Nat} {L : List PLLFormula}
    (hL : ∀ D ∈ L, crank D ≤ r ∧ ∀ a ∈ D.atoms, a ∈ V) :
    ∀ D ∈ L.map eraseBox, (crank D ≤ r ∧ ∀ a ∈ D.atoms, a ∈ V) ∧ boxFree D = true := by
  intro D hD
  obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
  exact ⟨⟨le_trans (crank_eraseBox_le E) (hL E hE).1,
    fun a ha => (hL E hE).2 a (mem_atoms_eraseBox ha)⟩, boxFree_eraseBox E⟩

/-- `≤`-forth from ◯-free agreement. -/
theorem AgreeI.forth {V : Finset String} {r : Nat} (hr : 1 ≤ r)
    {u : M.W} {u' : N.W} (h : AgreeI M N V (r+1) u u') {v : M.W}
    (huv : M.le u v) : ∃ v', N.le u' v' ∧ AgreeI M N V r v v' := by
  obtain ⟨L, hLb, hL⟩ := frag_reps_exist' V r
  have hLe := fun D hD => (erase_reps hLb D hD).1
  have hLf := fun D hD => (erase_reps hLb D hD).2
  have hc := crank_charImp_le (M := M) hr (fun D hD => (hLe D hD).1) v
  have ha := atoms_charImp (M := M) (fun D hD => (hLe D hD).2) v
  have hb := boxFree_charImp (M := M) hLf v
  have hN : ¬ N.force u' (charImp M (L.map eraseBox) v) := fun hN' =>
    not_force_charImp huv _ ((h _ hb hc ha).mpr hN')
  obtain ⟨v', hle, hag⟩ := exists_of_not_force_charImp hN
  exact ⟨v', hle, agreeI_of_reps hL hag⟩

/-- `≤`-back from ◯-free agreement. -/
theorem AgreeI.back {V : Finset String} {r : Nat} (hr : 1 ≤ r)
    {u : M.W} {u' : N.W} (h : AgreeI M N V (r+1) u u') {v' : N.W}
    (hv : N.le u' v') : ∃ v, M.le u v ∧ AgreeI M N V r v v' := by
  obtain ⟨v, hle, hag⟩ := h.symm.forth hr hv
  exact ⟨v, hle, hag.symm⟩

/-! ## Layered bisimulations -/

/-- A layered bisimulation of subframe models over the atoms `A`, without
the `S`-clauses: the ◯-free (IPC) notion. -/
structure LayeredBisimI (A : String → Prop) (M N : SubframeModel) where
  Z : Nat → M.W → N.W → Prop
  mono : ∀ {n w w'}, Z (n+1) w w' → Z n w w'
  atoms : ∀ {n w w'}, Z n w w' → ∀ a, A a → (w ∈ M.V a ↔ w' ∈ N.V a)
  forth : ∀ {n w w'}, Z (n+1) w w' → ∀ {v}, M.le w v →
    ∃ v', N.le w' v' ∧ Z n v v'
  back : ∀ {n w w'}, Z (n+1) w w' → ∀ {v'}, N.le w' v' →
    ∃ v, M.le w v ∧ Z n v v'

/-- A layered bisimulation of subframe models over the atoms `A`: the
◯-free clauses, and `S`-forth/back along `≤ ∩ S`. -/
structure LayeredBisim (A : String → Prop) (M N : SubframeModel)
    extends LayeredBisimI A M N where
  sforth : ∀ {n w w'}, Z (n+1) w w' → ∀ {v}, M.le w v → v ∈ M.S →
    ∃ v', N.le w' v' ∧ v' ∈ N.S ∧ Z n v v'
  sback : ∀ {n w w'}, Z (n+1) w w' → ∀ {v'}, N.le w' v' → v' ∈ N.S →
    ∃ v, M.le w v ∧ v ∈ M.S ∧ Z n v v'

/-- **Rank preservation**: worlds linked at level n agree on the formulas of
crank ≤ n over `A`. -/
theorem LayeredBisim.force_iff {A : String → Prop} (B : LayeredBisim A M N) :
    ∀ (φ : PLLFormula) {n : Nat} {w : M.W} {w' : N.W}, B.Z n w w' →
      crank φ ≤ n → (∀ a ∈ φ.atoms, A a) → (M.force w φ ↔ N.force w' φ)
  | .prop a, _, _, _, hZ, _, ha => B.atoms hZ a (ha a (by simp))
  | .falsePLL, _, _, _, _, _, _ => Iff.rfl
  | .and φ ψ, n, w, w', hZ, hc, ha => by
      have hcφ : crank φ ≤ n := by simp only [crank] at hc; omega
      have hcψ : crank ψ ≤ n := by simp only [crank] at hc; omega
      exact and_congr
        (LayeredBisim.force_iff B φ hZ hcφ fun a h =>
          ha a (mem_atoms_and.mpr (Or.inl h)))
        (LayeredBisim.force_iff B ψ hZ hcψ fun a h =>
          ha a (mem_atoms_and.mpr (Or.inr h)))
  | .or φ ψ, n, w, w', hZ, hc, ha => by
      have hcφ : crank φ ≤ n := by simp only [crank] at hc; omega
      have hcψ : crank ψ ≤ n := by simp only [crank] at hc; omega
      exact or_congr
        (LayeredBisim.force_iff B φ hZ hcφ fun a h =>
          ha a (mem_atoms_or.mpr (Or.inl h)))
        (LayeredBisim.force_iff B ψ hZ hcψ fun a h =>
          ha a (mem_atoms_or.mpr (Or.inr h)))
  | .ifThen φ ψ, n, w, w', hZ, hc, ha => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
        ⟨n - 1, by simp only [crank] at hc; omega⟩
      have hcφ : crank φ ≤ m := by simp only [crank] at hc; omega
      have hcψ : crank ψ ≤ m := by simp only [crank] at hc; omega
      have haφ : ∀ a ∈ φ.atoms, A a := fun a h =>
        ha a (mem_atoms_ifThen.mpr (Or.inl h))
      have haψ : ∀ a ∈ ψ.atoms, A a := fun a h =>
        ha a (mem_atoms_ifThen.mpr (Or.inr h))
      constructor
      · intro hM v' hle hφ
        obtain ⟨v, hv, hZ'⟩ := B.back hZ hle
        exact (LayeredBisim.force_iff B ψ hZ' hcψ haψ).mp
          (hM v hv ((LayeredBisim.force_iff B φ hZ' hcφ haφ).mpr hφ))
      · intro hN v hle hφ
        obtain ⟨v', hv', hZ'⟩ := B.forth hZ hle
        exact (LayeredBisim.force_iff B ψ hZ' hcψ haψ).mpr
          (hN v' hv' ((LayeredBisim.force_iff B φ hZ' hcφ haφ).mp hφ))
  | .somehow φ, n, w, w', hZ, hc, ha => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
        ⟨n - 1, by simp only [crank] at hc; omega⟩
      have hcφ : crank φ ≤ m := by simp only [crank] at hc; omega
      constructor
      · intro hM v' hle hS
        obtain ⟨v, hv, hvS, hZ'⟩ := B.sback hZ hle hS
        exact (LayeredBisim.force_iff B φ hZ' hcφ ha).mp (hM v hv hvS)
      · intro hN v hle hS
        obtain ⟨v', hv', hv'S, hZ'⟩ := B.sforth hZ hle hS
        exact (LayeredBisim.force_iff B φ hZ' hcφ ha).mpr (hN v' hv' hv'S)

/-- A `≤`-bisimulation is a layered bisimulation between the two models with `S`
emptied, where the `S`-clauses hold vacuously. -/
def LayeredBisimI.noS {A : String → Prop} (B : LayeredBisimI A M N) :
    LayeredBisim A M.noS N.noS where
  Z := B.Z
  mono := B.mono
  atoms := B.atoms
  forth := B.forth
  back := B.back
  sforth := fun _ _ _ hS => False.elim hS
  sback := fun _ _ _ hS => False.elim hS

/-- **Rank preservation, ◯-free**: worlds linked at level n agree on the
◯-free formulas of crank ≤ n over `A`.  A corollary of the full statement:
emptying `S` changes no ◯-free formula. -/
theorem LayeredBisimI.force_iff {A : String → Prop} (B : LayeredBisimI A M N) :
    ∀ (φ : PLLFormula) {n : Nat} {w : M.W} {w' : N.W}, B.Z n w w' →
      boxFree φ = true → crank φ ≤ n → (∀ a ∈ φ.atoms, A a) →
      (M.force w φ ↔ N.force w' φ) := fun φ _ _ _ hZ hb hc ha =>
  (force_noS_of_boxFree M φ hb _).symm.trans
    ((LayeredBisim.force_iff B.noS φ hZ hc ha).trans (force_noS_of_boxFree N φ hb _))

/-! ## The agreement bisimulations -/

theorem atoms_prop_sub {V : Finset String} {a : String} (ha : a ∈ V) :
    ∀ b ∈ (PLLFormula.prop a).atoms, b ∈ V := by
  intro b hb
  simp only [atoms_prop, Finset.mem_singleton] at hb
  rw [hb]
  exact ha

/-- ◯-free agreement as a layered bisimulation: level n is `≡°_{n+1}`. -/
def agreeBisimI (V : Finset String) (M N : SubframeModel) :
    LayeredBisimI (· ∈ V) M N where
  Z n w w' := AgreeI M N V (n+1) w w'
  mono h := h.mono (Nat.le_succ _)
  atoms h a ha := h (.prop a) rfl (Nat.zero_le _) (atoms_prop_sub ha)
  forth h _ huv := h.forth (Nat.succ_pos _) huv
  back h _ hv := h.back (Nat.succ_pos _) hv

/-- Agreement as a layered bisimulation: level n is `≡_{3n+1}`. -/
def agreeBisim (V : Finset String) (M N : SubframeModel) :
    LayeredBisim (· ∈ V) M N where
  Z n w w' := Agree M N V (3*n+1) w w'
  mono h := h.mono (by omega)
  atoms h a ha := h (.prop a) (Nat.zero_le _) (atoms_prop_sub ha)
  forth h _ huv := (h.mono (by omega)).forth (by omega) huv
  back h _ hv := (h.mono (by omega)).back (by omega) hv
  sforth h _ huv hvS := (h.mono (by omega)).sforth (by omega) huv hvS
  sback h _ hv hvS := (h.mono (by omega)).sback (by omega) hv hvS

/-! ## Step 2 -/

/-- **Step 2, ◯-free instance (IPC)**:
`w ≡°_{n+1} w' ⟹ w ⇄°ₙ w'`. -/
theorem layeredI_of_agree {V : Finset String} {n : Nat} {w : M.W} {w' : N.W}
    (h : AgreeI M N V (n+1) w w') :
    ∃ B : LayeredBisimI (· ∈ V) M N, B.Z n w w' :=
  ⟨agreeBisimI V M N, h⟩

/-- The converse, ◯-free: `w ⇄°ₙ w' ⟹ w ≡°ₙ w'`. -/
theorem agreeI_of_layeredI {V : Finset String} {n : Nat} {w : M.W} {w' : N.W}
    (B : LayeredBisimI (· ∈ V) M N) (h : B.Z n w w') : AgreeI M N V n w w' :=
  fun φ hb hc ha => B.force_iff φ h hb hc ha

/-- **Step 2 for PLL in the subframe semantics**:
`w ≡_{3n+1} w' ⟹ w ⇄ₙ w'`. -/
theorem layered_of_agree {V : Finset String} {n : Nat} {w : M.W} {w' : N.W}
    (h : Agree M N V (3*n+1) w w') :
    ∃ B : LayeredBisim (· ∈ V) M N, B.Z n w w' :=
  ⟨agreeBisim V M N, h⟩

/-- The converse: `w ⇄ₙ w' ⟹ w ≡ₙ w'`. -/
theorem agree_of_layered {V : Finset String} {n : Nat} {w : M.W} {w' : N.W}
    (B : LayeredBisim (· ∈ V) M N) (h : B.Z n w w') : Agree M N V n w w' :=
  fun φ hc ha => B.force_iff φ h hc ha

/-! ## The designed cell for the `S`-clauses -/

/-- One point, in `S` or not. -/
def pt (inS : Prop) : SubframeModel where
  W := Unit
  le _ _ := True
  S := {_u | inS}
  V _ := ∅
  refl _ := trivial
  trans _ _ := trivial
  hered _ h := h

/-- The `≤`-bisimulation linking the two points at every level. -/
def ptBisimI : LayeredBisimI (fun _ => True) (pt True) (pt False) where
  Z _ _ _ := True
  mono _ := trivial
  atoms _ _ _ := Iff.rfl
  forth _ _ _ := ⟨(), trivial, trivial⟩
  back _ _ _ := ⟨(), trivial, trivial⟩

/-- **The `S`-clauses are needed**: the two points are linked at every level
by a `≤`-bisimulation, yet `◯⊥` (crank 2) separates them. -/
theorem S_clause_needed :
    (∀ n, ptBisimI.Z n () ()) ∧
      ¬ ((pt True).force () (◯⊥) ↔ (pt False).force () (◯⊥)) := by
  refine ⟨fun _ => trivial, fun h => ?_⟩
  have hF : (pt False).force () (.somehow .falsePLL) :=
    fun _ _ hS => False.elim hS
  exact h.mpr hF () trivial trivial

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SubframeModel.layered_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms layered_of_agree

/--
info: 'PLLND.SubframeModel.agree_of_layered' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms agree_of_layered

/--
info: 'PLLND.SubframeModel.layeredI_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms layeredI_of_agree

/--
info: 'PLLND.SubframeModel.agreeI_of_layeredI' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms agreeI_of_layeredI

/--
info: 'PLLND.SubframeModel.S_clause_needed' does not depend on any axioms
-/
#guard_msgs in
#print axioms S_clause_needed

end SubframeModel

end PLLND
