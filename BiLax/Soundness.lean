/-
BiLax round 1 — soundness of `BiLaxND` over `BiModel` (local
consequence), with pinned axiom audits.
-/
import BiLax.Hilbert

namespace BiLax

/-- Local bi-lax consequence. -/
def BiConsequence (Γ : List BiForm) (φ : BiForm) : Prop :=
  ∀ (M : BiModel) (w : M.W), (∀ ψ ∈ Γ, bforce M w ψ) → bforce M w φ

/-- **Soundness of `BiLaxND`.**  The forward rules are PLL's argument
over `bforce`; exfalso uses fragment-relative fallibility; the
retrospective rules use the four semantic theorems of
BiLax/Frames.lean. -/
theorem biLaxND_sound {Γ : List BiForm} {φ : BiForm}
    (p : BiLaxND Γ φ) : BiConsequence Γ φ := by
  induction p with
  | iden h => exact fun M w hΓ => hΓ _ h
  | falsoElim φ hf _ ih =>
      exact fun M w hΓ => bforce_of_fallible_forward M hf (ih M w hΓ)
  | impIntro _ ih =>
      intro M w hΓ v hwv hv
      refine ih M v (fun χ hχ => ?_)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact hv
      · exact bforce_hered M hwv (hΓ χ hχ)
  | impElim _ _ ih₁ ih₂ =>
      intro M w hΓ
      exact ih₁ M w hΓ w (M.refl_i w) (ih₂ M w hΓ)
  | andIntro _ _ ih₁ ih₂ =>
      exact fun M w hΓ => ⟨ih₁ M w hΓ, ih₂ M w hΓ⟩
  | andElim1 _ ih => exact fun M w hΓ => (ih M w hΓ).1
  | andElim2 _ ih => exact fun M w hΓ => (ih M w hΓ).2
  | orIntro1 _ ih => exact fun M w hΓ => .inl (ih M w hΓ)
  | orIntro2 _ ih => exact fun M w hΓ => .inr (ih M w hΓ)
  | orElim _ _ _ ih₀ ih₁ ih₂ =>
      intro M w hΓ
      rcases ih₀ M w hΓ with h | h
      · refine ih₁ M w (fun χ hχ => ?_)
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact h
        · exact hΓ χ hχ
      · refine ih₂ M w (fun χ hχ => ?_)
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact h
        · exact hΓ χ hχ
  | laxIntro _ ih =>
      intro M w hΓ v hwv
      exact ⟨v, M.refl_m v, bforce_hered M hwv (ih M w hΓ)⟩
  | @laxElim Γ φ ψ _ _ ih₁ ih₂ =>
      intro M w hΓ v hwv
      obtain ⟨u, hvu, hφ⟩ := ih₁ M w hΓ v hwv
      have hΓu : ∀ χ ∈ φ :: Γ, bforce M u χ := by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact hφ
        · exact bforce_hered M
            (M.trans_i hwv (M.sub_mi hvu)) (hΓ χ hχ)
      obtain ⟨y, huy, hψ⟩ := ih₂ M u hΓu u (M.refl_i u)
      exact ⟨y, M.trans_m hvu huy, hψ⟩
  | coimpDisj φ ψ =>
      intro M w _ v hwv hφ
      classical
      by_cases hψ : bforce M v ψ
      · exact .inl hψ
      · exact .inr ⟨v, M.refl_i v, hφ, hψ⟩
  | @coimpMin φ ψ χ _ ih =>
      rintro M w _ v hwv ⟨u, huv, hφ, hnψ⟩
      rcases ih M u (by simp) u (M.refl_i u) hφ with h | h
      · exact absurd h hnψ
      · exact bforce_hered M huv h
  | @coimpMax φ ψ χ _ ih =>
      intro M w _ v hwv hφ
      classical
      by_cases hψ : bforce M v ψ
      · exact .inl hψ
      · exact .inr (ih M v (by simp) v (M.refl_i v)
          ⟨v, M.refl_i v, hφ, hψ⟩)
  | colaxMono _ ih =>
      rintro M w _ v hwv ⟨u, huv, hφ⟩
      exact ⟨u, huv, ih M u (by simp) u (M.refl_i u) hφ⟩
  | adjL _ ih =>
      intro M w _ v hwv hφ u hvu
      exact ⟨u, M.refl_m u,
        ih M u (by simp) u (M.refl_i u)
          ⟨u, M.refl_m u, bforce_hered M hvu hφ⟩⟩
  | adjR _ ih =>
      rintro M w _ v hwv ⟨u, huv, hφ⟩
      obtain ⟨t, hut, hall⟩ := M.counit_law huv
      obtain ⟨y, hty, hy⟩ :=
        ih M u (by simp) u (M.refl_i u) hφ t hut
      exact bforce_hered M (hall y hty) hy

/-- PLL derivations embed soundly: `LaxND Γ φ` gives bi-lax
consequence of the embedded sequent. -/
theorem emb_sound {Γ : List PLLFormula} {φ : PLLFormula}
    (p : PLLND.LaxND Γ φ) :
    BiConsequence (Γ.map emb) (emb φ) := by
  intro M w hΓ
  refine (bforce_emb M φ w).mpr
    (PLLND.soundness p M.toConstraintModel w ?_)
  intro ψ hψ
  exact (bforce_emb M ψ w).mp (hΓ (emb ψ) (List.mem_map_of_mem hψ))

/-! ## Pins -/

/--
info: 'BiLax.biLaxND_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms biLaxND_sound

/--
info: 'BiLax.emb_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms emb_sound

end BiLax
