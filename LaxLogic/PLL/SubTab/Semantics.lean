import LaxLogic.PLL.SemUI.SubframeLayered
import FRJ.Gbu.W.LaxND
import Meta.Audit

/-!
# Subframe models without choice: soundness, and completeness for finite ones

The choice-free semantics of subframe models (the models are defined in
`LaxLogic/PLL/Semantics/Subframe.lean`).

The classical `SubframeModel.derivable_iff_valid` depends on `Classical.choice`
in both directions: soundness through a case split on `S` in the translation
to constraint models (`toConstraint_force`), completeness through the
classical finite model property (`not_provable_iff_exists_finite_countermodel`)
and the existence of `Rₘ`-final successors on a `Finite` type.  This file
proves both directions again:

* `soundness`: by induction on the `LaxND` derivation, for every subframe
  model.
* `completeness`: for the finite subframe models with decidable order, `S`
  and valuation (`FinDec`).  A non-theorem `θ` has an FRJW disproof
  (`FRJ.Gbu.W.provable_or_disprovable`, `[propext, Quot.sound]`), whose
  extracted model refutes `θ` at its root (`FRJ.W.modR_countermodel`).  That
  model is a finite rooted poset with fallible worlds and a modal relation
  `Rm ⊆ ≤`; deleting the fallible worlds and taking `S` to be the
  `Rm`-maximal worlds gives a subframe model with the same forcing
  (`ofKripke_force`).  Every world has an `Rm`-maximal `Rm`-successor
  (`exists_rmMax`), by descent on the number of `Rm`-successors.

In a `FinDec` model forcing is decidable (`decForce`), which is what replaces
excluded middle in `exists_of_not_force_imp` and `exists_of_not_force_box`.
-/

open PLLFormula

namespace PLLND
namespace SubframeModel
namespace CF

/-! ## Finite decidable models -/

/-- A finite subframe model with decidable order, `S` and valuation: a list
of all its worlds and three decision procedures. -/
class FinDec (M : SubframeModel) where
  elems : List M.W
  complete : ∀ w, w ∈ elems
  decLe : ∀ a b, Decidable (M.le a b)
  decS : ∀ a, Decidable (a ∈ M.S)
  decV : ∀ (x : String) a, Decidable (a ∈ M.V x)

variable {M : SubframeModel}

instance [FinDec M] (a b : M.W) : Decidable (M.le a b) := FinDec.decLe a b
instance [FinDec M] (a : M.W) : Decidable (a ∈ M.S) := FinDec.decS a
instance [FinDec M] (x : String) (a : M.W) : Decidable (a ∈ M.V x) := FinDec.decV x a

/-- **Forcing is decidable in a finite decidable model.** -/
instance decForce (M : SubframeModel) [FinDec M] :
    ∀ (w : M.W) (φ : PLLFormula), Decidable (M.force w φ)
  | w, .prop a => FinDec.decV a w
  | _, .falsePLL => isFalse id
  | w, .and φ ψ =>
      have := decForce M w φ
      have := decForce M w ψ
      inferInstanceAs (Decidable (_ ∧ _))
  | w, .or φ ψ =>
      have := decForce M w φ
      have := decForce M w ψ
      inferInstanceAs (Decidable (_ ∨ _))
  | w, .ifThen φ ψ =>
      have : ∀ v, Decidable (M.force v φ) := fun v => decForce M v φ
      have : ∀ v, Decidable (M.force v ψ) := fun v => decForce M v ψ
      decidable_of_iff (∀ v ∈ FinDec.elems (M := M), M.le w v → M.force v φ → M.force v ψ)
        ⟨fun h v => h v (FinDec.complete v), fun h v _ => h v⟩
  | w, .somehow φ =>
      have : ∀ v, Decidable (M.force v φ) := fun v => decForce M v φ
      decidable_of_iff (∀ v ∈ FinDec.elems (M := M), M.le w v → v ∈ M.S → M.force v φ)
        ⟨fun h v => h v (FinDec.complete v), fun h v _ => h v⟩

/-- In a finite decidable model a bounded universal that fails has a
counterexample. -/
theorem exists_of_not_forall_le [FinDec M] {w : M.W} {P : M.W → Prop}
    [DecidablePred P] (h : ¬ ∀ v, M.le w v → P v) : ∃ v, M.le w v ∧ ¬ P v :=
  match List.decidableBEx (fun v => M.le w v ∧ ¬ P v) (FinDec.elems (M := M)) with
  | isTrue hex =>
      let ⟨v, _, hv⟩ := hex
      ⟨v, hv⟩
  | isFalse hno =>
      absurd (fun v hv => Decidable.byContradiction fun hn =>
        hno ⟨v, FinDec.complete v, hv, hn⟩) h

/-- A world refuting `φ ↠ ψ` has a successor forcing `φ` and refuting `ψ`. -/
theorem exists_of_not_force_imp [FinDec M] {k : M.W} {φ ψ : PLLFormula}
    (hn : ¬ M.force k (φ ↠ ψ)) :
    ∃ k₂, M.le k k₂ ∧ M.force k₂ φ ∧ ¬ M.force k₂ ψ := by
  have : ¬ ∀ v, M.le k v → (M.force v φ → M.force v ψ) := hn
  obtain ⟨v, hv, hn'⟩ := exists_of_not_forall_le this
  refine ⟨v, hv, ?_, fun h => hn' fun _ => h⟩
  exact Decidable.byContradiction fun hφ => hn' fun h => absurd h hφ

/-- A world refuting `◯ξ` has an `S`-point above it refuting `ξ`. -/
theorem exists_of_not_force_box [FinDec M] {k : M.W} {ξ : PLLFormula}
    (hn : ¬ M.force k (◯ξ)) :
    ∃ s, M.le k s ∧ s ∈ M.S ∧ ¬ M.force s ξ := by
  have : ¬ ∀ v, M.le k v → (v ∈ M.S → M.force v ξ) := hn
  obtain ⟨v, hv, hn'⟩ := exists_of_not_forall_le this
  refine ⟨v, hv, ?_, fun h => hn' fun _ => h⟩
  exact Decidable.byContradiction fun hS => hn' fun h => absurd h hS

/-! ## Soundness -/

/-- **Soundness for subframe models**, by induction on the derivation. -/
theorem soundness {Γ : List PLLFormula} {φ : PLLFormula} (p : Γ ⊢ φ) :
    ∀ (M : SubframeModel) (x : M.W), (∀ χ ∈ Γ, M.force x χ) → M.force x φ := by
  induction p with
  | iden h => exact fun M x hΓ => hΓ _ h
  | falsoElim _ _ ih => exact fun M x hΓ => False.elim (ih M x hΓ)
  | impIntro _ ih =>
      intro M x hΓ v hxv hv
      exact ih M v fun χ hχ => by
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact hv
        · exact force_mono M χ hxv (hΓ χ hχ)
  | impElim _ _ ih₁ ih₂ => exact fun M x hΓ => ih₁ M x hΓ x (M.refl x) (ih₂ M x hΓ)
  | andIntro _ _ ih₁ ih₂ => exact fun M x hΓ => ⟨ih₁ M x hΓ, ih₂ M x hΓ⟩
  | andElim1 _ ih => exact fun M x hΓ => (ih M x hΓ).1
  | andElim2 _ ih => exact fun M x hΓ => (ih M x hΓ).2
  | orIntro1 _ ih => exact fun M x hΓ => .inl (ih M x hΓ)
  | orIntro2 _ ih => exact fun M x hΓ => .inr (ih M x hΓ)
  | orElim _ _ _ ih₀ ih₁ ih₂ =>
      intro M x hΓ
      rcases ih₀ M x hΓ with hφ | hψ
      · exact ih₁ M x fun χ hχ => by
          rcases List.mem_cons.mp hχ with rfl | hχ
          · exact hφ
          · exact hΓ χ hχ
      · exact ih₂ M x fun χ hχ => by
          rcases List.mem_cons.mp hχ with rfl | hχ
          · exact hψ
          · exact hΓ χ hχ
  | laxIntro _ ih =>
      intro M x hΓ v hxv _
      exact force_mono M _ hxv (ih M x hΓ)
  | laxElim _ _ ih₁ ih₂ =>
      intro M x hΓ v hxv hvS
      have hv := ih₁ M x hΓ v hxv hvS
      exact ih₂ M v (fun χ hχ => by
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact hv
        · exact force_mono M χ hxv (hΓ χ hχ)) v (M.refl v) hvS

/-- Soundness for a one-formula context. -/
theorem soundness₁ {φ ψ : PLLFormula} (p : [φ] ⊢ ψ) (M : SubframeModel) (x : M.W)
    (h : M.force x φ) : M.force x ψ :=
  soundness p M x fun χ hχ => by
    rw [List.mem_singleton.mp hχ]
    exact h

/-- Soundness for an implication derived from no hypotheses. -/
theorem soundness_imp {φ ψ : PLLFormula} (p : [] ⊢ φ ↠ ψ) (M : SubframeModel)
    (x : M.W) (h : M.force x φ) : M.force x ψ :=
  soundness p M x (fun _ hχ => absurd hχ List.not_mem_nil) x (M.refl x) h

/-! ## FRJ models as subframe models -/

/-- **Every world of an FRJ model has an `Rm`-maximal `Rm`-successor**, or
it is itself `Rm`-maximal: a proper `Rm`-successor has strictly fewer
`Rm`-successors, by antisymmetry of `≤ ⊇ Rm`. -/
theorem rmMax_or_step (K : FRJ.Kripke) (v : K.W) :
    (∀ u, K.Rm v u → u = v) ∨
      ∃ u, K.Rm v u ∧ K.elems.countP (fun w => decide (K.Rm u w)) <
        K.elems.countP (fun w => decide (K.Rm v w)) :=
  match List.decidableBEx (fun u => K.Rm v u ∧ u ≠ v) K.elems with
  | isTrue hex =>
      let ⟨u, _, hvu, huv⟩ := hex
      .inr ⟨u, hvu, FRJ.countP_lt_countP
        (fun _ _ h => decide_eq_true (K.rm_trans hvu (of_decide_eq_true h)))
        (K.complete v) (decide_eq_true (K.rm_refl v))
        (decide_eq_false fun h => huv (K.le_antisymm (K.sub_mi h) (K.sub_mi hvu)))⟩
  | isFalse hno =>
      .inl fun u hvu => Decidable.byContradiction fun h => hno ⟨u, K.complete u, hvu, h⟩

theorem exists_rmMax_aux (K : FRJ.Kripke) (n : Nat) :
    ∀ v : K.W, K.elems.countP (fun w => decide (K.Rm v w)) ≤ n →
      ∃ z, K.Rm v z ∧ ∀ u, K.Rm z u → u = z := by
  induction n with
  | zero =>
      intro v hn
      rcases rmMax_or_step K v with hmax | ⟨u, _, hlt⟩
      · exact ⟨v, K.rm_refl v, hmax⟩
      · exact absurd (Nat.lt_of_lt_of_le hlt hn) (Nat.not_lt_zero _)
  | succ m ih =>
      intro v hn
      rcases rmMax_or_step K v with hmax | ⟨u, hvu, hlt⟩
      · exact ⟨v, K.rm_refl v, hmax⟩
      · obtain ⟨z, huz, hz⟩ := ih u (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hn))
        exact ⟨z, K.rm_trans hvu huz, hz⟩

theorem exists_rmMax (K : FRJ.Kripke) (v : K.W) :
    ∃ z, K.Rm v z ∧ ∀ u, K.Rm z u → u = z :=
  exists_rmMax_aux K _ v (Nat.le_refl _)

/-- The non-fallible worlds of an FRJ model, with `S` the `Rm`-maximal ones. -/
def ofKripke (K : FRJ.Kripke) : SubframeModel where
  W := {w : K.W // ¬ K.Fal w}
  le a b := K.le a.1 b.1
  S := {a | ∀ u, K.Rm a.1 u → u = a.1}
  V x := {a | K.V a.1 x}
  refl a := K.le_refl a.1
  trans h₁ h₂ := K.le_trans h₁ h₂
  hered h hv := K.V_mono h _ hv

instance (K : FRJ.Kripke) : FinDec (ofKripke K) where
  elems := K.elems.filterMap fun w => if h : K.Fal w then none else some ⟨w, h⟩
  complete a := List.mem_filterMap.mpr ⟨a.1, K.complete a.1, by rw [dif_neg a.2]; rfl⟩
  decLe a b := K.decLe a.1 b.1
  decS a := decidable_of_iff (∀ u ∈ K.elems, K.Rm a.1 u → u = a.1)
    ⟨fun h u => h u (K.complete u), fun h u _ => h u⟩
  decV x a := K.decV a.1 x

/-- **The translation preserves forcing** at every non-fallible world. -/
theorem ofKripke_force (K : FRJ.Kripke) :
    ∀ (φ : PLLFormula) (a : (ofKripke K).W),
      (K.force a.1 (FRJ.ofPLL φ) ↔ (ofKripke K).force a φ)
  | .prop _, _ => Iff.rfl
  | .falsePLL, a => ⟨fun h => a.2 h, False.elim⟩
  | .and φ ψ, a => and_congr (ofKripke_force K φ a) (ofKripke_force K ψ a)
  | .or φ ψ, a => or_congr (ofKripke_force K φ a) (ofKripke_force K ψ a)
  | .ifThen φ ψ, a => by
      constructor
      · intro h b hab hφ
        exact (ofKripke_force K ψ b).mp (h b.1 hab ((ofKripke_force K φ b).mpr hφ))
      · intro h b hab hφ
        by_cases hb : K.Fal b
        · exact K.fal_force _ hb
        · exact (ofKripke_force K ψ ⟨b, hb⟩).mpr
            (h ⟨b, hb⟩ hab ((ofKripke_force K φ ⟨b, hb⟩).mp hφ))
  | .somehow φ, a => by
      constructor
      · intro h b hab hbS
        obtain ⟨c, hbc, hc⟩ := h b.1 hab
        have hcb : c = b.1 := hbS c hbc
        rw [hcb] at hc
        exact (ofKripke_force K φ b).mp hc
      · intro h b hab
        obtain ⟨z, hbz, hz⟩ := exists_rmMax K b
        by_cases hzF : K.Fal z
        · exact ⟨z, hbz, K.fal_force _ hzF⟩
        · exact ⟨z, hbz, (ofKripke_force K φ ⟨z, hzF⟩).mpr
            (h ⟨z, hzF⟩ (K.le_trans hab (K.sub_mi hbz)) hz)⟩

/-! ## Completeness -/

/-- **A non-theorem has a finite decidable countermodel.** -/
theorem exists_countermodel {θ : PLLFormula} (h : [] ⊬ θ) :
    ∃ (K : SubframeModel) (_ : FinDec K) (k : K.W), ¬ K.force k θ := by
  rcases FRJ.Gbu.W.provable_or_disprovable (FRJ.ofPLL θ) with hp | ⟨_, _, ⟨d⟩⟩
  · exact absurd (FRJ.Gbu.W.PLL_iff_laxND.mp (FRJ.Gbu.pll_of_provableGbuC hp)) h
  · have hc := FRJ.W.modR_countermodel d
    have hroot : ¬ (FRJ.W.modR d).Fal (FRJ.W.modR d).root := fun hF =>
      hc ((FRJ.W.modR d).fal_force _ hF)
    exact ⟨ofKripke _, inferInstance, ⟨_, hroot⟩,
      fun hf => hc ((ofKripke_force _ θ ⟨_, hroot⟩).mpr hf)⟩

/-- **Completeness for finite decidable subframe models.** -/
theorem completeness {θ : PLLFormula}
    (h : ∀ (M : SubframeModel) [FinDec M] (x : M.W), M.force x θ) :
    Nonempty ([] ⊢ θ) :=
  match FRJ.Gbu.W.decideLaxND θ with
  | isTrue hd => hd
  | isFalse hn =>
      let ⟨K, _, k, hk⟩ := exists_countermodel hn
      absurd (h K k) hk

/-- `LaxND` derivability is validity in the finite decidable subframe models. -/
theorem derivable_iff_valid {θ : PLLFormula} :
    Nonempty ([] ⊢ θ) ↔ ∀ (M : SubframeModel) [FinDec M] (x : M.W), M.force x θ :=
  ⟨fun ⟨p⟩ M _ x => soundness p M x fun _ hχ => absurd hχ List.not_mem_nil,
    completeness⟩

/-- Completeness for an implication: it suffices that every world of a
finite decidable model forcing `φ` forces `ψ`. -/
theorem completeness_imp {φ ψ : PLLFormula}
    (h : ∀ (M : SubframeModel) [FinDec M] (x : M.W), M.force x φ → M.force x ψ) :
    Nonempty ([] ⊢ φ ↠ ψ) :=
  completeness fun M _ _ y _ hφ => h M y hφ

/-! ## Axiom audit (pinned, as upper bounds) -/

#axioms_within soundness [propext, Quot.sound]
#axioms_within exists_of_not_force_imp [propext, Quot.sound]
#axioms_within exists_of_not_force_box [propext, Quot.sound]
#axioms_within ofKripke_force [propext, Quot.sound]
#axioms_within exists_countermodel [propext, Quot.sound]
#axioms_within derivable_iff_valid [propext, Quot.sound]

end CF
end SubframeModel
end PLLND
