import LaxLogic.PLL.SemUI.SubframeAmalg

/-!
# Uniform interpolation for PLL

The assembly of the semantic route in the subframe semantics.  For every
formula `φ` and atom `p` there is a formula `ψ` (written `∃p φ`) in the atoms
of `φ` other than `p` with

    ⊢ φ ↠ ψ,      and for every p-free χ:   ⊢ φ ↠ χ  ⟹  ⊢ ψ ↠ χ.

(`uniform_ex`).  The ◯-free instance, Pitts's `∃p` for IPC read inside PLL,
comes first (`uniform_exI`, rule 8).

The interpolant.  Put `X` the subformulas of `φ` together with `⊥`, `V` the
atoms of `φ` other than `p`, `L := 3·ν(X) + 2` the level of the amalgamation
lemma and `r := 3L + 1` the crank at which agreement gives a level-`L` link
(step 2).  Then `∃p φ` is the conjunction of the representatives `D` of crank
≤ `r + 1` over `V` (`SemUI.frag_reps_exist'`) with `⊢ φ ↠ D`.

The proof that `∃p φ ⊢ χ`: let `w` force `∃p φ` in a subframe model, and let
`θ⁺ ↠ θ⁻` be the character of `w` over the representatives of crank ≤ `r`.

1. `⊬ φ ↠ (θ⁺ ↠ θ⁻)`: otherwise a representative of that crank-`(r+1)`
   formula is a conjunct of `∃p φ`, so `w` forces it, which `w` cannot.
2. Completeness gives a world `k ⊩ φ` with the same `r`-type as `w`.
3. Step 2 links `k` and `w` at level `L` (`layered_of_agree`).
4. Step 3 gives a `p`-variant of `w`'s model whose copy of `w` agrees with
   `k` on `X`, so forces `φ`, so forces `χ` (`amalgamation`).
5. `χ` is `p`-free, so `w ⊩ χ` (`PBisim.force_iff`); completeness gives
   `⊢ ∃p φ ↠ χ`.

The size of `L` affects only the crank of the fragment, hence the size of
`∃p φ`, not its existence.

## The `∀`-side

For every `φ` and `p` there is a formula `ψ` (written `∀p φ`) in the atoms of
`φ` other than `p` with

    ⊢ ψ ↠ φ,      and for every p-free χ:   ⊢ χ ↠ φ  ⟹  ⊢ χ ↠ ψ

(`uniform_all`; ◯-free instance `uniform_allI` first).  Semantically the two
sides do not depend on each other.  With `R` the representatives of crank ≤
`r` over `V` and, for `T ⊆ R`, `char(T) := ⋀T ↠ ⋁(R ∖ T)` (`charT`), which a
world refutes exactly when some world above it has `R`-type exactly `T`
(`type_of_char`),

    ∀p φ  :=  ⋀ { char(T)  |  T ⊆ R,  ⊬ ⋀T ↠ (⋁(R ∖ T) ∨ φ) }.

The side condition says that some world of type `T` refutes `φ` (Litak and
Visser's `Θ⁺ ⊬ Θ⁻ ∨ φ`).

* `⊢ ∀p φ ↠ φ` needs no amalgamation: a world `w` refuting `φ` qualifies its
  own type `T`, so it forces `char(T)` while having type `T`, which is
  impossible.
* `⊢ χ ↠ φ` gives `⊢ χ ↠ ∀p φ`: if `w ⊩ χ` refutes `char(T)`, some `v ≥ w`
  has type `T`; a countermodel world `k` has type `T` and refutes `φ`; step 2
  links `k` and `v`, step 3 gives a `p`-variant of `v` agreeing with `k` on
  `X`, which refutes `φ` and forces `χ` (persistence and invariance): a
  contradiction with `⊢ χ ↠ φ`.
-/

open PLLFormula

namespace PLLND
namespace SubframeModel

open SemUI (crank bigAnd boxFree nu eraseBox frag_reps_exist' atoms_bigAnd
  atoms_bigOr crank_eraseBox_le mem_atoms_eraseBox boxFree_eraseBox boxFree_bigAnd
  boxFree_bigOr)

namespace UIEx

attribute [local instance] Classical.propDecidable

/-! ## Subformulas -/

theorem atoms_of_mem_subF :
    ∀ {φ ψ : PLLFormula}, ψ ∈ subF φ → ∀ a ∈ ψ.atoms, a ∈ φ.atoms
  | .prop _, _, h, a, ha => by
      simp [subF] at h
      subst h
      exact ha
  | .falsePLL, _, h, a, ha => by
      simp [subF] at h
      subst h
      exact ha
  | .and φ₁ φ₂, _, h, a, ha => by
      simp [subF] at h
      rcases h with rfl | h | h
      · exact ha
      · exact mem_atoms_and.mpr (Or.inl (atoms_of_mem_subF h a ha))
      · exact mem_atoms_and.mpr (Or.inr (atoms_of_mem_subF h a ha))
  | .or φ₁ φ₂, _, h, a, ha => by
      simp [subF] at h
      rcases h with rfl | h | h
      · exact ha
      · exact mem_atoms_or.mpr (Or.inl (atoms_of_mem_subF h a ha))
      · exact mem_atoms_or.mpr (Or.inr (atoms_of_mem_subF h a ha))
  | .ifThen φ₁ φ₂, _, h, a, ha => by
      simp [subF] at h
      rcases h with rfl | h | h
      · exact ha
      · exact mem_atoms_ifThen.mpr (Or.inl (atoms_of_mem_subF h a ha))
      · exact mem_atoms_ifThen.mpr (Or.inr (atoms_of_mem_subF h a ha))
  | .somehow φ₁, _, h, a, ha => by
      simp [subF] at h
      rcases h with rfl | h
      · exact ha
      · exact atoms_of_mem_subF h a ha

theorem boxFree_of_mem_subF :
    ∀ {φ ψ : PLLFormula}, boxFree φ = true → ψ ∈ subF φ → boxFree ψ = true
  | .prop _, _, _, h => by
      simp [subF] at h
      subst h
      rfl
  | .falsePLL, _, _, h => by
      simp [subF] at h
      subst h
      rfl
  | .and φ₁ φ₂, _, hb, h => by
      simp [subF] at h
      rcases h with rfl | h | h
      · exact hb
      · simp only [boxFree, Bool.and_eq_true] at hb
        exact boxFree_of_mem_subF hb.1 h
      · simp only [boxFree, Bool.and_eq_true] at hb
        exact boxFree_of_mem_subF hb.2 h
  | .or φ₁ φ₂, _, hb, h => by
      simp [subF] at h
      rcases h with rfl | h | h
      · exact hb
      · simp only [boxFree, Bool.and_eq_true] at hb
        exact boxFree_of_mem_subF hb.1 h
      · simp only [boxFree, Bool.and_eq_true] at hb
        exact boxFree_of_mem_subF hb.2 h
  | .ifThen φ₁ φ₂, _, hb, h => by
      simp [subF] at h
      rcases h with rfl | h | h
      · exact hb
      · simp only [boxFree, Bool.and_eq_true] at hb
        exact boxFree_of_mem_subF hb.1 h
      · simp only [boxFree, Bool.and_eq_true] at hb
        exact boxFree_of_mem_subF hb.2 h
  | .somehow _, _, hb, _ => by simp [boxFree] at hb

/-- The atoms of `{⊥} ∪ subF φ` other than `p` are atoms of `φ` other than
`p`. -/
theorem protect (φ : PLLFormula) (p : String) :
    ∀ a, a ≠ p → PLLFormula.prop a ∈ insert ⊥ (subF φ) →
      a ∈ φ.atoms.erase p := by
  intro a ha h
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd h (by simp)
  · exact Finset.mem_erase.mpr ⟨ha, atoms_of_mem_subF h a (by simp)⟩

/-- A world refuting a formula exists when the formula is not derivable. -/
theorem exists_countermodel {θ : PLLFormula} (h : [] ⊬ θ) :
    ∃ (K : SubframeModel) (k : K.W), ¬ K.force k θ := by
  by_contra hc
  exact h (derivable_iff_valid.mpr fun K k => by
    by_contra hk
    exact hc ⟨K, k, hk⟩)

/-! ## Types over a list -/

/-- The members of `R` outside `T`. -/
noncomputable def compl (R T : List PLLFormula) : List PLLFormula :=
  R.filter fun D => decide (D ∉ T)

theorem mem_compl {R T : List PLLFormula} {D : PLLFormula} :
    D ∈ compl R T ↔ D ∈ R ∧ D ∉ T := by
  simp [compl]

/-- `⋀T ↠ ⋁(R ∖ T)`: refuted exactly above a world whose `R`-type is `T`. -/
noncomputable def charT (R T : List PLLFormula) : PLLFormula :=
  (bigAnd T).ifThen (bigOr (compl R T))

/-- A world forcing `⋀T` and refuting `⋁(R ∖ T)` has `R`-type `T`. -/
theorem type_of_char {M : SubframeModel} {v : M.W} {R T : List PLLFormula}
    (hT : M.force v (bigAnd T)) (hn : ¬ M.force v (bigOr (compl R T))) :
    ∀ D ∈ R, (M.force v D ↔ D ∈ T) := by
  intro D hD
  constructor
  · intro hf
    by_contra hDT
    exact hn ((force_bigOr_iff M v _).mpr ⟨D, mem_compl.mpr ⟨hD, hDT⟩, hf⟩)
  · intro hDT
    exact (force_bigAnd_iff M v T).mp hT D hDT

/-- A world refutes the complement of its own type. -/
theorem not_force_compl_posL (M : SubframeModel) (R : List PLLFormula) (w : M.W) :
    ¬ M.force w (bigOr (compl R (posL M R w))) := by
  intro h
  obtain ⟨D, hD, hf⟩ := (force_bigOr_iff M w _).mp h
  exact (mem_compl.mp hD).2 (mem_posL.mpr ⟨(mem_compl.mp hD).1, hf⟩)

/-- The `R`-type of a world is a sublist of `R`. -/
theorem posL_mem_sublists (M : SubframeModel) (R : List PLLFormula) (w : M.W) :
    posL M R w ∈ R.sublists :=
  List.mem_sublists.mpr List.filter_sublist

/-- A world qualifies its own type when it refutes `φ`. -/
theorem good_posL {M : SubframeModel} {R : List PLLFormula} {w : M.W}
    {φ : PLLFormula} (hφ : ¬ M.force w φ) :
    [] ⊬ bigAnd (posL M R w) ↠ bigOr (compl R (posL M R w)) ∨ φ := by
  rintro ⟨d⟩
  have h := SubframeModel.soundness d M w (by simp) w (M.refl w) (force_pos M R w)
  rcases h with h | h
  · exact not_force_compl_posL M R w h
  · exact hφ h

end UIEx

open UIEx Amalg

attribute [local instance] Classical.propDecidable

/-! ## The ◯-free instance (IPC) -/

/-- **The `∃`-side of uniform interpolation, ◯-free instance.**  For a
◯-free `φ` there is a ◯-free `ψ` in the atoms of `φ` other than `p` with
`⊢ φ ↠ ψ` and `⊢ ψ ↠ χ` for every ◯-free `p`-free `χ` with `⊢ φ ↠ χ`. -/
theorem uniform_exI (p : String) (φ : PLLFormula) (hφ : boxFree φ = true) :
    ∃ ψ : PLLFormula, boxFree ψ = true ∧ (∀ a ∈ ψ.atoms, a ∈ φ.atoms ∧ a ≠ p) ∧
      Nonempty ([] ⊢ φ ↠ ψ) ∧
      ∀ χ : PLLFormula, boxFree χ = true → p ∉ χ.atoms →
        Nonempty ([] ⊢ φ ↠ χ) → Nonempty ([] ⊢ ψ ↠ χ) := by
  have hX : SubClosed (insert PLLFormula.falsePLL (subF φ)) :=
    subClosed_insert_bot_subF φ
  have hX0 : ∀ ψ ∈ insert PLLFormula.falsePLL (subF φ), boxFree ψ = true := by
    intro ψ hψ
    rcases Finset.mem_insert.mp hψ with rfl | hψ
    · rfl
    · exact boxFree_of_mem_subF hφ hψ
  obtain ⟨R, hRb, hR⟩ := frag_reps_exist' (φ.atoms.erase p)
    (2 * nu (insert PLLFormula.falsePLL (subF φ)) + 1 + 1 + 1)
  obtain ⟨Q, hQb, hQ⟩ := frag_reps_exist' (φ.atoms.erase p)
    (2 * nu (insert PLLFormula.falsePLL (subF φ)) + 1 + 1)
  have hQe : ∀ D ∈ Q.map eraseBox,
      crank D ≤ 2 * nu (insert PLLFormula.falsePLL (subF φ)) + 1 + 1 ∧
        ∀ a ∈ D.atoms, a ∈ φ.atoms.erase p := by
    intro D hD
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    exact ⟨le_trans (crank_eraseBox_le E) (hQb E hE).1,
      fun a ha => (hQb E hE).2 a (mem_atoms_eraseBox ha)⟩
  have hQf : ∀ D ∈ Q.map eraseBox, boxFree D = true := by
    intro D hD
    obtain ⟨E, -, rfl⟩ := List.mem_map.mp hD
    exact boxFree_eraseBox E
  refine ⟨bigAnd ((R.map eraseBox).filter
    fun D => decide (Nonempty (LaxND [] (φ.ifThen D)))), ?_, ?_, ?_, ?_⟩
  · refine boxFree_bigAnd fun D hD => ?_
    obtain ⟨E, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hD).1
    exact boxFree_eraseBox E
  · intro a ha
    have h := atoms_bigAnd (Q := fun a => a ∈ φ.atoms.erase p) (fun D hD => by
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hD).1
      exact fun b hb => (hRb E hE).2 b (mem_atoms_eraseBox hb)) a ha
    exact ⟨(Finset.mem_erase.mp h).2, (Finset.mem_erase.mp h).1⟩
  · refine derivable_iff_valid.mpr fun M x y _ hφy => ?_
    refine (force_bigAnd_iff M y _).mpr fun D hD => ?_
    obtain ⟨d⟩ := of_decide_eq_true (List.mem_filter.mp hD).2
    exact SubframeModel.soundness d M y (by simp) y (M.refl y) hφy
  · intro χ hχb hp hχ
    refine derivable_iff_valid.mpr fun M x w _ hψ => ?_
    -- 1. the character of `w` is not a consequence of `φ`
    have hcζ := crank_charImp_le (M := M) (by omega) (fun D hD => (hQe D hD).1) w
    have haζ := atoms_charImp (M := M) (fun D hD => (hQe D hD).2) w
    have hbζ := boxFree_charImp (M := M) hQf w
    have hnot : ¬ Nonempty (LaxND [] (φ.ifThen (charImp M (Q.map eraseBox) w))) := by
      rintro ⟨d⟩
      obtain ⟨D, hD, h₁, h₂⟩ := hR _ hcζ haζ
      have hD' : Nonempty (LaxND [] (φ.ifThen (eraseBox D))) := by
        refine derivable_iff_valid.mpr fun M' x' y' hxy' hφ' => ?_
        exact (force_iff_eraseBox_of_interd hbζ h₁ h₂ M' y').mp
          (SubframeModel.soundness d M' x' (by simp) y' hxy' hφ')
      have hwD : M.force w (eraseBox D) := (force_bigAnd_iff M w _).mp hψ _
        (List.mem_filter.mpr ⟨List.mem_map_of_mem hD, decide_eq_true hD'⟩)
      exact not_force_charImp (M.refl w) _
        ((force_iff_eraseBox_of_interd hbζ h₁ h₂ M w).mpr hwD)
    -- 2. a world forcing `φ` with the type of `w`
    obtain ⟨K, k₀, hk₀⟩ := exists_countermodel hnot
    obtain ⟨k₁, hk₁, hφk₁, hnζ⟩ := exists_of_not_force_imp hk₀
    obtain ⟨k₂, hk₂, hagQ⟩ := exists_of_not_force_charImp hnζ
    have hag := (agreeI_of_reps hQ hagQ).symm
    -- 3. the link, 4. the amalgam, 5. invariance
    obtain ⟨B, hB⟩ := layeredI_of_agree hag
    obtain ⟨N, C, n₀, hC, hagr⟩ := amalgamationI _ hX hX0 p K M k₂ w
      (· ∈ φ.atoms.erase p) (protect φ p) B hB
    have hφn : N.force n₀ φ :=
      (hagr φ (Finset.mem_insert_of_mem (self_mem_subF φ))).mpr
        (K.force_mono φ hk₂ hφk₁)
    obtain ⟨dχ⟩ := hχ
    exact (C.force_iff χ hχb hp hC).mpr
      (SubframeModel.soundness dχ N n₀ (by simp) n₀ (N.refl n₀) hφn)

/-! ## PLL -/

/-- **The `∃`-side of uniform interpolation for PLL.**  For every `φ` and `p`
there is a `ψ` in the atoms of `φ` other than `p` with `⊢ φ ↠ ψ` and
`⊢ ψ ↠ χ` for every `p`-free `χ` with `⊢ φ ↠ χ`. -/
theorem uniform_ex (p : String) (φ : PLLFormula) :
    ∃ ψ : PLLFormula, (∀ a ∈ ψ.atoms, a ∈ φ.atoms ∧ a ≠ p) ∧
      Nonempty ([] ⊢ φ ↠ ψ) ∧
      ∀ χ : PLLFormula, p ∉ χ.atoms →
        Nonempty ([] ⊢ φ ↠ χ) → Nonempty ([] ⊢ ψ ↠ χ) := by
  have hX : SubClosed (insert PLLFormula.falsePLL (subF φ)) :=
    subClosed_insert_bot_subF φ
  obtain ⟨R, hRb, hR⟩ := frag_reps_exist' (φ.atoms.erase p)
    (3 * (3 * nu (insert PLLFormula.falsePLL (subF φ)) + 2) + 1 + 1)
  obtain ⟨Q, hQb, hQ⟩ := frag_reps_exist' (φ.atoms.erase p)
    (3 * (3 * nu (insert PLLFormula.falsePLL (subF φ)) + 2) + 1)
  refine ⟨bigAnd (R.filter fun D => decide (Nonempty (LaxND [] (φ.ifThen D)))),
    ?_, ?_, ?_⟩
  · intro a ha
    have h := atoms_bigAnd (Q := fun a => a ∈ φ.atoms.erase p)
      (fun D hD => (hRb D (List.mem_filter.mp hD).1).2) a ha
    exact ⟨(Finset.mem_erase.mp h).2, (Finset.mem_erase.mp h).1⟩
  · refine derivable_iff_valid.mpr fun M x y _ hφy => ?_
    refine (force_bigAnd_iff M y _).mpr fun D hD => ?_
    obtain ⟨d⟩ := of_decide_eq_true (List.mem_filter.mp hD).2
    exact SubframeModel.soundness d M y (by simp) y (M.refl y) hφy
  · intro χ hp hχ
    refine derivable_iff_valid.mpr fun M x w _ hψ => ?_
    -- 1. the character of `w` is not a consequence of `φ`
    have hcζ := crank_charImp_le (M := M) (by omega) (fun D hD => (hQb D hD).1) w
    have haζ := atoms_charImp (M := M) (fun D hD => (hQb D hD).2) w
    have hnot : ¬ Nonempty (LaxND [] (φ.ifThen (charImp M Q w))) := by
      rintro ⟨d⟩
      obtain ⟨D, hD, h₁, h₂⟩ := hR _ hcζ haζ
      have hD' : Nonempty (LaxND [] (φ.ifThen D)) := by
        refine derivable_iff_valid.mpr fun M' x' y' hxy' hφ' => ?_
        exact (force_iff_of_interd h₁ h₂ M' y').mp
          (SubframeModel.soundness d M' x' (by simp) y' hxy' hφ')
      have hwD : M.force w D := (force_bigAnd_iff M w _).mp hψ D
        (List.mem_filter.mpr ⟨hD, decide_eq_true hD'⟩)
      exact not_force_charImp (M.refl w) Q ((force_iff_of_interd h₁ h₂ M w).mpr hwD)
    -- 2. a world forcing `φ` with the type of `w`
    obtain ⟨K, k₀, hk₀⟩ := exists_countermodel hnot
    obtain ⟨k₁, hk₁, hφk₁, hnζ⟩ := exists_of_not_force_imp hk₀
    obtain ⟨k₂, hk₂, hagQ⟩ := exists_of_not_force_charImp hnζ
    have hag := (agree_of_reps hQ hagQ).symm
    -- 3. the link, 4. the amalgam, 5. invariance
    obtain ⟨B, hB⟩ := layered_of_agree hag
    obtain ⟨N, C, n₀, hC, hagr⟩ := amalgamation _ hX p K M k₂ w
      (· ∈ φ.atoms.erase p) (protect φ p) B hB
    have hφn : N.force n₀ φ :=
      (hagr φ (Finset.mem_insert_of_mem (self_mem_subF φ))).mpr
        (K.force_mono φ hk₂ hφk₁)
    obtain ⟨dχ⟩ := hχ
    exact (C.force_iff χ hp hC).mpr
      (SubframeModel.soundness dχ N n₀ (by simp) n₀ (N.refl n₀) hφn)

/-! ## The `∀`-side, ◯-free instance (IPC) -/

/-- **The `∀`-side of uniform interpolation, ◯-free instance.**  For a
◯-free `φ` there is a ◯-free `ψ` in the atoms of `φ` other than `p` with
`⊢ ψ ↠ φ` and `⊢ χ ↠ ψ` for every ◯-free `p`-free `χ` with `⊢ χ ↠ φ`. -/
theorem uniform_allI (p : String) (φ : PLLFormula) (hφ : boxFree φ = true) :
    ∃ ψ : PLLFormula, boxFree ψ = true ∧ (∀ a ∈ ψ.atoms, a ∈ φ.atoms ∧ a ≠ p) ∧
      Nonempty ([] ⊢ ψ ↠ φ) ∧
      ∀ χ : PLLFormula, boxFree χ = true → p ∉ χ.atoms →
        Nonempty ([] ⊢ χ ↠ φ) → Nonempty ([] ⊢ χ ↠ ψ) := by
  have hX : SubClosed (insert PLLFormula.falsePLL (subF φ)) :=
    subClosed_insert_bot_subF φ
  have hX0 : ∀ ψ ∈ insert PLLFormula.falsePLL (subF φ), boxFree ψ = true := by
    intro ψ hψ
    rcases Finset.mem_insert.mp hψ with rfl | hψ
    · rfl
    · exact boxFree_of_mem_subF hφ hψ
  obtain ⟨R, hRb, hR⟩ := frag_reps_exist' (φ.atoms.erase p)
    (2 * nu (insert PLLFormula.falsePLL (subF φ)) + 1 + 1)
  have hRe : ∀ D ∈ R.map eraseBox, ∀ a ∈ D.atoms, a ∈ φ.atoms.erase p := by
    intro D hD
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    exact fun a ha => (hRb E hE).2 a (mem_atoms_eraseBox ha)
  have hRf : ∀ D ∈ R.map eraseBox, boxFree D = true := by
    intro D hD
    obtain ⟨E, -, rfl⟩ := List.mem_map.mp hD
    exact boxFree_eraseBox E
  refine ⟨bigAnd ((((R.map eraseBox).sublists).filter fun T => decide
      (¬ Nonempty (LaxND [] ((bigAnd T).ifThen
        ((bigOr (compl (R.map eraseBox) T)).or φ))))).map (charT (R.map eraseBox))),
    ?_, ?_, ?_, ?_⟩
  · refine boxFree_bigAnd fun c hc => ?_
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hc
    have hTs := (List.mem_sublists.mp (List.mem_filter.mp hT).1).subset
    simp only [charT, boxFree, Bool.and_eq_true]
    exact ⟨boxFree_bigAnd fun D hD => hRf D (hTs hD),
      boxFree_bigOr fun D hD => hRf D (mem_compl.mp hD).1⟩
  · intro a ha
    have h := atoms_bigAnd (Q := fun a => a ∈ φ.atoms.erase p) (fun c hc => by
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hc
      have hTs := (List.mem_sublists.mp (List.mem_filter.mp hT).1).subset
      intro b hb
      rcases mem_atoms_ifThen.mp hb with hb | hb
      · exact atoms_bigAnd (fun D hD => hRe D (hTs hD)) b hb
      · exact atoms_bigOr (fun D hD => hRe D (mem_compl.mp hD).1) b hb) a ha
    exact ⟨(Finset.mem_erase.mp h).2, (Finset.mem_erase.mp h).1⟩
  · refine derivable_iff_valid.mpr fun M x w _ hψ => ?_
    by_contra hnφ
    have hc := (force_bigAnd_iff M w _).mp hψ (charT (R.map eraseBox)
      (posL M (R.map eraseBox) w)) (List.mem_map_of_mem (List.mem_filter.mpr
        ⟨posL_mem_sublists M _ w, decide_eq_true (good_posL hnφ)⟩))
    exact not_force_compl_posL M _ w (hc w (M.refl w) (force_pos M _ w))
  · intro χ hχb hp hχ
    refine derivable_iff_valid.mpr fun M x w _ hχw => ?_
    refine (force_bigAnd_iff M w _).mpr fun c hc => ?_
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hc
    have hng := of_decide_eq_true (List.mem_filter.mp hT).2
    intro v hwv hvT
    by_contra hvn
    have htv := type_of_char hvT hvn
    obtain ⟨K, k₀, hk₀⟩ := exists_countermodel hng
    obtain ⟨k₁, -, hT₁, hn₁⟩ := exists_of_not_force_imp hk₀
    have hn₁' : ¬ K.force k₁ (bigOr (compl (R.map eraseBox) T)) := fun h => hn₁ (Or.inl h)
    have hnφ : ¬ K.force k₁ φ := fun h => hn₁ (Or.inr h)
    have htk := type_of_char hT₁ hn₁'
    have hag := agreeI_of_reps hR fun D hD => (htk D hD).trans (htv D hD).symm
    obtain ⟨B, hB⟩ := layeredI_of_agree hag
    obtain ⟨N, C, n₀, hC, hagr⟩ := amalgamationI _ hX hX0 p K M k₁ v
      (· ∈ φ.atoms.erase p) (protect φ p) B hB
    have hχn : N.force n₀ χ :=
      (C.force_iff χ hχb hp hC).mp (M.force_mono χ hwv hχw)
    obtain ⟨dχ⟩ := hχ
    exact hnφ ((hagr φ (Finset.mem_insert_of_mem (self_mem_subF φ))).mp
      (SubframeModel.soundness dχ N n₀ (by simp) n₀ (N.refl n₀) hχn))

/-! ## The `∀`-side for PLL -/

/-- **The `∀`-side of uniform interpolation for PLL.**  For every `φ` and `p`
there is a `ψ` in the atoms of `φ` other than `p` with `⊢ ψ ↠ φ` and
`⊢ χ ↠ ψ` for every `p`-free `χ` with `⊢ χ ↠ φ`. -/
theorem uniform_all (p : String) (φ : PLLFormula) :
    ∃ ψ : PLLFormula, (∀ a ∈ ψ.atoms, a ∈ φ.atoms ∧ a ≠ p) ∧
      Nonempty ([] ⊢ ψ ↠ φ) ∧
      ∀ χ : PLLFormula, p ∉ χ.atoms →
        Nonempty ([] ⊢ χ ↠ φ) → Nonempty ([] ⊢ χ ↠ ψ) := by
  have hX : SubClosed (insert PLLFormula.falsePLL (subF φ)) :=
    subClosed_insert_bot_subF φ
  obtain ⟨R, hRb, hR⟩ := frag_reps_exist' (φ.atoms.erase p)
    (3 * (3 * nu (insert PLLFormula.falsePLL (subF φ)) + 2) + 1)
  refine ⟨bigAnd (((R.sublists).filter fun T => decide
      (¬ Nonempty (LaxND [] ((bigAnd T).ifThen ((bigOr (compl R T)).or φ))))).map
        (charT R)), ?_, ?_, ?_⟩
  · intro a ha
    have h := atoms_bigAnd (Q := fun a => a ∈ φ.atoms.erase p) (fun c hc => by
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hc
      have hTs := (List.mem_sublists.mp (List.mem_filter.mp hT).1).subset
      intro b hb
      rcases mem_atoms_ifThen.mp hb with hb | hb
      · exact atoms_bigAnd (fun D hD => (hRb D (hTs hD)).2) b hb
      · exact atoms_bigOr (fun D hD => (hRb D (mem_compl.mp hD).1).2) b hb) a ha
    exact ⟨(Finset.mem_erase.mp h).2, (Finset.mem_erase.mp h).1⟩
  · refine derivable_iff_valid.mpr fun M x w _ hψ => ?_
    by_contra hnφ
    have hc := (force_bigAnd_iff M w _).mp hψ (charT R (posL M R w))
      (List.mem_map_of_mem (List.mem_filter.mpr
        ⟨posL_mem_sublists M R w, decide_eq_true (good_posL hnφ)⟩))
    exact not_force_compl_posL M R w (hc w (M.refl w) (force_pos M R w))
  · intro χ hp hχ
    refine derivable_iff_valid.mpr fun M x w _ hχw => ?_
    refine (force_bigAnd_iff M w _).mpr fun c hc => ?_
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hc
    have hng := of_decide_eq_true (List.mem_filter.mp hT).2
    intro v hwv hvT
    by_contra hvn
    have htv := type_of_char hvT hvn
    obtain ⟨K, k₀, hk₀⟩ := exists_countermodel hng
    obtain ⟨k₁, -, hT₁, hn₁⟩ := exists_of_not_force_imp hk₀
    have hn₁' : ¬ K.force k₁ (bigOr (compl R T)) := fun h => hn₁ (Or.inl h)
    have hnφ : ¬ K.force k₁ φ := fun h => hn₁ (Or.inr h)
    have htk := type_of_char hT₁ hn₁'
    have hag := agree_of_reps hR fun D hD => (htk D hD).trans (htv D hD).symm
    obtain ⟨B, hB⟩ := layered_of_agree hag
    obtain ⟨N, C, n₀, hC, hagr⟩ := amalgamation _ hX p K M k₁ v
      (· ∈ φ.atoms.erase p) (protect φ p) B hB
    have hχn : N.force n₀ χ := (C.force_iff χ hp hC).mp (M.force_mono χ hwv hχw)
    obtain ⟨dχ⟩ := hχ
    exact hnφ ((hagr φ (Finset.mem_insert_of_mem (self_mem_subF φ))).mp
      (SubframeModel.soundness dχ N n₀ (by simp) n₀ (N.refl n₀) hχn))

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SubframeModel.uniform_exI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms uniform_exI

/--
info: 'PLLND.SubframeModel.uniform_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms uniform_ex

/--
info: 'PLLND.SubframeModel.uniform_allI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms uniform_allI

/--
info: 'PLLND.SubframeModel.uniform_all' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms uniform_all

end SubframeModel
end PLLND
