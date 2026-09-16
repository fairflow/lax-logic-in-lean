/-
# Shape lemmas for the V-join contexts

The `FRJ/SoundV.lean` case proofs consume these: which shapes inhabit
`joinCtxAtVBase`/`joinCtxOrVBase` and the kept zone, where each member
comes from, and the prime-exclusion for the conclusion label.  All
statements are about the CONTEXT FORMERS, not about derivations, so this
file depends only on `FRJ/CalculusV.lean`.
-/
import FRJ.CalculusV

namespace FRJ

open Form

variable {n : Nat} {stab th : Fin (n + 1) → List Form}
  {rhs : Fin (n + 1) → Form} {F : Form}

/-- An implication in the `⋈^At` base lies in `Σ^imp` (the atom zones
cannot hold it). -/
theorem baseAtV_imp {A B : Form}
    (h : Form.imp A B ∈ joinCtxAtVBase stab th F) :
    Form.imp A B ∈ unionAll (fun j => impPart (stab j)) := by
  simp only [joinCtxAtVBase, List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨j, hj⟩ := mem_unionAll.mp h
    exact absurd (List.mem_filter.mp hj).2 (by simp [Form.isPV])
  · have := (List.mem_filter.mp (interAll_subset' 0 (rm_subset h))).2
    exact absurd this (by simp [Form.isPV])
  · exact h

/-- The same for the `⋈^∨` base. -/
theorem baseOrV_imp {A B : Form}
    (h : Form.imp A B ∈ joinCtxOrVBase stab th) :
    Form.imp A B ∈ unionAll (fun j => impPart (stab j)) := by
  simp only [joinCtxOrVBase, List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨j, hj⟩ := mem_unionAll.mp h
    exact absurd (List.mem_filter.mp hj).2 (by simp [Form.isPV])
  · have := (List.mem_filter.mp (interAll_subset' 0 h)).2
    exact absurd this (by simp [Form.isPV])
  · exact h

/-- Hence, via (J2), an implication in either base has its antecedent
among the premises' right formulas. -/
theorem baseAtV_imp_head
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    {A B : Form} (h : Form.imp A B ∈ joinCtxAtVBase stab th F) :
    A ∈ upsilon rhs :=
  hJ2 A B (baseAtV_imp h)

theorem baseOrV_imp_head
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    {A B : Form} (h : Form.imp A B ∈ joinCtxOrVBase stab th) :
    A ∈ upsilon rhs :=
  hJ2 A B (baseOrV_imp h)

/-- No `◯`-formula inhabits the `⋈^At` base. -/
theorem circ_not_mem_baseAtV {Y : Form} :
    Form.circ Y ∉ joinCtxAtVBase stab th F := by
  intro h
  simp only [joinCtxAtVBase, List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨j, hj⟩ := mem_unionAll.mp h
    exact absurd (List.mem_filter.mp hj).2 (by simp [Form.isPV])
  · exact absurd (List.mem_filter.mp (interAll_subset' 0 (rm_subset h))).2
      (by simp [Form.isPV])
  · obtain ⟨j, hj⟩ := mem_unionAll.mp h
    exact absurd (List.mem_filter.mp hj).2 (by simp [Form.isImp])

theorem circ_not_mem_baseOrV {Y : Form} :
    Form.circ Y ∉ joinCtxOrVBase stab th := by
  intro h
  simp only [joinCtxOrVBase, List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨j, hj⟩ := mem_unionAll.mp h
    exact absurd (List.mem_filter.mp hj).2 (by simp [Form.isPV])
  · exact absurd (List.mem_filter.mp (interAll_subset' 0 h)).2
      (by simp [Form.isPV])
  · obtain ⟨j, hj⟩ := mem_unionAll.mp h
    exact absurd (List.mem_filter.mp hj).2 (by simp [Form.isImp])

/-- No `◯`-formula inhabits a kept zone (its members are implications). -/
theorem circ_not_mem_kept {Υ base pool kept : List Form}
    (hkc : KeptChain Υ base pool kept) {Y : Form} :
    Form.circ Y ∉ kept := fun h =>
  absurd (keptChain_isImp hkc _ h) (by simp [Form.isImp])

/-- A `Σ`-member of atomic or implicational shape lands in the `⋈^At`
base (mirrors `stab_mem_joinCtxAt`, without the second zone). -/
theorem stab_mem_baseAtV {G : Form}
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    {j : Fin (n + 1)} {K : Form} (hK : K ∈ stab j) (hKG : K ∈ gHat G) :
    K ∈ joinCtxAtVBase stab th F ∨ K = F := by
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with (h | h) | h
  · -- an atom: in `Σ^at`
    exact Or.inl (List.mem_append_left _ (List.mem_append_left _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp h).2⟩⟩)))
  · -- an implication: in `Σ^imp`
    exact Or.inl (List.mem_append_right _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp h).2⟩⟩))
  · -- a `◯`-formula: excluded by `hcirc`
    exfalso
    have : K ∈ unionAll (fun j => circPart (stab j)) :=
      mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp h).2⟩⟩
    rw [hcirc] at this
    exact List.not_mem_nil this

theorem stab_mem_baseOrV {G : Form}
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    {j : Fin (n + 1)} {K : Form} (hK : K ∈ stab j) (hKG : K ∈ gHat G) :
    K ∈ joinCtxOrVBase stab th := by
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with (h | h) | h
  · exact List.mem_append_left _ (List.mem_append_left _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp h).2⟩⟩))
  · exact List.mem_append_right _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp h).2⟩⟩)
  · exfalso
    have : K ∈ unionAll (fun j => circPart (stab j)) :=
      mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp h).2⟩⟩
    rw [hcirc] at this
    exact List.not_mem_nil this

/-- Local copy of `Sound.lean`'s `prime_not_isImp` (that module sits
above this one in the import order). -/
theorem prime_not_isImp'' {F : Form} (h : F.isPrime) : ¬ F.isImp := by
  cases F <;> simp_all [Form.isPrime, Form.isImp]

/-- A prime `F` outside `Σ^at` is not in the `⋈^At` conclusion label. -/
theorem prime_not_mem_ctxAtV {Υ pool kept : List Form}
    (hkc : KeptChain Υ (joinCtxAtVBase stab th F) pool kept)
    (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j))) :
    F ∉ joinCtxAtVBase stab th F ++ kept := by
  intro h
  rcases List.mem_append.mp h with h | h
  · simp only [joinCtxAtVBase, List.mem_append] at h
    rcases h with (h | h) | h
    · exact hFnot h
    · exact (mem_rm.mp h).1 rfl
    · obtain ⟨j, hj⟩ := mem_unionAll.mp h
      exact prime_not_isImp'' hF (List.mem_filter.mp hj).2
  · exact prime_not_isImp'' hF (keptChain_isImp hkc _ h)

/-- Kept-zone members sit in every premise's second zone. -/
theorem kept_mem_th {Υ base kept : List Form}
    (hkc : KeptChain Υ base (thPool th) kept)
    {K : Form} (hK : K ∈ kept) (j : Fin (n + 1)) : K ∈ th j :=
  interAll_subset' j (List.mem_filter.mp (keptChain_subset hkc hK)).1

/-- Kept-zone members are in `Ĝ` whenever the premises' zones are. -/
theorem kept_mem_gHat {G : Form} {Υ base kept : List Form}
    (hkc : KeptChain Υ base (thPool th) kept)
    (hwf : ∀ X ∈ th 0, X ∈ gHat G)
    {K : Form} (hK : K ∈ kept) : K ∈ gHat G :=
  hwf _ (kept_mem_th hkc hK 0)

end FRJ
