/-
# Completeness of FRJ(G): Lemma 6.4 and Theorem 6.3

Section 6's direct construction.  Triple induction, exactly the paper's:
(IH1) on `h(α)`, (IH2) on the sequent type (irregular before regular),
(IH3) on `size C` — realised as the lexicographic measure
`(ht K a, t, C.size)`.
-/
import FRJ.Complete

namespace FRJ

open Form

theorem not_mem_lamStar_of_not_force {K : Kripke} {a : K.W} {G C : Form}
    (h : ¬ K.force a C) : C ∉ lamStar K a G :=
  fun hc => h (K.forceStar_force (mem_lamStar.mp hc).2)

/-- Any nonempty finite set of formulas can be enumerated by `Fin (n+1)`,
which is the index shape the join rules take. -/
theorem exists_enum (S : Finset Form) (hS : S.Nonempty) :
    ∃ (n : Nat) (f : Fin (n + 1) → Form), upsilon f = S := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 :=
    ⟨S.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr hS)).symm⟩
  refine ⟨m, fun j => (S.equivFin.symm (Fin.cast hm.symm j)).1, ?_⟩
  ext y
  simp only [upsilon, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact (S.equivFin.symm _).2
  · intro hy
    refine ⟨Fin.cast hm (S.equivFin ⟨y, hy⟩), ?_⟩
    have hcc : Fin.cast hm.symm (Fin.cast hm (S.equivFin ⟨y, hy⟩))
        = S.equivFin ⟨y, hy⟩ := rfl
    rw [hcc]
    simp

/-- The antecedent of an implication. -/
def ante : Form → Form
  | .imp A _ => A
  | X => X

/-- `Υ` for the prime case: the antecedents of the implications of `Λ*_a`. -/
noncomputable def upsPrime (K : Kripke) (a : K.W) (G : Form) : Finset Form :=
  (impPart (lamStar K a G)).image ante

/-- Members of `Υ` are right subformulas that `a` refutes. -/
theorem upsPrime_spec {K : Kripke} {a : K.W} {G Y : Form}
    (h : Y ∈ upsPrime K a G) : Y ∈ sfR G ∧ ¬ K.force a Y := by
  obtain ⟨X, hX, hante⟩ := Finset.mem_image.mp h
  obtain ⟨hXl, hXimp⟩ := Finset.mem_filter.mp hX
  match X, hXimp with
  | .imp A B, _ =>
      obtain ⟨hsf, hst⟩ := mem_lamStar.mp hXl
      obtain ⟨hA, -⟩ := sfL_imp hsf
      subst hante
      exact ⟨hA, hst.2⟩

/-- An implication of `Λ*_a` has its antecedent in `Υ`. -/
theorem mem_upsPrime {K : Kripke} {a : K.W} {G A B : Form}
    (h : Form.imp A B ∈ lamStar K a G) : A ∈ upsPrime K a G :=
  Finset.mem_image.mpr ⟨.imp A B, Finset.mem_filter.mpr ⟨h, trivial⟩, rfl⟩

/-- The `⋈^At` case of Lemma 6.4: `C` prime, `Λ*_a` containing at least
one implication.  The join's premises are the irregular derivations for
the members of `Υ`, supplied by the induction hypothesis `ih`. -/
theorem regPrime_join (K : Kripke) (G : Form) (a : K.W) (C : Form)
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (hne : (upsPrime K a G).Nonempty)
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force a A →
        ∃ St Th : Finset Form, Nonempty (FRJi G St Th A) ∧
          St ⊆ lamStar K a G ∧ lamStar K a G ⊆ St ∪ Th) :
    ∃ Γ : Finset Form, Nonempty (FRJr G Γ C) ∧
      ∃ b : K.W, K.le a b ∧ lamStar K b G ⊆ Γ := by
  classical
  obtain ⟨n, f, hf⟩ := exists_enum (upsPrime K a G) hne
  have hfmem : ∀ j, f j ∈ upsPrime K a G := by
    intro j; rw [← hf]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hall : ∀ j, ∃ St Th : Finset Form, Nonempty (FRJi G St Th (f j)) ∧
      St ⊆ lamStar K a G ∧ lamStar K a G ⊆ St ∪ Th := by
    intro j
    obtain ⟨h1, h2⟩ := upsPrime_spec (hfmem j)
    exact ih (f j) h1 h2
  choose stab th hprem hs1 hs2 using hall
  have hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ∪ th j :=
    fun i j _ X hX => hs2 j (hs1 i hX)
  have hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
    rw [hf]
    exact mem_upsPrime (hs1 i (Finset.mem_of_mem_filter _ hi))
  have hFnot : C ∉ unionAll (fun j => atPart (stab j)) := by
    intro hmem
    obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
    exact not_mem_lamStar_of_not_force hnf (hs1 i (Finset.mem_of_mem_filter _ hi))
  refine ⟨joinCtxAt stab th f C,
    ⟨.joinAt (fun j => (hprem j).some) hJ1 hJ2 hCp hFnot hC⟩, a, K.le_refl a, ?_⟩
  -- `Λ*_a ⊆ Γ`
  intro X hX
  by_cases hin : ∃ j, X ∈ stab j
  · obtain ⟨j, hj⟩ := hin
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, Finset.mem_union] at hXG
    simp only [joinCtxAt, Finset.mem_union]
    rcases hXG with h | h
    · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
        ⟨j, Finset.mem_filter.mpr ⟨hj, (Finset.mem_filter.mp h).2⟩⟩)))
    · exact Or.inl (Or.inr (mem_unionAll.mpr
        ⟨j, Finset.mem_filter.mpr ⟨hj, (Finset.mem_filter.mp h).2⟩⟩))
  · push_neg at hin
    have hallTh : ∀ j, X ∈ th j :=
      fun j => (Finset.mem_union.mp (hs2 j hX)).resolve_left (hin j)
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, Finset.mem_union] at hXG
    simp only [joinCtxAt, Finset.mem_union]
    rcases hXG with h | h
    · refine Or.inl (Or.inl (Or.inr (Finset.mem_erase.mpr
        ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), ?_⟩)))
      exact mem_interAll.mpr (fun j =>
        Finset.mem_filter.mpr ⟨hallTh j, (Finset.mem_filter.mp h).2⟩)
    · refine Or.inr ?_
      have himp : X.isImp := (Finset.mem_filter.mp h).2
      match X, himp with
      | .imp A B, _ =>
          refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
            Finset.mem_filter.mpr ⟨hallTh j, trivial⟩), ?_⟩
          rw [hf]
          exact mem_upsPrime hX

/-- `C` prime with `Λ*_a` purely atomic: the `Ax^R` sub-case. -/
theorem regPrime_ax (K : Kripke) (G : Form) (a : K.W) (C : Form)
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (hempty : impPart (lamStar K a G) = ∅) :
    ∃ Γ : Finset Form, Nonempty (FRJr G Γ C) ∧
      ∃ b : K.W, K.le a b ∧ lamStar K b G ⊆ Γ := by
  refine ⟨(gAt G).erase C, ⟨.axR C hCp hC⟩, a, K.le_refl a, ?_⟩
  intro X hX
  have hXG := lamStar_subset_gHat hX
  simp only [gHat, Finset.mem_union] at hXG
  rcases hXG with h | h
  · exact Finset.mem_erase.mpr
      ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), h⟩
  · exfalso
    have hmem : X ∈ impPart (lamStar K a G) :=
      Finset.mem_filter.mpr ⟨hX, (Finset.mem_filter.mp h).2⟩
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty X)

/-- The `⋈^∨` case of Lemma 6.4. -/
theorem regOr_join (K : Kripke) (G : Form) (a : K.W) (C₁ C₂ : Form)
    (hC : Form.or C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.or C₁ C₂))
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force a A →
        ∃ St Th : Finset Form, Nonempty (FRJi G St Th A) ∧
          St ⊆ lamStar K a G ∧ lamStar K a G ⊆ St ∪ Th) :
    ∃ Γ : Finset Form, Nonempty (FRJr G Γ (.or C₁ C₂)) ∧
      ∃ b : K.W, K.le a b ∧ lamStar K b G ⊆ Γ := by
  classical
  obtain ⟨hC1, hC2⟩ := sfR_or hC
  have hn1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
  have hn2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
  set U : Finset Form := insert C₁ (insert C₂ (upsPrime K a G)) with hU
  have hUne : U.Nonempty := ⟨C₁, Finset.mem_insert_self _ _⟩
  obtain ⟨n, f, hf⟩ := exists_enum U hUne
  have hfmem : ∀ j, f j ∈ U := by
    intro j; rw [← hf]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hall : ∀ j, ∃ St Th : Finset Form, Nonempty (FRJi G St Th (f j)) ∧
      St ⊆ lamStar K a G ∧ lamStar K a G ⊆ St ∪ Th := by
    intro j
    have := hfmem j
    rw [hU] at this
    rcases Finset.mem_insert.mp this with h | h
    · exact h ▸ ih C₁ hC1 hn1
    · rcases Finset.mem_insert.mp h with h' | h'
      · exact h' ▸ ih C₂ hC2 hn2
      · obtain ⟨p1, p2⟩ := upsPrime_spec h'
        exact ih (f j) p1 p2
  choose stab th hprem hs1 hs2 using hall
  have hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ∪ th j :=
    fun i j _ X hX => hs2 j (hs1 i hX)
  have hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
    rw [hf, hU]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (mem_upsPrime (hs1 i (Finset.mem_of_mem_filter _ hi))))
  have hCin : C₁ ∈ upsilon f ∧ C₂ ∈ upsilon f := by
    rw [hf, hU]
    exact ⟨Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  refine ⟨joinCtxOr stab th f,
    ⟨.joinOr (fun j => (hprem j).some) hJ1 hJ2 hCin hC⟩, a, K.le_refl a, ?_⟩
  intro X hX
  by_cases hin : ∃ j, X ∈ stab j
  · obtain ⟨j, hj⟩ := hin
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, Finset.mem_union] at hXG
    simp only [joinCtxOr, Finset.mem_union]
    rcases hXG with h | h
    · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
        ⟨j, Finset.mem_filter.mpr ⟨hj, (Finset.mem_filter.mp h).2⟩⟩)))
    · exact Or.inl (Or.inr (mem_unionAll.mpr
        ⟨j, Finset.mem_filter.mpr ⟨hj, (Finset.mem_filter.mp h).2⟩⟩))
  · push_neg at hin
    have hallTh : ∀ j, X ∈ th j :=
      fun j => (Finset.mem_union.mp (hs2 j hX)).resolve_left (hin j)
    have hXG := lamStar_subset_gHat hX
    simp only [gHat, Finset.mem_union] at hXG
    simp only [joinCtxOr, Finset.mem_union]
    rcases hXG with h | h
    · exact Or.inl (Or.inl (Or.inr (mem_interAll.mpr (fun j =>
        Finset.mem_filter.mpr ⟨hallTh j, (Finset.mem_filter.mp h).2⟩))))
    · refine Or.inr ?_
      have himp : X.isImp := (Finset.mem_filter.mp h).2
      match X, himp with
      | .imp A B, _ =>
          refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
            Finset.mem_filter.mpr ⟨hallTh j, trivial⟩), ?_⟩
          rw [hf, hU]
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (mem_upsPrime hX))


/-- The two halves of Lemma 6.4 (existence part), indexed by `t`:
`t = 0` is the irregular half, `t ≠ 0` the regular one. -/
def MinModStmt (K : Kripke) (G : Form) (a : K.W) (t : Nat) (C : Form) : Prop :=
  match t with
  | 0 => ∃ St Th : Finset Form, Nonempty (FRJi G St Th C) ∧
           St ⊆ lamStar K a G ∧ lamStar K a G ⊆ St ∪ Th
  | _ => ∃ Γ : Finset Form, Nonempty (FRJr G Γ C) ∧
           ∃ b : K.W, K.le a b ∧ lamStar K b G ⊆ Γ

/-- The `Ax^I` zone contains `Λ*_a` whenever `C` is unforced there. -/
theorem lamStar_subset_axI {K : Kripke} {a : K.W} {G C : Form}
    (h : ¬ K.force a C) :
    lamStar K a G ⊆ ((gAt G).erase C ∪ gImp G) := by
  intro X hX
  have hne : X ≠ C := by
    intro hc; exact h (hc ▸ K.forceStar_force (mem_lamStar.mp hX).2)
  have := lamStar_subset_gHat hX
  simp only [gHat, Finset.mem_union] at this
  rcases this with h1 | h1
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, h1⟩)
  · exact Finset.mem_union_right _ h1

theorem minMod (K : Kripke) (G : Form) (a : K.W) (t : Nat) (C : Form)
    (hC : C ∈ sfR G) (hnf : ¬ K.force a C) : MinModStmt K G a t C := by
  match t, C with
  | 0, .atom p =>
      exact ⟨∅, (gAt G).erase (.atom p) ∪ gImp G, ⟨.axI (.atom p) trivial hC⟩,
        Finset.empty_subset _, by simpa using lamStar_subset_axI hnf⟩
  | 0, .bot =>
      exact ⟨∅, (gAt G).erase .bot ∪ gImp G, ⟨.axI .bot trivial hC⟩,
        Finset.empty_subset _, by simpa using lamStar_subset_axI hnf⟩
  | 0, .and C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_and hC
      by_cases h1 : K.force a C₁
      · have h2 : ¬ K.force a C₂ := fun hc => hnf ⟨h1, hc⟩
        obtain ⟨St, Th, ⟨d⟩, hs1, hs2⟩ := minMod K G a 0 C₂ hC2 h2
        exact ⟨St, Th, ⟨.andI2 d hC⟩, hs1, hs2⟩
      · obtain ⟨St, Th, ⟨d⟩, hs1, hs2⟩ := minMod K G a 0 C₁ hC1 h1
        exact ⟨St, Th, ⟨.andI1 d hC⟩, hs1, hs2⟩
  | 0, .or C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_or hC
      have h1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
      have h2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
      obtain ⟨St₁, Th₁, ⟨d₁⟩, hs1, hs2⟩ := minMod K G a 0 C₁ hC1 h1
      obtain ⟨St₂, Th₂, ⟨d₂⟩, hu1, hu2⟩ := minMod K G a 0 C₂ hC2 h2
      refine ⟨St₁ ∪ St₂, Th₁ ∩ Th₂, ⟨.orI d₁ d₂ (fun X hX => hu2 (hs1 hX))
        (fun X hX => hs2 (hu1 hX)) hC⟩, Finset.union_subset hs1 hu1, ?_⟩
      intro X hX
      by_cases hx1 : X ∈ St₁
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx1)
      · by_cases hx2 : X ∈ St₂
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx2)
        · have m1 := Finset.mem_union.mp (hs2 hX)
          have m2 := Finset.mem_union.mp (hu2 hX)
          exact Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨m1.resolve_left hx1, m2.resolve_left hx2⟩)
  | 0, .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      obtain ⟨e, hae, heA, heB, hmin⟩ := exists_min_eta hnf
      by_cases hea : e = a
      · rw [hea] at heA heB
        obtain ⟨St1, Th1, ⟨d⟩, hs1, hs2⟩ := minMod K G a 0 B hB heB
        have hLsub : (lamStar K a G) \ St1 ⊆ Th1 := by
          intro X hX
          obtain ⟨hXl, hXs⟩ := Finset.mem_sdiff.mp hX
          exact (Finset.mem_union.mp (hs2 hXl)).resolve_left hXs
        have hTh1 : Th1 \ ((lamStar K a G) \ St1) ∪ ((lamStar K a G) \ St1) = Th1 :=
          Finset.sdiff_union_of_subset hLsub
        have hStL : St1 ∪ ((lamStar K a G) \ St1) = lamStar K a G := by
          ext X
          simp only [Finset.mem_union, Finset.mem_sdiff]
          constructor
          · rintro (h | ⟨h, -⟩)
            · exact hs1 h
            · exact h
          · intro h
            by_cases hx : X ∈ St1
            · exact Or.inl hx
            · exact Or.inr ⟨h, hx⟩
        have d' : FRJi G St1 ((Th1 \ ((lamStar K a G) \ St1)) ∪
            ((lamStar K a G) \ St1)) B := by rw [hTh1]; exact d
        refine ⟨St1 ∪ ((lamStar K a G) \ St1), Th1 \ ((lamStar K a G) \ St1),
          ⟨.impInI d' ?_ ?_ hC⟩, ?_, ?_⟩
        · exact Finset.sdiff_inter_self _ _
        · rw [hStL]; exact mem_clo_lamStar hA heA
        · rw [hStL]
        · rw [hStL]; exact Finset.subset_union_left
      · have hnaA : ¬ K.force a A := hmin a (K.le_refl a) hae (fun hc => hea hc.symm)
        obtain ⟨Γ, ⟨dr⟩, b, heb, hbΓ⟩ := minMod K G e 1 B hB heB
        have hab : K.le a b := K.le_trans hae heb
        have hAG : Clo Γ A :=
          clo_mono hbΓ (mem_clo_lamStar hA (K.force_mono heb heA))
        refine ⟨∅, lamStar K a G, ⟨.impNotIn dr (fun X hX => ⟨?_, lamStar_subset_gHat hX⟩)
          hAG (fun hc => hnaA (forces_clo_lamStar hc)) hC⟩,
          Finset.empty_subset _, by simp⟩
        exact clo_mono hbΓ (lamStar_mono hab X hX)
  | (n+1), .atom p =>
      by_cases hempty : impPart (lamStar K a G) = ∅
      · exact regPrime_ax K G a (.atom p) trivial hC hnf hempty
      · exact regPrime_join K G a (.atom p) trivial hC hnf
          (by
            obtain ⟨X, hX⟩ := Finset.nonempty_of_ne_empty hempty
            obtain ⟨hXl, hXi⟩ := Finset.mem_filter.mp hX
            match X, hXi with
            | .imp A B, _ => exact ⟨A, mem_upsPrime hXl⟩)
          (fun A hA hnA => minMod K G a 0 A hA hnA)
  | (n+1), .bot =>
      by_cases hempty : impPart (lamStar K a G) = ∅
      · exact regPrime_ax K G a .bot trivial hC hnf hempty
      · exact regPrime_join K G a .bot trivial hC hnf
          (by
            obtain ⟨X, hX⟩ := Finset.nonempty_of_ne_empty hempty
            obtain ⟨hXl, hXi⟩ := Finset.mem_filter.mp hX
            match X, hXi with
            | .imp A B, _ => exact ⟨A, mem_upsPrime hXl⟩)
          (fun A hA hnA => minMod K G a 0 A hA hnA)
  | (n+1), .and C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_and hC
      by_cases h1 : K.force a C₁
      · have h2 : ¬ K.force a C₂ := fun hc => hnf ⟨h1, hc⟩
        obtain ⟨Γ, ⟨d⟩, b, hab, hbΓ⟩ := minMod K G a (n+1) C₂ hC2 h2
        exact ⟨Γ, ⟨.andR2 d hC⟩, b, hab, hbΓ⟩
      · obtain ⟨Γ, ⟨d⟩, b, hab, hbΓ⟩ := minMod K G a (n+1) C₁ hC1 h1
        exact ⟨Γ, ⟨.andR1 d hC⟩, b, hab, hbΓ⟩
  | (n+1), .or C₁ C₂ =>
      exact regOr_join K G a C₁ C₂ hC hnf (fun A hA hnA => minMod K G a 0 A hA hnA)
  | (n+1), .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      obtain ⟨e, hae, heA, heB, -⟩ := exists_min_eta hnf
      by_cases hea : e = a
      · rw [hea] at heA heB
        obtain ⟨Γ, ⟨dr⟩, b, heb, hbΓ⟩ := minMod K G a (n+1) B hB heB
        exact ⟨Γ, ⟨.impIn dr (clo_mono hbΓ
          (mem_clo_lamStar hA (K.force_mono heb heA))) hC⟩, b, heb, hbΓ⟩
      · obtain ⟨Γ, ⟨dr⟩, b, heb, hbΓ⟩ := minMod K G e 1 B hB heB
        exact ⟨Γ, ⟨.impIn dr (clo_mono hbΓ
          (mem_clo_lamStar hA (K.force_mono heb heA))) hC⟩, b,
          K.le_trans hae heb, hbΓ⟩
termination_by (ht K a, t, C.size)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left
         exact ht_lt hae hea)
      | (apply Prod.Lex.right
         apply Prod.Lex.left
         omega)
      | (apply Prod.Lex.right
         apply Prod.Lex.right
         first
           | omega
           | (simp only [Form.size]; omega))

/-! ## Theorem 6.3 (Completeness) and the biconditional -/

/-- **Completeness of `FRJ(G)`** (Theorem 6.2(i) / `theo:minMod`'s
corollary): `G ∉ IPL` implies `⊢_{FRJ(G)} G`.  Apply Lemma 6.4 at the
root of a countermodel, in the regular half, with goal `G`. -/
theorem completeness {G : Form} (h : ¬ IPL G) : Provable G := by
  simp only [IPL, not_forall] at h
  obtain ⟨K, hK⟩ := h
  obtain ⟨Γ, hd, -⟩ := minMod K G K.root 1 G (sfR_self G) hK
  exact ⟨Γ, hd⟩

/-- **The biconditional.**  `FRJ(G)` proves `G` exactly when `G` is not
intuitionistically valid: soundness (Theorem 3.1) and completeness
(Theorem 6.2) together. -/
theorem frj_iff_not_IPL (G : Form) : Provable G ↔ ¬ IPL G :=
  ⟨soundness, completeness⟩
