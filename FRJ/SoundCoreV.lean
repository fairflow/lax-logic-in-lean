import FRJ.SoundCore
import FRJ.CalculusVLemmas
import FRJ.ExtractV

/-!
# The join cases the V and W calculi share

`FRJ/SoundCore.lean` holds the five join cases all three calculi share.  Two
more — `joinAt` and `joinOr` — are shared by `FRJVr` and `FRJWr` only: both
carry the `kept` zone and a `KeptChain`, which `FRJr` has no analogue of, so
`FRJ/Sound.lean`'s versions are a different proof and stay where they are.

They live here rather than in `SoundCore` because they speak of `KeptChain`,
`RefAt` and `joinCtxAtVBase`, which arrive with `FRJ.RefAt` and `FRJ.CalculusV`
— modules `FRJ/Sound.lean` does not import and should not have to.
-/

namespace FRJ

open Form

/-- The `joinAt` case of soundness for the V and W calculi, for any family of component pre-models. -/
theorem joinAt_core {G : Form} {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {kept : List Form} {F : Form}
    {Idx : Fin (n + 1) → Type} [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    {elems : List ((j : Fin (n + 1)) × Idx j)} {hcomplete : ∀ ji, ji ∈ elems}
    {Ms : (j : Fin (n + 1)) → Idx j → PreModel}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (Ξs j)) = [])
    (hkc : KeptChain (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs) kept)
    (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (Ξs j)))
    (hMC : ∀ j i, ClosedLbl (Ms j i))
    (hwfR : (joinCtxAtVBase Ξs Θs F) ⊆ gHat G)
    (hwfI : ∀ j, Ξs j ++ Θs j ⊆ gHat G)
    (hlhs : ∀ j, ∀ X ∈ (joinCtxAtVBase Ξs Θs F ++ kept), Clo (Ξs j ++ Θs j) X)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : Idx j) (x : (Ms j i).W),
        ((Ms j i).toKripke (hMC j i)).forces x ((Ms j i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (Q : PreModel) (hQ : ClosedLbl Q) (w : Q.W),
        ¬ Q.fal w →
        (∀ X ∈ Q.lbl w, Clo (Ξs j ++ Θs j) X) →
        (∀ i : Idx j, RootAbove Q hQ w (Ms j i) (hMC j i)) →
        (Q.toKripke hQ).forces w (cap (Ξs j) (sfm (rhs j))) →
        ¬ (Q.toKripke hQ).force w (rhs j))
    (hP : ClosedLbl (joinIModel elems hcomplete (joinCtxAtVBase Ξs Θs F ++ kept) Ms)) :
    let P := joinIModel elems hcomplete (joinCtxAtVBase Ξs Θs F ++ kept) Ms
    (∀ w, (P.toKripke hP).forces w (P.lbl w)) ∧
      ¬ (P.toKripke hP).force P.root F := by
  intro P
  -- every component world forces its own label
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × Idx j)
      (x : (Ms ji.1 ji.2).W) (A : Form),
      A ∈ (Ms ji.1 ji.2).lbl x →
      (P.toKripke hP).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hP (hMC ji.1 ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  -- (P2) and (P3) over the BASE context, by the secondary induction on
  -- `size H`
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxAtVBase Ξs Θs F) →
        (P.toKripke hP).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (P.toKripke hP).force none H) := by
    intro k
    induction k with
    | zero => intro H hH; exfalso; cases H <;> simp [Form.size] at hH
    | succ k ih =>
        intro H hH
        constructor
        · -- (P2)
          intro hHimp
          obtain ⟨hHmem, hHsh⟩ := List.mem_filter.mp hHimp
          match H, hHsh with
          | .imp A B, _ =>
              have hAu : A ∈ upsilon rhs := baseAtV_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ k := by
                simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some jx =>
                  obtain ⟨ji, x⟩ := jx
                  have hlblv : ∀ Y ∈ (Ms ji.1 ji.2).lbl x,
                      (P.toKripke hP).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hmem : Form.imp A B ∈ (P).lbl none :=
                    List.mem_append_left _ hHmem
                  have hclo := hP none (some ⟨ji, x⟩) hv (.imp A B) hmem
                  have : (P.toKripke hP).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact this _ ((P.toKripke hP).le_refl _) hAv
        · -- (P3)
          intro j hj hcon
          refine ihI j (P) hP none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact hlhs j
          · intro i
            refine ⟨some ⟨⟨j, i⟩, (Ms j i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hP (hMC j i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := hwfI j (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  rcases stab_mem_baseAtV (G := G) (th := Θs) (F := F)
                    hcirc hK.1 hKG with hb | hb
                  · exact Or.inl (List.mem_append_left _ hb)
                  · exact absurd (hb ▸ (mem_unionAll.mpr
                      ⟨j, List.mem_filter.mpr
                        ⟨hK.1, (List.mem_filter.mp h).2⟩⟩)) hFnot
            · have hbase : K ∈ joinCtxAtVBase Ξs Θs F := by
                rcases stab_mem_baseAtV (G := G) (th := Θs) (F := F)
                  hcirc hK.1 hKG with hb | hb
                · exact hb
                · exact absurd (hb ▸ (List.mem_filter.mp h).2)
                    (prime_not_isImp hF)
              have hmem : K ∈ impPart (joinCtxAtVBase Ξs Θs F) :=
                List.mem_filter.mpr ⟨hbase, (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ k := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · exfalso
              have : K ∈ unionAll (fun j => circPart (Ξs j)) := mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hK.1, (List.mem_filter.mp h).2⟩⟩
              rw [hcirc] at this
              exact List.not_mem_nil this
  -- the base zone is forced at the root
  have base_forced : ∀ X ∈ joinCtxAtVBase Ξs Θs F,
      (P.toKripke hP).force none X := by
    intro X hX
    have hXG : X ∈ gHat G := hwfR hX
    simp only [gHat, List.mem_append] at hXG
    rcases hXG with (h | h) | h
    · have hpv : X.isPV := (List.mem_filter.mp h).2
      match X, hpv with
      | .atom p, _ => exact Or.inl (List.mem_append_left _ hX)
    · have himp : X.isImp := (List.mem_filter.mp h).2
      exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
    · have hcx : X.isCirc := (List.mem_filter.mp h).2
      match X, hcx with
      | .circ Y, _ => exact absurd hX circ_not_mem_baseAtV
  -- the four `refAt_refutes` invariants at the root
  have hups : ∀ C ∈ upsilon rhs, ¬ (P.toKripke hP).force none C := by
    intro C hC
    obtain ⟨j, -, hj⟩ := List.mem_map.mp hC
    exact (key C.size C (Nat.le_refl _)).2 j hj
  have hcone : ∀ c, (P.toKripke hP).Rm none c → c = none := by
    intro c hc
    have hc' : (PreModel.join (elems) (hcomplete)
        (joinCtxAtVBase Ξs Θs F ++ kept)
        (fun (ji : (j : Fin (n + 1)) × Idx j) => Ms ji.1 ji.2)
        (fun _ => false)).rm none c := hc
    exact PreModel.join_rm_root_barren (fun _ => rfl) hc'
  -- the kept zone is forced at the root, by induction on its chain
  -- certificate: each link's antecedent is `RefAt`-refuted over the
  -- base plus the earlier links
  have kept_forced : ∀ (ks : List Form),
      KeptChain (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs) ks →
      (∀ K ∈ ks, K ∈ kept) →
      ∀ K ∈ ks, (P.toKripke hP).force none K := by
    intro ks hks
    induction hks with
    | nil => intro _ K hK; exact absurd hK List.not_mem_nil
    | @cons Y B rest hrest hpool hY ih =>
        intro hsub K hK
        rcases List.mem_cons.mp hK with heq | hKmem
        · subst heq
          intro v hv hYv
          cases v with
          | none =>
              -- the root itself: the antecedent is refuted
              exact absurd hYv (refAt_refutes hups
                (fun X hX => (List.mem_append.mp hX).elim (base_forced X)
                  (fun hX' => ih
                    (fun K' hK' => hsub K' (List.mem_cons_of_mem _ hK')) X hX'))
                hcone (fun h => h) hY)
          | some jx =>
              -- above the root: (P2)'s above-root mechanism
              obtain ⟨ji, x⟩ := jx
              have hmem : Form.imp Y B ∈ (P).lbl none :=
                List.mem_append_right _ (hsub _ List.mem_cons_self)
              have hclo := hP none (some ⟨ji, x⟩) hv (.imp Y B) hmem
              exact clo_forces (fun X hX => hcomp ji x X hX) hclo _
                ((P.toKripke hP).le_refl _) hYv
        · exact ih (fun K' hK' => hsub K' (List.mem_cons_of_mem _ hK')) K hKmem
  -- assemble
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        rcases List.mem_append.mp hX with hX | hX
        · exact base_forced X hX
        · exact kept_forced kept hkc (fun _ h => h) X hX
    | some jx =>
        obtain ⟨ji, x⟩ := jx
        intro X hX
        exact hcomp ji x X hX
  · refine not_force_prime hP hF ?_ (fun h => h)
    intro hmem0
    have hmem : F ∈ joinCtxAtVBase Ξs Θs F ++ kept := hmem0
    exact prime_not_mem_ctxAtV hkc hF hFnot hmem

/-- The `joinOr` case of soundness for the V and W calculi, for any family of component pre-models. -/
theorem joinOr_core {G : Form} {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {kept : List Form} {C₁ C₂ : Form}
    {Idx : Fin (n + 1) → Type} [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    {elems : List ((j : Fin (n + 1)) × Idx j)} {hcomplete : ∀ ji, ji ∈ elems}
    {Ms : (j : Fin (n + 1)) → Idx j → PreModel}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (Ξs j)) = [])
    (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs) kept)
    (hC : RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++ kept) C₁ ∧
      RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++ kept) C₂)
    (hMC : ∀ j i, ClosedLbl (Ms j i))
    (hwfR : (joinCtxOrVBase Ξs Θs) ⊆ gHat G)
    (hwfI : ∀ j, Ξs j ++ Θs j ⊆ gHat G)
    (hlhs : ∀ j, ∀ X ∈ (joinCtxOrVBase Ξs Θs ++ kept), Clo (Ξs j ++ Θs j) X)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : Idx j) (x : (Ms j i).W),
        ((Ms j i).toKripke (hMC j i)).forces x ((Ms j i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (Q : PreModel) (hQ : ClosedLbl Q) (w : Q.W),
        ¬ Q.fal w →
        (∀ X ∈ Q.lbl w, Clo (Ξs j ++ Θs j) X) →
        (∀ i : Idx j, RootAbove Q hQ w (Ms j i) (hMC j i)) →
        (Q.toKripke hQ).forces w (cap (Ξs j) (sfm (rhs j))) →
        ¬ (Q.toKripke hQ).force w (rhs j))
    (hP : ClosedLbl (joinIModel elems hcomplete (joinCtxOrVBase Ξs Θs ++ kept) Ms)) :
    let P := joinIModel elems hcomplete (joinCtxOrVBase Ξs Θs ++ kept) Ms
    (∀ w, (P.toKripke hP).forces w (P.lbl w)) ∧
      ¬ (P.toKripke hP).force P.root (.or C₁ C₂) := by
  intro P
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × Idx j)
      (x : (Ms ji.1 ji.2).W) (A : Form),
      A ∈ (Ms ji.1 ji.2).lbl x →
      (P.toKripke hP).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hP (hMC ji.1 ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxOrVBase Ξs Θs) →
        (P.toKripke hP).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (P.toKripke hP).force none H) := by
    intro k
    induction k with
    | zero => intro H hH; exfalso; cases H <;> simp [Form.size] at hH
    | succ k ih =>
        intro H hH
        constructor
        · intro hHimp
          obtain ⟨hHmem, hHsh⟩ := List.mem_filter.mp hHimp
          match H, hHsh with
          | .imp A B, _ =>
              have hAu : A ∈ upsilon rhs := baseOrV_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ k := by simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some jx =>
                  obtain ⟨ji, x⟩ := jx
                  have hlblv : ∀ Y ∈ (Ms ji.1 ji.2).lbl x,
                      (P.toKripke hP).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hmem : Form.imp A B ∈ (P).lbl none :=
                    List.mem_append_left _ hHmem
                  have hclo := hP none (some ⟨ji, x⟩) hv (.imp A B) hmem
                  have hfv : (P.toKripke hP).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact hfv _ ((P.toKripke hP).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (P) hP none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact hlhs j
          · intro i
            refine ⟨some ⟨⟨j, i⟩, (Ms j i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hP (hMC j i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := hwfI j (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  exact Or.inl (List.mem_append_left _
                    (stab_mem_baseOrV (G := G) (th := Θs) hcirc hK.1 hKG))
            · have hmem : K ∈ impPart (joinCtxOrVBase Ξs Θs) :=
                List.mem_filter.mpr
                  ⟨stab_mem_baseOrV (G := G) (th := Θs) hcirc hK.1 hKG,
                    (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ k := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · exfalso
              have : K ∈ unionAll (fun j => circPart (Ξs j)) := mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hK.1, (List.mem_filter.mp h).2⟩⟩
              rw [hcirc] at this
              exact List.not_mem_nil this
  have base_forced : ∀ X ∈ joinCtxOrVBase Ξs Θs,
      (P.toKripke hP).force none X := by
    intro X hX
    have hXG : X ∈ gHat G := hwfR hX
    simp only [gHat, List.mem_append] at hXG
    rcases hXG with (h | h) | h
    · have hpv : X.isPV := (List.mem_filter.mp h).2
      match X, hpv with
      | .atom p, _ => exact Or.inl (List.mem_append_left _ hX)
    · have himp : X.isImp := (List.mem_filter.mp h).2
      exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
    · have hcx : X.isCirc := (List.mem_filter.mp h).2
      match X, hcx with
      | .circ Y, _ => exact absurd hX circ_not_mem_baseOrV
  have hups : ∀ C ∈ upsilon rhs, ¬ (P.toKripke hP).force none C := by
    intro C hC
    obtain ⟨j, -, hj⟩ := List.mem_map.mp hC
    exact (key C.size C (Nat.le_refl _)).2 j hj
  have hcone : ∀ c, (P.toKripke hP).Rm none c → c = none := by
    intro c hc
    have hc' : (PreModel.join (elems) (hcomplete)
        (joinCtxOrVBase Ξs Θs ++ kept)
        (fun (ji : (j : Fin (n + 1)) × Idx j) => Ms ji.1 ji.2)
        (fun _ => false)).rm none c := hc
    exact PreModel.join_rm_root_barren (fun _ => rfl) hc'
  have kept_forced : ∀ (ks : List Form),
      KeptChain (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs) ks →
      (∀ K ∈ ks, K ∈ kept) →
      ∀ K ∈ ks, (P.toKripke hP).force none K := by
    intro ks hks
    induction hks with
    | nil => intro _ K hK; exact absurd hK List.not_mem_nil
    | @cons Y B rest hrest hpool hY ih =>
        intro hsub K hK
        rcases List.mem_cons.mp hK with heq | hKmem
        · subst heq
          intro v hv hYv
          cases v with
          | none =>
              exact absurd hYv (refAt_refutes hups
                (fun X hX => (List.mem_append.mp hX).elim (base_forced X)
                  (fun hX' => ih
                    (fun K' hK' => hsub K' (List.mem_cons_of_mem _ hK')) X hX'))
                hcone (fun h => h) hY)
          | some jx =>
              obtain ⟨ji, x⟩ := jx
              have hmem : Form.imp Y B ∈ (P).lbl none :=
                List.mem_append_right _ (hsub _ List.mem_cons_self)
              have hclo := hP none (some ⟨ji, x⟩) hv (.imp Y B) hmem
              exact clo_forces (fun X hX => hcomp ji x X hX) hclo _
                ((P.toKripke hP).le_refl _) hYv
        · exact ih (fun K' hK' => hsub K' (List.mem_cons_of_mem _ hK')) K hKmem
  -- the whole conclusion label is forced at the root
  have hctxV : (P.toKripke hP).forces none (joinCtxOrVBase Ξs Θs ++ kept) :=
    fun X hX => (List.mem_append.mp hX).elim (base_forced X)
      (kept_forced kept hkc (fun _ h => h) X)
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        exact hctxV X hX
    | some jx =>
        obtain ⟨ji, x⟩ := jx
        intro X hX
        exact hcomp ji x X hX
  · intro hcon
    rcases hcon with h | h
    · exact refAt_refutes hups hctxV hcone (fun h => h) hC.1 h
    · exact refAt_refutes hups hctxV hcone (fun h => h) hC.2 h

end FRJ
