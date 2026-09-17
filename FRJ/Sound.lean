/-
# Lemma 3.9 and the soundness of FRJ(G)

The appendix "Soundness of FRJ(G)" of Fiorentini–Ferrari, case by case.

Lemma 3.9 reads, for every sequent `σ` occurring in `D`:

  (i)  if `σ = Γ ⇒ C`, then `φ(σ) ⊩ Γ` and `φ(σ) ⊮ C`;
  (ii) if `σ = Σ;Θ → C`, let `σ_p ∈ PS(D)` with `σ ↦ σ_p` and
       `σ_p ⊩ Σ ∩ Sf⁻(C)`; then `σ_p ⊮ C`.

The main induction is on the height of `σ` in `D`.  Height decreases
going UP, and every application of the induction hypothesis in the proof
is at an occurrence inside `σ`'s own subtree — in the join case (P2) at a
`σ_p` with `σ ≤ σ_p`, which by the model order means `σ_p ↦* σ` — so the
induction is structural on the derivation.

Below, (i) is split in two: `lemma39R` gives it at `d`'s own root
sequent, where `φ(σ)` is the model's root, and its first component gives
it at p-sequents ("every world forces its own label"), which is what the
join case consumes at worlds above itself.  In (ii) the world `σ_p` lies
BELOW `σ`, outside `d`; the paper may name it because it has fixed `D`
once and for all, and here it is quantified — which is what the paper's
own statement already does.
-/
import FRJ.SoundCore

namespace FRJ

open Form

theorem joinAt_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
    (hg : F ∈ sfR G)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : RegIdx (prem j)) (x : (preI (prem j) i).W),
        ((preI (prem j) i).toKripke (preI_closed (prem j) i)).forces x
          ((preI (prem j) i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
        ¬ P.fal w →
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j))
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAt stab th rhs F) :
    let d := FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root F := by
  intro d
  have hPJ : ClosedLbl (preR d) :=
    preR_closed _
  -- every component world forces its own label
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR d).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (preI_closed (prem ji.1) ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  -- (P2) and (P3), by the secondary induction on `size H`
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxAt stab th rhs F) →
        (modR d).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR d).force none H) := by
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
              have hAu : A ∈ upsilon rhs := joinCtxAt_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ k := by
                simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some jx =>
                  obtain ⟨ji, x⟩ := jx
                  have hlblv : ∀ Y ∈ (preI (prem ji.1) ji.2).lbl x,
                      (modR d).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hHmem
                  have : (modR d).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact this _ ((modR d).le_refl _) hAv
        · -- (P3)
          intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single ⟨_, Step.joinAt (G := G) (F := F) j hJ1 (CtxEq.refl _)⟩)
          · intro i
            refine ⟨some ⟨⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  exact Or.inl (stab_mem_joinCtxAt (G := G) hcirc hK.1 hKG)
            · have hmem : K ∈ impPart (joinCtxAt stab th rhs F) :=
                List.mem_filter.mpr
                  ⟨stab_mem_joinCtxAt (G := G) hcirc hK.1 hKG, (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ k := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · exfalso
              have : K ∈ unionAll (fun j => circPart (stab j)) := mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hK.1, (List.mem_filter.mp h).2⟩⟩
              rw [hcirc] at this
              exact List.not_mem_nil this
  -- assemble
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        have hXG : X ∈ gHat G := wfR d ((hΓ X).mpr hX)
        simp only [gHat, List.mem_append] at hXG
        rcases hXG with (h | h) | h
        · have : X.isPV := (List.mem_filter.mp h).2
          match X, this with
          | .atom p, _ => exact Or.inl hX
        · have himp : X.isImp := (List.mem_filter.mp h).2
          exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
        · have : X.isCirc := (List.mem_filter.mp h).2
          match X, this with
          | .circ Y, _ => exact absurd hX circ_not_mem_joinCtxAt
    | some jx =>
        obtain ⟨ji, x⟩ := jx
        intro X hX
        exact hcomp ji x X hX
  · refine not_force_prime hPJ hF ?_ (fun h => h)
    intro hmem0
    have hmem : F ∈ joinCtxAt stab th rhs F := hmem0
    simp only [joinCtxAt, List.mem_append] at hmem
    rcases hmem with ((h | h) | h) | h
    · exact hFnot h
    · exact (mem_rm.mp h).1 rfl
    · obtain ⟨i, hi⟩ := mem_unionAll.mp h
      exact prime_not_isImp hF (List.mem_filter.mp hi).2
    · exact prime_not_isImp hF
        (List.mem_filter.mp (interAll_subset 0 (restrict_subset h))).2

theorem joinOr_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
    (hg : Form.or C₁ C₂ ∈ sfR G)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : RegIdx (prem j)) (x : (preI (prem j) i).W),
        ((preI (prem j) i).toKripke (preI_closed (prem j) i)).forces x
          ((preI (prem j) i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
        ¬ P.fal w →
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j))
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOr stab th rhs) :
    let d := FRJr.joinOr prem hJ1 hJ2 hcirc hC hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root (.or C₁ C₂) := by
  intro d
  have hPJ : ClosedLbl (preR d) := preR_closed _
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR d).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (preI_closed (prem ji.1) ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxOr stab th rhs) →
        (modR d).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR d).force none H) := by
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
              have hAu : A ∈ upsilon rhs := joinCtxOr_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ k := by simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some jx =>
                  obtain ⟨ji, x⟩ := jx
                  have hlblv : ∀ Y ∈ (preI (prem ji.1) ji.2).lbl x,
                      (modR d).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hHmem
                  have hfv : (modR d).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact hfv _ ((modR d).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinOr (G := G) (C₁ := C₁) (C₂ := C₂) j hJ1 (CtxEq.refl _)⟩)
          · intro i
            refine ⟨some ⟨⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  exact Or.inl (stab_mem_joinCtxOr (G := G) hcirc hK.1 hKG)
            · have hmem : K ∈ impPart (joinCtxOr stab th rhs) :=
                List.mem_filter.mpr
                  ⟨stab_mem_joinCtxOr (G := G) hcirc hK.1 hKG, (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ k := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · exfalso
              have : K ∈ unionAll (fun j => circPart (stab j)) := mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hK.1, (List.mem_filter.mp h).2⟩⟩
              rw [hcirc] at this
              exact List.not_mem_nil this
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        have hXG : X ∈ gHat G := wfR d ((hΓ X).mpr hX)
        simp only [gHat, List.mem_append] at hXG
        rcases hXG with (h | h) | h
        · have hpv : X.isPV := (List.mem_filter.mp h).2
          match X, hpv with
          | .atom p, _ => exact Or.inl hX
        · have himp : X.isImp := (List.mem_filter.mp h).2
          exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
        · have : X.isCirc := (List.mem_filter.mp h).2
          match X, this with
          | .circ Y, _ => exact absurd hX circ_not_mem_joinCtxOr
    | some jx =>
        obtain ⟨ji, x⟩ := jx
        intro X hX
        exact hcomp ji x X hX
  · intro hcon
    obtain ⟨j₁, -, hj₁⟩ := List.mem_map.mp hC.1
    obtain ⟨j₂, -, hj₂⟩ := List.mem_map.mp hC.2
    rcases hcon with h | h
    · exact (key C₁.size C₁ (Nat.le_refl _)).2 j₁ hj₁ h
    · exact (key C₂.size C₂ (Nat.le_refl _)).2 j₂ hj₂ h


theorem joinAtP_case {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {t' : Tag}
    {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
    (dps : ∀ i, FRJr G (tps i) (Δs i) (Ds i))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (hJ7 : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
    (htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0))))
    (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
    (hg : F ∈ sfR G)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : RegIdx (prem j)) (x : (preI (prem j) i).W),
        ((preI (prem j) i).toKripke (preI_closed (prem j) i)).forces x
          ((preI (prem j) i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
        ¬ P.fal w →
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j))
    (ihP : ∀ i, (∀ w, (modR (dps i)).forces w ((preR (dps i)).lbl w)) ∧
        ¬ (modR (dps i)).force (modR (dps i)).root (Ds i))
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtP stab th rhs F Δs) :
    let d := FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root F := by
  intro d
  exact joinAtP_core (Ms := fun j i => preI (prem j) i) (Ns := fun i => preR (dps i))
    (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
    hJ2 hJ5 hJ7 hF hFnot
    (fun j i => preI_closed (prem j) i) (fun i => preR_closed (dps i))
    (fun i => preR_root_lbl (dps i))
    (fun {X} hX => wfR d ((hΓ X).mpr hX))
    (fun j => wfI (prem j))
    (fun j => lhs_clo_of_steps
      (Relation.ReflTransGen.single
        ⟨_, Step.joinAtP (G := G) (F := F) (Δs := Δs) j hJ1 (CtxEq.refl _)⟩))
    ihI0 ihI ihP (preR_closed d)

theorem joinAtF_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
    (hg : F ∈ sfR G)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : RegIdx (prem j)) (x : (preI (prem j) i).W),
        ((preI (prem j) i).toKripke (preI_closed (prem j) i)).forces x
          ((preI (prem j) i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
        ¬ P.fal w →
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j))
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtF stab th rhs F) :
    let d := FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root F := by
  intro d
  exact joinAtF_core (Ms := fun j i => preI (prem j) i)
    (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
    hJ2 hF hFnot
    (fun j i => preI_closed (prem j) i)
    (fun {X} hX => wfR d ((hΓ X).mpr hX))
    (fun j => wfI (prem j))
    (fun j => lhs_clo_of_steps
      (Relation.ReflTransGen.single
        ⟨_, Step.joinAtF (G := G) (F := F) j hJ1 (CtxEq.refl _)⟩))
    ihI0 ihI (preR_closed d)

theorem joinOrP_case {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {t' : Tag}
    {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
    (dps : ∀ i, FRJr G (tps i) (Δs i) (Ds i))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (hJ7 : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
    (htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0))))
    (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
    (hg : Form.or C₁ C₂ ∈ sfR G)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : RegIdx (prem j)) (x : (preI (prem j) i).W),
        ((preI (prem j) i).toKripke (preI_closed (prem j) i)).forces x
          ((preI (prem j) i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
        ¬ P.fal w →
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j))
    (ihP : ∀ i, (∀ w, (modR (dps i)).forces w ((preR (dps i)).lbl w)) ∧
        ¬ (modR (dps i)).force (modR (dps i)).root (Ds i))
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrP stab th rhs Δs) :
    let d := FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root (.or C₁ C₂) := by
  intro d
  exact joinOrP_core (Ms := fun j i => preI (prem j) i) (Ns := fun i => preR (dps i))
    (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
    hJ2 hJ5 hJ7 hC
    (fun j i => preI_closed (prem j) i) (fun i => preR_closed (dps i))
    (fun i => preR_root_lbl (dps i))
    (fun {X} hX => wfR d ((hΓ X).mpr hX))
    (fun j => wfI (prem j))
    (fun j => lhs_clo_of_steps
      (Relation.ReflTransGen.single
        ⟨_, Step.joinOrP (G := G) (C₁ := C₁) (C₂ := C₂) (Δs := Δs) j hJ1 (CtxEq.refl _)⟩))
    ihI0 ihI ihP (preR_closed d)

theorem joinOrF_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
    (hg : Form.or C₁ C₂ ∈ sfR G)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : RegIdx (prem j)) (x : (preI (prem j) i).W),
        ((preI (prem j) i).toKripke (preI_closed (prem j) i)).forces x
          ((preI (prem j) i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
        ¬ P.fal w →
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j))
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrF stab th rhs) :
    let d := FRJr.joinOrF prem hJ1 hJ2 hC hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root (.or C₁ C₂) := by
  intro d
  exact joinOrF_core (Ms := fun j i => preI (prem j) i)
    (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
    hJ2 hC
    (fun j i => preI_closed (prem j) i)
    (fun {X} hX => wfR d ((hΓ X).mpr hX))
    (fun j => wfI (prem j))
    (fun j => lhs_clo_of_steps
      (Relation.ReflTransGen.single
        ⟨_, Step.joinOrF (G := G) (C₁ := C₁) (C₂ := C₂) j hJ1 (CtxEq.refl _)⟩))
    ihI0 ihI (preR_closed d)

/-- `⋈^◯`, the barren modal join: the label-forcing machinery is `⋈^∨`'s
verbatim; the root refutes `◯Z` because its modal cone is itself and it
refutes `Z` through the premise slot with `rhs j = Z` — the (P3)
mechanism, which is what `◯∈` cannot supply for compound `Z` at roots
not forcing the antecedent. -/
theorem joinCirc_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Z : Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hZ : Z ∈ upsilon rhs)
    (hg : Form.circ Z ∈ sfR G)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : RegIdx (prem j)) (x : (preI (prem j) i).W),
        ((preI (prem j) i).toKripke (preI_closed (prem j) i)).forces x
          ((preI (prem j) i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
        ¬ P.fal w →
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j))
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOr stab th rhs) :
    let d := FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root (.circ Z) := by
  intro d
  have hPJ : ClosedLbl (preR d) := preR_closed _
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR d).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (preI_closed (prem ji.1) ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxOr stab th rhs) →
        (modR d).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR d).force none H) := by
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
              have hAu : A ∈ upsilon rhs := joinCtxOr_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ k := by simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some jx =>
                  obtain ⟨ji, x⟩ := jx
                  have hlblv : ∀ Y ∈ (preI (prem ji.1) ji.2).lbl x,
                      (modR d).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hHmem
                  have hfv : (modR d).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact hfv _ ((modR d).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinCirc (G := G) (Z := Z) j hJ1 (CtxEq.refl _)⟩)
          · intro i
            refine ⟨some ⟨⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  exact Or.inl (stab_mem_joinCtxOr (G := G) hcirc hK.1 hKG)
            · have hmem : K ∈ impPart (joinCtxOr stab th rhs) :=
                List.mem_filter.mpr
                  ⟨stab_mem_joinCtxOr (G := G) hcirc hK.1 hKG, (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ k := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · exfalso
              have : K ∈ unionAll (fun j => circPart (stab j)) := mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hK.1, (List.mem_filter.mp h).2⟩⟩
              rw [hcirc] at this
              exact List.not_mem_nil this
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        have hXG : X ∈ gHat G := wfR d ((hΓ X).mpr hX)
        simp only [gHat, List.mem_append] at hXG
        rcases hXG with (h | h) | h
        · have hpv : X.isPV := (List.mem_filter.mp h).2
          match X, hpv with
          | .atom p, _ => exact Or.inl hX
        · have himp : X.isImp := (List.mem_filter.mp h).2
          exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
        · have : X.isCirc := (List.mem_filter.mp h).2
          match X, this with
          | .circ Y, _ => exact absurd hX circ_not_mem_joinCtxOr
    | some jx =>
        obtain ⟨ji, x⟩ := jx
        intro X hX
        exact hcomp ji x X hX
  · obtain ⟨j₀, -, hj₀⟩ := List.mem_map.mp hZ
    refine Kripke.not_force_circ _ ?_
    intro u hu hf
    have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxOr stab th rhs)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)).rm none u := hu
    have h0 := PreModel.join_rm_root_barren (fun _ => rfl) hu'
    rw [h0] at hf
    exact (key Z.size Z (Nat.le_refl _)).2 j₀ hj₀ hf


/-- `⋈^◯,p`, the promise modal join: label-forcing as `⋈^∨,p`; the root
refutes `◯Z` with the whole cone — itself through the premise slot, each
promise component through its right formula `Z` at the component root
(`ihP`) and its `Covers`-certified tag below it (`ihT` = `tag_cone`). -/
theorem joinCircP_case {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Z : Form}
    {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
    (dps : ∀ i, FRJr G (tps i) (Δs i) (Ds i))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (hJ7 : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
    (hDs : ∀ i, Ds i = Z ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z))
    (hZ : Z ∈ upsilon rhs)
    (hg : Form.circ Z ∈ sfR G)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : RegIdx (prem j)) (x : (preI (prem j) i).W),
        ((preI (prem j) i).toKripke (preI_closed (prem j) i)).forces x
          ((preI (prem j) i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
        ¬ P.fal w →
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j))
    (ihP : ∀ i, (∀ w, (modR (dps i)).forces w ((preR (dps i)).lbl w)) ∧
        ¬ (modR (dps i)).force (modR (dps i)).root (Ds i))
    (ihT : ∀ i (Z' : Form),
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z') →
        ∀ u, (modR (dps i)).Rm (modR (dps i)).root u →
          u ≠ (modR (dps i)).root → ¬ (modR (dps i)).force u Z')
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrP stab th rhs Δs) :
    let d := FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root (.circ Z) := by
  intro d
  exact joinCircP_core (Ms := fun j i => preI (prem j) i) (Ns := fun i => preR (dps i))
    (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
    hJ2 hJ5 hJ7 hDs hZ
    (fun j i => preI_closed (prem j) i) (fun i => preR_closed (dps i))
    (fun i => preR_root_lbl (dps i))
    (fun {X} hX => wfR d ((hΓ X).mpr hX))
    (fun j => wfI (prem j))
    (fun j => lhs_clo_of_steps
      (Relation.ReflTransGen.single
        ⟨_, Step.joinCircP (G := G) (Z := Z) (Δs := Δs) j hJ1 (CtxEq.refl _)⟩))
    ihI0 ihI ihP ihT (preR_closed d)

mutual

theorem lemma39R {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C),
    (∀ w : (preR d).W, (modR d).forces w ((preR d).lbl w)) ∧
      ¬ (modR d).force (modR d).root C
  | _, _, _, .axR F hF hg hΓ => by
      constructor
      · intro w X hX
        have hpv : X.isPV := by
          have hmem := rm_subset hX
          simpa [gAt] using (List.mem_filter.mp hmem).2
        match X, hpv with
        | .atom p, _ => exact Or.inl hX
      · match F, hF with
        | .bot, _ => exact fun h => h
        | .atom p, _ =>
            exact fun h => h.elim (fun h => (mem_rm.mp h).1 rfl) (fun h => h)
  | _, _, _, .andR1 d hg => by
      obtain ⟨ha, hb⟩ := lemma39R d
      exact ⟨ha, fun hcon => hb hcon.1⟩
  | _, _, _, .andR2 d hg => by
      obtain ⟨ha, hb⟩ := lemma39R d
      exact ⟨ha, fun hcon => hb hcon.2⟩
  | _, _, _, .impIn d hA hg => by
      obtain ⟨ha, hb⟩ := lemma39R d
      refine ⟨ha, fun hcon => hb ?_⟩
      have hlblr := ha (preR d).root
      exact hcon _ ((modR d).le_refl _)
        (clo_forces (fun X hX => hlblr X ((preR_root_lbl d X).mpr hX)) hA)
  | _, _, _, .circIn d htag hg => by
      -- `◯∈`: the model is the premise's; the root refutes `Z`
      -- (recursively) and its whole modal cone refutes `Z` (`tag_cone`,
      -- from the pledge the tag records), so `◯Z` fails at the root.
      obtain ⟨ha, hb⟩ := lemma39R d
      refine ⟨ha, ?_⟩
      refine Kripke.not_force_circ (modR d) ?_
      intro u hu hf
      by_cases hroot : u = (modR d).root
      · exact hb (hroot ▸ hf)
      · exact tag_cone d _ htag u hu hroot hf
  | _, _, _, @FRJr.joinAt _ n stab th rhs F prem hJ1 hJ2 hcirc hF hFnot hg _ hΓ =>
      joinAt_case prem hJ1 hJ2 hcirc hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg _ hΓ =>
      joinAtP_case prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i)) hΓ
  | _, _, _, @FRJr.joinAtF _ n stab th rhs F prem hJ1 hJ2 hF hFnot hg _ hΓ =>
      joinAtF_case prem hJ1 hJ2 hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJr.joinOr _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hcirc hC hg _ hΓ =>
      joinOr_case prem hJ1 hJ2 hcirc hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg _ hΓ =>
      joinOrP_case prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i)) hΓ
  | _, _, _, @FRJr.joinOrF _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hC hg _ hΓ =>
      joinOrF_case prem hJ1 hJ2 hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJr.joinCirc _ n stab th rhs Z prem hJ1 hJ2 hcirc hZ hg _ hΓ =>
      joinCirc_case prem hJ1 hJ2 hcirc hZ hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJr.joinCircP _ n k stab th rhs Z tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg _ hΓ =>
      joinCircP_case prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i))
        (fun i => tag_cone (dps i)) hΓ

/-- **The pledge is honoured.**  If the tag is `barren` or `chain Z`, every
world of the root's modal cone other than the root itself refutes `Z`: a
barren root has no such world, and a `chain Z` root's cone consists of
promise components whose goals are all `Z`, each root refuting its goal
(Lemma 3.9(i)) and each deeper cone refuting `Z` recursively.

This is the semantic content of the tag — the single-pledge form of the
canonical model's `mfal` component — and the soundness of `◯∈`. -/
theorem tag_cone {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C) (Z : Form),
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z) →
    ∀ u, (modR d).Rm (modR d).root u → u ≠ (modR d).root →
      ¬ (modR d).force u Z
  | _, _, _, .axR F hF hg hΓ, Z, ht, u, hu, hne, hf => hne rfl
  | _, _, _, .andR1 d _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .andR2 d _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .impIn d _ _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .circIn d _ _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, @FRJr.joinAt _ n stab th rhs F prem hJ1 hJ2 hcirc hF hFnot hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxAt stab th rhs F)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hPJ : ClosedLbl (preR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg hΓ)) :=
        preR_closed _
      rcases htag with h' | ⟨h', hall⟩
      · rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion (h'.symm.trans h)
      · rcases ht with h | ⟨W, h, hcov⟩
        · exact Tag.noConfusion (h'.symm.trans h)
        · have hDW : Ds 0 = W := by
            have hcc := h'.symm.trans h
            injection hcc
          subst hDW
          exact tagConeP_core (Ms := fun j i => preI (prem j) i)
            (Ns := fun i => preR (dps i))
            (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
            (fun i => preR_closed (dps i)) (fun i => preR_root_lbl (dps i))
            hcov hall (fun i => joinCtxAtP_clo i) hΓ.subset
            (fun i => lemma39R (dps i)) (fun i => tag_cone (dps i))
            hPJ u hu hne hf
  | _, _, _, .joinAtF prem hJ1 hJ2 hF hFnot hg hΓ, Z, ht, u, hu, hne, hf => by
      rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion h
  | _, _, _, @FRJr.joinOr _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hcirc hC hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxOr stab th rhs)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hPJ : ClosedLbl (preR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg hΓ)) :=
        preR_closed _
      rcases htag with h' | ⟨h', hall⟩
      · rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion (h'.symm.trans h)
      · rcases ht with h | ⟨W, h, hcov⟩
        · exact Tag.noConfusion (h'.symm.trans h)
        · have hDW : Ds 0 = W := by
            have hcc := h'.symm.trans h
            injection hcc
          subst hDW
          exact tagConeP_core (Ms := fun j i => preI (prem j) i)
            (Ns := fun i => preR (dps i))
            (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
            (fun i => preR_closed (dps i)) (fun i => preR_root_lbl (dps i))
            hcov hall (fun i => joinCtxOrP_clo i) hΓ.subset
            (fun i => lemma39R (dps i)) (fun i => tag_cone (dps i))
            hPJ u hu hne hf
  | _, _, _, .joinOrF prem hJ1 hJ2 hC hg hΓ, Z, ht, u, hu, hne, hf => by
      rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion h

  | _, _, _, @FRJr.joinCirc _ n stab th rhs Z0 prem hJ1 hJ2 hcirc hZ0 hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxOr stab th rhs)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJr.joinCircP _ n k stab th rhs Z0 tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ0 hg _ hΓ, Z, ht, u, hu, hne, hf => by
      rcases ht with h | ⟨W, h, hcov⟩
      · exact Tag.noConfusion h
      · have hWZ : Z0 = W := by injection h
        subst hWZ
        exact tagConeP_core (Ms := fun j i => preI (prem j) i)
          (Ns := fun i => preR (dps i))
          (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
          (fun i => preR_closed (dps i)) (fun i => preR_root_lbl (dps i))
          hcov hDs (fun i => joinCtxOrP_clo i) hΓ.subset
          (fun i => lemma39R (dps i)) (fun i => tag_cone (dps i))
          (preR_closed (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ0 hg hΓ))
          u hu hne hf

theorem lemma39I0 {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C) (i : RegIdx d) (w : (preI d i).W),
    ((preI d i).toKripke (preI_closed d i)).forces w ((preI d i).lbl w)
  | _, _, _, .axI _ _ _ _, i, _ => (i : Empty).elim
  | _, _, _, .andI1 d _, i, w => lemma39I0 d i w
  | _, _, _, .andI2 d _, i, w => lemma39I0 d i w
  | _, _, _, .orI d₁ d₂ _ _ _ _ _, i, w => by
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ => exact lemma39I0 d₁ i₁ w
      | .inr i₂ => exact lemma39I0 d₂ i₂ w
  | _, _, _, .impInI d _ _ _ _ _ _, i, w => lemma39I0 d i w
  | _, _, _, .impNotIn d _ _ _ _, _, w => (lemma39R d).1 w
  | _, _, _, .circNotIn d _ _ _, _, w => (lemma39R d).1 w
  | _, _, _, @FRJi.axIC _ F ats hats hFf hg _ hTh, _, w => by
      -- the mounted BARE final world (the ◯⊥-false species: no fallible
      -- Rm-access, so `◯Y ≡ Y` on its own cone) forces its zone: every
      -- member is `classForce`-true by construction, and single-world
      -- forcing IS `classForce`
      intro X hX
      have hcf : classForce ats X = true :=
        (List.mem_filter.mp ((hTh X).mp hX)).2
      exact (PreModel.leaf_force_iff
        (fun p => (hTh _).trans (vacZoneA_atom hats)) X).mpr hcf

theorem lemma39I {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
    ¬ P.fal w →
    (∀ X ∈ P.lbl w, Clo (St ++ Th) X) →
    (∀ i : RegIdx d, RootAbove P hP w (preI d i) (preI_closed d i)) →
    (P.toKripke hP).forces w (cap St (sfm C)) →
    ¬ (P.toKripke hP).force w C
  | _, _, _, .axI F hF hg hTh, P, hP, w, hw, hlbl, _, _ => by
      match F, hF with
      | .bot, _ => exact fun h => hw h
      | .atom p, _ =>
          intro hcon
          have hmem : Form.atom p ∈ P.lbl w := hcon.elim (fun h => h)
            (fun h => absurd h hw)
          have hin := clo_pv (hlbl _ hmem)
          simp only [List.nil_append] at hin
          rcases List.mem_append.mp ((hTh _).mp hin) with hin' | hin'
          · rcases List.mem_append.mp hin' with hin'' | hin''
            · exact (mem_rm.mp hin'').1 rfl
            · have himp := (List.mem_filter.mp hin'').2
              simp [Form.isImp] at himp
          · have hcx := (List.mem_filter.mp hin').2
            simp [Form.isCirc] at hcx
  | _, _, _, .andI1 d hg, P, hP, w, hw, hlbl, hroot, hforce => by
      intro hcon
      refine lemma39I d P hP w hw hlbl hroot ?_ hcon.1
      intro X hX
      rw [mem_cap] at hX
      exact hforce X (mem_cap.mpr ⟨hX.1, sfm_subset_sfm_and₁ hX.2⟩)
  | _, _, _, .andI2 d hg, P, hP, w, hw, hlbl, hroot, hforce => by
      intro hcon
      refine lemma39I d P hP w hw hlbl hroot ?_ hcon.2
      intro X hX
      rw [mem_cap] at hX
      exact hforce X (mem_cap.mpr ⟨hX.1, sfm_subset_sfm_and₂ hX.2⟩)
  | _, _, _, @FRJi.orI _ St₁ Th₁ St₂ Th₂ C₁ C₂ d₁ d₂ h₁ h₂ hg _ _ hStE hThE,
      P, hP, w, hw, hlbl, hroot, hforce => by
      intro hcon
      rcases hcon with hcon | hcon
      · refine lemma39I d₁ P hP w hw ?_ (fun i => hroot (Sum.inl i)) ?_ hcon
        · intro X hX
          refine clo_mono ?_ (hlbl X hX)
          intro Y hY
          simp only [List.mem_append] at hY ⊢
          rcases hY with hY | hY
          · rcases List.mem_append.mp ((hStE Y).mp hY) with hY' | hY'
            · exact Or.inl hY'
            · exact List.mem_append.mp (h₂ hY')
          · exact Or.inr (mem_cap.mp ((hThE Y).mp hY)).1
        · intro X hX
          rw [mem_cap] at hX
          exact hforce X (mem_cap.mpr
            ⟨(hStE X).mpr (List.mem_append_left _ hX.1), sfm_subset_sfm_or₁ hX.2⟩)
      · refine lemma39I d₂ P hP w hw ?_ (fun i => hroot (Sum.inr i)) ?_ hcon
        · intro X hX
          refine clo_mono ?_ (hlbl X hX)
          intro Y hY
          simp only [List.mem_append] at hY ⊢
          rcases hY with hY | hY
          · rcases List.mem_append.mp ((hStE Y).mp hY) with hY' | hY'
            · exact List.mem_append.mp (h₁ hY')
            · exact Or.inl hY'
          · exact Or.inr (mem_cap.mp ((hThE Y).mp hY)).2
        · intro X hX
          rw [mem_cap] at hX
          exact hforce X (mem_cap.mpr
            ⟨(hStE X).mpr (List.mem_append_right _ hX.1), sfm_subset_sfm_or₂ hX.2⟩)
  | _, _, _, @FRJi.impInI _ St Th Lam ThLam A B d hpre hdisj hA hg _ _ hStE hThE,
      P, hP, w, hw, hlbl, hroot, hforce => by
      intro hcon
      have hSA : (P.toKripke hP).forces w (cap (St ++ Lam) (sf A)) := by
        intro X hX
        rw [mem_cap] at hX
        exact hforce X (mem_cap.mpr ⟨(hStE X).mpr hX.1, sf_subset_sfm_impL hX.2⟩)
      have hAf : (P.toKripke hP).force w A := clo_forces hSA (clo_sf hA)
      refine lemma39I d P hP w hw ?_ hroot ?_ (hcon w ((P.toKripke hP).le_refl w) hAf)
      · intro X hX
        refine clo_mono ?_ (hlbl X hX)
        intro Y hY
        simp only [List.mem_append] at hY ⊢
        rcases hY with hY | hY
        · rcases List.mem_append.mp ((hStE Y).mp hY) with hY' | hY'
          · exact Or.inl hY'
          · exact Or.inr ((hpre Y).mpr (List.mem_append_right _ hY'))
        · exact Or.inr ((hpre Y).mpr (List.mem_append_left _ ((hThE Y).mp hY)))
      · intro X hX
        rw [mem_cap] at hX
        exact hforce X (mem_cap.mpr
          ⟨(hStE X).mpr (List.mem_append_left _ hX.1),
            sfm_subset_sfm_impR hX.2⟩)
  | _, _, _, @FRJi.impNotIn _ t Γ Th A B d hTh hA hAnot hg,
      P, hP, w, hw, hlbl, hroot, hforce => by
      intro hcon
      obtain ⟨v, hwv, hiff⟩ := hroot ()
      obtain ⟨ha, hb⟩ := lemma39R d
      have hlblr := ha (preR d).root
      have hvΓ : (P.toKripke hP).forces v Γ := fun X hX =>
        (hiff X).mpr (hlblr X ((preR_root_lbl d X).mpr hX))
      exact hb ((hiff B).mp (hcon v hwv (clo_forces hvΓ hA)))
  | _, _, _, @FRJi.axIC _ F ats hats hFf hg _ hTh, P, hP, w, hw, hlbl, hroot, hforce => by
      -- `w ⊩ ◯F` would persist up to the mounted bare final world, which
      -- refutes `◯F` because it refutes `F` (the recorded classical
      -- refutation `hFf`) and is its own modal cone.
      intro hcon
      obtain ⟨v, hwv, hiff⟩ := hroot ()
      have hv : (P.toKripke hP).force v (.circ F) :=
        (P.toKripke hP).force_mono hwv hcon
      have hr := (hiff _).mp hv
      have hcf := (PreModel.leaf_force_iff
        (fun p => (hTh _).trans (vacZoneA_atom hats)) _).mp hr
      simp only [classForce] at hcf
      rw [hFf] at hcf
      exact Bool.noConfusion hcf
  | _, _, _, @FRJi.circNotIn _ t Γ Th Z d htag hTh hg,
      P, hP, w, hw, hlbl, hroot, hforce => by
      -- `w ⊩ ◯Z` persists up to the embedded premise root `v`, transfers
      -- into the component, and there the `◯∈` argument (root refutes `Z`
      -- by Lemma 3.9(i), the rest of the modal cone by `tag_cone`)
      -- refutes it.
      intro hcon
      obtain ⟨v, hwv, hiff⟩ := hroot ()
      have hv : (P.toKripke hP).force v (.circ Z) :=
        (P.toKripke hP).force_mono hwv hcon
      have hr : (modR d).force (modR d).root (.circ Z) := (hiff _).mp hv
      obtain ⟨ha, hb⟩ := lemma39R d
      refine Kripke.not_force_circ (modR d) ?_ hr
      intro u hu hf
      by_cases hru : u = (modR d).root
      · exact hb (hru ▸ hf)
      · exact tag_cone d Z htag u hu hru hf

end
/-! ## Theorem 3.10 and Theorem 3.1 -/

/-- **Theorem 3.10.**  "Let `D` be an `FRJ(G)`-derivation of `G`.  Then
`Mod(D)` is a countermodel for `G`."  Immediate from Lemma 3.9(i) at the
root sequent, whose `φ` is the model's root. -/
theorem modR_countermodel {G : Form} {t : Tag} {Γ : List Form} (d : FRJr G t Γ G) :
    Countermodel (modR d) G := (lemma39R d).2

/-- **Theorem 3.1 (Soundness of `FRJ(G)`), for PLL**: `⊢_{FRJ(G)} G`
implies `G` is not valid in all constraint models.

The paper concludes `G ∉ IPL`; here the conclusion is against the wider
class because a derivation using the fallible join builds a model with a
fallible world — a genuine constraint model, but not one of the paper's.
For derivations avoiding the fallible join the extracted model is
infallible and the paper's conclusion returns; the fallible join is
exactly what lets the calculus refute formulas, like `¬◯⊥`, that every
infallible model validates. -/
theorem soundness {G : Form} (h : Provable G) : ¬ PLL G := by
  obtain ⟨t, Γ, ⟨d⟩⟩ := h
  exact not_PLL_of_countermodel (modR_countermodel d)

/-! ## Sanity checks

An atom and `⊥` are underivable and provable in `FRJ(G)` by `Ax^R`
alone; soundness then re-derives their underivability. -/

example (p : String) : ¬ PLL (.atom p) :=
  soundness ⟨.barren, rm (gAt (.atom p)) (.atom p),
    ⟨.axR (.atom p) rfl (sfR_self _) (CtxEq.refl _)⟩⟩

example : ¬ PLL .bot :=
  soundness ⟨.barren, rm (gAt .bot) .bot, ⟨.axR .bot rfl (sfR_self _) (CtxEq.refl _)⟩⟩


end FRJ
