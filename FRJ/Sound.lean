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
import FRJ.Extract

namespace FRJ

open Form

theorem prime_not_isImp {F : Form} (h : F.isPrime) : ¬ F.isImp := by
  cases F <;> simp_all [Form.isPrime, Form.isImp]

/-- A prime formula is forced exactly when it is a variable present in the
label; so if it is absent from the label it is not forced. -/
theorem not_force_prime {P : PreModel} (h : ClosedLbl P) {w : P.W} {F : Form}
    (hF : F.isPrime) (hnot : F ∉ P.lbl w) : ¬ (P.toKripke h).force w F := by
  cases F with
  | atom p => exact fun hc => hnot hc
  | bot => exact fun hc => hc
  | and A B => exact absurd hF (by simp [Form.isPrime])
  | or A B => exact absurd hF (by simp [Form.isPrime])
  | imp A B => exact absurd hF (by simp [Form.isPrime])

theorem imp_not_mem_atPart {A B : Form} {Γ : List Form} :
    Form.imp A B ∉ atPart Γ := fun h => by
  have hpv := (List.mem_filter.mp h).2
  simp [Form.isPV] at hpv

theorem mem_impPart_of {A B : Form} {Γ : List Form} (h : Form.imp A B ∈ Γ) :
    Form.imp A B ∈ impPart Γ := List.mem_filter.mpr ⟨h, rfl⟩

/-- An implication in the conclusion context of `⋈^At` has its antecedent
in `Υ`: from (J2) if it comes from `Σ^imp`, and from the definition of
the restriction if it comes from `Θ^imp`. -/
theorem joinCtxAt_imp_head {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F A B : Form}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (h : Form.imp A B ∈ joinCtxAt stab th rhs F) : A ∈ upsilon rhs := by
  simp only [joinCtxAt, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · exact absurd (mem_unionAll.mp h) (by rintro ⟨i, hi⟩; exact imp_not_mem_atPart hi)
  · exact absurd (interAll_subset 0 (rm_subset h)) imp_not_mem_atPart
  · exact hJ2 A B h
  · exact (mem_restrict.mp h).2

/-- The same for `⋈^∨`. -/
theorem joinCtxOr_imp_head {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {A B : Form}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (h : Form.imp A B ∈ joinCtxOr stab th rhs) : A ∈ upsilon rhs := by
  simp only [joinCtxOr, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · exact absurd (mem_unionAll.mp h) (by rintro ⟨i, hi⟩; exact imp_not_mem_atPart hi)
  · exact absurd (interAll_subset 0 h) imp_not_mem_atPart
  · exact hJ2 A B h
  · exact (mem_restrict.mp h).2

/-- `Σ_j` sits inside the join's conclusion context, split by shape. -/
theorem stab_mem_joinCtxAt {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {j : Fin (n + 1)} {K : Form}
    (hK : K ∈ stab j) (hKG : K ∈ gHat G) :
    K ∈ joinCtxAt stab th rhs F := by
  simp only [joinCtxAt, List.mem_append]
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with hKG | hKG
  · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩)))
  · exact Or.inl (Or.inr (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))

theorem stab_mem_joinCtxOr {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {j : Fin (n + 1)} {K : Form}
    (hK : K ∈ stab j) (hKG : K ∈ gHat G) :
    K ∈ joinCtxOr stab th rhs := by
  simp only [joinCtxOr, List.mem_append]
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with hKG | hKG
  · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩)))
  · exact Or.inl (Or.inr (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))

theorem joinAt_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
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
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j)) :
    (∀ w, (modR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).forces w
        ((preR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).force
          (modR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).root F := by
  have hPJ : ClosedLbl (preR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)) :=
    preR_closed _
  -- every component world forces its own label
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (preI_closed (prem ji.1) ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  -- (P2) and (P3), by the secondary induction on `size H`
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxAt stab th rhs F) →
        (modR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).force none H) := by
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
                      (modR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hHmem
                  have : (modR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact this _ ((modR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)).le_refl _) hAv
        · -- (P3)
          intro j hj hcon
          refine ihI j (preR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg)) hPJ none ?_ ?_ ?_
            (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single ⟨_, Step.joinAt (G := G) (F := F) j hJ1⟩)
          · intro i
            refine ⟨some ⟨⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            by_cases hpv : K.isPV
            · match K, hpv with
              | .atom p, _ =>
                  show Form.atom p ∈ joinCtxAt stab th rhs F
                  exact stab_mem_joinCtxAt (G := G) hK.1 hKG
            · have himp : K.isImp := by
                simp only [gHat, List.mem_append] at hKG
                rcases hKG with h | h
                · exact absurd (List.mem_filter.mp h).2 hpv
                · exact (List.mem_filter.mp h).2
              have hmem : K ∈ impPart (joinCtxAt stab th rhs F) :=
                List.mem_filter.mpr ⟨stab_mem_joinCtxAt (G := G) hK.1 hKG, himp⟩
              have hsz : K.size ≤ k := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
  -- assemble
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        have hXG : X ∈ gHat G := wfR (FRJr.joinAt prem hJ1 hJ2 hF hFnot hg) hX
        simp only [gHat, List.mem_append] at hXG
        rcases hXG with h | h
        · have : X.isPV := (List.mem_filter.mp h).2
          match X, this with
          | .atom p, _ => exact hX
        · have himp : X.isImp := (List.mem_filter.mp h).2
          exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
    | some jx =>
        obtain ⟨ji, x⟩ := jx
        intro X hX
        exact hcomp ji x X hX
  · refine not_force_prime hPJ hF ?_
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
    (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
    (hg : Form.or C₁ C₂ ∈ sfR G)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : RegIdx (prem j)) (x : (preI (prem j) i).W),
        ((preI (prem j) i).toKripke (preI_closed (prem j) i)).forces x
          ((preI (prem j) i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
        (∀ X ∈ P.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : RegIdx (prem j), RootAbove P hP w (preI (prem j) i) (preI_closed (prem j) i)) →
        (P.toKripke hP).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (P.toKripke hP).force w (rhs j)) :
    (∀ w, (modR (FRJr.joinOr prem hJ1 hJ2 hC hg)).forces w
        ((preR (FRJr.joinOr prem hJ1 hJ2 hC hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinOr prem hJ1 hJ2 hC hg)).force
          (modR (FRJr.joinOr prem hJ1 hJ2 hC hg)).root (.or C₁ C₂) := by
  have hPJ : ClosedLbl (preR (FRJr.joinOr prem hJ1 hJ2 hC hg)) := preR_closed _
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinOr prem hJ1 hJ2 hC hg)).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (preI_closed (prem ji.1) ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxOr stab th rhs) →
        (modR (FRJr.joinOr prem hJ1 hJ2 hC hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinOr prem hJ1 hJ2 hC hg)).force none H) := by
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
                      (modR (FRJr.joinOr prem hJ1 hJ2 hC hg)).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hHmem
                  have hfv : (modR (FRJr.joinOr prem hJ1 hJ2 hC hg)).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact hfv _ ((modR (FRJr.joinOr prem hJ1 hJ2 hC hg)).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR (FRJr.joinOr prem hJ1 hJ2 hC hg)) hPJ none ?_ ?_ ?_
            (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinOr (G := G) (C₁ := C₁) (C₂ := C₂) j hJ1⟩)
          · intro i
            refine ⟨some ⟨⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            by_cases hpv : K.isPV
            · match K, hpv with
              | .atom p, _ =>
                  show Form.atom p ∈ joinCtxOr stab th rhs
                  exact stab_mem_joinCtxOr (G := G) hK.1 hKG
            · have himp : K.isImp := by
                simp only [gHat, List.mem_append] at hKG
                rcases hKG with h | h
                · exact absurd (List.mem_filter.mp h).2 hpv
                · exact (List.mem_filter.mp h).2
              have hmem : K ∈ impPart (joinCtxOr stab th rhs) :=
                List.mem_filter.mpr ⟨stab_mem_joinCtxOr (G := G) hK.1 hKG, himp⟩
              have hsz : K.size ≤ k := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        have hXG : X ∈ gHat G := wfR (FRJr.joinOr prem hJ1 hJ2 hC hg) hX
        simp only [gHat, List.mem_append] at hXG
        rcases hXG with h | h
        · have hpv : X.isPV := (List.mem_filter.mp h).2
          match X, hpv with
          | .atom p, _ => exact hX
        · have himp : X.isImp := (List.mem_filter.mp h).2
          exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
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



mutual

theorem lemma39R {G : Form} : ∀ {Γ : List Form} {C : Form} (d : FRJr G Γ C),
    (∀ w : (preR d).W, (modR d).forces w ((preR d).lbl w)) ∧
      ¬ (modR d).force (modR d).root C
  | _, _, .axR F hF hg => by
      constructor
      · intro w X hX
        have hpv : X.isPV := by
          have hmem := rm_subset hX
          simpa [gAt] using (List.mem_filter.mp hmem).2
        match X, hpv with
        | .atom p, _ => exact hX
      · match F, hF with
        | .bot, _ => exact fun h => h
        | .atom p, _ => exact fun h => (mem_rm.mp h).1 rfl
  | _, _, .andR1 d hg => by
      obtain ⟨ha, hb⟩ := lemma39R d
      exact ⟨ha, fun hcon => hb hcon.1⟩
  | _, _, .andR2 d hg => by
      obtain ⟨ha, hb⟩ := lemma39R d
      exact ⟨ha, fun hcon => hb hcon.2⟩
  | _, _, .impIn d hA hg => by
      obtain ⟨ha, hb⟩ := lemma39R d
      refine ⟨ha, fun hcon => hb ?_⟩
      have hΓ := ha (preR d).root
      rw [preR_root_lbl d] at hΓ
      exact hcon _ ((modR d).le_refl _) (clo_forces hΓ hA)
  | _, _, @FRJr.joinAt _ n stab th rhs F prem hJ1 hJ2 hF hFnot hg =>
      joinAt_case prem hJ1 hJ2 hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w h1 h2 h3 => lemma39I (prem j) P hP w h1 h2 h3)
  | _, _, @FRJr.joinOr _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hC hg =>
      joinOr_case prem hJ1 hJ2 hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w h1 h2 h3 => lemma39I (prem j) P hP w h1 h2 h3)

theorem lemma39I0 {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C) (i : RegIdx d) (w : (preI d i).W),
    ((preI d i).toKripke (preI_closed d i)).forces w ((preI d i).lbl w)
  | _, _, _, .axI _ _ _, i, _ => (i : Empty).elim
  | _, _, _, .andI1 d _, i, w => lemma39I0 d i w
  | _, _, _, .andI2 d _, i, w => lemma39I0 d i w
  | _, _, _, .orI d₁ d₂ _ _ _, i, w => by
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ => exact lemma39I0 d₁ i₁ w
      | .inr i₂ => exact lemma39I0 d₂ i₂ w
  | _, _, _, .impInI d _ _ _, i, w => lemma39I0 d i w
  | _, _, _, .impNotIn d _ _ _ _, _, w => (lemma39R d).1 w

theorem lemma39I {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
    (∀ X ∈ P.lbl w, Clo (St ++ Th) X) →
    (∀ i : RegIdx d, RootAbove P hP w (preI d i) (preI_closed d i)) →
    (P.toKripke hP).forces w (cap St (sfm C)) →
    ¬ (P.toKripke hP).force w C
  | _, _, _, .axI F hF hg, P, hP, w, hlbl, _, _ => by
      match F, hF with
      | .bot, _ => exact fun h => h
      | .atom p, _ =>
          intro hcon
          have hmem : Form.atom p ∈ P.lbl w := hcon
          have hin := clo_pv (hlbl _ hmem)
          simp only [List.nil_append, List.mem_append] at hin
          rcases hin with hin | hin
          · exact (mem_rm.mp hin).1 rfl
          · have himp := (List.mem_filter.mp hin).2
            simp [Form.isImp] at himp
  | _, _, _, .andI1 d hg, P, hP, w, hlbl, hroot, hforce => by
      intro hcon
      refine lemma39I d P hP w hlbl hroot ?_ hcon.1
      intro X hX
      rw [mem_cap] at hX
      exact hforce X (mem_cap.mpr ⟨hX.1, sfm_subset_sfm_and₁ hX.2⟩)
  | _, _, _, .andI2 d hg, P, hP, w, hlbl, hroot, hforce => by
      intro hcon
      refine lemma39I d P hP w hlbl hroot ?_ hcon.2
      intro X hX
      rw [mem_cap] at hX
      exact hforce X (mem_cap.mpr ⟨hX.1, sfm_subset_sfm_and₂ hX.2⟩)
  | _, _, _, @FRJi.orI _ St₁ Th₁ St₂ Th₂ C₁ C₂ d₁ d₂ h₁ h₂ hg,
      P, hP, w, hlbl, hroot, hforce => by
      intro hcon
      rcases hcon with hcon | hcon
      · refine lemma39I d₁ P hP w ?_ (fun i => hroot (Sum.inl i)) ?_ hcon
        · intro X hX
          refine clo_mono ?_ (hlbl X hX)
          intro Y hY
          simp only [List.mem_append, mem_cap] at hY ⊢
          rcases hY with (hY | hY) | hY
          · exact Or.inl hY
          · exact List.mem_append.mp (h₂ hY)
          · exact Or.inr hY.1
        · intro X hX
          rw [mem_cap] at hX
          exact hforce X (mem_cap.mpr
            ⟨List.mem_append_left _ hX.1, sfm_subset_sfm_or₁ hX.2⟩)
      · refine lemma39I d₂ P hP w ?_ (fun i => hroot (Sum.inr i)) ?_ hcon
        · intro X hX
          refine clo_mono ?_ (hlbl X hX)
          intro Y hY
          simp only [List.mem_append, mem_cap] at hY ⊢
          rcases hY with (hY | hY) | hY
          · exact List.mem_append.mp (h₁ hY)
          · exact Or.inl hY
          · exact Or.inr hY.2
        · intro X hX
          rw [mem_cap] at hX
          exact hforce X (mem_cap.mpr
            ⟨List.mem_append_right _ hX.1, sfm_subset_sfm_or₂ hX.2⟩)
  | _, _, _, @FRJi.impInI _ St Th Lam A B d hdisj hA hg,
      P, hP, w, hlbl, hroot, hforce => by
      intro hcon
      have hSA : (P.toKripke hP).forces w (cap (St ++ Lam) (sf A)) := by
        intro X hX
        rw [mem_cap] at hX
        exact hforce X (mem_cap.mpr ⟨hX.1, sf_subset_sfm_impL hX.2⟩)
      have hAf : (P.toKripke hP).force w A := clo_forces hSA (clo_sf hA)
      refine lemma39I d P hP w ?_ hroot ?_ (hcon w ((P.toKripke hP).le_refl w) hAf)
      · intro X hX
        refine clo_mono ?_ (hlbl X hX)
        intro Y hY
        simp only [List.mem_append] at hY ⊢
        tauto
      · intro X hX
        rw [mem_cap] at hX
        exact hforce X (mem_cap.mpr
          ⟨List.mem_append_left _ hX.1, sfm_subset_sfm_impR hX.2⟩)
  | _, _, _, @FRJi.impNotIn _ Γ Th A B d hTh hA hAnot hg,
      P, hP, w, hlbl, hroot, hforce => by
      intro hcon
      obtain ⟨v, hwv, hiff⟩ := hroot ()
      obtain ⟨ha, hb⟩ := lemma39R d
      have hΓ := ha (preR d).root
      rw [preR_root_lbl d] at hΓ
      have hvΓ : (P.toKripke hP).forces v Γ := fun X hX => (hiff X).mpr (hΓ X hX)
      exact hb ((hiff B).mp (hcon v hwv (clo_forces hvΓ hA)))

end
/-! ## Theorem 3.10 and Theorem 3.1 -/

/-- **Theorem 3.10.**  "Let `D` be an `FRJ(G)`-derivation of `G`.  Then
`Mod(D)` is a countermodel for `G`."  Immediate from Lemma 3.9(i) at the
root sequent, whose `φ` is the model's root. -/
theorem modR_countermodel {G : Form} {Γ : List Form} (d : FRJr G Γ G) :
    Countermodel (modR d) G := (lemma39R d).2

/-- **Theorem 3.1 (Soundness of `FRJ(G)`).**  "`⊢_{FRJ(G)} G` implies
`G ∉ IPL`." -/
theorem soundness {G : Form} (h : Provable G) : ¬ IPL G := by
  obtain ⟨Γ, ⟨d⟩⟩ := h
  exact not_IPL_of_countermodel (modR_countermodel d)

/-! ## Sanity checks

An atom and `⊥` are IPC-underivable and provable in `FRJ(G)` by `Ax^R`
alone; soundness then re-derives their underivability. -/

example (p : String) : ¬ IPL (.atom p) :=
  soundness ⟨rm (gAt (.atom p)) (.atom p), ⟨.axR (.atom p) rfl (sfR_self _)⟩⟩

example : ¬ IPL .bot :=
  soundness ⟨rm (gAt .bot) .bot, ⟨.axR .bot rfl (sfR_self _)⟩⟩


end FRJ
