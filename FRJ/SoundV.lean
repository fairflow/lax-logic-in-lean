/-
# Lemma 3.9 and the soundness of the repaired calculus `FRJV(G)`

`FRJ/Sound.lean` transported to the repaired family `FRJVr`/`FRJVi` of
`FRJ/CalculusV.lean`.  Six of the nine join case lemmas concern
constructors that are verbatim in `FRJV` (the promise and fallible
joins), and are pure qualifier renames of the originals; the three
BARREN joins (`⋈^At`, `⋈^∨`, `⋈^◯`) changed — their conclusion context
is `base ++ kept` with a `KeptChain` certificate, and the `⋈^∨`/`⋈^◯`
side conditions test `RefAt` instead of Υ-membership — and their case
lemmas are re-proved here:

* the old secondary induction `key` ((P2)+(P3)) survives restricted to
  the BASE context (`baseAtV_imp_head`/`baseOrV_imp_head` replace the
  old `joinCtx*_imp_head`);
* a new induction over the `KeptChain` certificate forces the kept zone
  at the root: each link's antecedent is refuted by `refAt_refutes`,
  whose four hypotheses (Υ refuted, context forced, cone = {root},
  infallible) are exactly the invariants the barren case already
  carries;
* the rhs refutation for `⋈^∨`/`⋈^◯` is `refAt_refutes` applied to the
  rule's `RefAt` side condition.

Derivation-free lemmas of `FRJ.Sound` (`not_force_prime`,
`covers_refutes`, the promise/fallible context shape lemmas, …) are
imported and cited, not re-proved.
-/
import FRJ.Sound
import FRJ.ExtractV
import FRJ.CalculusVLemmas
import FRJ.SoundCore
import FRJ.SoundCoreV

namespace FRJ.V

open FRJ Form

/-! ## The three changed barren cases -/

theorem joinAt_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {kept : List Form}
    (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hkc : KeptChain (upsilon rhs) (joinCtxAtVBase stab th F)
      (thPool th) kept)
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
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtVBase stab th F ++ kept) :
    let d := FRJVr.joinAt prem hJ1 hJ2 hcirc hkc hF hFnot hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root F := by
  intro d
  exact joinAt_core (Ms := fun j i => preI (prem j) i)
    (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
    hJ2 hcirc hkc hF hFnot
    (fun j i => preI_closed (prem j) i)
    (fun {X} hX => wfR d ((hΓ X).mpr (List.mem_append_left _ hX)))
    (fun j => wfI (prem j))
    (fun j => lhs_clo_of_steps
      (Relation.ReflTransGen.single
        ⟨_, Step.joinAt (G := G) (F := F) j hJ1 hkc (CtxEq.refl _)⟩))
    ihI0 ihI (preR_closed d)

theorem joinOr_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {kept : List Form}
    (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase stab th)
      (thPool th) kept)
    (hC : RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) C₁ ∧
      RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) C₂)
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
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrVBase stab th ++ kept) :
    let d := FRJVr.joinOr prem hJ1 hJ2 hcirc hkc hC hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root (.or C₁ C₂) := by
  intro d
  exact joinOr_core (Ms := fun j i => preI (prem j) i)
    (elems := premIdxElems prem) (hcomplete := premIdxComplete prem)
    hJ2 hcirc hkc hC
    (fun j i => preI_closed (prem j) i)
    (fun {X} hX => wfR d ((hΓ X).mpr (List.mem_append_left _ hX)))
    (fun j => wfI (prem j))
    (fun j => lhs_clo_of_steps
      (Relation.ReflTransGen.single
        ⟨_, Step.joinOr (G := G) (C₁ := C₁) (C₂ := C₂) j hJ1 hkc (CtxEq.refl _)⟩))
    ihI0 ihI (preR_closed d)

/-- `⋈^◯`, the barren modal join, with the kept zone and the
`RefAt`-relaxed body condition: label-forcing as `⋈^∨`; the root refutes
`◯Z` because its modal cone is itself and it refutes `Z` — now by
`refAt_refutes` on the rule's `RefAt` certificate rather than only
through a premise slot. -/
theorem joinCirc_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Z : Form} {kept : List Form}
    (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase stab th)
      (thPool th) kept)
    (hZ : RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) Z)
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
    {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrVBase stab th ++ kept) :
    let d := FRJVr.joinCirc prem hJ1 hJ2 hcirc hkc hZ hg hΓ
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
      (H ∈ impPart (joinCtxOrVBase stab th) →
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
              have hAu : A ∈ upsilon rhs := baseOrV_imp_head hJ2 hHmem
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
                  have hmem : Form.imp A B ∈ (preR d).lbl none :=
                    List.mem_append_left _ hHmem
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hmem
                  have hfv : (modR d).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact hfv _ ((modR d).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinCirc (G := G) (Z := Z) j hJ1 hkc (CtxEq.refl _)⟩)
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
                  exact Or.inl (List.mem_append_left _
                    (stab_mem_baseOrV (G := G) (th := th) hcirc hK.1 hKG))
            · have hmem : K ∈ impPart (joinCtxOrVBase stab th) :=
                List.mem_filter.mpr
                  ⟨stab_mem_baseOrV (G := G) (th := th) hcirc hK.1 hKG,
                    (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ k := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · exfalso
              have : K ∈ unionAll (fun j => circPart (stab j)) := mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hK.1, (List.mem_filter.mp h).2⟩⟩
              rw [hcirc] at this
              exact List.not_mem_nil this
  have base_forced : ∀ X ∈ joinCtxOrVBase stab th,
      (modR d).force none X := by
    intro X hX
    have hXG : X ∈ gHat G := wfR d ((hΓ X).mpr (List.mem_append_left _ hX))
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
  have hups : ∀ C ∈ upsilon rhs, ¬ (modR d).force none C := by
    intro C hC
    obtain ⟨j, -, hj⟩ := List.mem_map.mp hC
    exact (key C.size C (Nat.le_refl _)).2 j hj
  have hcone : ∀ c, (modR d).Rm none c → c = none := by
    intro c hc
    have hc' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxOrVBase stab th ++ kept)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)).rm none c := hc
    exact PreModel.join_rm_root_barren (fun _ => rfl) hc'
  have kept_forced : ∀ (ks : List Form),
      KeptChain (upsilon rhs) (joinCtxOrVBase stab th) (thPool th) ks →
      (∀ K ∈ ks, K ∈ kept) →
      ∀ K ∈ ks, (modR d).force none K := by
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
              have hmem : Form.imp Y B ∈ (preR d).lbl none :=
                List.mem_append_right _ (hsub _ List.mem_cons_self)
              have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp Y B) hmem
              exact clo_forces (fun X hX => hcomp ji x X hX) hclo _
                ((modR d).le_refl _) hYv
        · exact ih (fun K' hK' => hsub K' (List.mem_cons_of_mem _ hK')) K hKmem
  have hctxV : (modR d).forces none (joinCtxOrVBase stab th ++ kept) :=
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
  · refine Kripke.not_force_circ _ ?_
    intro u hu hf
    have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxOrVBase stab th ++ kept)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)).rm none u := hu
    have h0 := PreModel.join_rm_root_barren (fun _ => rfl) hu'
    rw [h0] at hf
    exact refAt_refutes hups hctxV hcone (fun h => h) hZ hf

/-! ## The six unchanged cases (qualifier renames of `FRJ.Sound`) -/

theorem joinAtP_case {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {t' : Tag}
    {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
    (dps : ∀ i, FRJVr G (tps i) (Δs i) (Ds i))
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
    let d := FRJVr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg hΓ
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
    (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
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
    let d := FRJVr.joinAtF prem hJ1 hJ2 hF hFnot hg hΓ
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
    (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
    (dps : ∀ i, FRJVr G (tps i) (Δs i) (Ds i))
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
    let d := FRJVr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg hΓ
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
    (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
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
    let d := FRJVr.joinOrF prem hJ1 hJ2 hC hg hΓ
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

/-- `⋈^◯,p`, the promise modal join: label-forcing as `⋈^∨,p`; the root
refutes `◯Z` with the whole cone — itself through the premise slot, each
promise component through its right formula `Z` at the component root
(`ihP`) and its `Covers`-certified tag below it (`ihT` = `tag_cone`). -/
theorem joinCircP_case {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Z : Form}
    {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
    (dps : ∀ i, FRJVr G (tps i) (Δs i) (Ds i))
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
    let d := FRJVr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg hΓ
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

/-! ## Lemma 3.9 for the repaired family -/

mutual

theorem lemma39R {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJVr G t Γ C),
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
  | _, _, _, @FRJVr.joinAt _ n stab th rhs F kept prem hJ1 hJ2 hcirc hkc hF hFnot hg _ hΓ =>
      joinAt_case prem hJ1 hJ2 hcirc hkc hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJVr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg _ hΓ =>
      joinAtP_case prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i)) hΓ
  | _, _, _, @FRJVr.joinAtF _ n stab th rhs F prem hJ1 hJ2 hF hFnot hg _ hΓ =>
      joinAtF_case prem hJ1 hJ2 hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJVr.joinOr _ n stab th rhs C₁ C₂ kept prem hJ1 hJ2 hcirc hkc hC hg _ hΓ =>
      joinOr_case prem hJ1 hJ2 hcirc hkc hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJVr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg _ hΓ =>
      joinOrP_case prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i)) hΓ
  | _, _, _, @FRJVr.joinOrF _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hC hg _ hΓ =>
      joinOrF_case prem hJ1 hJ2 hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJVr.joinCirc _ n stab th rhs Z kept prem hJ1 hJ2 hcirc hkc hZ hg _ hΓ =>
      joinCirc_case prem hJ1 hJ2 hcirc hkc hZ hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJVr.joinCircP _ n k stab th rhs Z tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg _ hΓ =>
      joinCircP_case prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i))
        (fun i => tag_cone (dps i)) hΓ

/-- **The pledge is honoured.**  If the tag is `barren` or `chain Z`, every
world of the root's modal cone other than the root itself refutes `Z`: a
barren root has no such world — for the V-joins because their extracted
premodel designates no promise component, exactly as before — and a
`chain Z` root's cone consists of promise components whose goals are all
`Z`, each root refuting its goal (Lemma 3.9(i)) and each deeper cone
refuting `Z` recursively. -/
theorem tag_cone {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJVr G t Γ C) (Z : Form),
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z) →
    ∀ u, (modR d).Rm (modR d).root u → u ≠ (modR d).root →
      ¬ (modR d).force u Z
  | _, _, _, .axR F hF hg hΓ, Z, ht, u, hu, hne, hf => hne rfl
  | _, _, _, .andR1 d _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .andR2 d _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .impIn d _ _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .circIn d _ _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, @FRJVr.joinAt _ n stab th rhs F kept prem hJ1 hJ2 hcirc hkc hF hFnot hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxAtVBase stab th F ++ kept)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJVr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hPJ : ClosedLbl (preR (FRJVr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg hΓ)) :=
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
  | _, _, _, @FRJVr.joinOr _ n stab th rhs C₁ C₂ kept prem hJ1 hJ2 hcirc hkc hC hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxOrVBase stab th ++ kept)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJVr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hPJ : ClosedLbl (preR (FRJVr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg hΓ)) :=
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
  | _, _, _, @FRJVr.joinCirc _ n stab th rhs Z0 kept prem hJ1 hJ2 hcirc hkc hZ0 hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxOrVBase stab th ++ kept)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJVr.joinCircP _ n k stab th rhs Z0 tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ0 hg _ hΓ, Z, ht, u, hu, hne, hf => by
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
          (preR_closed (FRJVr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ0 hg hΓ))
          u hu hne hf

theorem lemma39I0 {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJVi G St Th C) (i : RegIdx d) (w : (preI d i).W),
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
  | _, _, _, .liftI d _, _, w => (lemma39R d).1 w
  | _, _, _, @FRJVi.axIC _ F ats hats hFf hg _ hTh, _, w => by
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
    (d : FRJVi G St Th C) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
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
  | _, _, _, @FRJVi.orI _ St₁ Th₁ St₂ Th₂ C₁ C₂ d₁ d₂ h₁ h₂ hg _ _ hStE hThE,
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
  | _, _, _, @FRJVi.impInI _ St Th Lam ThLam A B d hpre hdisj hA hg _ _ hStE hThE,
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
  | _, _, _, @FRJVi.impNotIn _ t Γ Th A B d hTh hA hAnot hg,
      P, hP, w, hw, hlbl, hroot, hforce => by
      intro hcon
      obtain ⟨v, hwv, hiff⟩ := hroot ()
      obtain ⟨ha, hb⟩ := lemma39R d
      have hlblr := ha (preR d).root
      have hvΓ : (P.toKripke hP).forces v Γ := fun X hX =>
        (hiff X).mpr (hlblr X ((preR_root_lbl d X).mpr hX))
      exact hb ((hiff B).mp (hcon v hwv (clo_forces hvΓ hA)))
  | _, _, _, @FRJVi.axIC _ F ats hats hFf hg _ hTh, P, hP, w, hw, hlbl, hroot, hforce => by
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
  | _, _, _, @FRJVi.liftI _ t Γ Th C d hTh,
      P, hP, w, hw, hlbl, hroot, hforce => by
      -- (Lift) is sound for the SCHEMA reading and for no other reason:
      -- `w ⊩ C` would persist to the embedded component root `v`, transfer
      -- into the component, and be refuted there by Lemma 3.9(ii).  Note
      -- what is NOT used: the rule needs neither `w`'s infallibility, nor
      -- the zone bound `hlbl`, nor the stable-part hypothesis `hforce`.
      -- Its whole content is that a regular disproof refutes its goal at
      -- the root of the model it extracts.
      intro hcon
      obtain ⟨v, hwv, hiff⟩ := hroot ()
      exact (lemma39R d).2 ((hiff C).mp ((P.toKripke hP).force_mono hwv hcon))
  | _, _, _, @FRJVi.circNotIn _ t Γ Th Z d htag hTh hg,
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

/-! ## Theorem 3.10 and Theorem 3.1 for the repaired calculus -/

/-- **Theorem 3.10 for `FRJV(G)`.**  The model extracted from an
`FRJV(G)`-derivation of `G` is a countermodel for `G`. -/
theorem modR_countermodel {G : Form} {t : Tag} {Γ : List Form} (d : FRJVr G t Γ G) :
    Countermodel (modR d) G := (lemma39R d).2

end FRJ.V

namespace FRJ

/-- **Soundness of the repaired calculus `FRJV(G)`, for PLL**:
`⊢_{FRJV(G)} G` implies `G` is not valid in all constraint models.
(As for `FRJ.soundness`, the conclusion is against the wider fallible
class because the fallible join builds a model with a fallible world.) -/
theorem soundnessV {G : Form} (h : ProvableV G) : ¬ PLL G := by
  obtain ⟨t, Γ, ⟨d⟩⟩ := h
  exact not_PLL_of_countermodel (V.modR_countermodel d)

/-! ## Sanity checks

An atom is underivable in PLL, re-derived through `FRJV(G)` (via `Ax^R`
alone); and every paper derivation transfers, so `soundness` factors
through `soundnessV`. -/

example (p : String) : ¬ PLL (.atom p) :=
  soundnessV ⟨.barren, rm (gAt (.atom p)) (.atom p),
    ⟨.axR (.atom p) rfl (sfR_self _) (CtxEq.refl _)⟩⟩

example {G : Form} (h : Provable G) : ¬ PLL G :=
  soundnessV (provableV_of_provable h)

end FRJ

/-! ## Axiom pins -/

/-- info: 'FRJ.V.lemma39R' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.V.lemma39R

/-- info: 'FRJ.V.tag_cone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.V.tag_cone

/-- info: 'FRJ.soundnessV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.soundnessV
