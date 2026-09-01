/-
# Lemma 3.9 and the soundness of the NEW calculus `FRJW(G)`

`FRJ/SoundV.lean` transported to the family `FRJWr`/`FRJWi` of
`FRJ/CalculusW.lean` — a FRESH soundness proof over the W-constructors,
not a transfer: `FRJW` has `lift` where `FRJVi` had `⊃∉`, every other
rule is verbatim, and every case below is re-run and re-checked over the
W-family.

The `lift` delta, stage W3 of `docs/frjw-plan.md`:

* `RegIdx (lift d) = Unit` and `preI (lift d) () = preR d`
  (`FRJ/ExtractW.lean`), exactly `⊃∉`'s clauses;
* the new `lemma39I` case is `(R^bar)`'s soundness clause, certified in
  advance as `not_force_of_rootAbove` (`wip/rbar.lean`): `RootAbove`
  places a world `v ≥ w` agreeing with the root of `preR d`, that root
  refutes `C` by Lemma 3.9(i), and forcing is monotone — none of
  `lift`'s own side conditions are needed;
* the joins' obligations `RootAbove P hP w (preI (prem j) i) …` are
  index-generic, so they discharge for components supplied by `lift`
  exactly as for `⊃∉`'s — this file is where that argument becomes a
  machine-checked fact.

Derivation-free lemmas of `FRJ.Sound` (`not_force_prime`,
`covers_refutes`, the promise/fallible context shape lemmas, …) and the
context-only V-join lemmas of `FRJ.CalculusVLemmas` are imported and
cited, not re-proved.
-/
import FRJ.Sound
import FRJ.ExtractW
import FRJ.CalculusVLemmas

namespace FRJ.W

open FRJ Form

/-! ## The three changed barren cases -/

theorem joinAt_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {kept : List Form}
    (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
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
    let d := FRJWr.joinAt prem hJ1 hJ2 hcirc hkc hF hFnot hg hΓ
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
  -- (P2) and (P3) over the BASE context, by the secondary induction on
  -- `size H`
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxAtVBase stab th F) →
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
                  have hlblv : ∀ Y ∈ (preI (prem ji.1) ji.2).lbl x,
                      (modR d).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hmem : Form.imp A B ∈ (preR d).lbl none :=
                    List.mem_append_left _ hHmem
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hmem
                  have : (modR d).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact this _ ((modR d).le_refl _) hAv
        · -- (P3)
          intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinAt (G := G) (F := F) j hJ1 hkc (CtxEq.refl _)⟩)
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
                  rcases stab_mem_baseAtV (G := G) (th := th) (F := F)
                    hcirc hK.1 hKG with hb | hb
                  · exact Or.inl (List.mem_append_left _ hb)
                  · exact absurd (hb ▸ (mem_unionAll.mpr
                      ⟨j, List.mem_filter.mpr
                        ⟨hK.1, (List.mem_filter.mp h).2⟩⟩)) hFnot
            · have hbase : K ∈ joinCtxAtVBase stab th F := by
                rcases stab_mem_baseAtV (G := G) (th := th) (F := F)
                  hcirc hK.1 hKG with hb | hb
                · exact hb
                · exact absurd (hb ▸ (List.mem_filter.mp h).2)
                    (prime_not_isImp hF)
              have hmem : K ∈ impPart (joinCtxAtVBase stab th F) :=
                List.mem_filter.mpr ⟨hbase, (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ k := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · exfalso
              have : K ∈ unionAll (fun j => circPart (stab j)) := mem_unionAll.mpr
                ⟨j, List.mem_filter.mpr ⟨hK.1, (List.mem_filter.mp h).2⟩⟩
              rw [hcirc] at this
              exact List.not_mem_nil this
  -- the base zone is forced at the root
  have base_forced : ∀ X ∈ joinCtxAtVBase stab th F,
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
      | .circ Y, _ => exact absurd hX circ_not_mem_baseAtV
  -- the four `refAt_refutes` invariants at the root
  have hups : ∀ C ∈ upsilon rhs, ¬ (modR d).force none C := by
    intro C hC
    obtain ⟨j, -, hj⟩ := List.mem_map.mp hC
    exact (key C.size C (Nat.le_refl _)).2 j hj
  have hcone : ∀ c, (modR d).Rm none c → c = none := by
    intro c hc
    have hc' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxAtVBase stab th F ++ kept)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)).rm none c := hc
    exact PreModel.join_rm_root_barren (fun _ => rfl) hc'
  -- the kept zone is forced at the root, by induction on its chain
  -- certificate: each link's antecedent is `RefAt`-refuted over the
  -- base plus the earlier links
  have kept_forced : ∀ (ks : List Form),
      KeptChain (upsilon rhs) (joinCtxAtVBase stab th F) (thPool th) ks →
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
              -- the root itself: the antecedent is refuted
              exact absurd hYv (refAt_refutes hups
                (fun X hX => (List.mem_append.mp hX).elim (base_forced X)
                  (fun hX' => ih
                    (fun K' hK' => hsub K' (List.mem_cons_of_mem _ hK')) X hX'))
                hcone (fun h => h) hY)
          | some jx =>
              -- above the root: (P2)'s above-root mechanism
              obtain ⟨ji, x⟩ := jx
              have hmem : Form.imp Y B ∈ (preR d).lbl none :=
                List.mem_append_right _ (hsub _ List.mem_cons_self)
              have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp Y B) hmem
              exact clo_forces (fun X hX => hcomp ji x X hX) hclo _
                ((modR d).le_refl _) hYv
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
  · refine not_force_prime hPJ hF ?_ (fun h => h)
    intro hmem0
    have hmem : F ∈ joinCtxAtVBase stab th F ++ kept := hmem0
    exact prime_not_mem_ctxAtV hkc hF hFnot hmem

theorem joinOr_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {kept : List Form}
    (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
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
    let d := FRJWr.joinOr prem hJ1 hJ2 hcirc hkc hC hg hΓ
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
                ⟨_, Step.joinOr (G := G) (C₁ := C₁) (C₂ := C₂) j hJ1 hkc (CtxEq.refl _)⟩)
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
  -- the whole conclusion label is forced at the root
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
  · intro hcon
    rcases hcon with h | h
    · exact refAt_refutes hups hctxV hcone (fun h => h) hC.1 h
    · exact refAt_refutes hups hctxV hcone (fun h => h) hC.2 h

/-- Each kept-chain member's antecedent has a `RefAt` certificate over
the FULL conclusion context: the chain certifies it over the base plus
the earlier links, and `RefAt` is context-monotone. -/
theorem keptChain_refAt_mem {Υ base pool : List Form} :
    ∀ {kept : List Form}, KeptChain Υ base pool kept →
      ∀ {Y B : Form}, Form.imp Y B ∈ kept →
        RefAt true Υ (base ++ kept) Y := by
  intro kept hkc
  induction hkc with
  | nil => intro _ _ h; exact absurd h List.not_mem_nil
  | @cons Y' B' rest hrest hpool hY' ih =>
      intro Y B hmem
      have hgrow : base ++ rest ⊆ base ++ (Form.imp Y' B' :: rest) := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      rcases List.mem_cons.mp hmem with heq | hmem'
      · cases heq
        exact refAt_mono (fun _ h => h) hgrow hY'
      · exact refAt_mono (fun _ h => h) hgrow (ih hmem')

/-- `⋈^◯`, the barren modal join, with the kept zone, the
`RefAt`-relaxed body condition, AND the `RefAt`-relaxed barren (J2)
(2026-09-01): label-forcing as `⋈^∨`; the root refutes `◯Z` because its
modal cone is itself and it refutes `Z`.  The stable-zone implications'
antecedents now carry `RefAt` certificates instead of `Υ`-membership;
the size-mutual induction stays founded because both the `ups`- and the
`Clo`-leaves of a certificate are subformulas of its target
(`refAt_refutes_sf`), and the kept zone joins the same induction
through `keptChain_refAt_mem`. -/
theorem joinCirc_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Z : Form} {kept : List Form}
    (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
    (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) A)
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
    let d := FRJWr.joinCirc prem hJ1 hJ2 hcirc hkc hZ hg hΓ
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
  have hcone : ∀ c, (modR d).Rm none c → c = none := by
    intro c hc
    have hc' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxOrVBase stab th ++ kept)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)).rm none c := hc
    exact PreModel.join_rm_root_barren (fun _ => rfl) hc'
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxOrVBase stab th ++ kept) →
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
              have hrA : RefAt true (upsilon rhs)
                  (joinCtxOrVBase stab th ++ kept) A := by
                rcases List.mem_append.mp hHmem with hb | hk
                · exact hJ2 A B (baseOrV_imp hb)
                · exact keptChain_refAt_mem hkc hk
              have hsz : A.size ≤ k := by simp only [Form.size] at hH; omega
              have hnA : ¬ (modR d).force none A := by
                refine refAt_refutes_sf hcone (fun h => h) hrA ?_ ?_
                · intro C hC hCs
                  obtain ⟨j, -, hj⟩ := List.mem_map.mp hC
                  exact (ih C (Nat.le_trans (size_le_of_mem_sf hCs) hsz)).2 j hj
                · intro C hC hCs
                  have hCG : C ∈ gHat G := wfR d ((hΓ C).mpr hC)
                  simp only [gHat, List.mem_append] at hCG
                  rcases hCG with (h | h) | h
                  · match C, (List.mem_filter.mp h).2 with
                    | .atom p, _ => exact Or.inl hC
                  · exact (ih C (Nat.le_trans (size_le_of_mem_sf hCs) hsz)).1
                      (List.mem_filter.mpr ⟨hC, (List.mem_filter.mp h).2⟩)
                  · match C, (List.mem_filter.mp h).2 with
                    | .circ Y, _ =>
                        rcases List.mem_append.mp hC with hb | hk
                        · exact absurd hb circ_not_mem_baseOrV
                        · exact absurd (keptChain_isImp hkc _ hk)
                            (by simp [Form.isImp])
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some jx =>
                  obtain ⟨ji, x⟩ := jx
                  have hlblv : ∀ Y ∈ (preI (prem ji.1) ji.2).lbl x,
                      (modR d).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hmem : Form.imp A B ∈ (preR d).lbl none := hHmem
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
            · have hmem : K ∈ impPart (joinCtxOrVBase stab th ++ kept) :=
                List.mem_filter.mpr
                  ⟨List.mem_append_left _
                    (stab_mem_baseOrV (G := G) (th := th) hcirc hK.1 hKG),
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
      exact (key X.size X (Nat.le_refl _)).1
        (List.mem_filter.mpr ⟨List.mem_append_left _ hX, himp⟩)
    · have hcx : X.isCirc := (List.mem_filter.mp h).2
      match X, hcx with
      | .circ Y, _ => exact absurd hX circ_not_mem_baseOrV
  have hups : ∀ C ∈ upsilon rhs, ¬ (modR d).force none C := by
    intro C hC
    obtain ⟨j, -, hj⟩ := List.mem_map.mp hC
    exact (key C.size C (Nat.le_refl _)).2 j hj
  have kept_forced : ∀ K ∈ kept, (modR d).force none K := by
    intro K hK
    have hKi : K.isImp = true := keptChain_isImp hkc _ hK
    match K, hKi with
    | .imp Y B, _ =>
        exact (key (Form.imp Y B).size _ (Nat.le_refl _)).1
          (List.mem_filter.mpr ⟨List.mem_append_right _ hK, rfl⟩)
  have hctxV : (modR d).forces none (joinCtxOrVBase stab th ++ kept) :=
    fun X hX => (List.mem_append.mp hX).elim (base_forced X) (kept_forced X)
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
    (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
    (dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i))
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
    let d := FRJWr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root F := by
  intro d
  have hPJ : ClosedLbl (preR d) :=
    preR_closed _
  -- the two component families force their own labels
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR d).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompR : ∀ (i : Fin (k + 1)) (x : (preR (dps i)).W) (A : Form),
      A ∈ (preR (dps i)).lbl x →
      (modR d).force
        (some ⟨Sum.inr i, x⟩) A := by
    intro i x A hA
    exact (join_force_comp hPJ (i := Sum.inr i)
      (preR_closed (dps i)) A x).mpr ((ihP i).1 x A hA)
  -- (P2◯): every kept modal formula is forced at the root, by `circ_intro`
  -- with the designated promise root as witness
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxAtP stab th rhs F Δs →
      (modR d).force
        none (.circ Y) := by
    intro Y hY
    obtain ⟨i, hi⟩ := joinCtxAtP_circ_body hJ5 hY
    refine Kripke.circ_intro _ ?_ ?_
    · refine ⟨some ⟨Sum.inr i, (preR (dps i)).root⟩,
        PJRm.prom rfl ((preR (dps i)).rm_refl _), ?_⟩
      have hiC : Clo ((preR (dps i)).lbl (preR (dps i)).root) Y :=
        clo_mono (preR_root_lbl (dps i)).subset' hi
      exact clo_forces (fun X hX => hcompR i _ X hX) hiC
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hPJ none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr i' => exact clo_forces (fun X hX => hcompR i' x X hX) hclo
  -- (P2) and (P3), by the secondary induction on `size H`
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxAtP stab th rhs F Δs) →
        (modR d).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR d).force none H) := by
    intro m
    induction m with
    | zero => intro H hH; exfalso; cases H <;> simp [Form.size] at hH
    | succ m ih =>
        intro H hH
        constructor
        · intro hHimp
          obtain ⟨hHmem, hHsh⟩ := List.mem_filter.mp hHimp
          match H, hHsh with
          | .imp A B, _ =>
              have hAu : A ∈ upsilon rhs := joinCtxAtP_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ m := by
                simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some cx =>
                  obtain ⟨c, x⟩ := cx
                  have hclo := hPJ none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (modR d).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr i' => exact clo_forces (fun Y hY => hcompR i' x Y hY) hclo
                  exact hforced _
                    ((modR d).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinAtP (G := G) (F := F) (Δs := Δs) j hJ1 (CtxEq.refl _)⟩)
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (i := Sum.inl ⟨j, i⟩)
              (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  exact Or.inl (stab_mem_joinCtxAtP (G := G) hK.1 hKG (fun i => hJ7 i j _ hK.1))
            · have hmem : K ∈ impPart (joinCtxAtP stab th rhs F Δs) :=
                List.mem_filter.mpr
                  ⟨stab_mem_joinCtxAtP (G := G) hK.1 hKG (fun i => hJ7 i j _ hK.1), (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ m := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · match K, (List.mem_filter.mp h).2 with
              | .circ Y, _ =>
                  exact hcircF Y (stab_mem_joinCtxAtP (G := G) hK.1 hKG (fun i => hJ7 i j _ hK.1))
  -- assemble
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        have hXG : X ∈ gHat G :=
          wfR d ((hΓ X).mpr hX)
        simp only [gHat, List.mem_append] at hXG
        rcases hXG with (h | h) | h
        · have : X.isPV := (List.mem_filter.mp h).2
          match X, this with
          | .atom p, _ => exact Or.inl hX
        · have himp : X.isImp := (List.mem_filter.mp h).2
          exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
        · have : X.isCirc := (List.mem_filter.mp h).2
          match X, this with
          | .circ Y, _ => exact hcircF Y hX
    | some cx =>
        obtain ⟨c, x⟩ := cx
        intro X hX
        cases c with
        | inl ji => exact hcompL ji x X hX
        | inr i => exact hcompR i x X hX
  · refine not_force_prime hPJ hF ?_ (fun h => h)
    intro hmem0
    have hmem : F ∈ joinCtxAt stab th rhs F ++ joinCtxCircP stab th Δs :=
      restrictP_subset hmem0
    rcases List.mem_append.mp hmem with hmem | hmem
    · simp only [joinCtxAt, List.mem_append] at hmem
      rcases hmem with ((h | h) | h) | h
      · exact hFnot h
      · exact (mem_rm.mp h).1 rfl
      · obtain ⟨i, hi⟩ := mem_unionAll.mp h
        exact prime_not_isImp hF (List.mem_filter.mp hi).2
      · exact prime_not_isImp hF
          (List.mem_filter.mp (interAll_subset 0 (restrict_subset h))).2
    · rcases List.mem_append.mp hmem with h | h
      · obtain ⟨i, hi⟩ := mem_unionAll.mp h
        exact prime_not_isCirc hF (List.mem_filter.mp hi).2
      · exact prime_not_isCirc hF (isCirc_of_mem_restrictC h)

theorem joinAtF_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form}
    (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
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
    let d := FRJWr.joinAtF prem hJ1 hJ2 hF hFnot hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root F := by
  intro d
  have hPJ : ClosedLbl (preR d) :=
    preR_closed _
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR d).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  -- the declared fallible world forces everything
  have hcompF : ∀ (x : Unit) (A : Form),
      (modR d).force
        (some ⟨Sum.inr (), x⟩) A := by
    intro x A
    exact Kripke.fal_force _ A trivial
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxAtF stab th rhs F →
      (modR d).force none (.circ Y) := by
    intro Y hY
    refine Kripke.circ_intro _ ?_ ?_
    · exact ⟨some ⟨Sum.inr (), ()⟩, PJRm.prom rfl trivial, hcompF () Y⟩
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hPJ none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr u => exact hcompF u (.circ Y)
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxAtF stab th rhs F) →
        (modR d).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR d).force none H) := by
    intro m
    induction m with
    | zero => intro H hH; exfalso; cases H <;> simp [Form.size] at hH
    | succ m ih =>
        intro H hH
        constructor
        · intro hHimp
          obtain ⟨hHmem, hHsh⟩ := List.mem_filter.mp hHimp
          match H, hHsh with
          | .imp A B, _ =>
              have hAu : A ∈ upsilon rhs := joinCtxAtF_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ m := by
                simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some cx =>
                  obtain ⟨c, x⟩ := cx
                  have hclo := hPJ none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (modR d).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr u => exact hcompF u (.imp A B)
                  exact hforced _
                    ((modR d).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinAtF (G := G) (F := F) j hJ1 (CtxEq.refl _)⟩)
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (i := Sum.inl ⟨j, i⟩)
              (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  exact Or.inl (stab_mem_joinCtxAtF (G := G) hK.1 hKG)
            · have hmem : K ∈ impPart (joinCtxAtF stab th rhs F) :=
                List.mem_filter.mpr
                  ⟨stab_mem_joinCtxAtF (G := G) hK.1 hKG, (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ m := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · match K, (List.mem_filter.mp h).2 with
              | .circ Y, _ =>
                  exact hcircF Y (stab_mem_joinCtxAtF (G := G) hK.1 hKG)
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
          | .circ Y, _ => exact hcircF Y hX
    | some cx =>
        obtain ⟨c, x⟩ := cx
        intro X hX
        cases c with
        | inl ji => exact hcompL ji x X hX
        | inr u => exact hcompF u X
  · refine not_force_prime hPJ hF ?_ (fun h => h)
    intro hmem0
    have hmem : F ∈ joinCtxAtF stab th rhs F := hmem0
    rcases List.mem_append.mp hmem with hmem | hmem
    · simp only [joinCtxAt, List.mem_append] at hmem
      rcases hmem with ((h | h) | h) | h
      · exact hFnot h
      · exact (mem_rm.mp h).1 rfl
      · obtain ⟨i, hi⟩ := mem_unionAll.mp h
        exact prime_not_isImp hF (List.mem_filter.mp hi).2
      · exact prime_not_isImp hF
          (List.mem_filter.mp (interAll_subset 0 (restrict_subset h))).2
    · rcases List.mem_append.mp hmem with h | h
      · obtain ⟨i, hi⟩ := mem_unionAll.mp h
        exact prime_not_isCirc hF (List.mem_filter.mp hi).2
      · exact prime_not_isCirc hF
          (List.mem_filter.mp (interAll_subset 0 h)).2

theorem joinOrP_case {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {t' : Tag}
    {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
    (dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i))
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
    let d := FRJWr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root (.or C₁ C₂) := by
  intro d
  have hPJ : ClosedLbl (preR d) :=
    preR_closed _
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR d).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompR : ∀ (i : Fin (k + 1)) (x : (preR (dps i)).W) (A : Form),
      A ∈ (preR (dps i)).lbl x →
      (modR d).force
        (some ⟨Sum.inr i, x⟩) A := by
    intro i x A hA
    exact (join_force_comp hPJ (i := Sum.inr i)
      (preR_closed (dps i)) A x).mpr ((ihP i).1 x A hA)
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxOrP stab th rhs Δs →
      (modR d).force
        none (.circ Y) := by
    intro Y hY
    obtain ⟨i, hi⟩ := joinCtxOrP_circ_body hJ5 hY
    refine Kripke.circ_intro _ ?_ ?_
    · refine ⟨some ⟨Sum.inr i, (preR (dps i)).root⟩,
        PJRm.prom rfl ((preR (dps i)).rm_refl _), ?_⟩
      have hiC : Clo ((preR (dps i)).lbl (preR (dps i)).root) Y :=
        clo_mono (preR_root_lbl (dps i)).subset' hi
      exact clo_forces (fun X hX => hcompR i _ X hX) hiC
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hPJ none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr i' => exact clo_forces (fun X hX => hcompR i' x X hX) hclo
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxOrP stab th rhs Δs) →
        (modR d).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR d).force none H) := by
    intro m
    induction m with
    | zero => intro H hH; exfalso; cases H <;> simp [Form.size] at hH
    | succ m ih =>
        intro H hH
        constructor
        · intro hHimp
          obtain ⟨hHmem, hHsh⟩ := List.mem_filter.mp hHimp
          match H, hHsh with
          | .imp A B, _ =>
              have hAu : A ∈ upsilon rhs := joinCtxOrP_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ m := by
                simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some cx =>
                  obtain ⟨c, x⟩ := cx
                  have hclo := hPJ none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (modR d).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr i' => exact clo_forces (fun Y hY => hcompR i' x Y hY) hclo
                  exact hforced _
                    ((modR d).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinOrP (G := G) (C₁ := C₁) (C₂ := C₂) (Δs := Δs) j hJ1 (CtxEq.refl _)⟩)
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (i := Sum.inl ⟨j, i⟩)
              (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  exact Or.inl (stab_mem_joinCtxOrP (G := G) hK.1 hKG (fun i => hJ7 i j _ hK.1))
            · have hmem : K ∈ impPart (joinCtxOrP stab th rhs Δs) :=
                List.mem_filter.mpr
                  ⟨stab_mem_joinCtxOrP (G := G) hK.1 hKG (fun i => hJ7 i j _ hK.1), (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ m := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · match K, (List.mem_filter.mp h).2 with
              | .circ Y, _ =>
                  exact hcircF Y (stab_mem_joinCtxOrP (G := G) hK.1 hKG (fun i => hJ7 i j _ hK.1))
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        have hXG : X ∈ gHat G :=
          wfR d ((hΓ X).mpr hX)
        simp only [gHat, List.mem_append] at hXG
        rcases hXG with (h | h) | h
        · have : X.isPV := (List.mem_filter.mp h).2
          match X, this with
          | .atom p, _ => exact Or.inl hX
        · have himp : X.isImp := (List.mem_filter.mp h).2
          exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
        · have : X.isCirc := (List.mem_filter.mp h).2
          match X, this with
          | .circ Y, _ => exact hcircF Y hX
    | some cx =>
        obtain ⟨c, x⟩ := cx
        intro X hX
        cases c with
        | inl ji => exact hcompL ji x X hX
        | inr i => exact hcompR i x X hX
  · intro hcon
    obtain ⟨j₁, -, hj₁⟩ := List.mem_map.mp hC.1
    obtain ⟨j₂, -, hj₂⟩ := List.mem_map.mp hC.2
    rcases hcon with h | h
    · exact (key C₁.size C₁ (Nat.le_refl _)).2 j₁ hj₁ h
    · exact (key C₂.size C₂ (Nat.le_refl _)).2 j₂ hj₂ h

theorem joinOrF_case {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
    (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
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
    let d := FRJWr.joinOrF prem hJ1 hJ2 hC hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root (.or C₁ C₂) := by
  intro d
  have hPJ : ClosedLbl (preR d) := preR_closed _
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR d).force (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompF : ∀ (x : Unit) (A : Form),
      (modR d).force (some ⟨Sum.inr (), x⟩) A := by
    intro x A
    exact Kripke.fal_force _ A trivial
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxOrF stab th rhs →
      (modR d).force none (.circ Y) := by
    intro Y hY
    refine Kripke.circ_intro _ ?_ ?_
    · exact ⟨some ⟨Sum.inr (), ()⟩, PJRm.prom rfl trivial, hcompF () Y⟩
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hPJ none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr u => exact hcompF u (.circ Y)
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxOrF stab th rhs) →
        (modR d).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR d).force none H) := by
    intro m
    induction m with
    | zero => intro H hH; exfalso; cases H <;> simp [Form.size] at hH
    | succ m ih =>
        intro H hH
        constructor
        · intro hHimp
          obtain ⟨hHmem, hHsh⟩ := List.mem_filter.mp hHimp
          match H, hHsh with
          | .imp A B, _ =>
              have hAu : A ∈ upsilon rhs := joinCtxOrF_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ m := by
                simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some cx =>
                  obtain ⟨c, x⟩ := cx
                  have hclo := hPJ none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (modR d).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr u => exact hcompF u (.imp A B)
                  exact hforced _
                    ((modR d).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinOrF (G := G) (C₁ := C₁) (C₂ := C₂) j hJ1 (CtxEq.refl _)⟩)
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (i := Sum.inl ⟨j, i⟩)
              (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  exact Or.inl (stab_mem_joinCtxOrF (G := G) hK.1 hKG)
            · have hmem : K ∈ impPart (joinCtxOrF stab th rhs) :=
                List.mem_filter.mpr
                  ⟨stab_mem_joinCtxOrF (G := G) hK.1 hKG, (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ m := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · match K, (List.mem_filter.mp h).2 with
              | .circ Y, _ =>
                  exact hcircF Y (stab_mem_joinCtxOrF (G := G) hK.1 hKG)
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
          | .circ Y, _ => exact hcircF Y hX
    | some cx =>
        obtain ⟨c, x⟩ := cx
        intro X hX
        cases c with
        | inl ji => exact hcompL ji x X hX
        | inr u => exact hcompF u X
  · intro hcon
    obtain ⟨j₁, -, hj₁⟩ := List.mem_map.mp hC.1
    obtain ⟨j₂, -, hj₂⟩ := List.mem_map.mp hC.2
    rcases hcon with h | h
    · exact (key C₁.size C₁ (Nat.le_refl _)).2 j₁ hj₁ h
    · exact (key C₂.size C₂ (Nat.le_refl _)).2 j₂ hj₂ h

/-- `⋈^◯,p`, the promise modal join: label-forcing as `⋈^∨,p`; the root
refutes `◯Z` with the whole cone — itself through the premise slot, each
promise component through its right formula `Z` at the component root
(`ihP`) and its `Covers`-certified tag below it (`ihT` = `tag_cone`). -/
theorem joinCircP_case {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Z : Form}
    {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form}
    (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
    (dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i))
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
    let d := FRJWr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg hΓ
    (∀ w, (modR d).forces w
        ((preR d).lbl w)) ∧
      ¬ (modR d).force
          (modR d).root (.circ Z) := by
  intro d
  have hPJ : ClosedLbl (preR d) :=
    preR_closed _
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR d).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompR : ∀ (i : Fin (k + 1)) (x : (preR (dps i)).W) (A : Form),
      A ∈ (preR (dps i)).lbl x →
      (modR d).force
        (some ⟨Sum.inr i, x⟩) A := by
    intro i x A hA
    exact (join_force_comp hPJ (i := Sum.inr i)
      (preR_closed (dps i)) A x).mpr ((ihP i).1 x A hA)
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxOrP stab th rhs Δs →
      (modR d).force
        none (.circ Y) := by
    intro Y hY
    obtain ⟨i, hi⟩ := joinCtxOrP_circ_body hJ5 hY
    refine Kripke.circ_intro _ ?_ ?_
    · refine ⟨some ⟨Sum.inr i, (preR (dps i)).root⟩,
        PJRm.prom rfl ((preR (dps i)).rm_refl _), ?_⟩
      have hiC : Clo ((preR (dps i)).lbl (preR (dps i)).root) Y :=
        clo_mono (preR_root_lbl (dps i)).subset' hi
      exact clo_forces (fun X hX => hcompR i _ X hX) hiC
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hPJ none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr i' => exact clo_forces (fun X hX => hcompR i' x X hX) hclo
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxOrP stab th rhs Δs) →
        (modR d).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR d).force none H) := by
    intro m
    induction m with
    | zero => intro H hH; exfalso; cases H <;> simp [Form.size] at hH
    | succ m ih =>
        intro H hH
        constructor
        · intro hHimp
          obtain ⟨hHmem, hHsh⟩ := List.mem_filter.mp hHimp
          match H, hHsh with
          | .imp A B, _ =>
              have hAu : A ∈ upsilon rhs := joinCtxOrP_imp_head hJ2 hHmem
              obtain ⟨j, -, hj⟩ := List.mem_map.mp hAu
              have hsz : A.size ≤ m := by
                simp only [Form.size] at hH; omega
              have hnA := (ih A hsz).2 j hj
              intro v hv hAv
              cases v with
              | none => exact absurd hAv hnA
              | some cx =>
                  obtain ⟨c, x⟩ := cx
                  have hclo := hPJ none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (modR d).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr i' => exact clo_forces (fun Y hY => hcompR i' x Y hY) hclo
                  exact hforced _
                    ((modR d).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR d) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinCircP (G := G) (Z := Z) (Δs := Δs) j hJ1 (CtxEq.refl _)⟩)
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (preI (prem j) i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hPJ (i := Sum.inl ⟨j, i⟩)
              (preI_closed (prem j) i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := wfI (prem j) (List.mem_append_left _ hK.1)
            have hKG3 := hKG
            simp only [gHat, List.mem_append] at hKG3
            rcases hKG3 with (h | h) | h
            · match K, (List.mem_filter.mp h).2 with
              | .atom p, _ =>
                  exact Or.inl (stab_mem_joinCtxOrP (G := G) hK.1 hKG (fun i => hJ7 i j _ hK.1))
            · have hmem : K ∈ impPart (joinCtxOrP stab th rhs Δs) :=
                List.mem_filter.mpr
                  ⟨stab_mem_joinCtxOrP (G := G) hK.1 hKG (fun i => hJ7 i j _ hK.1), (List.mem_filter.mp h).2⟩
              have hsz : K.size ≤ m := by
                have := size_lt_of_mem_sfm hK.2
                rw [hj] at this; omega
              exact (ih K hsz).1 hmem
            · match K, (List.mem_filter.mp h).2 with
              | .circ Y, _ =>
                  exact hcircF Y (stab_mem_joinCtxOrP (G := G) hK.1 hKG (fun i => hJ7 i j _ hK.1))
  constructor
  · intro w
    cases w with
    | none =>
        intro X hX
        have hXG : X ∈ gHat G :=
          wfR d ((hΓ X).mpr hX)
        simp only [gHat, List.mem_append] at hXG
        rcases hXG with (h | h) | h
        · have : X.isPV := (List.mem_filter.mp h).2
          match X, this with
          | .atom p, _ => exact Or.inl hX
        · have himp : X.isImp := (List.mem_filter.mp h).2
          exact (key X.size X (Nat.le_refl _)).1 (List.mem_filter.mpr ⟨hX, himp⟩)
        · have : X.isCirc := (List.mem_filter.mp h).2
          match X, this with
          | .circ Y, _ => exact hcircF Y hX
    | some cx =>
        obtain ⟨c, x⟩ := cx
        intro X hX
        cases c with
        | inl ji => exact hcompL ji x X hX
        | inr i => exact hcompR i x X hX
  · obtain ⟨j₀, -, hj₀⟩ := List.mem_map.mp hZ
    refine Kripke.not_force_circ _ ?_
    intro u hu hf
    have hu' : (PreModel.join
        (sumElems (premIdxElems prem) (List.finRange (k + 1)))
        (sumElems_complete (premIdxComplete prem) List.mem_finRange)
        (joinCtxOrP stab th rhs Δs)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun i => preR (dps i)))
        (Sum.elim (fun _ => false) (fun _ => true))).rm none u := hu
    rcases PreModel.join_rm_root hu' with h0 | ⟨c, a, hc, hra, hy⟩
    · rw [h0] at hf
      exact (key Z.size Z (Nat.le_refl _)).2 j₀ hj₀ hf
    · rw [hy] at hf
      cases c with
      | inl ji => exact Bool.noConfusion hc
      | inr i =>
          have hf' : (modR (dps i)).force a Z :=
            (join_force_comp hPJ (i := Sum.inr i)
              (preR_closed (dps i)) Z a).mp hf
          by_cases ha : a = (modR (dps i)).root
          · rw [ha] at hf'
            have hDi := (hDs i).1
            rw [← hDi] at hf'
            exact (ihP i).2 hf'
          · exact ihT i Z (hDs i).2 a hra ha hf'

/-! ## Lemma 3.9 for the repaired family -/

mutual

theorem lemma39R {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJWr G t Γ C),
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
  | _, _, _, @FRJWr.joinAt _ n stab th rhs F kept prem hJ1 hJ2 hcirc hkc hF hFnot hg _ hΓ =>
      joinAt_case prem hJ1 hJ2 hcirc hkc hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJWr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg _ hΓ =>
      joinAtP_case prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i)) hΓ
  | _, _, _, @FRJWr.joinAtF _ n stab th rhs F prem hJ1 hJ2 hF hFnot hg _ hΓ =>
      joinAtF_case prem hJ1 hJ2 hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJWr.joinOr _ n stab th rhs C₁ C₂ kept prem hJ1 hJ2 hcirc hkc hC hg _ hΓ =>
      joinOr_case prem hJ1 hJ2 hcirc hkc hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJWr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg _ hΓ =>
      joinOrP_case prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i)) hΓ
  | _, _, _, @FRJWr.joinOrF _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hC hg _ hΓ =>
      joinOrF_case prem hJ1 hJ2 hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJWr.joinCirc _ n stab th rhs Z kept prem hJ1 hJ2 hcirc hkc hZ hg _ hΓ =>
      joinCirc_case prem hJ1 hJ2 hcirc hkc hZ hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3) hΓ
  | _, _, _, @FRJWr.joinCircP _ n k stab th rhs Z tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg _ hΓ =>
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
    (d : FRJWr G t Γ C) (Z : Form),
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z) →
    ∀ u, (modR d).Rm (modR d).root u → u ≠ (modR d).root →
      ¬ (modR d).force u Z
  | _, _, _, .axR F hF hg hΓ, Z, ht, u, hu, hne, hf => hne rfl
  | _, _, _, .andR1 d _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .andR2 d _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .impIn d _ _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .circIn d _ _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, @FRJWr.joinAt _ n stab th rhs F kept prem hJ1 hJ2 hcirc hkc hF hFnot hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxAtVBase stab th F ++ kept)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJWr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hPJ : ClosedLbl (preR (FRJWr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg hΓ)) :=
        preR_closed _
      rcases htag with h' | ⟨h', hall⟩
      · rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion (h'.symm.trans h)
      · rcases ht with h | ⟨W, h, hcov⟩
        · exact Tag.noConfusion (h'.symm.trans h)
        · have hDW : Ds 0 = W := by
            have hcc := h'.symm.trans h
            injection hcc
          subst hDW
          have hu' : (PreModel.join
              (sumElems (premIdxElems prem) (List.finRange (k + 1)))
              (sumElems_complete (premIdxComplete prem) List.mem_finRange)
              (joinCtxAtP stab th rhs F Δs)
              (Sum.elim
                (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
                (fun i => preR (dps i)))
              (Sum.elim (fun _ => false) (fun _ => true))).rm none u := hu
          rcases PreModel.join_rm_root hu' with h0 | ⟨c, a, hc, hra, hy⟩
          · exact hne h0
          · rw [hy] at hf
            cases c with
            | inl ji => exact Bool.noConfusion hc
            | inr i =>
                have hf' : (modR (dps i)).force a Z :=
                  (join_force_comp hPJ (i := Sum.inr i)
                    (preR_closed (dps i)) Z a).mp hf
                refine covers_refutes hcov
                  (fun x => (modR (dps i)).Rm (modR (dps i)).root x) ?_ ?_ ?_ a hra hf'
                · exact fun x hx y hxy => (modR (dps i)).rm_trans hx hxy
                · intro x hx hfx
                  by_cases hxr : x = (modR (dps i)).root
                  · rw [hxr] at hfx
                    have hDi := (hall i).1
                    rw [← hDi] at hfx
                    exact (lemma39R (dps i)).2 hfx
                  · exact tag_cone (dps i) (Ds 0) (hall i).2 x hx hxr hfx
                · intro x hx A hA
                  have h1 : Clo (Δs i) A := clo_trans (joinCtxAtP_clo i) (clo_mono hΓ.subset hA)
                  have h2 : Clo ((preR (dps i)).lbl x) A :=
                    clo_trans (fun Y hY => preR_closed (dps i) _ _
                      ((preR (dps i)).root_le x) Y
                      ((preR_root_lbl (dps i) Y).mpr hY)) h1
                  exact clo_forces (fun Y hY => (lemma39R (dps i)).1 x Y hY) h2
  | _, _, _, .joinAtF prem hJ1 hJ2 hF hFnot hg hΓ, Z, ht, u, hu, hne, hf => by
      rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion h
  | _, _, _, @FRJWr.joinOr _ n stab th rhs C₁ C₂ kept prem hJ1 hJ2 hcirc hkc hC hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxOrVBase stab th ++ kept)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJWr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hPJ : ClosedLbl (preR (FRJWr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg hΓ)) :=
        preR_closed _
      rcases htag with h' | ⟨h', hall⟩
      · rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion (h'.symm.trans h)
      · rcases ht with h | ⟨W, h, hcov⟩
        · exact Tag.noConfusion (h'.symm.trans h)
        · have hDW : Ds 0 = W := by
            have hcc := h'.symm.trans h
            injection hcc
          subst hDW
          have hu' : (PreModel.join
              (sumElems (premIdxElems prem) (List.finRange (k + 1)))
              (sumElems_complete (premIdxComplete prem) List.mem_finRange)
              (joinCtxOrP stab th rhs Δs)
              (Sum.elim
                (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
                (fun i => preR (dps i)))
              (Sum.elim (fun _ => false) (fun _ => true))).rm none u := hu
          rcases PreModel.join_rm_root hu' with h0 | ⟨c, a, hc, hra, hy⟩
          · exact hne h0
          · rw [hy] at hf
            cases c with
            | inl ji => exact Bool.noConfusion hc
            | inr i =>
                have hf' : (modR (dps i)).force a Z :=
                  (join_force_comp hPJ (i := Sum.inr i)
                    (preR_closed (dps i)) Z a).mp hf
                refine covers_refutes hcov
                  (fun x => (modR (dps i)).Rm (modR (dps i)).root x) ?_ ?_ ?_ a hra hf'
                · exact fun x hx y hxy => (modR (dps i)).rm_trans hx hxy
                · intro x hx hfx
                  by_cases hxr : x = (modR (dps i)).root
                  · rw [hxr] at hfx
                    have hDi := (hall i).1
                    rw [← hDi] at hfx
                    exact (lemma39R (dps i)).2 hfx
                  · exact tag_cone (dps i) (Ds 0) (hall i).2 x hx hxr hfx
                · intro x hx A hA
                  have h1 : Clo (Δs i) A := clo_trans (joinCtxOrP_clo i) (clo_mono hΓ.subset hA)
                  have h2 : Clo ((preR (dps i)).lbl x) A :=
                    clo_trans (fun Y hY => preR_closed (dps i) _ _
                      ((preR (dps i)).root_le x) Y
                      ((preR_root_lbl (dps i) Y).mpr hY)) h1
                  exact clo_forces (fun Y hY => (lemma39R (dps i)).1 x Y hY) h2
  | _, _, _, .joinOrF prem hJ1 hJ2 hC hg hΓ, Z, ht, u, hu, hne, hf => by
      rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion h
  | _, _, _, @FRJWr.joinCirc _ n stab th rhs Z0 kept prem hJ1 hJ2 hcirc hkc hZ0 hg _ hΓ, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxOrVBase stab th ++ kept)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJWr.joinCircP _ n k stab th rhs Z0 tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ0 hg _ hΓ, Z, ht, u, hu, hne, hf => by
      rcases ht with h | ⟨W, h, hcov⟩
      · exact Tag.noConfusion h
      · have hWZ : Z0 = W := by injection h
        subst hWZ
        have hu' : (PreModel.join
            (sumElems (premIdxElems prem) (List.finRange (k + 1)))
            (sumElems_complete (premIdxComplete prem) List.mem_finRange)
            (joinCtxOrP stab th rhs Δs)
            (Sum.elim
              (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
              (fun i => preR (dps i)))
            (Sum.elim (fun _ => false) (fun _ => true))).rm none u := hu
        rcases PreModel.join_rm_root hu' with h0 | ⟨c, a, hc, hra, hy⟩
        · exact hne h0
        · rw [hy] at hf
          cases c with
          | inl ji => exact Bool.noConfusion hc
          | inr i =>
              have hPJ : ClosedLbl
                  (preR (FRJWr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ0 hg hΓ)) :=
                preR_closed _
              have hf' : (modR (dps i)).force a Z :=
                (join_force_comp hPJ (i := Sum.inr i)
                  (preR_closed (dps i)) Z a).mp hf
              refine covers_refutes hcov
                (fun x => (modR (dps i)).Rm (modR (dps i)).root x) ?_ ?_ ?_ a hra hf'
              · exact fun x hx y hxy => (modR (dps i)).rm_trans hx hxy
              · intro x hx hfx
                by_cases hxr : x = (modR (dps i)).root
                · rw [hxr] at hfx
                  have hDi := (hDs i).1
                  rw [← hDi] at hfx
                  exact (lemma39R (dps i)).2 hfx
                · exact tag_cone (dps i) Z0 (hDs i).2 x hx hxr hfx
              · intro x hx A hA
                have h1 : Clo (Δs i) A := clo_trans (joinCtxOrP_clo i) (clo_mono hΓ.subset hA)
                have h2 : Clo ((preR (dps i)).lbl x) A :=
                  clo_trans (fun Y hY => preR_closed (dps i) _ _
                    ((preR (dps i)).root_le x) Y
                    ((preR_root_lbl (dps i) Y).mpr hY)) h1
                exact clo_forces (fun Y hY => (lemma39R (dps i)).1 x Y hY) h2

theorem lemma39I0 {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJWi G St Th C) (i : RegIdx d) (w : (preI d i).W),
    ((preI d i).toKripke (preI_closed d i)).forces w ((preI d i).lbl w)
  | _, _, _, .axI _ _ _ _, i, _ => (i : Empty).elim
  | _, _, _, .andI1 d _, i, w => lemma39I0 d i w
  | _, _, _, .andI2 d _, i, w => lemma39I0 d i w
  | _, _, _, .orI d₁ d₂ _ _ _ _ _, i, w => by
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ => exact lemma39I0 d₁ i₁ w
      | .inr i₂ => exact lemma39I0 d₂ i₂ w
  | _, _, _, .impInI d _ _ _ _ _ _, i, w => lemma39I0 d i w
  | _, _, _, .lift d _, _, w => (lemma39R d).1 w
  | _, _, _, .circNotIn d _ _ _, _, w => (lemma39R d).1 w
  | _, _, _, @FRJWi.axIC _ F ats hats hFf hg _ hTh, _, w => by
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
    (d : FRJWi G St Th C) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
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
  | _, _, _, @FRJWi.orI _ St₁ Th₁ St₂ Th₂ C₁ C₂ d₁ d₂ h₁ h₂ hg _ _ hStE hThE,
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
  | _, _, _, @FRJWi.impInI _ St Th Lam ThLam A B d hpre hdisj hA hg _ _ hStE hThE,
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
  | _, _, _, @FRJWi.lift _ t Γ Th C d hTh,
      P, hP, w, hw, hlbl, hroot, hforce => by
      -- `(R^bar)`'s clause (`not_force_of_rootAbove`, `wip/rbar.lean`):
      -- `RootAbove` places `v ≥ w` agreeing with the root of `preR d`;
      -- that root refutes `C` by Lemma 3.9(i); forcing is monotone.
      -- `lift`'s own side condition `hTh` plays no part.
      intro hcon
      obtain ⟨v, hwv, hiff⟩ := hroot ()
      exact (lemma39R d).2 ((hiff C).mp ((P.toKripke hP).force_mono hwv hcon))
  | _, _, _, @FRJWi.axIC _ F ats hats hFf hg _ hTh, P, hP, w, hw, hlbl, hroot, hforce => by
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
  | _, _, _, @FRJWi.circNotIn _ t Γ Th Z d htag hTh hg,
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

/-! ## Theorem 3.10 and Theorem 3.1 for `FRJW(G)` -/

/-- **Theorem 3.10 for `FRJW(G)`.**  The model extracted from an
`FRJW(G)`-disproof of `G` is a countermodel for `G`. -/
theorem modR_countermodel {G : Form} {t : Tag} {Γ : List Form} (d : FRJWr G t Γ G) :
    Countermodel (modR d) G := (lemma39R d).2

end FRJ.W

namespace FRJ

/-- **Soundness of `FRJW(G)`, for PLL**: an FRJW disproof of `G` means
`G` is not valid in all constraint models.  (As for `FRJ.soundness`, the
conclusion is against the wider fallible class because the fallible join
builds a model with a fallible world.) -/
theorem soundnessW {G : Form} (h : DisprovableW G) : ¬ PLL G := by
  obtain ⟨t, Γ, ⟨d⟩⟩ := h
  exact not_PLL_of_countermodel (W.modR_countermodel d)

/-! ## Sanity checks

An atom is underivable in PLL, re-derived through `FRJW(G)` (via `Ax^R`
alone); and by W2's conservativity every FRJV disproof transfers, so
`soundnessV` factors through `soundnessW`. -/

example (p : String) : ¬ PLL (.atom p) :=
  soundnessW ⟨.barren, rm (gAt (.atom p)) (.atom p),
    ⟨.axR (.atom p) rfl (sfR_self _) (CtxEq.refl _)⟩⟩

example {G : Form} (h : ProvableV G) : ¬ PLL G :=
  soundnessW (disprovableW_of_provableV h)

end FRJ

/-! ## Axiom pins -/

/-- info: 'FRJ.W.lemma39R' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.W.lemma39R

/-- info: 'FRJ.W.tag_cone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.W.tag_cone

/-- info: 'FRJ.soundnessW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.soundnessW
