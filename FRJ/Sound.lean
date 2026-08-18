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

theorem prime_not_isCirc {F : Form} (h : F.isPrime) : ¬ F.isCirc := by
  cases F <;> simp_all [Form.isPrime, Form.isCirc]

/-- A prime formula is forced at an INFALLIBLE world exactly when it is a
variable present in the label; so if it is absent it is not forced.  (At
a fallible world everything is forced, which is why the hypothesis is
needed; every join root and axiom world is infallible.) -/
theorem not_force_prime {P : PreModel} (h : ClosedLbl P) {w : P.W} {F : Form}
    (hF : F.isPrime) (hnot : F ∉ P.lbl w) (hfal : ¬ P.fal w) :
    ¬ (P.toKripke h).force w F := by
  cases F with
  | atom p => exact fun hc => hc.elim (fun hc => hnot hc) hfal
  | bot => exact fun hc => hfal hc
  | and A B => exact absurd hF (by simp [Form.isPrime])
  | or A B => exact absurd hF (by simp [Form.isPrime])
  | imp A B => exact absurd hF (by simp [Form.isPrime])
  | circ A => exact absurd hF (by simp [Form.isPrime])

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

/-- An implication never inhabits a modal zone. -/
theorem imp_not_mem_joinCtxCircP {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {Δs : Fin (k + 1) → List Form} {A B : Form} :
    Form.imp A B ∉ joinCtxCircP stab th Δs := by
  intro h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact Bool.noConfusion (List.mem_filter.mp hi).2
  · exact Bool.noConfusion (isCirc_of_mem_restrictC h)

theorem imp_not_mem_joinCtxCircF {n : Nat} {stab th : Fin (n + 1) → List Form}
    {A B : Form} :
    Form.imp A B ∉ joinCtxCircF stab th := by
  intro h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact Bool.noConfusion (List.mem_filter.mp hi).2
  · exact Bool.noConfusion
      (List.mem_filter.mp (interAll_subset 0 h)).2

theorem joinCtxAtP_imp_head {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F A B : Form} {Δs : Fin (k + 1) → List Form}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (h : Form.imp A B ∈ joinCtxAtP stab th rhs F Δs) : A ∈ upsilon rhs := by
  rcases List.mem_append.mp (restrictP_subset h) with h | h
  · exact joinCtxAt_imp_head hJ2 h
  · exact absurd h imp_not_mem_joinCtxCircP

theorem joinCtxAtF_imp_head {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F A B : Form}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (h : Form.imp A B ∈ joinCtxAtF stab th rhs F) : A ∈ upsilon rhs := by
  rcases List.mem_append.mp h with h | h
  · exact joinCtxAt_imp_head hJ2 h
  · exact absurd h imp_not_mem_joinCtxCircF

theorem joinCtxOrP_imp_head {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {A B : Form} {Δs : Fin (k + 1) → List Form}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (h : Form.imp A B ∈ joinCtxOrP stab th rhs Δs) : A ∈ upsilon rhs := by
  rcases List.mem_append.mp (restrictP_subset h) with h | h
  · exact joinCtxOr_imp_head hJ2 h
  · exact absurd h imp_not_mem_joinCtxCircP

theorem joinCtxOrF_imp_head {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {A B : Form}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (h : Form.imp A B ∈ joinCtxOrF stab th rhs) : A ∈ upsilon rhs := by
  rcases List.mem_append.mp h with h | h
  · exact joinCtxOr_imp_head hJ2 h
  · exact absurd h imp_not_mem_joinCtxCircF

/-- `Σ_j` sits inside the join's conclusion context, split by shape.  For
the BARREN joins the modal shape is excluded by the side condition
`Σ^◯ = ∅`. -/
theorem stab_mem_joinCtxAt {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {j : Fin (n + 1)} {K : Form}
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hK : K ∈ stab j) (hKG : K ∈ gHat G) :
    K ∈ joinCtxAt stab th rhs F := by
  simp only [joinCtxAt, List.mem_append]
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with (hKG | hKG) | hKG
  · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩)))
  · exact Or.inl (Or.inr (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))
  · exfalso
    have : K ∈ unionAll (fun j => circPart (stab j)) := mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩
    rw [hcirc] at this
    exact List.not_mem_nil this

theorem stab_mem_joinCtxOr {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {j : Fin (n + 1)} {K : Form}
    (hcirc : unionAll (fun j => circPart (stab j)) = [])
    (hK : K ∈ stab j) (hKG : K ∈ gHat G) :
    K ∈ joinCtxOr stab th rhs := by
  simp only [joinCtxOr, List.mem_append]
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with (hKG | hKG) | hKG
  · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩)))
  · exact Or.inl (Or.inr (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))
  · exfalso
    have : K ∈ unionAll (fun j => circPart (stab j)) := mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩
    rw [hcirc] at this
    exact List.not_mem_nil this

/-- For the PROMISE and FALLIBLE joins the modal shape lands in the kept
modal zone (`Σ^◯`). -/
theorem stab_mem_joinCtxAtP {G : Form} {n k : Nat}
    {stab th : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form} {F : Form}
    {Δs : Fin (k + 1) → List Form} {j : Fin (n + 1)} {K : Form}
    (hK : K ∈ stab j) (hKG : K ∈ gHat G) (hcl : ∀ i, Clo (Δs i) K) :
    K ∈ joinCtxAtP stab th rhs F Δs := by
  refine mem_restrictP.mpr ⟨?_, hcl⟩
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with (hKG | hKG) | hKG
  · exact List.mem_append_left _ (by
      simp only [joinCtxAt, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
        ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))))
  · exact List.mem_append_left _ (by
      simp only [joinCtxAt, List.mem_append]
      exact Or.inl (Or.inr (mem_unionAll.mpr
        ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩)))
  · exact List.mem_append_right _ (List.mem_append_left _ (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))

theorem stab_mem_joinCtxAtF {G : Form} {n : Nat}
    {stab th : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form} {F : Form}
    {j : Fin (n + 1)} {K : Form}
    (hK : K ∈ stab j) (hKG : K ∈ gHat G) :
    K ∈ joinCtxAtF stab th rhs F := by
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with (hKG | hKG) | hKG
  · exact List.mem_append_left _ (by
      simp only [joinCtxAt, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
        ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))))
  · exact List.mem_append_left _ (by
      simp only [joinCtxAt, List.mem_append]
      exact Or.inl (Or.inr (mem_unionAll.mpr
        ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩)))
  · exact List.mem_append_right _ (List.mem_append_left _ (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))

theorem stab_mem_joinCtxOrP {G : Form} {n k : Nat}
    {stab th : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form}
    {Δs : Fin (k + 1) → List Form} {j : Fin (n + 1)} {K : Form}
    (hK : K ∈ stab j) (hKG : K ∈ gHat G) (hcl : ∀ i, Clo (Δs i) K) :
    K ∈ joinCtxOrP stab th rhs Δs := by
  refine mem_restrictP.mpr ⟨?_, hcl⟩
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with (hKG | hKG) | hKG
  · exact List.mem_append_left _ (by
      simp only [joinCtxOr, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
        ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))))
  · exact List.mem_append_left _ (by
      simp only [joinCtxOr, List.mem_append]
      exact Or.inl (Or.inr (mem_unionAll.mpr
        ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩)))
  · exact List.mem_append_right _ (List.mem_append_left _ (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))

theorem stab_mem_joinCtxOrF {G : Form} {n : Nat}
    {stab th : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form}
    {j : Fin (n + 1)} {K : Form}
    (hK : K ∈ stab j) (hKG : K ∈ gHat G) :
    K ∈ joinCtxOrF stab th rhs := by
  simp only [gHat, List.mem_append] at hKG
  rcases hKG with (hKG | hKG) | hKG
  · exact List.mem_append_left _ (by
      simp only [joinCtxOr, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
        ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))))
  · exact List.mem_append_left _ (by
      simp only [joinCtxOr, List.mem_append]
      exact Or.inl (Or.inr (mem_unionAll.mpr
        ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩)))
  · exact List.mem_append_right _ (List.mem_append_left _ (mem_unionAll.mpr
      ⟨j, List.mem_filter.mpr ⟨hK, (List.mem_filter.mp hKG).2⟩⟩))

/-- No `◯`-formula inhabits the paper's join context: its four parts are
atomic or implicational by construction. -/
theorem circ_not_mem_joinCtxAt {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F Y : Form} :
    Form.circ Y ∉ joinCtxAt stab th rhs F := by
  intro h
  simp only [joinCtxAt, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact Bool.noConfusion (List.mem_filter.mp hi).2
  · exact Bool.noConfusion
      (List.mem_filter.mp (interAll_subset 0 (rm_subset h))).2
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact Bool.noConfusion (List.mem_filter.mp hi).2
  · exact Bool.noConfusion
      (List.mem_filter.mp (interAll_subset 0 (restrict_subset h))).2

theorem circ_not_mem_joinCtxOr {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Y : Form} :
    Form.circ Y ∉ joinCtxOr stab th rhs := by
  intro h
  simp only [joinCtxOr, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact Bool.noConfusion (List.mem_filter.mp hi).2
  · exact Bool.noConfusion (List.mem_filter.mp (interAll_subset 0 h)).2
  · obtain ⟨i, hi⟩ := mem_unionAll.mp h
    exact Bool.noConfusion (List.mem_filter.mp hi).2
  · exact Bool.noConfusion
      (List.mem_filter.mp (interAll_subset 0 (restrict_subset h))).2

/-- A `◯`-formula kept by a promise join has its body in the closure of
SOME promise context: (J5) for the stable part, the restriction for the
second-zone part. -/
theorem joinCtxAtP_circ_body {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F Y : Form} {Δs : Fin (k + 1) → List Form}
    (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (h : Form.circ Y ∈ joinCtxAtP stab th rhs F Δs) : ∃ i, Clo (Δs i) Y := by
  rcases List.mem_append.mp (restrictP_subset h) with h | h
  · exact absurd h circ_not_mem_joinCtxAt
  · rcases List.mem_append.mp h with h | h
    · exact hJ5 Y h
    · exact (mem_restrictC.mp h).2

theorem joinCtxOrP_circ_body {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Y : Form} {Δs : Fin (k + 1) → List Form}
    (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (h : Form.circ Y ∈ joinCtxOrP stab th rhs Δs) : ∃ i, Clo (Δs i) Y := by
  rcases List.mem_append.mp (restrictP_subset h) with h | h
  · exact absurd h circ_not_mem_joinCtxOr
  · rcases List.mem_append.mp h with h | h
    · exact hJ5 Y h
    · exact (mem_restrictC.mp h).2

/-- **The chain certificate refutes what it covers.**  Over any set `S` of
worlds that is `Rm`-forward-closed, hereditarily refutes `W`, and forces
the closure of `Γ`, every member refutes every `Z` with `Covers Γ W Z`:
`◯`-iterates through the sub-cone, conjunctions through the refuted
conjunct, implications through the forced antecedent. -/
theorem covers_refutes {K : Kripke} {Γ : List Form} {W Z : Form}
    (hcov : Covers Γ W Z) (S : K.W → Prop)
    (hfwd : ∀ x, S x → ∀ y, K.Rm x y → S y)
    (hW : ∀ x, S x → ¬ K.force x W)
    (hΓ : ∀ x, S x → ∀ A : Form, Clo Γ A → K.force x A) :
    ∀ u, S u → ¬ K.force u Z := by
  induction hcov with
  | refl => exact fun u hu => hW u hu
  | circ _ ih =>
      intro u hu hf
      obtain ⟨y, hRy, hy⟩ := hf u (K.le_refl u)
      exact ih y (hfwd u hu y hRy) hy
  | andL _ ih => exact fun u hu hf => ih u hu hf.1
  | andR _ ih => exact fun u hu hf => ih u hu hf.2
  | imp _ hA ih =>
      intro u hu hf
      exact ih u hu (hf u (K.le_refl u) (hΓ u hu _ hA))

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
        ¬ (P.toKripke hP).force w (rhs j)) :
    (∀ w, (modR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).forces w
        ((preR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).force
          (modR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).root F := by
  have hPJ : ClosedLbl (preR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)) :=
    preR_closed _
  -- every component world forces its own label
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (preI_closed (prem ji.1) ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  -- (P2) and (P3), by the secondary induction on `size H`
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxAt stab th rhs F) →
        (modR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).force none H) := by
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
                      (modR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hHmem
                  have : (modR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact this _ ((modR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)).le_refl _) hAv
        · -- (P3)
          intro j hj hcon
          refine ihI j (preR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg)) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single ⟨_, Step.joinAt (G := G) (F := F) j hJ1⟩)
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
        have hXG : X ∈ gHat G := wfR (FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg) hX
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
        ¬ (P.toKripke hP).force w (rhs j)) :
    (∀ w, (modR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).forces w
        ((preR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).force
          (modR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).root (.or C₁ C₂) := by
  have hPJ : ClosedLbl (preR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)) := preR_closed _
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (preI_closed (prem ji.1) ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxOr stab th rhs) →
        (modR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).force none H) := by
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
                      (modR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hHmem
                  have hfv : (modR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact hfv _ ((modR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg)) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
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
        have hXG : X ∈ gHat G := wfR (FRJr.joinOr prem hJ1 hJ2 hcirc hC hg) hX
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
        ¬ (modR (dps i)).force (modR (dps i)).root (Ds i)) :
    (∀ w, (modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).forces w
        ((preR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).force
          (modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).root F := by
  have hPJ : ClosedLbl (preR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)) :=
    preR_closed _
  -- the two component families force their own labels
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompR : ∀ (i : Fin (k + 1)) (x : (preR (dps i)).W) (A : Form),
      A ∈ (preR (dps i)).lbl x →
      (modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).force
        (some ⟨Sum.inr i, x⟩) A := by
    intro i x A hA
    exact (join_force_comp hPJ (i := Sum.inr i)
      (preR_closed (dps i)) A x).mpr ((ihP i).1 x A hA)
  -- (P2◯): every kept modal formula is forced at the root, by `circ_intro`
  -- with the designated promise root as witness
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxAtP stab th rhs F Δs →
      (modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).force
        none (.circ Y) := by
    intro Y hY
    obtain ⟨i, hi⟩ := joinCtxAtP_circ_body hJ5 hY
    refine Kripke.circ_intro _ ?_ ?_
    · refine ⟨some ⟨Sum.inr i, (preR (dps i)).root⟩,
        PJRm.prom rfl ((preR (dps i)).rm_refl _), ?_⟩
      have hiC : Clo ((preR (dps i)).lbl (preR (dps i)).root) Y := by
        rw [preR_root_lbl (dps i)]; exact hi
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
        (modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).force none H) := by
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
                  have hforced : (modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr i' => exact clo_forces (fun Y hY => hcompR i' x Y hY) hclo
                  exact hforced _
                    ((modR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinAtP (G := G) (F := F) (Δs := Δs) j hJ1⟩)
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
          wfR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg) hX
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
        ¬ (P.toKripke hP).force w (rhs j)) :
    (∀ w, (modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).forces w
        ((preR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).force
          (modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).root F := by
  have hPJ : ClosedLbl (preR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)) :=
    preR_closed _
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  -- the declared fallible world forces everything
  have hcompF : ∀ (x : Unit) (A : Form),
      (modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).force
        (some ⟨Sum.inr (), x⟩) A := by
    intro x A
    exact Kripke.fal_force _ A trivial
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxAtF stab th rhs F →
      (modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).force none (.circ Y) := by
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
        (modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).force none H) := by
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
                  have hforced : (modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr u => exact hcompF u (.imp A B)
                  exact hforced _
                    ((modR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg)) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinAtF (G := G) (F := F) j hJ1⟩)
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
        have hXG : X ∈ gHat G := wfR (FRJr.joinAtF prem hJ1 hJ2 hF hFnot hg) hX
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
        ¬ (modR (dps i)).force (modR (dps i)).root (Ds i)) :
    (∀ w, (modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).forces w
        ((preR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).force
          (modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).root (.or C₁ C₂) := by
  have hPJ : ClosedLbl (preR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)) :=
    preR_closed _
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompR : ∀ (i : Fin (k + 1)) (x : (preR (dps i)).W) (A : Form),
      A ∈ (preR (dps i)).lbl x →
      (modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).force
        (some ⟨Sum.inr i, x⟩) A := by
    intro i x A hA
    exact (join_force_comp hPJ (i := Sum.inr i)
      (preR_closed (dps i)) A x).mpr ((ihP i).1 x A hA)
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxOrP stab th rhs Δs →
      (modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).force
        none (.circ Y) := by
    intro Y hY
    obtain ⟨i, hi⟩ := joinCtxOrP_circ_body hJ5 hY
    refine Kripke.circ_intro _ ?_ ?_
    · refine ⟨some ⟨Sum.inr i, (preR (dps i)).root⟩,
        PJRm.prom rfl ((preR (dps i)).rm_refl _), ?_⟩
      have hiC : Clo ((preR (dps i)).lbl (preR (dps i)).root) Y := by
        rw [preR_root_lbl (dps i)]; exact hi
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
        (modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).force none H) := by
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
                  have hforced : (modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr i' => exact clo_forces (fun Y hY => hcompR i' x Y hY) hclo
                  exact hforced _
                    ((modR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinOrP (G := G) (C₁ := C₁) (C₂ := C₂) (Δs := Δs) j hJ1⟩)
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
          wfR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg) hX
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
        ¬ (P.toKripke hP).force w (rhs j)) :
    (∀ w, (modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).forces w
        ((preR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).force
          (modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).root (.or C₁ C₂) := by
  have hPJ : ClosedLbl (preR (FRJr.joinOrF prem hJ1 hJ2 hC hg)) := preR_closed _
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).force (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompF : ∀ (x : Unit) (A : Form),
      (modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).force (some ⟨Sum.inr (), x⟩) A := by
    intro x A
    exact Kripke.fal_force _ A trivial
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxOrF stab th rhs →
      (modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).force none (.circ Y) := by
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
        (modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).force none H) := by
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
                  have hforced : (modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr u => exact hcompF u (.imp A B)
                  exact hforced _
                    ((modR (FRJr.joinOrF prem hJ1 hJ2 hC hg)).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR (FRJr.joinOrF prem hJ1 hJ2 hC hg)) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinOrF (G := G) (C₁ := C₁) (C₂ := C₂) j hJ1⟩)
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
        have hXG : X ∈ gHat G := wfR (FRJr.joinOrF prem hJ1 hJ2 hC hg) hX
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
        ¬ (P.toKripke hP).force w (rhs j)) :
    (∀ w, (modR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).forces w
        ((preR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).force
          (modR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).root (.circ Z) := by
  have hPJ : ClosedLbl (preR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)) := preR_closed _
  have hcomp : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).force (some ⟨ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (preI_closed (prem ji.1) ji.2) A x).mpr
      (ihI0 ji.1 ji.2 x A hA)
  have key : ∀ (k : Nat) (H : Form), H.size ≤ k →
      (H ∈ impPart (joinCtxOr stab th rhs) →
        (modR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).force none H) := by
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
                      (modR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).force (some ⟨ji, x⟩) Y :=
                    fun Y hY => hcomp ji x Y hY
                  have hclo := hPJ none (some ⟨ji, x⟩) hv (.imp A B) hHmem
                  have hfv : (modR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).force
                      (some ⟨ji, x⟩) (.imp A B) := clo_forces hlblv hclo
                  exact hfv _ ((modR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg)) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinCirc (G := G) (Z := Z) j hJ1⟩)
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
        have hXG : X ∈ gHat G := wfR (FRJr.joinCirc prem hJ1 hJ2 hcirc hZ hg) hX
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
          u ≠ (modR (dps i)).root → ¬ (modR (dps i)).force u Z') :
    (∀ w, (modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).forces w
        ((preR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).lbl w)) ∧
      ¬ (modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).force
          (modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).root (.circ Z) := by
  have hPJ : ClosedLbl (preR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)) :=
    preR_closed _
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × RegIdx (prem j))
      (x : (preI (prem ji.1) ji.2).W) (A : Form),
      A ∈ (preI (prem ji.1) ji.2).lbl x →
      (modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hPJ (i := Sum.inl ji)
      (preI_closed (prem ji.1) ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompR : ∀ (i : Fin (k + 1)) (x : (preR (dps i)).W) (A : Form),
      A ∈ (preR (dps i)).lbl x →
      (modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).force
        (some ⟨Sum.inr i, x⟩) A := by
    intro i x A hA
    exact (join_force_comp hPJ (i := Sum.inr i)
      (preR_closed (dps i)) A x).mpr ((ihP i).1 x A hA)
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxOrP stab th rhs Δs →
      (modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).force
        none (.circ Y) := by
    intro Y hY
    obtain ⟨i, hi⟩ := joinCtxOrP_circ_body hJ5 hY
    refine Kripke.circ_intro _ ?_ ?_
    · refine ⟨some ⟨Sum.inr i, (preR (dps i)).root⟩,
        PJRm.prom rfl ((preR (dps i)).rm_refl _), ?_⟩
      have hiC : Clo ((preR (dps i)).lbl (preR (dps i)).root) Y := by
        rw [preR_root_lbl (dps i)]; exact hi
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
        (modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).force none H) := by
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
                  have hforced : (modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr i' => exact clo_forces (fun Y hY => hcompR i' x Y hY) hclo
                  exact hforced _
                    ((modR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (preR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg)) hPJ none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact lhs_clo_of_steps
              (Relation.ReflTransGen.single
                ⟨_, Step.joinCircP (G := G) (Z := Z) (Δs := Δs) j hJ1⟩)
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
          wfR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg) hX
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


mutual

theorem lemma39R {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C),
    (∀ w : (preR d).W, (modR d).forces w ((preR d).lbl w)) ∧
      ¬ (modR d).force (modR d).root C
  | _, _, _, .axR F hF hg => by
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
      have hΓ := ha (preR d).root
      rw [preR_root_lbl d] at hΓ
      exact hcon _ ((modR d).le_refl _) (clo_forces hΓ hA)
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
  | _, _, _, @FRJr.joinAt _ n stab th rhs F prem hJ1 hJ2 hcirc hF hFnot hg =>
      joinAt_case prem hJ1 hJ2 hcirc hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
  | _, _, _, @FRJr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg =>
      joinAtP_case prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i))
  | _, _, _, @FRJr.joinAtF _ n stab th rhs F prem hJ1 hJ2 hF hFnot hg =>
      joinAtF_case prem hJ1 hJ2 hF hFnot hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
  | _, _, _, @FRJr.joinOr _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hcirc hC hg =>
      joinOr_case prem hJ1 hJ2 hcirc hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
  | _, _, _, @FRJr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg =>
      joinOrP_case prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i))
  | _, _, _, @FRJr.joinOrF _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hC hg =>
      joinOrF_case prem hJ1 hJ2 hC hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
  | _, _, _, @FRJr.joinCirc _ n stab th rhs Z prem hJ1 hJ2 hcirc hZ hg =>
      joinCirc_case prem hJ1 hJ2 hcirc hZ hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
  | _, _, _, @FRJr.joinCircP _ n k stab th rhs Z tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg =>
      joinCircP_case prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ hg
        (fun j i x => lemma39I0 (prem j) i x)
        (fun j P hP w hw h1 h2 h3 => lemma39I (prem j) P hP w hw h1 h2 h3)
        (fun i => lemma39R (dps i))
        (fun i => tag_cone (dps i))

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
  | _, _, _, .axR F hF hg, Z, ht, u, hu, hne, hf => hne rfl
  | _, _, _, .andR1 d _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .andR2 d _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .impIn d _ _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, .circIn d _ _, Z, ht, u, hu, hne, hf => tag_cone d Z ht u hu hne hf
  | _, _, _, @FRJr.joinAt _ n stab th rhs F prem hJ1 hJ2 hcirc hF hFnot hg, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxAt stab th rhs F)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg, Z, ht, u, hu, hne, hf => by
      have hPJ : ClosedLbl (preR (FRJr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7 htag hF hFnot hg)) :=
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
                  have h1 : Clo (Δs i) A := clo_trans (joinCtxAtP_clo i) hA
                  have h2 : Clo ((preR (dps i)).lbl x) A :=
                    clo_trans (fun Y hY => preR_closed (dps i) _ _
                      ((preR (dps i)).root_le x) Y
                      (by rw [preR_root_lbl (dps i)]; exact hY)) h1
                  exact clo_forces (fun Y hY => (lemma39R (dps i)).1 x Y hY) h2
  | _, _, _, .joinAtF prem hJ1 hJ2 hF hFnot hg, Z, ht, u, hu, hne, hf => by
      rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion h
  | _, _, _, @FRJr.joinOr _ n stab th rhs C₁ C₂ prem hJ1 hJ2 hcirc hC hg, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxOr stab th rhs)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg, Z, ht, u, hu, hne, hf => by
      have hPJ : ClosedLbl (preR (FRJr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7 htag hC hg)) :=
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
                  have h1 : Clo (Δs i) A := clo_trans (joinCtxOrP_clo i) hA
                  have h2 : Clo ((preR (dps i)).lbl x) A :=
                    clo_trans (fun Y hY => preR_closed (dps i) _ _
                      ((preR (dps i)).root_le x) Y
                      (by rw [preR_root_lbl (dps i)]; exact hY)) h1
                  exact clo_forces (fun Y hY => (lemma39R (dps i)).1 x Y hY) h2
  | _, _, _, .joinOrF prem hJ1 hJ2 hC hg, Z, ht, u, hu, hne, hf => by
      rcases ht with h | ⟨W, h, -⟩ <;> exact Tag.noConfusion h

  | _, _, _, @FRJr.joinCirc _ n stab th rhs Z0 prem hJ1 hJ2 hcirc hZ0 hg, Z, ht, u, hu, hne, hf => by
      have hu' : (PreModel.join (premIdxElems prem) (premIdxComplete prem)
          (joinCtxOr stab th rhs)
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ => false)).rm none u := hu
      exact hne (PreModel.join_rm_root_barren (fun _ => rfl) hu')
  | _, _, _, @FRJr.joinCircP _ n k stab th rhs Z0 tps Δs Ds prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ0 hg, Z, ht, u, hu, hne, hf => by
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
                  (preR (FRJr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7 hDs hZ0 hg)) :=
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
                have h1 : Clo (Δs i) A := clo_trans (joinCtxOrP_clo i) hA
                have h2 : Clo ((preR (dps i)).lbl x) A :=
                  clo_trans (fun Y hY => preR_closed (dps i) _ _
                    ((preR (dps i)).root_le x) Y
                    (by rw [preR_root_lbl (dps i)]; exact hY)) h1
                exact clo_forces (fun Y hY => (lemma39R (dps i)).1 x Y hY) h2

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
  | _, _, _, .circNotIn d _ _ _, _, w => (lemma39R d).1 w
  | _, _, _, @FRJi.axIC _ F ats hats hFf hg, _, w => by
      -- the mounted BARE final world (the ◯⊥-false species: no fallible
      -- Rm-access, so `◯Y ≡ Y` on its own cone) forces its zone: every
      -- member is `classForce`-true by construction, and single-world
      -- forcing IS `classForce`
      intro X hX
      have hcf : classForce ats X = true :=
        (List.mem_filter.mp (mem_nf.mp hX).2).2
      exact (PreModel.leaf_force_iff (fun p => vacZoneA_atom hats) X).mpr hcf

theorem lemma39I {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C) (P : PreModel) (hP : ClosedLbl P) (w : P.W),
    ¬ P.fal w →
    (∀ X ∈ P.lbl w, Clo (St ++ Th) X) →
    (∀ i : RegIdx d, RootAbove P hP w (preI d i) (preI_closed d i)) →
    (P.toKripke hP).forces w (cap St (sfm C)) →
    ¬ (P.toKripke hP).force w C
  | _, _, _, .axI F hF hg, P, hP, w, hw, hlbl, _, _ => by
      match F, hF with
      | .bot, _ => exact fun h => hw h
      | .atom p, _ =>
          intro hcon
          have hmem : Form.atom p ∈ P.lbl w := hcon.elim (fun h => h)
            (fun h => absurd h hw)
          have hin := clo_pv (hlbl _ hmem)
          simp only [List.nil_append, mem_nf, List.mem_append] at hin
          rcases hin.2 with (hin' | hin') | hin'
          · exact (mem_rm.mp hin').1 rfl
          · have himp := (List.mem_filter.mp hin').2
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
  | _, _, _, @FRJi.orI _ St₁ Th₁ St₂ Th₂ C₁ C₂ d₁ d₂ h₁ h₂ hg,
      P, hP, w, hw, hlbl, hroot, hforce => by
      intro hcon
      rcases hcon with hcon | hcon
      · refine lemma39I d₁ P hP w hw ?_ (fun i => hroot (Sum.inl i)) ?_ hcon
        · intro X hX
          refine clo_mono ?_ (hlbl X hX)
          intro Y hY
          simp only [List.mem_append, mem_nf, mem_cap] at hY ⊢
          rcases hY with (hY | hY) | ⟨-, hY⟩
          · exact Or.inl hY
          · exact List.mem_append.mp (h₂ hY)
          · exact Or.inr hY.1
        · intro X hX
          rw [mem_cap] at hX
          exact hforce X (mem_cap.mpr
            ⟨List.mem_append_left _ hX.1, sfm_subset_sfm_or₁ hX.2⟩)
      · refine lemma39I d₂ P hP w hw ?_ (fun i => hroot (Sum.inr i)) ?_ hcon
        · intro X hX
          refine clo_mono ?_ (hlbl X hX)
          intro Y hY
          simp only [List.mem_append, mem_nf, mem_cap] at hY ⊢
          rcases hY with (hY | hY) | ⟨-, hY⟩
          · exact List.mem_append.mp (h₁ hY)
          · exact Or.inl hY
          · exact Or.inr hY.2
        · intro X hX
          rw [mem_cap] at hX
          exact hforce X (mem_cap.mpr
            ⟨List.mem_append_right _ hX.1, sfm_subset_sfm_or₂ hX.2⟩)
  | _, _, _, @FRJi.impInI _ St Th Lam A B d hdisj hA hg,
      P, hP, w, hw, hlbl, hroot, hforce => by
      intro hcon
      have hSA : (P.toKripke hP).forces w (cap (nf G (St ++ Lam)) (sf A)) := by
        intro X hX
        rw [mem_cap] at hX
        exact hforce X (mem_cap.mpr ⟨hX.1, sf_subset_sfm_impL hX.2⟩)
      have hAf : (P.toKripke hP).force w A := clo_forces hSA (clo_sf hA)
      refine lemma39I d P hP w hw ?_ hroot ?_ (hcon w ((P.toKripke hP).le_refl w) hAf)
      · intro X hX
        refine clo_mono ?_ (hlbl X hX)
        intro Y hY
        simp only [List.mem_append, mem_nf] at hY ⊢
        rcases hY with ⟨hg', hY | hY⟩ | ⟨hg', hY⟩
        · exact Or.inl hY
        · exact Or.inr ⟨hg', Or.inr hY⟩
        · exact Or.inr ⟨hg', Or.inl hY⟩
      · intro X hX
        rw [mem_cap] at hX
        have hXG : X ∈ gHat G := wfI d (List.mem_append_left _ hX.1)
        exact hforce X (mem_cap.mpr
          ⟨mem_nf.mpr ⟨hXG, List.mem_append_left _ hX.1⟩,
            sfm_subset_sfm_impR hX.2⟩)
  | _, _, _, @FRJi.impNotIn _ t Γ Th A B d hTh hA hAnot hg,
      P, hP, w, hw, hlbl, hroot, hforce => by
      intro hcon
      obtain ⟨v, hwv, hiff⟩ := hroot ()
      obtain ⟨ha, hb⟩ := lemma39R d
      have hΓ := ha (preR d).root
      rw [preR_root_lbl d] at hΓ
      have hvΓ : (P.toKripke hP).forces v Γ := fun X hX => (hiff X).mpr (hΓ X hX)
      exact hb ((hiff B).mp (hcon v hwv (clo_forces hvΓ hA)))
  | _, _, _, @FRJi.axIC _ F ats hats hFf hg, P, hP, w, hw, hlbl, hroot, hforce => by
      -- `w ⊩ ◯F` would persist up to the mounted bare final world, which
      -- refutes `◯F` because it refutes `F` (the recorded classical
      -- refutation `hFf`) and is its own modal cone.
      intro hcon
      obtain ⟨v, hwv, hiff⟩ := hroot ()
      have hv : (P.toKripke hP).force v (.circ F) :=
        (P.toKripke hP).force_mono hwv hcon
      have hr := (hiff _).mp hv
      have hcf := (PreModel.leaf_force_iff (fun p => vacZoneA_atom hats) _).mp hr
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
    ⟨.axR (.atom p) rfl (sfR_self _)⟩⟩

example : ¬ PLL .bot :=
  soundness ⟨.barren, rm (gAt .bot) .bot, ⟨.axR .bot rfl (sfR_self _)⟩⟩


end FRJ
