import FRJ.Extract

/-!
# The calculus-free core of the join cases of soundness

`FRJ/Sound.lean`, `FRJ/SoundV.lean` and `FRJ/SoundW.lean` prove the same five
join cases — `joinAtP`, `joinAtF`, `joinOrP`, `joinOrF`, `joinCircP` — for
`FRJr`, `FRJVr` and `FRJWr`, and the three copies differ only in type names:
2,523 lines of which about 1,700 are duplicates.

The proofs cannot be abstracted over the derivation.  They do not use `preR d`
through an interface, they use it through REDUCTION: they `cases` inhabitants
of `(preR d).W`, feed `none` where a world is expected, and call
`join_force_comp`, whose statement mentions `PreModel.join` syntactically.  A
hypothesis `preR (joinAtP …) = PreModel.join …` would be a propositional
equation between structures whose first field is a `Type`, and every one of
those steps would then need a `cast`.

So the core lemma is stated about the join pre-model itself, with the facts the
proof took from the derivation supplied as ordinary hypotheses.  Each calculus's
wrapper then holds by `rfl`, because `preR (FRJr.joinAtP …)` IS that pre-model.
-/

namespace FRJ

open Form

/-! ## Context and forcing lemmas shared by every join case

These were the first 300 lines of `FRJ/Sound.lean` and mention no calculus;
`SoundV.lean` and `SoundW.lean` each carry their own copy in their own
namespace, which the same move will remove. -/

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

/-- The pre-model `preR` builds at a promise join — `joinAtP` and `joinOrP`
alike, since the context is a parameter — named so that the join cases can be
stated without a derivation. -/
def joinPModel {n k : Nat} {Idx : Fin (n + 1) → Type}
    [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    (elems : List ((j : Fin (n + 1)) × Idx j)) (hcomplete : ∀ ji, ji ∈ elems)
    (Ψ : List Form) (Ms : (j : Fin (n + 1)) → Idx j → PreModel)
    (Ns : Fin (k + 1) → PreModel) : PreModel :=
  PreModel.join (sumElems elems (List.finRange (k + 1)))
    (sumElems_complete hcomplete List.mem_finRange) Ψ
    (Sum.elim (fun ji => Ms ji.1 ji.2) Ns)
    (Sum.elim (fun _ => false) (fun _ => true))

/-- The pre-model `preR` builds at a FALLIBLE join (`joinAtF`, `joinOrF`): the
same shape as `joinPModel`, with one declared fallible leaf over the join's own
context in place of the promise premises. -/
def joinFModel {n : Nat} {Idx : Fin (n + 1) → Type}
    [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    (elems : List ((j : Fin (n + 1)) × Idx j)) (hcomplete : ∀ ji, ji ∈ elems)
    (Ψ : List Form) (Ms : (j : Fin (n + 1)) → Idx j → PreModel) : PreModel :=
  PreModel.join (sumElems elems [()])
    (sumElems_complete hcomplete (fun _ => List.mem_cons_self)) Ψ
    (Sum.elim (fun ji => Ms ji.1 ji.2) (fun _ : Unit => PreModel.leafF Ψ))
    (Sum.elim (fun _ => false) (fun _ => true))

/-- The pre-model `preR` builds at an INFALLIBLE join (`joinAt`, `joinOr` of the
V and W calculi): one component per premise, none of them a promise, over the
join's own context. -/
def joinIModel {n : Nat} {Idx : Fin (n + 1) → Type}
    [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    (elems : List ((j : Fin (n + 1)) × Idx j)) (hcomplete : ∀ ji, ji ∈ elems)
    (Ψ : List Form) (Ms : (j : Fin (n + 1)) → Idx j → PreModel) : PreModel :=
  PreModel.join elems hcomplete Ψ (fun ji => Ms ji.1 ji.2) (fun _ => false)

/-- The `joinAtP` case of soundness, for any family of component pre-models.

`FRJ/Sound.lean`, `SoundV.lean` and `SoundW.lean` each instantiate this; the
six hypotheses `hMC`–`hlhs` are what those proofs previously read off the
derivation (`preI_closed`, `preR_closed`, `preR_root_lbl`, `wfR`, `wfI`,
`lhs_clo_of_steps`). -/
theorem joinAtP_core {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form} {Idx : Fin (n + 1) → Type}
    [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    {elems : List ((j : Fin (n + 1)) × Idx j)} {hcomplete : ∀ ji, ji ∈ elems}
    {Ms : (j : Fin (n + 1)) → Idx j → PreModel} {Ns : Fin (k + 1) → PreModel}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (hJ7 : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
    (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
    (hMC : ∀ j i, ClosedLbl (Ms j i)) (hNC : ∀ i, ClosedLbl (Ns i))
    (hNroot : ∀ i, (Ns i).lbl (Ns i).root ≐ Δs i)
    (hwfR : joinCtxAtP stab th rhs F Δs ⊆ gHat G)
    (hwfI : ∀ j, stab j ++ th j ⊆ gHat G)
    (hlhs : ∀ j, ∀ X ∈ joinCtxAtP stab th rhs F Δs, Clo (stab j ++ th j) X)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : Idx j) (x : (Ms j i).W),
        ((Ms j i).toKripke (hMC j i)).forces x ((Ms j i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (Q : PreModel) (hQ : ClosedLbl Q) (w : Q.W),
        ¬ Q.fal w →
        (∀ X ∈ Q.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : Idx j, RootAbove Q hQ w (Ms j i) (hMC j i)) →
        (Q.toKripke hQ).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (Q.toKripke hQ).force w (rhs j))
    (ihP : ∀ i, (∀ w, ((Ns i).toKripke (hNC i)).forces w ((Ns i).lbl w)) ∧
        ¬ ((Ns i).toKripke (hNC i)).force ((Ns i)).root (Ds i))
    (hP : ClosedLbl (joinPModel elems hcomplete (joinCtxAtP stab th rhs F Δs) Ms Ns)) :
    let P := joinPModel elems hcomplete (joinCtxAtP stab th rhs F Δs) Ms Ns
    (∀ w, (P.toKripke hP).forces w (P.lbl w)) ∧
      ¬ (P.toKripke hP).force P.root F := by
  intro P
  -- the two component families force their own labels
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × Idx j)
      (x : (Ms ji.1 ji.2).W) (A : Form),
      A ∈ (Ms ji.1 ji.2).lbl x →
      (P.toKripke hP).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hP (i := Sum.inl ji)
      (hMC ji.1 ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompR : ∀ (i : Fin (k + 1)) (x : (Ns i).W) (A : Form),
      A ∈ (Ns i).lbl x →
      (P.toKripke hP).force
        (some ⟨Sum.inr i, x⟩) A := by
    intro i x A hA
    exact (join_force_comp hP (i := Sum.inr i)
      (hNC i) A x).mpr ((ihP i).1 x A hA)
  -- (P2◯): every kept modal formula is forced at the root, by `circ_intro`
  -- with the designated promise root as witness
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxAtP stab th rhs F Δs →
      (P.toKripke hP).force
        none (.circ Y) := by
    intro Y hY
    obtain ⟨i, hi⟩ := joinCtxAtP_circ_body hJ5 hY
    refine Kripke.circ_intro _ ?_ ?_
    · refine ⟨some ⟨Sum.inr i, (Ns i).root⟩,
        PJRm.prom rfl ((Ns i).rm_refl _), ?_⟩
      have hiC : Clo ((Ns i).lbl (Ns i).root) Y :=
        clo_mono (hNroot i).subset' hi
      exact clo_forces (fun X hX => hcompR i _ X hX) hiC
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hP none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr i' => exact clo_forces (fun X hX => hcompR i' x X hX) hclo
  -- (P2) and (P3), by the secondary induction on `size H`
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxAtP stab th rhs F Δs) →
        (P.toKripke hP).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (P.toKripke hP).force none H) := by
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
                  have hclo := hP none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (P.toKripke hP).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr i' => exact clo_forces (fun Y hY => hcompR i' x Y hY) hclo
                  exact hforced _
                    ((P.toKripke hP).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (P) hP none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact hlhs j
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (Ms j i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hP (i := Sum.inl ⟨j, i⟩)
              (hMC j i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := hwfI j (List.mem_append_left _ hK.1)
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
          hwfR hX
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
  · refine not_force_prime hP hF ?_ (fun h => h)
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

/-- The `joinOrP` case of soundness, for any family of component pre-models.
The `joinAtP` remarks apply verbatim; only the context and the goal differ. -/
theorem joinOrP_core {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form} {Idx : Fin (n + 1) → Type}
    [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    {elems : List ((j : Fin (n + 1)) × Idx j)} {hcomplete : ∀ ji, ji ∈ elems}
    {Ms : (j : Fin (n + 1)) → Idx j → PreModel} {Ns : Fin (k + 1) → PreModel}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (hJ7 : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
    (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
    (hMC : ∀ j i, ClosedLbl (Ms j i)) (hNC : ∀ i, ClosedLbl (Ns i))
    (hNroot : ∀ i, (Ns i).lbl (Ns i).root ≐ Δs i)
    (hwfR : joinCtxOrP stab th rhs Δs ⊆ gHat G)
    (hwfI : ∀ j, stab j ++ th j ⊆ gHat G)
    (hlhs : ∀ j, ∀ X ∈ joinCtxOrP stab th rhs Δs, Clo (stab j ++ th j) X)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : Idx j) (x : (Ms j i).W),
        ((Ms j i).toKripke (hMC j i)).forces x ((Ms j i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (Q : PreModel) (hQ : ClosedLbl Q) (w : Q.W),
        ¬ Q.fal w →
        (∀ X ∈ Q.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : Idx j, RootAbove Q hQ w (Ms j i) (hMC j i)) →
        (Q.toKripke hQ).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (Q.toKripke hQ).force w (rhs j))
    (ihP : ∀ i, (∀ w, ((Ns i).toKripke (hNC i)).forces w ((Ns i).lbl w)) ∧
        ¬ ((Ns i).toKripke (hNC i)).force ((Ns i)).root (Ds i))
    (hP : ClosedLbl (joinPModel elems hcomplete (joinCtxOrP stab th rhs Δs) Ms Ns)) :
    let P := joinPModel elems hcomplete (joinCtxOrP stab th rhs Δs) Ms Ns
    (∀ w, (P.toKripke hP).forces w (P.lbl w)) ∧
      ¬ (P.toKripke hP).force P.root (.or C₁ C₂) := by
  intro P
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × Idx j)
      (x : (Ms ji.1 ji.2).W) (A : Form),
      A ∈ (Ms ji.1 ji.2).lbl x →
      (P.toKripke hP).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hP (i := Sum.inl ji)
      (hMC ji.1 ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompR : ∀ (i : Fin (k + 1)) (x : (Ns i).W) (A : Form),
      A ∈ (Ns i).lbl x →
      (P.toKripke hP).force
        (some ⟨Sum.inr i, x⟩) A := by
    intro i x A hA
    exact (join_force_comp hP (i := Sum.inr i)
      (hNC i) A x).mpr ((ihP i).1 x A hA)
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxOrP stab th rhs Δs →
      (P.toKripke hP).force
        none (.circ Y) := by
    intro Y hY
    obtain ⟨i, hi⟩ := joinCtxOrP_circ_body hJ5 hY
    refine Kripke.circ_intro _ ?_ ?_
    · refine ⟨some ⟨Sum.inr i, (Ns i).root⟩,
        PJRm.prom rfl ((Ns i).rm_refl _), ?_⟩
      have hiC : Clo ((Ns i).lbl (Ns i).root) Y :=
        clo_mono (hNroot i).subset' hi
      exact clo_forces (fun X hX => hcompR i _ X hX) hiC
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hP none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr i' => exact clo_forces (fun X hX => hcompR i' x X hX) hclo
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxOrP stab th rhs Δs) →
        (P.toKripke hP).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (P.toKripke hP).force none H) := by
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
                  have hclo := hP none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (P.toKripke hP).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr i' => exact clo_forces (fun Y hY => hcompR i' x Y hY) hclo
                  exact hforced _
                    ((P.toKripke hP).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (P) hP none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact hlhs j
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (Ms j i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hP (i := Sum.inl ⟨j, i⟩)
              (hMC j i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := hwfI j (List.mem_append_left _ hK.1)
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
          hwfR hX
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

/-- The `joinAtF` case of soundness, for any family of component pre-models. -/
theorem joinAtF_core {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} {Idx : Fin (n + 1) → Type}
    [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    {elems : List ((j : Fin (n + 1)) × Idx j)} {hcomplete : ∀ ji, ji ∈ elems}
    {Ms : (j : Fin (n + 1)) → Idx j → PreModel}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
    (hMC : ∀ j i, ClosedLbl (Ms j i))
    (hwfR : (joinCtxAtF stab th rhs F) ⊆ gHat G)
    (hwfI : ∀ j, stab j ++ th j ⊆ gHat G)
    (hlhs : ∀ j, ∀ X ∈ (joinCtxAtF stab th rhs F), Clo (stab j ++ th j) X)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : Idx j) (x : (Ms j i).W),
        ((Ms j i).toKripke (hMC j i)).forces x ((Ms j i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (Q : PreModel) (hQ : ClosedLbl Q) (w : Q.W),
        ¬ Q.fal w →
        (∀ X ∈ Q.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : Idx j, RootAbove Q hQ w (Ms j i) (hMC j i)) →
        (Q.toKripke hQ).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (Q.toKripke hQ).force w (rhs j))
    (hP : ClosedLbl (joinFModel elems hcomplete (joinCtxAtF stab th rhs F) Ms)) :
    let P := joinFModel elems hcomplete (joinCtxAtF stab th rhs F) Ms
    (∀ w, (P.toKripke hP).forces w (P.lbl w)) ∧
      ¬ (P.toKripke hP).force P.root F := by
  intro P
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × Idx j)
      (x : (Ms ji.1 ji.2).W) (A : Form),
      A ∈ (Ms ji.1 ji.2).lbl x →
      (P.toKripke hP).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hP (i := Sum.inl ji)
      (hMC ji.1 ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  -- the declared fallible world forces everything
  have hcompF : ∀ (x : Unit) (A : Form),
      (P.toKripke hP).force
        (some ⟨Sum.inr (), x⟩) A := by
    intro x A
    exact Kripke.fal_force _ A trivial
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxAtF stab th rhs F →
      (P.toKripke hP).force none (.circ Y) := by
    intro Y hY
    refine Kripke.circ_intro _ ?_ ?_
    · exact ⟨some ⟨Sum.inr (), ()⟩, PJRm.prom rfl trivial, hcompF () Y⟩
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hP none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr u => exact hcompF u (.circ Y)
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxAtF stab th rhs F) →
        (P.toKripke hP).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (P.toKripke hP).force none H) := by
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
                  have hclo := hP none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (P.toKripke hP).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr u => exact hcompF u (.imp A B)
                  exact hforced _
                    ((P.toKripke hP).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (P) hP none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact hlhs j
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (Ms j i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hP (i := Sum.inl ⟨j, i⟩)
              (hMC j i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := hwfI j (List.mem_append_left _ hK.1)
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
        have hXG : X ∈ gHat G := hwfR hX
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
  · refine not_force_prime hP hF ?_ (fun h => h)
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

/-- The `joinOrF` case of soundness, for any family of component pre-models. -/
theorem joinOrF_core {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {Idx : Fin (n + 1) → Type}
    [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    {elems : List ((j : Fin (n + 1)) × Idx j)} {hcomplete : ∀ ji, ji ∈ elems}
    {Ms : (j : Fin (n + 1)) → Idx j → PreModel}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
    (hMC : ∀ j i, ClosedLbl (Ms j i))
    (hwfR : (joinCtxOrF stab th rhs) ⊆ gHat G)
    (hwfI : ∀ j, stab j ++ th j ⊆ gHat G)
    (hlhs : ∀ j, ∀ X ∈ (joinCtxOrF stab th rhs), Clo (stab j ++ th j) X)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : Idx j) (x : (Ms j i).W),
        ((Ms j i).toKripke (hMC j i)).forces x ((Ms j i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (Q : PreModel) (hQ : ClosedLbl Q) (w : Q.W),
        ¬ Q.fal w →
        (∀ X ∈ Q.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : Idx j, RootAbove Q hQ w (Ms j i) (hMC j i)) →
        (Q.toKripke hQ).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (Q.toKripke hQ).force w (rhs j))
    (hP : ClosedLbl (joinFModel elems hcomplete (joinCtxOrF stab th rhs) Ms)) :
    let P := joinFModel elems hcomplete (joinCtxOrF stab th rhs) Ms
    (∀ w, (P.toKripke hP).forces w (P.lbl w)) ∧
      ¬ (P.toKripke hP).force P.root (.or C₁ C₂) := by
  intro P
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × Idx j)
      (x : (Ms ji.1 ji.2).W) (A : Form),
      A ∈ (Ms ji.1 ji.2).lbl x →
      (P.toKripke hP).force (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hP (i := Sum.inl ji)
      (hMC ji.1 ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompF : ∀ (x : Unit) (A : Form),
      (P.toKripke hP).force (some ⟨Sum.inr (), x⟩) A := by
    intro x A
    exact Kripke.fal_force _ A trivial
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxOrF stab th rhs →
      (P.toKripke hP).force none (.circ Y) := by
    intro Y hY
    refine Kripke.circ_intro _ ?_ ?_
    · exact ⟨some ⟨Sum.inr (), ()⟩, PJRm.prom rfl trivial, hcompF () Y⟩
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hP none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr u => exact hcompF u (.circ Y)
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxOrF stab th rhs) →
        (P.toKripke hP).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (P.toKripke hP).force none H) := by
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
                  have hclo := hP none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (P.toKripke hP).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr u => exact hcompF u (.imp A B)
                  exact hforced _
                    ((P.toKripke hP).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (P) hP none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact hlhs j
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (Ms j i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hP (i := Sum.inl ⟨j, i⟩)
              (hMC j i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := hwfI j (List.mem_append_left _ hK.1)
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
        have hXG : X ∈ gHat G := hwfR hX
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

/-- The `joinCircP` case of soundness, for any family of component pre-models.
Besides the `joinOrP` hypotheses this needs `ihT`, the premise models' tag
condition, which is what makes the join's root refute `◯Z`. -/
theorem joinCircP_core {G : Form} {n k : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {Z : Form} {tps : Fin (k + 1) → Tag}
    {Δs : Fin (k + 1) → List Form} {Ds : Fin (k + 1) → Form}
    {Idx : Fin (n + 1) → Type} [DecidableEq ((j : Fin (n + 1)) × Idx j)]
    {elems : List ((j : Fin (n + 1)) × Idx j)} {hcomplete : ∀ ji, ji ∈ elems}
    {Ms : (j : Fin (n + 1)) → Idx j → PreModel} {Ns : Fin (k + 1) → PreModel}
    (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
      A ∈ upsilon rhs)
    (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y)
    (hJ7 : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
    (hDs : ∀ i, Ds i = Z ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z))
    (hZ : Z ∈ upsilon rhs)
    (hMC : ∀ j i, ClosedLbl (Ms j i)) (hNC : ∀ i, ClosedLbl (Ns i))
    (hNroot : ∀ i, (Ns i).lbl (Ns i).root ≐ Δs i)
    (hwfR : joinCtxOrP stab th rhs Δs ⊆ gHat G)
    (hwfI : ∀ j, stab j ++ th j ⊆ gHat G)
    (hlhs : ∀ j, ∀ X ∈ joinCtxOrP stab th rhs Δs, Clo (stab j ++ th j) X)
    (ihI0 : ∀ (j : Fin (n + 1)) (i : Idx j) (x : (Ms j i).W),
        ((Ms j i).toKripke (hMC j i)).forces x ((Ms j i).lbl x))
    (ihI : ∀ (j : Fin (n + 1)) (Q : PreModel) (hQ : ClosedLbl Q) (w : Q.W),
        ¬ Q.fal w →
        (∀ X ∈ Q.lbl w, Clo (stab j ++ th j) X) →
        (∀ i : Idx j, RootAbove Q hQ w (Ms j i) (hMC j i)) →
        (Q.toKripke hQ).forces w (cap (stab j) (sfm (rhs j))) →
        ¬ (Q.toKripke hQ).force w (rhs j))
    (ihP : ∀ i, (∀ w, ((Ns i).toKripke (hNC i)).forces w ((Ns i).lbl w)) ∧
        ¬ ((Ns i).toKripke (hNC i)).force ((Ns i)).root (Ds i))
    (ihT : ∀ i (Z' : Form),
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z') →
        ∀ u, ((Ns i).toKripke (hNC i)).Rm ((Ns i).toKripke (hNC i)).root u →
          u ≠ ((Ns i).toKripke (hNC i)).root →
          ¬ ((Ns i).toKripke (hNC i)).force u Z')
    (hP : ClosedLbl (joinPModel elems hcomplete (joinCtxOrP stab th rhs Δs) Ms Ns)) :
    let P := joinPModel elems hcomplete (joinCtxOrP stab th rhs Δs) Ms Ns
    (∀ w, (P.toKripke hP).forces w (P.lbl w)) ∧
      ¬ (P.toKripke hP).force P.root (.circ Z) := by
  intro P
  have hcompL : ∀ (ji : (j : Fin (n + 1)) × Idx j)
      (x : (Ms ji.1 ji.2).W) (A : Form),
      A ∈ (Ms ji.1 ji.2).lbl x →
      (P.toKripke hP).force
        (some ⟨Sum.inl ji, x⟩) A := by
    intro ji x A hA
    exact (join_force_comp hP (i := Sum.inl ji)
      (hMC ji.1 ji.2) A x).mpr (ihI0 ji.1 ji.2 x A hA)
  have hcompR : ∀ (i : Fin (k + 1)) (x : (Ns i).W) (A : Form),
      A ∈ (Ns i).lbl x →
      (P.toKripke hP).force
        (some ⟨Sum.inr i, x⟩) A := by
    intro i x A hA
    exact (join_force_comp hP (i := Sum.inr i)
      (hNC i) A x).mpr ((ihP i).1 x A hA)
  have hcircF : ∀ Y : Form, Form.circ Y ∈ joinCtxOrP stab th rhs Δs →
      (P.toKripke hP).force
        none (.circ Y) := by
    intro Y hY
    obtain ⟨i, hi⟩ := joinCtxOrP_circ_body hJ5 hY
    refine Kripke.circ_intro _ ?_ ?_
    · refine ⟨some ⟨Sum.inr i, (Ns i).root⟩,
        PJRm.prom rfl ((Ns i).rm_refl _), ?_⟩
      have hiC : Clo ((Ns i).lbl (Ns i).root) Y :=
        clo_mono (hNroot i).subset' hi
      exact clo_forces (fun X hX => hcompR i _ X hX) hiC
    · intro v hv hne
      cases v with
      | none => exact absurd rfl hne
      | some cx =>
          obtain ⟨c, x⟩ := cx
          have hclo := hP none (some ⟨c, x⟩) hv (.circ Y) hY
          cases c with
          | inl ji => exact clo_forces (fun X hX => hcompL ji x X hX) hclo
          | inr i' => exact clo_forces (fun X hX => hcompR i' x X hX) hclo
  have key : ∀ (m : Nat) (H : Form), H.size ≤ m →
      (H ∈ impPart (joinCtxOrP stab th rhs Δs) →
        (P.toKripke hP).force none H) ∧
      (∀ j : Fin (n + 1), rhs j = H →
        ¬ (P.toKripke hP).force none H) := by
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
                  have hclo := hP none (some ⟨c, x⟩) hv (.imp A B) hHmem
                  have hforced : (P.toKripke hP).force
                      (some ⟨c, x⟩) (.imp A B) := by
                    cases c with
                    | inl ji => exact clo_forces (fun Y hY => hcompL ji x Y hY) hclo
                    | inr i' => exact clo_forces (fun Y hY => hcompR i' x Y hY) hclo
                  exact hforced _
                    ((P.toKripke hP).le_refl _) hAv
        · intro j hj hcon
          refine ihI j (P) hP none
            (fun h => h) ?_ ?_ ?_ (by rw [hj]; exact hcon)
          · exact hlhs j
          · intro i
            refine ⟨some ⟨Sum.inl ⟨j, i⟩, (Ms j i).root⟩, .root _, ?_⟩
            intro A
            exact join_force_comp hP (i := Sum.inl ⟨j, i⟩)
              (hMC j i) A _
          · intro K hK
            rw [mem_cap] at hK
            have hKG : K ∈ gHat G := hwfI j (List.mem_append_left _ hK.1)
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
          hwfR hX
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
        (sumElems (elems) (List.finRange (k + 1)))
        (sumElems_complete (hcomplete) List.mem_finRange)
        (joinCtxOrP stab th rhs Δs)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × Idx j) => Ms ji.1 ji.2)
          (fun i => Ns i))
        (Sum.elim (fun _ => false) (fun _ => true))).rm none u := hu
    rcases PreModel.join_rm_root hu' with h0 | ⟨c, a, hc, hra, hy⟩
    · rw [h0] at hf
      exact (key Z.size Z (Nat.le_refl _)).2 j₀ hj₀ hf
    · rw [hy] at hf
      cases c with
      | inl ji => exact Bool.noConfusion hc
      | inr i =>
          have hf' : ((Ns i).toKripke (hNC i)).force a Z :=
            (join_force_comp hP (i := Sum.inr i)
              (hNC i) Z a).mp hf
          by_cases ha : a = ((Ns i).toKripke (hNC i)).root
          · rw [ha] at hf'
            have hDi := (hDs i).1
            rw [← hDi] at hf'
            exact (ihP i).2 hf'
          · exact ihT i Z (hDs i).2 a hra ha hf'

end FRJ
