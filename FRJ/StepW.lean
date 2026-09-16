/-
W-adaptation of `FRJ/StepV.lean` for the NEW calculus `FRJW`
(`FRJ/CalculusW.lean`): `FRJWr`/`FRJWi` have `lift` where `FRJVi` had
`⊃∉` (`impNotIn`); every other rule is verbatim, so every proof here is
the V-proof re-run over the W-family — fresh, not aliased.

# The relation `↦` and the sequents occurring in a disproof (Lemma 3.4)

* `σ₁ ↦_R σ₂` iff `R` is a rule of `FRJW(G)` such that `σ₂` is the
  conclusion of `R` and `σ₁` is one of its premises;
* `σ₁ ↦₀ σ₂` iff there exists a rule `R` such that `σ₁ ↦_R σ₂`;
* `↦*` is the reflexive-transitive closure;

and then **Lemma 3.4** (`lemma:lhs`) for `FRJW`:

* (i)   `σ₁ ↦_R σ₂` and `R` not world-changing imply `Lhs(σ₂) ⊆ Lhs(σ₁)`;
* (ii)  `σ₁ ↦₀ σ₂` implies `Lhs(σ₂) ⊆ Cl(Lhs(σ₁))`;
* (iii) `σ₁ ↦* σ₂` implies `Lhs(σ₂) ⊆ Cl(Lhs(σ₁))`.

The `lift` delta: `lift` changes world exactly as `⊃∉` did, and its
side condition `Θ ⊆ Cl(Γ) ∩ Ĝ` is verbatim `⊃∉`'s, so it takes `⊃∉`'s
place on the exception list of (i) and discharges (ii) by its own
condition.  `FRJ.W` gets its own `RuleName` (the shared paper one in
`FRJ/Step.lean` names `impNotIn`, which `FRJW` does not have).

`Sequent` and the context-shape lemmas about the promise and fallible
join contexts are reused from `FRJ.Step`; the V-join context lemmas
(`joinCtxAtVBase_subset`, …) are about the shared context FORMERS, and
are re-proved here over the W step relation only where they mention it.
-/
import FRJ.CalculusW
import FRJ.Step

namespace FRJ.W

open FRJ Form

/-! ## `↦_R`, `↦₀`, `↦*` for the W-family -/

/-- The rule names of `FRJW(G)`: the shared `FRJ.RuleName` with `lift`
in place of `impNotIn`. -/
inductive RuleName where
  | andR1 | andR2 | impIn | circIn | joinAt | joinAtP | joinAtF | joinOr
  | joinOrP | joinOrF | joinCirc | joinCircP | promAt | promOr | promCirc
  | andI1 | andI2 | orI | impInI | lift | circNotIn
  deriving DecidableEq

/-- `σ₁ ↦_R σ₂`: `σ₂` is the conclusion of an instance of rule `R` of
`FRJW(G)` and `σ₁` is one of its premises.  Only the side conditions
that Lemma 3.4 consumes are carried; the three barren joins carry their
`kept` zone and its `KeptChain` certificate. -/
inductive Step (G : Form) : RuleName → Sequent → Sequent → Prop
  | andR1 {Γ : List Form} {A₁ A₂ : Form} :
      Step G .andR1 (.reg Γ A₁) (.reg Γ (.and A₁ A₂))
  | andR2 {Γ : List Form} {A₁ A₂ : Form} :
      Step G .andR2 (.reg Γ A₂) (.reg Γ (.and A₁ A₂))
  | impIn {Γ : List Form} {A B : Form} :
      Step G .impIn (.reg Γ B) (.reg Γ (.imp A B))
  | circIn {Γ : List Form} {Z : Form} :
      Step G .circIn (.reg Γ Z) (.reg Γ (.circ Z))
  | andI1 {Ξ Θ : List Form} {A₁ A₂ : Form} :
      Step G .andI1 (.irr Ξ Θ A₁) (.irr Ξ Θ (.and A₁ A₂))
  | andI2 {Ξ Θ : List Form} {A₁ A₂ : Form} :
      Step G .andI2 (.irr Ξ Θ A₂) (.irr Ξ Θ (.and A₁ A₂))
  | orI₁ {Ξ₁ Θ₁ Ξ₂ Θ₂ Ξ' Θ' : List Form} {C₁ C₂ : Form}
      (h₁ : Ξ₁ ⊆ Ξ₂ ++ Θ₂) (h₂ : Ξ₂ ⊆ Ξ₁ ++ Θ₁)
      (hSt : Ξ' ≐ Ξ₁ ++ Ξ₂) (hTh : Θ' ≐ cap Θ₁ Θ₂) :
      Step G .orI (.irr Ξ₁ Θ₁ C₁) (.irr Ξ' Θ' (.or C₁ C₂))
  | orI₂ {Ξ₁ Θ₁ Ξ₂ Θ₂ Ξ' Θ' : List Form} {C₁ C₂ : Form}
      (h₁ : Ξ₁ ⊆ Ξ₂ ++ Θ₂) (h₂ : Ξ₂ ⊆ Ξ₁ ++ Θ₁)
      (hSt : Ξ' ≐ Ξ₁ ++ Ξ₂) (hTh : Θ' ≐ cap Θ₁ Θ₂) :
      Step G .orI (.irr Ξ₂ Θ₂ C₂) (.irr Ξ' Θ' (.or C₁ C₂))
  | impInI {Ξ Θ Λ ΘΛ Ξ' Θ' : List Form} {A B : Form}
      (hdisj : cap Θ Λ = []) (hpre : ΘΛ ≐ Θ ++ Λ)
      (hSt : Ξ' ≐ Ξ ++ Λ) (hTh : Θ' ≐ Θ) :
      Step G .impInI (.irr Ξ ΘΛ B) (.irr Ξ' Θ' (.imp A B))
  | lift {Γ Θ : List Form} {C : Form}
      (hTh : ∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) :
      Step G .lift (.reg Γ C) (.irr [] Θ C)
  | circNotIn {Γ Θ : List Form} {Z : Form}
      (hTh : ∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) :
      Step G .circNotIn (.reg Γ Z) (.irr [] Θ (.circ Z))
  /-- the V-join `⋈^At`: the conclusion context is base + kept. -/
  | joinAt {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {kept : List Form} (j : Fin (n + 1))
      (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
      (hkc : KeptChain (upsilon rhs) (joinCtxAtVBase Ξs Θs F)
        (thPool Θs) kept)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtVBase Ξs Θs F ++ kept) :
      Step G .joinAt (.irr (Ξs j) (Θs j) (rhs j)) (.reg Γ' F)
  /-- the V-join `⋈^∨`: the conclusion context is base + kept. -/
  | joinOr {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {kept : List Form} (j : Fin (n + 1))
      (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
      (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase Ξs Θs)
        (thPool Θs) kept)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrVBase Ξs Θs ++ kept) :
      Step G .joinOr (.irr (Ξs j) (Θs j) (rhs j)) (.reg Γ' (.or C₁ C₂))
  | joinAtP {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {Δs : Fin (k + 1) → List Form}
      (j : Fin (n + 1))
      (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtP Ξs Θs rhs F Δs) :
      Step G .joinAtP (.irr (Ξs j) (Θs j) (rhs j)) (.reg Γ' F)
  /-- the promise edge of `⋈^At,p`: condition (J7) is what Lemma 3.5
  consumes, exactly as `⊃∉` supplies its `Θ ⊆ Cl(Γ)` condition. -/
  | promAt {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form} (i : Fin (k + 1))
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtP Ξs Θs rhs F Δs)
      (hJ7 : ∀ X ∈ Γ', Clo (Δs i) X) :
      Step G .promAt (.reg (Δs i) (Ds i)) (.reg Γ' F)
  | joinAtF {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} (j : Fin (n + 1))
      (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtF Ξs Θs rhs F) :
      Step G .joinAtF (.irr (Ξs j) (Θs j) (rhs j)) (.reg Γ' F)
  | joinOrP {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {Δs : Fin (k + 1) → List Form}
      (j : Fin (n + 1))
      (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrP Ξs Θs rhs Δs) :
      Step G .joinOrP (.irr (Ξs j) (Θs j) (rhs j)) (.reg Γ' (.or C₁ C₂))
  | promOr {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form} (i : Fin (k + 1))
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrP Ξs Θs rhs Δs)
      (hJ7 : ∀ X ∈ Γ', Clo (Δs i) X) :
      Step G .promOr (.reg (Δs i) (Ds i)) (.reg Γ' (.or C₁ C₂))
  | joinOrF {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} (j : Fin (n + 1))
      (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrF Ξs Θs rhs) :
      Step G .joinOrF (.irr (Ξs j) (Θs j) (rhs j)) (.reg Γ' (.or C₁ C₂))
  /-- the V-join `⋈^◯`: the conclusion context is base + kept. -/
  | joinCirc {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form} {kept : List Form} (j : Fin (n + 1))
      (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
      (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase Ξs Θs)
        (thPool Θs) kept)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrVBase Ξs Θs ++ kept) :
      Step G .joinCirc (.irr (Ξs j) (Θs j) (rhs j)) (.reg Γ' (.circ Z))
  | joinCircP {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form} {Δs : Fin (k + 1) → List Form}
      (j : Fin (n + 1))
      (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrP Ξs Θs rhs Δs) :
      Step G .joinCircP (.irr (Ξs j) (Θs j) (rhs j)) (.reg Γ' (.circ Z))
  | promCirc {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form} (i : Fin (k + 1))
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrP Ξs Θs rhs Δs)
      (hJ7 : ∀ X ∈ Γ', Clo (Δs i) X) :
      Step G .promCirc (.reg (Δs i) (Ds i)) (.reg Γ' (.circ Z))

/-- `σ₁ ↦₀ σ₂`: "there exists a rule `R` such that `σ₁ ↦_R σ₂`." -/
def Step₀ (G : Form) (s₁ s₂ : Sequent) : Prop := ∃ R, Step G R s₁ s₂

/-- `↦*`, the reflexive-transitive closure. -/
abbrev StepsRfl (G : Form) : Sequent → Sequent → Prop :=
  Relation.ReflTransGen (Step₀ G)

/-! ## Auxiliary facts about the V-join contexts

The base is a sublist-in-spirit of the old join context (the old context
minus its restricted second zone), so it obeys the same inclusion; the
kept zone lies in `Θ^⊃∩ ⊆ Θs j` for EVERY `j`, which is a strictly
simpler inclusion than the old restricted zone's. -/

/-- Every member of the retention pool `Θ^⊃∩` is in every premise's
second zone. -/
theorem thPool_subset {n : Nat} {Θs : Fin (n + 1) → List Form}
    (j : Fin (n + 1)) : thPool Θs ⊆ Θs j :=
  fun _ hx => interAll_subset j (impPart_subset hx)

theorem joinCtxAtVBase_subset {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {F : Form}
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) (j : Fin (n + 1)) :
    joinCtxAtVBase Ξs Θs F ⊆ Ξs j ++ Θs j := by
  intro x hx
  simp only [joinCtxAtVBase, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact unionAll_part_subset hJ1 j atPart (fun _ => atPart_subset) hx
  · exact List.mem_append_right _
      (atPart_subset (interAll_subset j (rm_subset hx)))
  · exact unionAll_part_subset hJ1 j impPart (fun _ => impPart_subset) hx

theorem joinCtxOrVBase_subset {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) (j : Fin (n + 1)) :
    joinCtxOrVBase Ξs Θs ⊆ Ξs j ++ Θs j := by
  intro x hx
  simp only [joinCtxOrVBase, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact unionAll_part_subset hJ1 j atPart (fun _ => atPart_subset) hx
  · exact List.mem_append_right _ (atPart_subset (interAll_subset j hx))
  · exact unionAll_part_subset hJ1 j impPart (fun _ => impPart_subset) hx

/-- The whole `⋈^At` V-context (base + kept) lands inside every
premise's left formulas: the base by the shape of its zones and (J1),
the kept zone because `kept ⊆ Θ^⊃∩ ⊆ Θs j`. -/
theorem joinCtxAtV_subset {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {F : Form} {kept : List Form}
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hkept : kept ⊆ thPool Θs) (j : Fin (n + 1)) :
    joinCtxAtVBase Ξs Θs F ++ kept ⊆ Ξs j ++ Θs j := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact joinCtxAtVBase_subset hJ1 j hx
  · exact List.mem_append_right _ (thPool_subset j (hkept hx))

theorem joinCtxOrV_subset {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {kept : List Form}
    (hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j)
    (hkept : kept ⊆ thPool Θs) (j : Fin (n + 1)) :
    joinCtxOrVBase Ξs Θs ++ kept ⊆ Ξs j ++ Θs j := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact joinCtxOrVBase_subset hJ1 j hx
  · exact List.mem_append_right _ (thPool_subset j (hkept hx))

/-! ## Lemma 3.4 -/

/-- **Lemma 3.4(i).**  "`σ₁ ↦_R σ₂` and `R ≠ Lift` imply
`Lhs(σ₂) ⊆ Lhs(σ₁)`."  `◯∉` joins `lift` on the exception list: both
change world, so their conclusion's zone is contained in the premise's
only modulo `Cl`. -/
theorem lhs_subset_of_step {G : Form} {R : RuleName} {s₁ s₂ : Sequent}
    (h : Step G R s₁ s₂)
    (hR : R ≠ .lift) (hRc : R ≠ .circNotIn)
    (hRp : R ≠ .promAt) (hRq : R ≠ .promOr) (hRr : R ≠ .promCirc) :
    s₂.lhs ⊆ s₁.lhs := by
  cases h with
  | andR1 => exact List.Subset.refl _
  | andR2 => exact List.Subset.refl _
  | impIn => exact List.Subset.refl _
  | circIn => exact List.Subset.refl _
  | andI1 => exact List.Subset.refl _
  | andI2 => exact List.Subset.refl _
  | orI₁ h₁ h₂ hSt hTh =>
      intro x hx
      simp only [Sequent.lhs_irr, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · rcases List.mem_append.mp ((hSt x).mp hx) with hx' | hx'
        · exact Or.inl hx'
        · exact List.mem_append.mp (h₂ hx')
      · exact Or.inr (mem_cap.mp ((hTh x).mp hx)).1
  | orI₂ h₁ h₂ hSt hTh =>
      intro x hx
      simp only [Sequent.lhs_irr, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · rcases List.mem_append.mp ((hSt x).mp hx) with hx' | hx'
        · exact List.mem_append.mp (h₁ hx')
        · exact Or.inl hx'
      · exact Or.inr (mem_cap.mp ((hTh x).mp hx)).2
  | impInI hdisj hpre hSt hTh =>
      intro x hx
      simp only [Sequent.lhs_irr, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · rcases List.mem_append.mp ((hSt x).mp hx) with hx' | hx'
        · exact Or.inl hx'
        · exact Or.inr ((hpre x).mpr (List.mem_append_right _ hx'))
      · exact Or.inr ((hpre x).mpr (List.mem_append_left _ ((hTh x).mp hx)))
  | lift => exact absurd rfl hR
  | circNotIn => exact absurd rfl hRc
  | promAt i hΓ hJ7 => exact absurd rfl hRp
  | promOr i hΓ hJ7 => exact absurd rfl hRq
  | promCirc i hΓ hJ7 => exact absurd rfl hRr
  | joinCirc j hJ1 hkc hΓ =>
      intro x hx
      exact joinCtxOrV_subset hJ1 (keptChain_subset hkc) j ((hΓ x).mp hx)
  | joinCircP j hJ1 hΓ =>
      intro x hx
      exact joinCtxOrP_subset hJ1 j ((hΓ x).mp hx)
  | joinAt j hJ1 hkc hΓ =>
      intro x hx
      exact joinCtxAtV_subset hJ1 (keptChain_subset hkc) j ((hΓ x).mp hx)
  | joinOr j hJ1 hkc hΓ =>
      intro x hx
      exact joinCtxOrV_subset hJ1 (keptChain_subset hkc) j ((hΓ x).mp hx)
  | joinAtP j hJ1 hΓ =>
      intro x hx
      exact joinCtxAtP_subset hJ1 j ((hΓ x).mp hx)
  | joinAtF j hJ1 hΓ =>
      intro x hx
      exact joinCtxAtF_subset hJ1 j ((hΓ x).mp hx)
  | joinOrP j hJ1 hΓ =>
      intro x hx
      exact joinCtxOrP_subset hJ1 j ((hΓ x).mp hx)
  | joinOrF j hJ1 hΓ =>
      intro x hx
      exact joinCtxOrF_subset hJ1 j ((hΓ x).mp hx)

/-- **Lemma 3.4(ii).**  "`σ₁ ↦₀ σ₂` implies `Lhs(σ₂) ⊆ Cl(Lhs(σ₁))`."
For every rule but `lift`/`◯∉`/the promise edges this is (i) together
with (Cl3); for `lift` it is that rule's own side condition
`Θ ⊆ Cl(Γ) ∩ Ĝ`. -/
theorem lhs_clo_of_step₀ {G : Form} {s₁ s₂ : Sequent} (h : Step₀ G s₁ s₂) :
    ∀ X ∈ s₂.lhs, Clo s₁.lhs X := by
  obtain ⟨R, hR⟩ := h
  intro X hX
  by_cases hname : R = .lift
  · subst hname
    cases hR with
    | lift hTh =>
        refine (hTh X ?_).1
        simpa using hX
  by_cases hnameC : R = .circNotIn
  · subst hnameC
    cases hR with
    | circNotIn hTh =>
        refine (hTh X ?_).1
        simpa using hX
  by_cases hnameP : R = .promAt
  · subst hnameP
    cases hR with
    | promAt i hΓ hJ7 => exact hJ7 X hX
  by_cases hnameQ : R = .promOr
  · subst hnameQ
    cases hR with
    | promOr i hΓ hJ7 => exact hJ7 X hX
  by_cases hnameR : R = .promCirc
  · subst hnameR
    cases hR with
    | promCirc i hΓ hJ7 => exact hJ7 X hX
  exact .base (lhs_subset_of_step hR hname hnameC hnameP hnameQ hnameR hX)

/-- **Lemma 3.4(iii).**  "`σ₁ ↦* σ₂` implies `Lhs(σ₂) ⊆ Cl(Lhs(σ₁))`."
By (ii) along the chain, glued with (Cl6). -/
theorem lhs_clo_of_steps {G : Form} {s₁ s₂ : Sequent} (h : StepsRfl G s₁ s₂) :
    ∀ X ∈ s₂.lhs, Clo s₁.lhs X := by
  induction h with
  | refl => exact fun X hX => .base hX
  | tail _ hbc ih => exact fun X hX => clo_trans ih (lhs_clo_of_step₀ hbc X hX)

/-! ## The sequents occurring in a derivation

"σ occurs in D": the root sequent of `D`, or a sequent occurring in one
of its sub-derivations.  An inductive relation, one constructor per
premise slot.
-/

mutual

/-- `σ` occurs in the regular derivation `d`.

The variable-packing below quantifies whole side-condition bundles as
implicit records rather than naming each; what matters is only which
PREMISE SLOT each constructor descends into. -/
inductive OccR {G : Form} : {t : Tag} → {Γ : List Form} → {C : Form} →
    FRJWr G t Γ C → Sequent → Prop
  | root {t : Tag} {Γ : List Form} {C : Form} (d : FRJWr G t Γ C) : OccR d (.reg Γ C)
  | andR1 {t : Tag} {Γ : List Form} {A₁ A₂ : Form} {d : FRJWr G t Γ A₁}
      {hg : Form.and A₁ A₂ ∈ sfR G} {s : Sequent} :
      OccR d s → OccR (FRJWr.andR1 d hg) s
  | andR2 {t : Tag} {Γ : List Form} {A₁ A₂ : Form} {d : FRJWr G t Γ A₂}
      {hg : Form.and A₁ A₂ ∈ sfR G} {s : Sequent} :
      OccR d s → OccR (FRJWr.andR2 d hg) s
  | impIn {t : Tag} {Γ : List Form} {A B : Form} {d : FRJWr G t Γ B} {hA : Clo Γ A}
      {hg : Form.imp A B ∈ sfR G} {s : Sequent} :
      OccR d s → OccR (FRJWr.impIn d hA hg) s
  | circIn {t : Tag} {Γ : List Form} {Z : Form} {d : FRJWr G t Γ Z}
      {htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z}
      {hg : Form.circ Z ∈ sfR G} {s : Sequent} :
      OccR d s → OccR (FRJWr.circIn d htag hg) s
  | joinAt {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {kept : List Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hcirc : unionAll (fun j => circPart (Ξs j)) = []}
      {hkc : KeptChain (upsilon rhs) (joinCtxAtVBase Ξs Θs F)
        (thPool Θs) kept}
      {hF : F.isPrime} {hFnot : F ∉ unionAll (fun j => atPart (Ξs j))}
      {hg : F ∈ sfR G} {Γ' : List Form}
      {hΓ : Γ' ≐ joinCtxAtVBase Ξs Θs F ++ kept} {s : Sequent} (j : Fin (n + 1)) :
      OccI (prem j) s → OccR (FRJWr.joinAt prem hJ1 hJ2 hcirc hkc hF hFnot hg hΓ) s
  | joinAtP {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
        ∃ i, Clo (Δs i) Y}
      {hJ7s : ∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X}
      {htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))}
      {hF : F.isPrime} {hFnot : F ∉ unionAll (fun j => atPart (Ξs j))}
      {hg : F ∈ sfR G} {Γ' : List Form} {hΓ : Γ' ≐ joinCtxAtP Ξs Θs rhs F Δs} {s : Sequent} (j : Fin (n + 1)) :
      OccI (prem j) s →
      OccR (FRJWr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7s htag hF hFnot hg hΓ) s
  | joinAtPprom {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
        ∃ i, Clo (Δs i) Y}
      {hJ7s : ∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X}
      {htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))}
      {hF : F.isPrime} {hFnot : F ∉ unionAll (fun j => atPart (Ξs j))}
      {hg : F ∈ sfR G} {Γ' : List Form} {hΓ : Γ' ≐ joinCtxAtP Ξs Θs rhs F Δs} {s : Sequent} (i : Fin (k + 1)) :
      OccR (dps i) s →
      OccR (FRJWr.joinAtP prem dps hJ1 hJ2 hJ5 hJ7s htag hF hFnot hg hΓ) s
  | joinAtF {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hF : F.isPrime} {hFnot : F ∉ unionAll (fun j => atPart (Ξs j))}
      {hg : F ∈ sfR G} {Γ' : List Form} {hΓ : Γ' ≐ joinCtxAtF Ξs Θs rhs F} {s : Sequent} (j : Fin (n + 1)) :
      OccI (prem j) s → OccR (FRJWr.joinAtF prem hJ1 hJ2 hF hFnot hg hΓ) s
  | joinOr {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {kept : List Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hcirc : unionAll (fun j => circPart (Ξs j)) = []}
      {hkc : KeptChain (upsilon rhs) (joinCtxOrVBase Ξs Θs)
        (thPool Θs) kept}
      {hC : RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++ kept) C₁ ∧
        RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++ kept) C₂}
      {hg : Form.or C₁ C₂ ∈ sfR G} {Γ' : List Form}
      {hΓ : Γ' ≐ joinCtxOrVBase Ξs Θs ++ kept} {s : Sequent} (j : Fin (n + 1)) :
      OccI (prem j) s → OccR (FRJWr.joinOr prem hJ1 hJ2 hcirc hkc hC hg hΓ) s
  | joinOrP {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
        ∃ i, Clo (Δs i) Y}
      {hJ7s : ∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X}
      {htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))}
      {hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs}
      {hg : Form.or C₁ C₂ ∈ sfR G} {Γ' : List Form} {hΓ : Γ' ≐ joinCtxOrP Ξs Θs rhs Δs} {s : Sequent} (j : Fin (n + 1)) :
      OccI (prem j) s →
      OccR (FRJWr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7s htag hC hg hΓ) s
  | joinOrPprom {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
        ∃ i, Clo (Δs i) Y}
      {hJ7s : ∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X}
      {htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))}
      {hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs}
      {hg : Form.or C₁ C₂ ∈ sfR G} {Γ' : List Form} {hΓ : Γ' ≐ joinCtxOrP Ξs Θs rhs Δs} {s : Sequent} (i : Fin (k + 1)) :
      OccR (dps i) s →
      OccR (FRJWr.joinOrP prem dps hJ1 hJ2 hJ5 hJ7s htag hC hg hΓ) s
  | joinOrF {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs}
      {hg : Form.or C₁ C₂ ∈ sfR G} {Γ' : List Form} {hΓ : Γ' ≐ joinCtxOrF Ξs Θs rhs} {s : Sequent} (j : Fin (n + 1)) :
      OccI (prem j) s → OccR (FRJWr.joinOrF prem hJ1 hJ2 hC hg hΓ) s
  | joinCirc {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form} {kept : List Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++ kept) A}
      {hcirc : unionAll (fun j => circPart (Ξs j)) = []}
      {hkc : KeptChain (upsilon rhs) (joinCtxOrVBase Ξs Θs)
        (thPool Θs) kept}
      {hZ : RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++ kept) Z}
      {hg : Form.circ Z ∈ sfR G} {Γ' : List Form}
      {hΓ : Γ' ≐ joinCtxOrVBase Ξs Θs ++ kept} {s : Sequent} (j : Fin (n + 1)) :
      OccI (prem j) s → OccR (FRJWr.joinCirc prem hJ1 hJ2 hcirc hkc hZ hg hΓ) s
  | joinCircP {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
        ∃ i, Clo (Δs i) Y}
      {hJ7s : ∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X}
      {hDs : ∀ i, Ds i = Z ∧
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z)}
      {hZ : Z ∈ upsilon rhs}
      {hg : Form.circ Z ∈ sfR G} {Γ' : List Form} {hΓ : Γ' ≐ joinCtxOrP Ξs Θs rhs Δs} {s : Sequent} (j : Fin (n + 1)) :
      OccI (prem j) s →
      OccR (FRJWr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7s hDs hZ hg hΓ) s
  | joinCircPprom {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      {prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)}
      {dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i)}
      {hJ1 : ∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j}
      {hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
        A ∈ upsilon rhs}
      {hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
        ∃ i, Clo (Δs i) Y}
      {hJ7s : ∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X}
      {hDs : ∀ i, Ds i = Z ∧
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z)}
      {hZ : Z ∈ upsilon rhs}
      {hg : Form.circ Z ∈ sfR G} {Γ' : List Form} {hΓ : Γ' ≐ joinCtxOrP Ξs Θs rhs Δs} {s : Sequent} (i : Fin (k + 1)) :
      OccR (dps i) s →
      OccR (FRJWr.joinCircP prem dps hJ1 hJ2 hJ5 hJ7s hDs hZ hg hΓ) s

/-- `σ` occurs in the irregular derivation `d`. -/
inductive OccI {G : Form} :
    {Ξ Θ : List Form} → {C : Form} → FRJWi G Ξ Θ C → Sequent → Prop
  | root {Ξ Θ : List Form} {C : Form} (d : FRJWi G Ξ Θ C) : OccI d (.irr Ξ Θ C)
  | andI1 {Ξ Θ : List Form} {A₁ A₂ : Form} {d : FRJWi G Ξ Θ A₁}
      {hg : Form.and A₁ A₂ ∈ sfR G} {s : Sequent} :
      OccI d s → OccI (FRJWi.andI1 d hg) s
  | andI2 {Ξ Θ : List Form} {A₁ A₂ : Form} {d : FRJWi G Ξ Θ A₂}
      {hg : Form.and A₁ A₂ ∈ sfR G} {s : Sequent} :
      OccI d s → OccI (FRJWi.andI2 d hg) s
  | orI₁ {Ξ₁ Θ₁ Ξ₂ Θ₂ : List Form} {C₁ C₂ : Form}
      {d₁ : FRJWi G Ξ₁ Θ₁ C₁} {d₂ : FRJWi G Ξ₂ Θ₂ C₂}
      {h₁ : Ξ₁ ⊆ Ξ₂ ++ Θ₂} {h₂ : Ξ₂ ⊆ Ξ₁ ++ Θ₁}
      {hg : Form.or C₁ C₂ ∈ sfR G} {Ξ' Θ' : List Form} {hSt : Ξ' ≐ Ξ₁ ++ Ξ₂} {hTh : Θ' ≐ cap Θ₁ Θ₂} {s : Sequent} :
      OccI d₁ s → OccI (FRJWi.orI d₁ d₂ h₁ h₂ hg hSt hTh) s
  | orI₂ {Ξ₁ Θ₁ Ξ₂ Θ₂ : List Form} {C₁ C₂ : Form}
      {d₁ : FRJWi G Ξ₁ Θ₁ C₁} {d₂ : FRJWi G Ξ₂ Θ₂ C₂}
      {h₁ : Ξ₁ ⊆ Ξ₂ ++ Θ₂} {h₂ : Ξ₂ ⊆ Ξ₁ ++ Θ₁}
      {hg : Form.or C₁ C₂ ∈ sfR G} {Ξ' Θ' : List Form} {hSt : Ξ' ≐ Ξ₁ ++ Ξ₂} {hTh : Θ' ≐ cap Θ₁ Θ₂} {s : Sequent} :
      OccI d₂ s → OccI (FRJWi.orI d₁ d₂ h₁ h₂ hg hSt hTh) s
  | impInI {Ξ Θ Λ ΘΛ : List Form} {A B : Form}
      {d : FRJWi G Ξ ΘΛ B} {hpre : ΘΛ ≐ Θ ++ Λ}
      {hdisj : cap Θ Λ = []} {hA : Clo (Ξ ++ Λ) A}
      {hg : Form.imp A B ∈ sfR G} {Ξ' Θ' : List Form} {hSt : Ξ' ≐ Ξ ++ Λ} {hTh : Θ' ≐ Θ} {s : Sequent} :
      OccI d s → OccI (FRJWi.impInI d hpre hdisj hA hg hSt hTh) s
  | lift {t : Tag} {Γ Θ : List Form} {C : Form} {d : FRJWr G t Γ C}
      {hTh : ∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G} {s : Sequent} :
      OccR d s → OccI (FRJWi.lift d hTh) s
  | circNotIn {t : Tag} {Γ Θ : List Form} {Z : Form} {d : FRJWr G t Γ Z}
      {htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z}
      {hTh : ∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G}
      {hg : Form.circ Z ∈ sfR G} {s : Sequent} :
      OccR d s → OccI (FRJWi.circNotIn d htag hTh hg) s

end

/-! ## Occurrence reaches the root by `↦*`

This is the bridge that lets the soundness proof apply Lemma 3.4(iii) to
an arbitrary sequent of `D`.  Each step up the derivation is an instance
of `↦` supplied by the rule that was applied, with its side conditions
taken from the derivation itself. -/

mutual

theorem occR_steps {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    {d : FRJWr G t Γ C}
    {s : Sequent} : OccR d s → StepsRfl G s (.reg Γ C)
  | .root _ => .refl
  | .andR1 h' => (occR_steps h').tail ⟨_, .andR1⟩
  | .andR2 h' => (occR_steps h').tail ⟨_, .andR2⟩
  | .impIn h' => (occR_steps h').tail ⟨_, .impIn⟩
  | .circIn h' => (occR_steps h').tail ⟨_, .circIn⟩
  | .joinAt (hΓ := hΓ) (hJ1 := hJ1) (hkc := hkc) j h' =>
      (occI_steps h').tail ⟨_, .joinAt j hJ1 hkc hΓ⟩
  | .joinAtP (hΓ := hΓ) (hJ1 := hJ1) j h' =>
      (occI_steps h').tail ⟨_, .joinAtP j hJ1 hΓ⟩
  | .joinAtPprom (hΓ := hΓ) i h' =>
      (occR_steps h').tail
        ⟨_, .promAt i hΓ (fun X hX => joinCtxAtP_clo i X ((hΓ X).mp hX))⟩
  | .joinAtF (hΓ := hΓ) (hJ1 := hJ1) j h' =>
      (occI_steps h').tail ⟨_, .joinAtF j hJ1 hΓ⟩
  | .joinOr (hΓ := hΓ) (hJ1 := hJ1) (hkc := hkc) j h' =>
      (occI_steps h').tail ⟨_, .joinOr j hJ1 hkc hΓ⟩
  | .joinOrP (hΓ := hΓ) (hJ1 := hJ1) j h' =>
      (occI_steps h').tail ⟨_, .joinOrP j hJ1 hΓ⟩
  | .joinOrPprom (hΓ := hΓ) i h' =>
      (occR_steps h').tail
        ⟨_, .promOr i hΓ (fun X hX => joinCtxOrP_clo i X ((hΓ X).mp hX))⟩
  | .joinOrF (hΓ := hΓ) (hJ1 := hJ1) j h' =>
      (occI_steps h').tail ⟨_, .joinOrF j hJ1 hΓ⟩
  | .joinCirc (hΓ := hΓ) (hJ1 := hJ1) (hkc := hkc) j h' =>
      (occI_steps h').tail ⟨_, .joinCirc j hJ1 hkc hΓ⟩
  | .joinCircP (hΓ := hΓ) (hJ1 := hJ1) j h' =>
      (occI_steps h').tail ⟨_, .joinCircP j hJ1 hΓ⟩
  | .joinCircPprom (hΓ := hΓ) i h' =>
      (occR_steps h').tail
        ⟨_, .promCirc i hΓ (fun X hX => joinCtxOrP_clo i X ((hΓ X).mp hX))⟩

theorem occI_steps {G : Form} {Ξ Θ : List Form} {C : Form}
    {d : FRJWi G Ξ Θ C} {s : Sequent} : OccI d s → StepsRfl G s (.irr Ξ Θ C)
  | .root _ => .refl
  | .andI1 h' => (occI_steps h').tail ⟨_, .andI1⟩
  | .andI2 h' => (occI_steps h').tail ⟨_, .andI2⟩
  | .orI₁ (hSt := hSt) (hTh := hTh) (h₁ := h₁) (h₂ := h₂) h' =>
      (occI_steps h').tail ⟨_, .orI₁ h₁ h₂ hSt hTh⟩
  | .orI₂ (hSt := hSt) (hTh := hTh) (h₁ := h₁) (h₂ := h₂) h' =>
      (occI_steps h').tail ⟨_, .orI₂ h₁ h₂ hSt hTh⟩
  | .impInI (hpre := hpre) (hSt := hSt) (hTh := hTh) (hdisj := hd) h' =>
      (occI_steps h').tail ⟨_, .impInI hd hpre hSt hTh⟩
  | .lift (hTh := hTh) h' => (occR_steps h').tail ⟨_, .lift hTh⟩
  | .circNotIn (hTh := hTh) h' => (occR_steps h').tail ⟨_, .circNotIn hTh⟩

end

/-- **Lemma 3.4(iii), in the form the soundness proof uses it.**  For any
sequent `σ` occurring in a derivation `D` of `Γ ⇒ C`, the left formulas
of `D`'s root sequent lie in `Cl(Lhs(σ))`. -/
theorem lhs_clo_of_occR {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    {d : FRJWr G t Γ C} {s : Sequent} (h : OccR d s) :
    ∀ X ∈ Γ, Clo s.lhs X :=
  lhs_clo_of_steps (occR_steps h)

/-! ## Well-formedness of derivable sequents

The paper builds the constraints `Γ ⊆ Ĝ` and `Ξ ++ Θ ⊆ Ĝ` into the
definition of the sequent set.  We carry them as a lemma instead
(divergence 4 of `docs/frj-fidelity.md`), and this is that lemma.  For
the V-joins the kept zone is inside `Θs 0`, so `wfI (prem 0)` covers it
exactly as it covers the base. -/

mutual

/-- Every context of a derivable regular sequent lies inside `Ĝ`. -/
theorem wfR {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form},
    FRJWr G t Γ C → Γ ⊆ gHat G
  | _, _, _, .axR _ _ _ hΓ => fun x hx =>
      List.mem_append_left _ (List.mem_append_left _ (rm_subset ((hΓ x).mp hx)))
  | _, _, _, .andR1 d _ => wfR d
  | _, _, _, .andR2 d _ => wfR d
  | _, _, _, .impIn d _ _ => wfR d
  | _, _, _, .circIn d _ _ => wfR d
  | _, _, _, .joinAt prem hJ1 _ _ hkc _ _ _ hΓ => fun x hx =>
      wfI (prem 0)
        (joinCtxAtV_subset hJ1 (keptChain_subset hkc) 0 ((hΓ x).mp hx))
  | _, _, _, .joinAtP prem _ hJ1 _ _ _ _ _ _ _ hΓ => fun x hx =>
      wfI (prem 0) (joinCtxAtP_subset hJ1 0 ((hΓ x).mp hx))
  | _, _, _, .joinAtF prem hJ1 _ _ _ _ hΓ => fun x hx =>
      wfI (prem 0) (joinCtxAtF_subset hJ1 0 ((hΓ x).mp hx))
  | _, _, _, .joinOr prem hJ1 _ _ hkc _ _ hΓ => fun x hx =>
      wfI (prem 0)
        (joinCtxOrV_subset hJ1 (keptChain_subset hkc) 0 ((hΓ x).mp hx))
  | _, _, _, .joinOrP prem _ hJ1 _ _ _ _ _ _ hΓ => fun x hx =>
      wfI (prem 0) (joinCtxOrP_subset hJ1 0 ((hΓ x).mp hx))
  | _, _, _, .joinOrF prem hJ1 _ _ _ hΓ => fun x hx =>
      wfI (prem 0) (joinCtxOrF_subset hJ1 0 ((hΓ x).mp hx))
  | _, _, _, .joinCirc prem hJ1 _ _ hkc _ _ hΓ => fun x hx =>
      wfI (prem 0)
        (joinCtxOrV_subset hJ1 (keptChain_subset hkc) 0 ((hΓ x).mp hx))
  | _, _, _, .joinCircP prem _ hJ1 _ _ _ _ _ _ hΓ => fun x hx =>
      wfI (prem 0) (joinCtxOrP_subset hJ1 0 ((hΓ x).mp hx))

/-- Every zone of a derivable irregular sequent lies inside `Ĝ`. -/
theorem wfI {G : Form} : ∀ {Ξ Θ : List Form} {C : Form},
    FRJWi G Ξ Θ C → Ξ ++ Θ ⊆ gHat G
  | _, _, _, .axI _ _ _ hTh => by
      intro x hx
      simp only [List.nil_append] at hx
      rcases List.mem_append.mp ((hTh x).mp hx) with hx' | hx'
      · rcases List.mem_append.mp hx' with hx'' | hx''
        · exact List.mem_append_left _ (List.mem_append_left _ (rm_subset hx''))
        · exact List.mem_append_left _ (List.mem_append_right _ hx'')
      · exact List.mem_append_right _ hx'
  | _, _, _, .andI1 d _ => wfI d
  | _, _, _, .andI2 d _ => wfI d
  | _, _, _, .orI d₁ _ _ h₂ _ hSt hTh => by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp ((hSt x).mp hx) with hx | hx
        · exact wfI d₁ (List.mem_append_left _ hx)
        · exact wfI d₁ (h₂ hx)
      · exact wfI d₁ (List.mem_append_right _ (mem_cap.mp ((hTh x).mp hx)).1)
  | _, _, _, .impInI d hpre _ _ _ hSt hTh => by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp ((hSt x).mp hx) with hx' | hx'
        · exact wfI d (List.mem_append_left _ hx')
        · exact wfI d (List.mem_append_right _ ((hpre x).mpr (List.mem_append_right _ hx')))
      · exact wfI d (List.mem_append_right _
          ((hpre x).mpr (List.mem_append_left _ ((hTh x).mp hx))))
  | _, _, _, .lift _ hTh => by
      intro x hx
      simp only [List.nil_append] at hx
      exact (hTh x hx).2
  | _, _, _, .circNotIn _ _ hTh _ => by
      intro x hx
      simp only [List.nil_append] at hx
      exact (hTh x hx).2
  | _, _, _, .axIC _ _ _ _ _ hTh => by
      intro x hx
      simp only [List.nil_append] at hx
      exact (List.mem_filter.mp ((hTh x).mp hx)).1

end

/-- The three parts of a derivable context exhaust it:
`Γ = Γ^at ++ Γ^⊃ ++ Γ^◯`.  This is what the join rules' split silently
relies on — the invariant the third zone would have broken had it been
added without the modal rules, and keeps now that it is added with
them. -/
theorem atPart_union_impPart {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJWr G t Γ C) : Γ ⊆ atPart Γ ++ impPart Γ ++ circPart Γ := by
  intro x hx
  have hG := wfR d hx
  simp only [gHat, List.mem_append] at hG
  rcases hG with (hG | hG) | hG
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_filter.mpr ⟨hx, (List.mem_filter.mp hG).2⟩))
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_filter.mpr ⟨hx, (List.mem_filter.mp hG).2⟩))
  · exact List.mem_append_right _
      (List.mem_filter.mpr ⟨hx, (List.mem_filter.mp hG).2⟩)

/-! ## The `Ax^I` case of Lemma 3.9(ii), in label form

The argument is entirely about labels, so it is available already: it
needs Lemma 3.4(iii) and (Cl5) and nothing about the model. -/

/-- For a variable `p`, no sequent reachable from the `Ax^I` conclusion
for `p` has `p` among its left formulas. -/
theorem axI_not_mem_lhs {G : Form} {p : String} {s : Sequent}
    (h : StepsRfl G
      (.irr [] (rm (gAt G) (.atom p) ++ gImp G ++ gCirc G) (.atom p)) s) :
    Form.atom p ∉ s.lhs := by
  intro hmem
  have hclo := lhs_clo_of_steps h _ hmem
  have hin := clo_pv hclo
  simp only [Sequent.lhs_irr, List.nil_append, List.mem_append] at hin
  rcases hin with (hin | hin) | hin
  · exact (mem_rm.mp hin).1 rfl
  · rw [gImp] at hin
    exact Bool.noConfusion ((List.mem_filter.mp hin).2)
  · rw [gCirc] at hin
    exact Bool.noConfusion ((List.mem_filter.mp hin).2)


end FRJ.W
