import LaxLogic.PLL.SubTab.Complete

/-!
# Closed subframe tableaux as derivations

2026-10-20.  Statements approved by Matthew before the proofs (lean-certify
R10).

A closed tableau (`TCert`, checked by `check`) is translated directly into a
natural-deduction derivation, under the reading

    ⌈⟨false, Γ, Δ⟩⌉ = ⋁Δ          (a world outside S)
    ⌈⟨true,  Γ, Δ⟩⌉ = ◯⋁Δ         (an S-point),        ⋁[] = ⊥

so the yes side of the subframe tableau no longer goes through a completeness
theorem (`SubframeModel.CF.completeness`, i.e. FRJW), and completeness for
finite subframe models follows from the tableau's own dichotomy (`dich`, as in
`complete`, restated here without the certifiers so that no constant of the
old route is reached).
Nothing existing is changed: `yes`, `CF.completeness` and FRJW stay as they
are; `yes'` is an alternative.

Each tableau rule is one lemma below (`r_bot`, …, `r_boxR`), stated for both
kinds of world at once through `gl b Δ` (`⋁Δ`, or `◯⋁Δ` when
`b`).  Fragment first (CLAUDE.md rule 8): the ◯-free instance
(`derive_of_check_boxFree`, `completeness_fin_boxFree`) uses the nine ◯-free
rules only.
-/

open PLLFormula

namespace PLLND
namespace SubTab

open SubframeModel.CF

/-! ## The reading of a signed sequent -/

/-- `⋁Δ`, with `⋁[] = ⊥`. -/
def bigOr : List PLLFormula → PLLFormula
  | [] => .falsePLL
  | δ :: Δ => .or δ (bigOr Δ)

/-- What a signed sequent asserts when it has a closed tableau. -/
def goal (s : SSeq) : PLLFormula := if s.isS then .somehow (bigOr s.suc) else bigOr s.suc

/-- The reading by the kind of world. -/
def gl : Bool → List PLLFormula → PLLFormula
  | true, Δ => .somehow (bigOr Δ)
  | false, Δ => bigOr Δ

theorem goal_eq (s : SSeq) : goal s = gl s.isS s.suc := by
  obtain ⟨b, Γ, Δ⟩ := s
  cases b <;> rfl

/-- No ◯ rule anywhere in the certificate. -/
def TCert.boxFree : TCert → Bool
  | .bot | .ax _ => true
  | .andL _ _ c | .orR _ _ c | .impLoc _ _ c | .impR _ _ c => c.boxFree
  | .orL _ _ c₁ c₂ | .impL _ _ c₁ c₂ | .andR _ _ c₁ c₂ => c₁.boxFree && c₂.boxFree
  | .boxL _ _ | .boxLoc _ _ | .boxR _ _ => false

/-! ## Derived rules -/

/-- Weakening, exchange, contraction (`LaxND.rename`). -/
theorem rn {Γ Γ' : List PLLFormula} {φ : PLLFormula} (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ')
    (d : Nonempty (Γ ⊢ φ)) : Nonempty (Γ' ⊢ φ) :=
  d.elim fun d => ⟨d.rename H⟩

theorem sub_cons {Γ : List PLLFormula} {A : PLLFormula} : ∀ ψ, ψ ∈ Γ → ψ ∈ A :: Γ :=
  fun _ h => List.mem_cons_of_mem _ h

theorem app_cons {Γ : List PLLFormula} {A : PLLFormula} : ∀ ψ, ψ ∈ Γ ++ [A] → ψ ∈ A :: Γ :=
  fun _ h => (List.mem_append.mp h).elim (List.mem_cons_of_mem _)
    fun h => List.mem_singleton.mp h ▸ List.mem_cons_self

theorem cons_cons {Γ : List PLLFormula} {A B : PLLFormula} :
    ∀ ψ, ψ ∈ B :: Γ → ψ ∈ B :: A :: Γ := fun _ h =>
  (List.mem_cons.mp h).elim (fun e => e ▸ List.mem_cons_self)
    fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- Cut on an appended hypothesis. -/
theorem cutApp {Γ : List PLLFormula} {A G : PLLFormula} (hA : Nonempty (Γ ⊢ A))
    (d : Nonempty ((Γ ++ [A]) ⊢ G)) : Nonempty (Γ ⊢ G) := by
  obtain ⟨hA⟩ := hA
  obtain ⟨d⟩ := rn app_cons d
  exact ⟨.impElim (.impIntro d) hA⟩

/-- Elimination of a big disjunction. -/
theorem orElimBig {G : PLLFormula} : ∀ (L : List PLLFormula) {Γ : List PLLFormula},
    Nonempty (Γ ⊢ bigOr L) → (∀ δ ∈ L, Nonempty ((δ :: Γ) ⊢ G)) → Nonempty (Γ ⊢ G)
  | [], _, ⟨d⟩, _ => ⟨.falsoElim G d⟩
  | δ :: L, Γ, ⟨d⟩, h => by
      obtain ⟨d₁⟩ := h δ List.mem_cons_self
      obtain ⟨d₂⟩ := orElimBig L (Γ := bigOr L :: Γ) ⟨.iden List.mem_cons_self⟩
        fun δ' hδ' => rn cons_cons (h δ' (List.mem_cons_of_mem _ hδ'))
      exact ⟨.orElim d d₁ d₂⟩

/-- Introduction into a big disjunction. -/
theorem injBig {Γ : List PLLFormula} {A : PLLFormula} (d : Nonempty (Γ ⊢ A)) :
    ∀ {Δ : List PLLFormula}, A ∈ Δ → Nonempty (Γ ⊢ bigOr Δ)
  | [], h => absurd h List.not_mem_nil
  | _ :: _, h => by
      rcases List.mem_cons.mp h with e | h
      · subst e; exact d.elim fun d => ⟨.orIntro1 d⟩
      · exact (injBig d h).elim fun d => ⟨.orIntro2 d⟩

/-- A member of `Δ` gives the reading (with the ◯-unit at an S-point). -/
theorem injGl {b : Bool} {Γ Δ : List PLLFormula} {A : PLLFormula} (d : Nonempty (Γ ⊢ A))
    (h : A ∈ Δ) : Nonempty (Γ ⊢ gl b Δ) := by
  cases b with
  | false => exact injBig d h
  | true => exact (injBig d h).elim fun d => ⟨.laxIntro d⟩

/-- **Transfer**: from the reading of `L`, the reading of `Δ`, when each member
of `L` gives the reading of `Δ` (at an S-point by ◯-elimination first). -/
theorem transfer {b : Bool} {Γ L Δ : List PLLFormula} (d : Nonempty (Γ ⊢ gl b L))
    (h : ∀ δ ∈ L, Nonempty ((δ :: Γ) ⊢ gl b Δ)) : Nonempty (Γ ⊢ gl b Δ) := by
  cases b with
  | false => exact orElimBig L d h
  | true =>
      obtain ⟨d⟩ := d
      obtain ⟨k⟩ := orElimBig L (Γ := bigOr L :: Γ) ⟨.iden List.mem_cons_self⟩
        fun δ hδ => rn cons_cons (h δ hδ)
      exact ⟨.laxElim d k⟩

theorem mem_app1 {Δ : List PLLFormula} {A δ : PLLFormula} (h : δ ∈ Δ ++ [A]) :
    δ ∈ Δ ∨ δ = A :=
  (List.mem_append.mp h).imp_right List.mem_singleton.mp

theorem mem_app2 {Δ : List PLLFormula} {A B δ : PLLFormula} (h : δ ∈ Δ ++ [A, B]) :
    δ ∈ Δ ∨ δ = A ∨ δ = B :=
  (List.mem_append.mp h).imp_right fun h =>
    (List.mem_cons.mp h).imp_right List.mem_singleton.mp

theorem mem_head_one {Γ : List PLLFormula} {δ B : PLLFormula} (h : δ ∈ [B]) : B ∈ δ :: Γ := by
  rw [List.mem_singleton.mp h]
  exact List.mem_cons_self

/-- A member of `Δ` taken as hypothesis gives the reading of `Δ`. -/
theorem selfGl {b : Bool} {Γ Δ : List PLLFormula} {δ : PLLFormula} (h : δ ∈ Δ) :
    Nonempty ((δ :: Γ) ⊢ gl b Δ) :=
  injGl ⟨.iden List.mem_cons_self⟩ h

/-! ## The rules, one lemma each -/

section Rules
variable {b : Bool} {Γ Δ : List PLLFormula} {A B : PLLFormula}

theorem r_bot (h : PLLFormula.falsePLL ∈ Γ) : Nonempty (Γ ⊢ gl b Δ) :=
  ⟨.falsoElim _ (.iden h)⟩

theorem r_ax (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : Nonempty (Γ ⊢ gl b Δ) :=
  injGl ⟨.iden hΓ⟩ hΔ

theorem r_andL (h : PLLFormula.and A B ∈ Γ) (d : Nonempty ((Γ ++ [A, B]) ⊢ gl b Δ)) :
    Nonempty (Γ ⊢ gl b Δ) := by
  have dAB : Γ ⊢ PLLFormula.and A B := .iden h
  have d' : Nonempty (((Γ ++ [A]) ++ [B]) ⊢ gl b Δ) := rn (fun ψ hψ => by
    rcases mem_app2 hψ with hψ | e | e
    · exact List.mem_append_left _ (List.mem_append_left _ hψ)
    · exact List.mem_append_left _ (List.mem_append_right _ (e ▸ List.mem_singleton_self A))
    · exact List.mem_append_right _ (e ▸ List.mem_singleton_self B)) d
  exact cutApp ⟨.andElim1 dAB⟩ (cutApp (rn (fun _ h => List.mem_append_left _ h)
    ⟨.andElim2 dAB⟩) d')

theorem r_orL (h : PLLFormula.or A B ∈ Γ) (d₁ : Nonempty ((Γ ++ [A]) ⊢ gl b Δ))
    (d₂ : Nonempty ((Γ ++ [B]) ⊢ gl b Δ)) : Nonempty (Γ ⊢ gl b Δ) := by
  obtain ⟨d₁⟩ := rn app_cons d₁
  obtain ⟨d₂⟩ := rn app_cons d₂
  exact ⟨.orElim (.iden h) d₁ d₂⟩

theorem r_impL (h : PLLFormula.ifThen A B ∈ Γ) (d₁ : Nonempty (Γ ⊢ gl b (Δ ++ [A])))
    (d₂ : Nonempty ((Γ ++ [B]) ⊢ gl b Δ)) : Nonempty (Γ ⊢ gl b Δ) :=
  transfer d₁ fun δ hδ => (mem_app1 hδ).elim selfGl fun e => by
    subst e
    exact cutApp ⟨.impElim (.iden (List.mem_cons_of_mem _ h)) (.iden List.mem_cons_self)⟩
      (rn (fun ψ hψ => (List.mem_append.mp hψ).elim
        (fun hψ => List.mem_append_left _ (List.mem_cons_of_mem _ hψ))
        (List.mem_append_right _)) d₂)

theorem r_andR (h : PLLFormula.and A B ∈ Δ) (d₁ : Nonempty (Γ ⊢ gl b (Δ ++ [A])))
    (d₂ : Nonempty (Γ ⊢ gl b (Δ ++ [B]))) : Nonempty (Γ ⊢ gl b Δ) :=
  transfer d₁ fun δ hδ => (mem_app1 hδ).elim selfGl fun e => by
    subst e
    exact transfer (rn sub_cons d₂) fun δ' hδ' => (mem_app1 hδ').elim selfGl fun e' => by
      subst e'
      exact injGl ⟨.andIntro (.iden (List.mem_cons_of_mem _ List.mem_cons_self))
        (.iden List.mem_cons_self)⟩ h

theorem r_orR (h : PLLFormula.or A B ∈ Δ) (d : Nonempty (Γ ⊢ gl b (Δ ++ [A, B]))) :
    Nonempty (Γ ⊢ gl b Δ) :=
  transfer d fun δ hδ => by
    rcases mem_app2 hδ with hδ | e | e
    · exact selfGl hδ
    · subst e; exact injGl ⟨.orIntro1 (.iden List.mem_cons_self)⟩ h
    · subst e; exact injGl ⟨.orIntro2 (.iden List.mem_cons_self)⟩ h

theorem r_impLoc (h : PLLFormula.ifThen A B ∈ Δ) (d : Nonempty (Γ ⊢ gl b (Δ ++ [B]))) :
    Nonempty (Γ ⊢ gl b Δ) :=
  transfer d fun δ hδ => (mem_app1 hδ).elim selfGl fun e => by
    subst e
    exact injGl ⟨.impIntro (.iden (List.mem_cons_of_mem _ List.mem_cons_self))⟩ h

theorem r_impR (h : PLLFormula.ifThen A B ∈ Δ) (d : Nonempty ((Γ ++ [A]) ⊢ gl false [B])) :
    Nonempty (Γ ⊢ gl b Δ) := by
  obtain ⟨dB⟩ := rn app_cons (orElimBig [B] d fun _ hδ => ⟨.iden (mem_head_one hδ)⟩)
  exact injGl ⟨.impIntro dB⟩ h

end Rules

/-! ## (T₀) The translation, ◯-free instance -/

theorem derive_bf : ∀ (c : TCert) (Γ Δ : List PLLFormula), c.boxFree = true →
    check ⟨false, Γ, Δ⟩ c = true → Nonempty (Γ ⊢ gl false Δ) := by
  intro c
  induction c with
  | bot =>
    intro Γ Δ _ h
    simp only [check] at h
    exact r_bot (mem_of h)
  | ax A =>
    intro Γ Δ _ h
    simp only [check, Bool.and_eq_true] at h
    exact r_ax (mem_of h.1) (mem_of h.2)
  | andL A B c ih =>
    intro Γ Δ hb h
    simp only [check, Bool.and_eq_true] at h
    exact r_andL (mem_of h.1) (ih _ _ hb h.2)
  | orL A B c₁ c₂ ih₁ ih₂ =>
    intro Γ Δ hb h
    simp only [check, Bool.and_eq_true] at h
    simp only [TCert.boxFree, Bool.and_eq_true] at hb
    exact r_orL (mem_of h.1.1) (ih₁ _ _ hb.1 h.1.2) (ih₂ _ _ hb.2 h.2)
  | impL A B c₁ c₂ ih₁ ih₂ =>
    intro Γ Δ hb h
    simp only [check, Bool.and_eq_true] at h
    simp only [TCert.boxFree, Bool.and_eq_true] at hb
    exact r_impL (mem_of h.1.1) (ih₁ _ _ hb.1 h.1.2) (ih₂ _ _ hb.2 h.2)
  | boxL A c _ =>
    intro Γ Δ hb _
    exact absurd hb Bool.false_ne_true
  | andR A B c₁ c₂ ih₁ ih₂ =>
    intro Γ Δ hb h
    simp only [check, Bool.and_eq_true] at h
    simp only [TCert.boxFree, Bool.and_eq_true] at hb
    exact r_andR (mem_of h.1.1) (ih₁ _ _ hb.1 h.1.2) (ih₂ _ _ hb.2 h.2)
  | orR A B c ih =>
    intro Γ Δ hb h
    simp only [check, Bool.and_eq_true] at h
    exact r_orR (mem_of h.1) (ih _ _ hb h.2)
  | impLoc A B c ih =>
    intro Γ Δ hb h
    simp only [check, Bool.and_eq_true] at h
    exact r_impLoc (mem_of h.1.1) (ih _ _ hb h.2)
  | boxLoc A c _ =>
    intro Γ Δ hb _
    exact absurd hb Bool.false_ne_true
  | impR A B c ih =>
    intro Γ Δ hb h
    simp only [check, Bool.and_eq_true] at h
    exact r_impR (mem_of h.1) (ih _ _ hb h.2)
  | boxR A c _ =>
    intro Γ Δ hb _
    exact absurd hb Bool.false_ne_true

/-- **(T₀) Translation, ◯-free instance.** -/
theorem derive_of_check_boxFree : ∀ (c : TCert) (s : SSeq),
    c.boxFree = true → s.isS = false → check s c = true → Nonempty (s.ant ⊢ bigOr s.suc) := by
  intro c s hb hs h
  obtain ⟨b, Γ, Δ⟩ := s
  subst hs
  exact derive_bf c Γ Δ hb h

/-! ## Completeness for finite subframe models, ◯-free instance -/

/-- A finite countermodel contradicts validity in finite decidable models. -/
theorem refutes_valid {φ : PLLFormula} {m : SubCM} (hm : m.refutes φ = true)
    (h : ∀ (M : SubframeModel) [FinDec M] (x : M.W), M.force x φ) : False := by
  simp only [SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm
  have hr := (SubCM.ok_parts hm.1).1
  have := (SubCM.forceB_iff hm.1 φ ⟨m.root, hr⟩).mpr (h (m.toModel hm.1) ⟨m.root, hr⟩)
  rw [hm.2] at this
  exact Bool.false_ne_true this

/-- Over a closed universe without ◯, a certificate that checks uses no ◯ rule. -/
theorem boxFree_of_check {U : List PLLFormula} (hU : Closed U) (hB : NoBox U) :
    ∀ (c : TCert) (s : SSeq), s.ant ⊆ U → s.suc ⊆ U → check s c = true → c.boxFree = true := by
  intro c
  induction c with
  | bot => intros; rfl
  | ax _ => intros; rfl
  | andL A B c ih =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.and A B (hΓ (mem_of h.1))
    exact ih ⟨s.isS, s.ant ++ [A, B], s.suc⟩ (app_sub hΓ (all_two hAB.1 hAB.2)) hΔ h.2
  | orL A B c₁ c₂ ih₁ ih₂ =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.or A B (hΓ (mem_of h.1.1))
    simp only [TCert.boxFree, Bool.and_eq_true]
    exact ⟨ih₁ ⟨s.isS, s.ant ++ [A], s.suc⟩ (app_sub hΓ (all_one hAB.1)) hΔ h.1.2,
      ih₂ ⟨s.isS, s.ant ++ [B], s.suc⟩ (app_sub hΓ (all_one hAB.2)) hΔ h.2⟩
  | impL A B c₁ c₂ ih₁ ih₂ =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.imp A B (hΓ (mem_of h.1.1))
    simp only [TCert.boxFree, Bool.and_eq_true]
    exact ⟨ih₁ ⟨s.isS, s.ant, s.suc ++ [A]⟩ hΓ (app_sub hΔ (all_one hAB.1)) h.1.2,
      ih₂ ⟨s.isS, s.ant ++ [B], s.suc⟩ (app_sub hΓ (all_one hAB.2)) hΔ h.2⟩
  | boxL A c _ =>
    intro s hΓ _ h
    simp only [check, Bool.and_eq_true] at h
    exact absurd (hΓ (mem_of h.1.2)) (hB A)
  | andR A B c₁ c₂ ih₁ ih₂ =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.and A B (hΔ (mem_of h.1.1))
    simp only [TCert.boxFree, Bool.and_eq_true]
    exact ⟨ih₁ ⟨s.isS, s.ant, s.suc ++ [A]⟩ hΓ (app_sub hΔ (all_one hAB.1)) h.1.2,
      ih₂ ⟨s.isS, s.ant, s.suc ++ [B]⟩ hΓ (app_sub hΔ (all_one hAB.2)) h.2⟩
  | orR A B c ih =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.or A B (hΔ (mem_of h.1))
    exact ih ⟨s.isS, s.ant, s.suc ++ [A, B]⟩ hΓ (app_sub hΔ (all_two hAB.1 hAB.2)) h.2
  | impLoc A B c ih =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.imp A B (hΔ (mem_of h.1.1))
    exact ih ⟨s.isS, s.ant, s.suc ++ [B]⟩ hΓ (app_sub hΔ (all_one hAB.2)) h.2
  | boxLoc A c _ =>
    intro s _ hΔ h
    simp only [check, Bool.and_eq_true] at h
    exact absurd (hΔ (mem_of h.1.2)) (hB A)
  | impR A B c ih =>
    intro s hΓ hΔ h
    simp only [check, Bool.and_eq_true] at h
    have hAB := hU.imp A B (hΔ (mem_of h.1))
    exact ih ⟨false, s.ant ++ [A], [B]⟩ (app_sub hΓ (all_one hAB.1)) (all_one hAB.2) h.2
  | boxR A c _ =>
    intro s _ hΔ h
    simp only [check, Bool.and_eq_true] at h
    exact absurd (hΔ (mem_of h.1)) (hB A)

/-- `⋁[φ]` gives `φ`. -/
theorem of_bigOr_one {Γ : List PLLFormula} {φ : PLLFormula} (d : Nonempty (Γ ⊢ bigOr [φ])) :
    Nonempty (Γ ⊢ φ) :=
  orElimBig [φ] d fun _ hδ => ⟨.iden (mem_head_one hδ)⟩

/-- The dichotomy of `complete_boxFree`, stated with `check` and `refutes`
directly: the certifier `yes` carries the old soundness proof (through
`CF.completeness`), and a statement that names it would put FRJW among the
constants the new route depends on.  Same proof as `complete_boxFree`. -/
theorem dichotomy_boxFree (φ : PLLFormula) (hφ : NoBox (subs φ)) :
    (∃ c, check ⟨false, [], [φ]⟩ c = true) ∨ (∃ m : SubCM, m.refutes φ = true) := by
  rcases dich_boxFree (subs φ) (subs_closed φ) hφ _ ⟨false, [], [φ]⟩ rfl
      (fun _ h => absurd h List.not_mem_nil) (all_one (self_mem_subs φ)) with
    ⟨c, hc⟩ | ⟨t, hg, hcov⟩
  · exact .inl ⟨c, hc⟩
  · exact .inr ⟨extract (model t hg) (rootW t hg) φ,
      extract_refutes ((root_refutes t hg hcov).2.2 φ List.mem_cons_self)⟩

/-- The dichotomy of `complete`, stated with `check` and `refutes` directly
(see `dichotomy_boxFree`).  Same proof as `complete`. -/
theorem dichotomy (φ : PLLFormula) :
    (∃ c, check ⟨false, [], [φ]⟩ c = true) ∨ (∃ m : SubCM, m.refutes φ = true) := by
  rcases dich (subs φ) (subs_closed φ) _ ⟨false, [], [φ]⟩ rfl
      (fun _ h => absurd h List.not_mem_nil) (all_one (self_mem_subs φ)) with
    ⟨c, hc⟩ | ⟨t, hg, hcov⟩
  · exact .inl ⟨c, hc⟩
  · exact .inr ⟨extract (model t hg) (rootW t hg) φ,
      extract_refutes ((root_refutes t hg hcov).2.2 φ List.mem_cons_self)⟩

/-- **Completeness for finite subframe models, ◯-free instance**, from the
tableau: the dichotomy and (T₀). -/
theorem completeness_fin_boxFree (φ : PLLFormula) (hφ : NoBox (subs φ))
    (h : ∀ (M : SubframeModel) [FinDec M] (x : M.W), M.force x φ) : Holds φ := by
  rcases dichotomy_boxFree φ hφ with ⟨c, hc⟩ | ⟨m, hm⟩
  · have hbf := boxFree_of_check (subs_closed φ) hφ c ⟨false, [], [φ]⟩
      (fun _ h => absurd h List.not_mem_nil) (all_one (self_mem_subs φ)) hc
    exact of_bigOr_one (derive_of_check_boxFree c ⟨false, [], [φ]⟩ hbf rfl hc)
  · exact (refutes_valid hm h).elim

/-! ## The three ◯ rules -/

section BoxRules
variable {Γ Δ : List PLLFormula} {A : PLLFormula}

theorem r_boxL (h : PLLFormula.somehow A ∈ Γ) (d : Nonempty ((Γ ++ [A]) ⊢ gl true Δ)) :
    Nonempty (Γ ⊢ gl true Δ) := by
  obtain ⟨d⟩ := rn app_cons d
  exact ⟨.laxElim (.iden h) d⟩

theorem r_boxLoc (h : PLLFormula.somehow A ∈ Δ) (d : Nonempty (Γ ⊢ gl true (Δ ++ [A]))) :
    Nonempty (Γ ⊢ gl true Δ) :=
  transfer d fun δ hδ => (mem_app1 hδ).elim selfGl fun e => by
    subst e
    exact injGl ⟨.laxIntro (.iden List.mem_cons_self)⟩ h

theorem r_boxR {b : Bool} (h : PLLFormula.somehow A ∈ Δ) (d : Nonempty (Γ ⊢ gl true [A])) :
    Nonempty (Γ ⊢ gl b Δ) := by
  obtain ⟨d⟩ := d
  obtain ⟨k⟩ := orElimBig [A] (G := .somehow A) (Γ := bigOr [A] :: Γ) ⟨.iden List.mem_cons_self⟩
    fun _ hδ => ⟨.laxIntro (.iden (mem_head_one hδ))⟩
  exact injGl ⟨.laxElim d k⟩ h

end BoxRules

/-! ## (T) The translation, PLL -/

theorem derive_gl : ∀ (c : TCert) (b : Bool) (Γ Δ : List PLLFormula),
    check ⟨b, Γ, Δ⟩ c = true → Nonempty (Γ ⊢ gl b Δ) := by
  intro c
  induction c with
  | bot =>
    intro b Γ Δ h
    simp only [check] at h
    exact r_bot (mem_of h)
  | ax A =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    exact r_ax (mem_of h.1) (mem_of h.2)
  | andL A B c ih =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    exact r_andL (mem_of h.1) (ih _ _ _ h.2)
  | orL A B c₁ c₂ ih₁ ih₂ =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    exact r_orL (mem_of h.1.1) (ih₁ _ _ _ h.1.2) (ih₂ _ _ _ h.2)
  | impL A B c₁ c₂ ih₁ ih₂ =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    exact r_impL (mem_of h.1.1) (ih₁ _ _ _ h.1.2) (ih₂ _ _ _ h.2)
  | boxL A c ih =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨hb, hm⟩, hc⟩ := h
    subst hb
    exact r_boxL (mem_of hm) (ih _ _ _ hc)
  | andR A B c₁ c₂ ih₁ ih₂ =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    exact r_andR (mem_of h.1.1) (ih₁ _ _ _ h.1.2) (ih₂ _ _ _ h.2)
  | orR A B c ih =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    exact r_orR (mem_of h.1) (ih _ _ _ h.2)
  | impLoc A B c ih =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    exact r_impLoc (mem_of h.1.1) (ih _ _ _ h.2)
  | boxLoc A c ih =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨hb, hm⟩, hc⟩ := h
    subst hb
    exact r_boxLoc (mem_of hm) (ih _ _ _ hc)
  | impR A B c ih =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    exact r_impR (mem_of h.1) (ih _ _ _ h.2)
  | boxR A c ih =>
    intro b Γ Δ h
    simp only [check, Bool.and_eq_true] at h
    exact r_boxR (mem_of h.1) (ih _ _ _ h.2)

/-- **(T) Translation, PLL.** -/
theorem derive_of_check : ∀ (c : TCert) (s : SSeq),
    check s c = true → Nonempty (s.ant ⊢ goal s) := by
  intro c s h
  obtain ⟨b, Γ, Δ⟩ := s
  rw [goal_eq]
  exact derive_gl c b Γ Δ h

/-! ## (Y) The yes side without a completeness theorem -/

/-- **(Y)** A closed tableau for `⊢ φ` proves `φ`, by the tableau's own rules. -/
theorem holds_of_check' {φ : PLLFormula} {c : TCert}
    (h : check ⟨false, [], [φ]⟩ c = true) : Holds φ :=
  of_bigOr_one (derive_gl c false [] [φ] h)

/-- The yes side, justified by the tableau's own rules (an alternative to `yes`;
both kept and pinned). -/
def yes' : Certify.Certifier PLLFormula TCert Holds where
  check φ c := check ⟨false, [], [φ]⟩ c
  sound _ _ h := holds_of_check' h

/-! ## (C) Completeness for finite subframe models -/

/-- **(C) Completeness for finite subframe models**, from the tableau: the
dichotomy and (Y). -/
theorem completeness_fin (φ : PLLFormula)
    (h : ∀ (M : SubframeModel) [FinDec M] (x : M.W), M.force x φ) : Holds φ := by
  rcases dichotomy φ with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact holds_of_check' hc
  · exact (refutes_valid hm h).elim

end SubTab
end PLLND

#axioms_within PLLND.SubTab.derive_of_check_boxFree [propext, Quot.sound]
#axioms_within PLLND.SubTab.completeness_fin_boxFree [propext, Quot.sound]
#axioms_within PLLND.SubTab.derive_of_check [propext, Quot.sound]
#axioms_within PLLND.SubTab.holds_of_check' [propext, Quot.sound]
#axioms_within PLLND.SubTab.yes' [propext, Quot.sound]
#axioms_within PLLND.SubTab.completeness_fin [propext, Quot.sound]
