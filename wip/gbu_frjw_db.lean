/-
# The W-database lemma layer — Lemma 9/11/12 over `WSeq`

The `wip/gbu_db.lean` layer (F&F Lemmas 9–12) transcribed to the
W-database of `wip/gbu_frjw_dichotomy.lean`.  Family-independent
helpers (`finPi`, `finEx`, `keptChainRestrict`, the `Ĝ`-zone facts and
the `enumOf` machinery) are imported from `wip/gbu_db.lean`, not
duplicated.  Three real changes:

* **(ix) is Lift-based and STRONGER.**  The V-version went through
  `⊃∉` and needed `¬ Clo Ω A`; the W-family deletes `⊃∉`, and the
  route is `⊃∈` on the regular witness followed by `Lift` at `Θ := Ω`
  — the `¬ Clo` hypothesis disappears.
* **The clean-refutation layer concludes the PLEDGED query.**  The old
  `evalR_of_refutedCleanly` lost the tag through (DB2) — the §10a′
  obstruction, "the database forgets it".  The tag-explicit `WSeq` and
  the `tagLeB`-aware `WSubsumes` keep it: `covers_mono` carries a
  `chain` pledge across context growth, and `barren` tops the order,
  so subsumption preserves pledge-goodness and the lookup lands in
  `WEvalRP`.  `EvalRC`/`regC` have no W-analogue at all.
* Regular rows are tag-indexed throughout: `hsat.1` yields the
  derivation directly, and (DB2) is queried at the witness's own tag.
-/
import wip.gbu_frjw_dichotomy
import wip.gbu_db

namespace FRJ.Gbu.W

open FRJ Form FRJ.Gbu FRJ.Search

variable {G : Form} {D : WSeq → Prop}

/-! ## The pledge survives subsumption -/

/-- `tagLeB`-subsumption preserves the pledge: `barren` tops the order,
`chain` pledges travel by `covers_mono`, and `blocked` pledges
nothing. -/
theorem pledge_of_le {t t' : Tag} {Γ Γ' : List Form} {C : Form}
    (hle : tagLeB t t' = true) (hΓ : Γ ⊆ Γ')
    (h : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C) :
    t' = .barren ∨ ∃ W, t' = .chain W ∧ Covers Γ' W C := by
  rcases h with rfl | ⟨W, rfl, hc⟩
  · cases t' with
    | barren => exact Or.inl rfl
    | chain _ => exact absurd hle (by simp [tagLeB])
    | blocked => exact absurd hle (by simp [tagLeB])
  · cases t' with
    | barren => exact Or.inl rfl
    | chain W' =>
        have : W = W' := by simpa [tagLeB] using hle
        exact Or.inr ⟨W', rfl, this ▸ covers_mono hΓ hc⟩
    | blocked => exact absurd hle (by simp [tagLeB])

/-- The pledged lookup weakens to the plain one. -/
theorem wEvalR_of_wEvalRP {Ψ : List Form} {C : Form}
    (h : WEvalRP D Ψ C) : WEvalR D Ψ C :=
  let ⟨t, Γ, hmem, _, hcov⟩ := h
  ⟨t, Γ, hmem, hcov⟩

/-! ## Lemma 9 (`lemma:gbuInv`) — the inversion clauses, W-form -/

/-- **(i)** `A,B,Ψ ⇒g C` gives `A∧B,Ψ ⇒g C`. -/
theorem gbuInv1 {Ψ : List Form} {A B C : Form}
    (h : WEvalR D (A :: B :: Ψ) C) : WEvalR D (.and A B :: Ψ) C := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h
  refine ⟨t, Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .and (hcl A List.mem_cons_self)
      (hcl B (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact hcl X (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hX'))

/-- **(iii)** `Aₖ,Ψ ⇒g C` gives `A₁∨A₂,Ψ ⇒g C`. -/
theorem gbuInv3L {Ψ : List Form} {A₁ A₂ C : Form}
    (h : WEvalR D (A₁ :: Ψ) C) : WEvalR D (.or A₁ A₂ :: Ψ) C := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h
  refine ⟨t, Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .orL (hcl A₁ List.mem_cons_self)
  · exact hcl X (List.mem_cons_of_mem _ hX')

theorem gbuInv3R {Ψ : List Form} {A₁ A₂ C : Form}
    (h : WEvalR D (A₂ :: Ψ) C) : WEvalR D (.or A₁ A₂ :: Ψ) C := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h
  refine ⟨t, Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .orR (hcl A₂ List.mem_cons_self)
  · exact hcl X (List.mem_cons_of_mem _ hX')

/-- **(iv)** `B,Ψ ⇒g C` gives `A⊃B,Ψ ⇒g C`. -/
theorem gbuInv4 {Ψ : List Form} {A B C : Form}
    (h : WEvalR D (B :: Ψ) C) : WEvalR D (.imp A B :: Ψ) C := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h
  refine ⟨t, Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .imp (hcl B List.mem_cons_self)
  · exact hcl X (List.mem_cons_of_mem _ hX')

/-- **(ii)** `Ψ ⇒g Cₖ` gives `Ψ ⇒g C₁∧C₂`. -/
theorem gbuInv2 (hsat : WSaturated G D)
    {Ψ : List Form} {C₁ C₂ : Form} (hgoal : Form.and C₁ C₂ ∈ sfR G)
    (h : WEvalR D Ψ C₁ ∨ WEvalR D Ψ C₂) : WEvalR D Ψ (.and C₁ C₂) := by
  have step : ∀ {C : Form}, WEvalR D Ψ C →
      (∀ {t : Tag} {Γ : List Form}, FRJWr G t Γ C →
        FRJWr G t Γ (.and C₁ C₂)) → WEvalR D Ψ (.and C₁ C₂) := by
    rintro C ⟨t, Γ, hmem, hcl⟩ mk
    obtain ⟨d⟩ := hsat.1 _ hmem
    obtain ⟨s', hs'mem, hsub⟩ := hsat.2 (.reg t Γ (.and C₁ C₂)) ⟨mk d⟩
    match s', hsub with
    | .reg t' Γ' _, ⟨rfl, _, hΓ⟩ =>
        exact ⟨t', Γ', hs'mem, fun X hX => clo_mono hΓ (hcl X hX)⟩
  rcases h with h | h
  · exact step h (fun d => .andR1 d hgoal)
  · exact step h (fun d => .andR2 d hgoal)

/-- **(v)** `Ψ ⇒g B` with `A ∈ Cl(Ψ)` gives `Ψ ⇒g A⊃B`, through `⊃∈`. -/
theorem gbuInv5 (hsat : WSaturated G D)
    {Ψ : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ψ A) (h : WEvalR D Ψ B) : WEvalR D Ψ (.imp A B) := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h
  obtain ⟨d⟩ := hsat.1 _ hmem
  have hAΓ : Clo Γ A := clo_trans hcl hA
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg t Γ (.imp A B)) ⟨.impIn d hAΓ hgoal⟩
  match s', hsub with
  | .reg t' Γ' _, ⟨rfl, _, hΓ⟩ =>
      exact ⟨t', Γ', hs'mem, fun X hX => clo_mono hΓ (hcl X hX)⟩

/-- **(vi)** `A,Ψ ⇒g B` gives `Ψ ⇒g A⊃B`, also through `⊃∈`. -/
theorem gbuInv6 (hsat : WSaturated G D)
    {Ψ : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (h : WEvalR D (A :: Ψ) B) : WEvalR D Ψ (.imp A B) := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h
  obtain ⟨d⟩ := hsat.1 _ hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg t Γ (.imp A B)) ⟨.impIn d (hcl A List.mem_cons_self) hgoal⟩
  match s', hsub with
  | .reg t' Γ' _, ⟨rfl, _, hΓ⟩ =>
      exact ⟨t', Γ', hs'mem,
        fun X hX => clo_mono hΓ (hcl X (List.mem_cons_of_mem _ hX))⟩

/-- **(vii)** `Ω →g Cₖ` gives `Ω →g C₁∧C₂`. -/
theorem gbuInv7 (hsat : WSaturated G D)
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.and C₁ C₂ ∈ sfR G)
    (h : WEvalI D Ω C₁ ∨ WEvalI D Ω C₂) : WEvalI D Ω (.and C₁ C₂) := by
  have step : ∀ {C : Form}, WEvalI D Ω C →
      (∀ {St Th : List Form}, FRJWi G St Th C →
        FRJWi G St Th (.and C₁ C₂)) → WEvalI D Ω (.and C₁ C₂) := by
    rintro C ⟨St, Th, hmem, hSt, hΩ⟩ mk
    obtain ⟨d⟩ := hsat.1 _ hmem
    obtain ⟨s', hs'mem, hsub⟩ :=
      hsat.2 (.irr St Th (.and C₁ C₂)) ⟨mk d⟩
    match s', hsub with
    | .irr St' Th' _, ⟨rfl, hSteq, hTh⟩ =>
        refine ⟨St', Th', hs'mem, fun X hX => hSt ((hSteq X).mpr hX),
          fun X hX => ?_⟩
        rcases List.mem_append.mp (hΩ hX) with hX' | hX'
        · exact List.mem_append_left _ ((hSteq X).mp hX')
        · exact List.mem_append_right _ (hTh hX')
  rcases h with h | h
  · exact step h (fun d => .andI1 d hgoal)
  · exact step h (fun d => .andI2 d hgoal)

/-- **(viii)** `Ω →g B` with `A ∈ Cl(Ω)` gives `Ω →g A⊃B`, through
`⊃∈ᵢ`. -/
theorem gbuInv8 (hsat : WSaturated G D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ω A) (h : WEvalI D Ω B) : WEvalI D Ω (.imp A B) := by
  obtain ⟨St₀, Th₀, hmem, hSt₀, hΩ⟩ := h
  obtain ⟨d⟩ := hsat.1 _ hmem
  set Lam := Ω.filter (fun X => !(decide (X ∈ St₀))) with hLamdef
  set Th := Th₀.filter (fun X => !(decide (X ∈ Lam))) with hThdef
  have hLamΩ : ∀ X ∈ Lam, X ∈ Ω := fun X hX => (List.mem_filter.mp hX).1
  have hLamTh₀ : ∀ X ∈ Lam, X ∈ Th₀ := by
    intro X hX
    obtain ⟨hXΩ, hXnot⟩ := List.mem_filter.mp hX
    have := hΩ hXΩ
    rcases List.mem_append.mp this with h' | h'
    · exact absurd (by simp [h'] : (!(decide (X ∈ St₀))) = false) (by
        simp [hXnot])
    · exact h'
  have hΩsplit : ∀ X ∈ Ω, X ∈ St₀ ++ Lam := by
    intro X hX
    by_cases hs : X ∈ St₀
    · exact List.mem_append_left _ hs
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hX, by simp [hs]⟩)
  have hpre : Th₀ ≐ Th ++ Lam := by
    intro X
    constructor
    · intro hX
      by_cases hl : X ∈ Lam
      · exact List.mem_append_right _ hl
      · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hX, by simp [hl]⟩)
    · intro hX
      rcases List.mem_append.mp hX with hX' | hX'
      · exact (List.mem_filter.mp hX').1
      · exact hLamTh₀ X hX'
  have hdisj : cap Th Lam = [] := by
    refine eq_nil_of_forall_not_mem (fun X hX => ?_)
    obtain ⟨hXTh, hXLam⟩ := mem_cap.mp hX
    exact absurd (List.mem_filter.mp hXTh).2 (by simp [hXLam])
  have hAcl : Clo (St₀ ++ Lam) A := clo_trans (fun X hX => .base (hΩsplit X hX)) hA
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr (St₀ ++ Lam) Th (.imp A B))
      ⟨.impInI d hpre hdisj hAcl hgoal (CtxEq.refl _) (CtxEq.refl _)⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSteq, hTh'⟩ =>
      refine ⟨St', Th', hs'mem, fun X hX => ?_, fun X hX => ?_⟩
      · rcases List.mem_append.mp ((hSteq X).mpr hX) with h' | h'
        · exact hSt₀ h'
        · exact hLamΩ X h'
      · exact List.mem_append_left _ ((hSteq X).mp (hΩsplit X hX))

/-- **(ix), W-form** `A,Ω ⇒g B` gives `Ω →g A⊃B` — through `⊃∈` on the
regular witness followed by `Lift` at `Θ := Ω`.  STRONGER than the
V-lemma: the `¬ Clo Ω A` hypothesis of the deleted `⊃∉` is gone. -/
theorem gbuInv9 (hsat : WSaturated G D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (h : WEvalR D (A :: Ω) B) : WEvalI D Ω (.imp A B) := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h
  obtain ⟨d⟩ := hsat.1 _ hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] Ω (.imp A B))
      ⟨.lift (.impIn d (hcl A List.mem_cons_self) hgoal)
        (fun X hX => ⟨hcl X (List.mem_cons_of_mem _ hX), hΩ X hX⟩)⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSteq, hTh'⟩ =>
      refine ⟨St', Th', hs'mem, fun X hX => ?_, fun X hX => ?_⟩
      · exact absurd ((hSteq X).mpr hX) List.not_mem_nil
      · exact List.mem_append_right _ (hTh' hX)

/-- **(x)** `Ω →g Cₖ` for both `k` gives `Ω →g C₁∨C₂`, through the
`∨` join. -/
theorem gbuInv10 (hsat : WSaturated G D)
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (h₁ : WEvalI D Ω C₁) (h₂ : WEvalI D Ω C₂) : WEvalI D Ω (.or C₁ C₂) := by
  obtain ⟨St₁, Th₁, hmem₁, hSt₁, hΩ₁⟩ := h₁
  obtain ⟨St₂, Th₂, hmem₂, hSt₂, hΩ₂⟩ := h₂
  obtain ⟨d₁⟩ := hsat.1 _ hmem₁
  obtain ⟨d₂⟩ := hsat.1 _ hmem₂
  have hj₁ : St₁ ⊆ St₂ ++ Th₂ := fun {_} hX => hΩ₂ (hSt₁ hX)
  have hj₂ : St₂ ⊆ St₁ ++ Th₁ := fun {_} hX => hΩ₁ (hSt₂ hX)
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr (St₁ ++ St₂) (cap Th₁ Th₂) (.or C₁ C₂))
      ⟨.orI d₁ d₂ hj₁ hj₂ hgoal (CtxEq.refl _) (CtxEq.refl _)⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSteq, hTh'⟩ =>
      refine ⟨St', Th', hs'mem, fun X hX => ?_, fun X hX => ?_⟩
      · rcases List.mem_append.mp ((hSteq X).mpr hX) with h' | h'
        · exact hSt₁ h'
        · exact hSt₂ h'
      · by_cases hs : X ∈ St₁ ++ St₂
        · exact List.mem_append_left _ ((hSteq X).mp hs)
        · refine List.mem_append_right _ (hTh' (mem_cap.mpr ⟨?_, ?_⟩))
          · rcases List.mem_append.mp (hΩ₁ hX) with h' | h'
            · exact absurd (List.mem_append_left _ h') hs
            · exact h'
          · rcases List.mem_append.mp (hΩ₂ hX) with h' | h'
            · exact absurd (List.mem_append_right _ h') hs
            · exact h'

/-! ## The pledged-refutation layer, and Lemmas 11/12

`WRefutedCleanly` is `RefutedCleanly` over the W-family.  Under the
tag-aware (DB2) it coincides with the PLEDGED lookup `WEvalRP` — the
§10a′ obstruction ("the database forgets the tag") is gone, and the
`regC` stratum with it. -/

/-- An `FRJW` derivation of `Γ ⇒ C` whose tag `◯∈`/`◯∉` can lift, with
`Γ` covering `Ω`. -/
def WRefutedCleanly (G : Form) (Ω : List Form) (C : Form) : Prop :=
  ∃ (Γ : List Form) (t : Tag), Nonempty (FRJWr G t Γ C) ∧
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C) ∧ (∀ X ∈ Ω, Clo Γ X)

/-- A clean refutation reaches the database WITH its pledge: the
tag-aware (DB2) subsumes it by a row of at-least-equal claim, and
`pledge_of_le` carries the pledge across. -/
theorem wEvalRP_of_refutedCleanly (hsat : WSaturated G D)
    {Ω : List Form} {C : Form}
    (h : WRefutedCleanly G Ω C) : WEvalRP D Ω C := by
  obtain ⟨Γ, t, ⟨d⟩, htag, hcov⟩ := h
  obtain ⟨s', hs'mem, hsub⟩ := hsat.2 (.reg t Γ C) ⟨d⟩
  match s', hsub with
  | .reg t' Γ' _, ⟨rfl, hle, hΓ⟩ =>
      exact ⟨t', Γ', hs'mem, pledge_of_le hle hΓ htag,
        fun X hX => clo_mono hΓ (hcov X hX)⟩

/-- …and in particular plainly. -/
theorem wEvalR_of_refutedCleanly (hsat : WSaturated G D)
    {Ω : List Form} {C : Form}
    (h : WRefutedCleanly G Ω C) : WEvalR D Ω C :=
  wEvalR_of_wEvalRP (wEvalRP_of_refutedCleanly hsat h)

theorem refutedCleanly_mono {Ω Ω' : List Form} {C : Form}
    (h : Ω ⊆ Ω') (hr : WRefutedCleanly G Ω' C) : WRefutedCleanly G Ω C :=
  let ⟨Γ, t, d, htag, hcov⟩ := hr
  ⟨Γ, t, d, htag, fun X hX => hcov X (h hX)⟩

theorem refutedCleanly_clo {Ω Ω' : List Form} {C : Form}
    (h : ∀ X ∈ Ω, Clo Ω' X) (hr : WRefutedCleanly G Ω' C) :
    WRefutedCleanly G Ω C :=
  let ⟨Γ, t, d, htag, hcov⟩ := hr
  ⟨Γ, t, d, htag, fun X hX => clo_trans hcov (h X hX)⟩

/-- **Lemma 11, manufacture form** — a prime goal not in a critical
`Ω`, all of whose implication antecedents are `▷`-refuted, is refuted
cleanly: `Ax^R` if `Ω` has no implications, the `⋈^At` join over their
antecedents otherwise. -/
theorem refutedCleanly_at (hsat : WSaturated G D)
    {Ω : List Form} {F : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hFp : F.isPrime) (hFgoal : F ∈ sfR G) (hFmem : F ∉ Ω)
    (himp : ∀ A B, Form.imp A B ∈ Ω → WEvalI D Ω A) :
    WRefutedCleanly G Ω F := by
  by_cases hne : (impPart Ω).map ante = []
  · have hnoimp : ∀ X ∈ Ω, X.isImp = false := by
      intro X hX
      by_cases hi : X.isImp
      · have hmem : ante X ∈ (impPart Ω).map ante :=
          List.mem_map.mpr ⟨X, List.mem_filter.mpr ⟨hX, hi⟩, rfl⟩
        rw [hne] at hmem
        exact absurd hmem List.not_mem_nil
      · simpa using hi
    refine ⟨_, .barren, ⟨.axR F hFp hFgoal (CtxEq.refl _)⟩,
      Or.inl rfl, fun X hX => .base ((mem_rm.mpr ⟨?_, ?_⟩))⟩
    · exact fun hc => hFmem (hc ▸ hX)
    · exact mem_gAt_of_not_imp (hΩ X hX) (hnoimp X hX)
  · let E := enumOf ((impPart Ω).map ante) hne
    let f := E.f
    have hfmem : ∀ j, ∃ B, Form.imp (f j) B ∈ Ω := by
      intro j
      have : f j ∈ (impPart Ω).map ante :=
        (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
      obtain ⟨X, hXmem, hante⟩ := List.mem_map.mp this
      obtain ⟨hXΩ, hXi⟩ := List.mem_filter.mp hXmem
      match X, hXi with
      | .imp A B, _ =>
          refine ⟨B, ?_⟩
          have hA : A = f j := hante
          subst hA
          exact hXΩ
    have hwit : ∀ j, ∃ p : List Form × List Form,
        D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
      intro j
      obtain ⟨B, hB⟩ := hfmem j
      obtain ⟨St, Th, h₁, h₂, h₃⟩ := himp (f j) B hB
      exact ⟨(St, Th), h₁, h₂, h₃⟩
    obtain ⟨g, hg⟩ := finEx hwit
    set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
    set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
    have hStTh : ∀ j, D (.irr (St j) (Th j) (f j)) := fun j => (hg j).1
    have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
    have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
    have hder : ∀ j, Nonempty (FRJWi G (St j) (Th j) (f j)) :=
      fun j => hsat.1 _ (hStTh j)
    obtain ⟨d⟩ := finPi hder
    have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
      fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
    have hJ2 : ∀ A B : Form,
        Form.imp A B ∈ unionAll (fun j => impPart (St j)) → A ∈ upsilon f := by
      intro A B hmem
      obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
      have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
      exact (E.spec A).mpr
        (List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩)
    have hcirc : unionAll (fun j => circPart (St j)) = [] := by
      refine eq_nil_of_forall_not_mem (fun X hX => ?_)
      obtain ⟨j, hj⟩ := mem_unionAll.mp hX
      obtain ⟨hmem, hc⟩ := List.mem_filter.mp hj
      exact absurd hc (by
        rw [not_isCirc_of_gHatAtImp (hΩ X (hStΩ j hmem))]
        exact fun h => Bool.noConfusion h)
    have hFn : F ∉ unionAll (fun j => atPart (St j)) := by
      intro hX
      obtain ⟨j, hj⟩ := mem_unionAll.mp hX
      exact hFmem (hStΩ j (List.mem_filter.mp hj).1)
    refine ⟨_, .barren, ⟨.joinAt (fun j => d j) hJ1 hJ2 hcirc
          (keptChainRestrict _ Th) hFp hFn hFgoal (CtxEq.refl _)⟩,
      Or.inl rfl, fun X hX => .base (?_)⟩
    by_cases hin : ∃ j, X ∈ St j
    · obtain ⟨j, hj⟩ := hin
      refine List.mem_append_left _ ?_
      by_cases hi : X.isImp
      · exact List.mem_append_right _
          (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hi⟩⟩)
      · refine List.mem_append_left _ (List.mem_append_left _
          (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, ?_⟩⟩))
        have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
        exact (List.mem_filter.mp this).2
    · have hall : ∀ j, X ∈ Th j := by
        intro j
        rcases List.mem_append.mp (hΩSt j hX) with h' | h'
        · exact absurd ⟨j, h'⟩ hin
        · exact h'
      by_cases hi : X.isImp
      · refine List.mem_append_right _ ?_
        match X, hi with
        | .imp A B, _ =>
            refine mem_restrict.mpr ⟨?_, ?_⟩
            · exact List.mem_filter.mpr ⟨mem_interAll.mpr hall, rfl⟩
            · exact (E.spec A).mpr (List.mem_map.mpr
                ⟨.imp A B, List.mem_filter.mpr ⟨hX, rfl⟩, rfl⟩)
      · refine List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (mem_rm.mpr ⟨?_, ?_⟩)))
        · exact fun hc => hFmem (hc ▸ hX)
        · refine mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, ?_⟩)
          have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
          exact (List.mem_filter.mp this).2

/-- **Lemma 11 (`gbuSuccAt`), W-form.** -/
theorem gbuSuccAt (hsat : WSaturated G D)
    {Ω : List Form} {F : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hFp : F.isPrime) (hFgoal : F ∈ sfR G) (hFmem : F ∉ Ω)
    (himp : ∀ A B, Form.imp A B ∈ Ω → WEvalI D Ω A) :
    WEvalR D Ω F :=
  wEvalR_of_refutedCleanly hsat
    (refutedCleanly_at hsat hΩ hFp hFgoal hFmem himp)

/-- **Lemma 12, manufacture form** — `⋈^∨` over the disjuncts and the
implication antecedents. -/
theorem refutedCleanly_or (hsat : WSaturated G D)
    {Ω : List Form} {C₁ C₂ : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → WEvalI D Ω A)
    (h₁ : WEvalI D Ω C₁) (h₂ : WEvalI D Ω C₂) :
    WRefutedCleanly G Ω (.or C₁ C₂) := by
  let U := C₁ :: C₂ :: (impPart Ω).map ante
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : WEvalI D Ω (f j) := by
      by_cases e₁ : f j = C₁
      · exact e₁ ▸ h₁
      by_cases e₂ : f j = C₂
      · exact e₂ ▸ h₂
      have hm : f j ∈ (impPart Ω).map ante := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h e₁
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' e₂
          · exact h'
      obtain ⟨X, hXmem, hante⟩ := List.mem_map.mp hm
      obtain ⟨hXΩ, hXi⟩ := List.mem_filter.mp hXmem
      match X, hXi with
      | .imp A B, _ =>
          have hA : A = f j := hante
          exact hA ▸ himp A B hXΩ
    obtain ⟨St, Th, k₁, k₂, k₃⟩ := hev
    exact ⟨(St, Th), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (St j) (Th j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
  have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
    fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
  have hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (St j)) → A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩)))
  have hcirc : unionAll (fun j => circPart (St j)) = [] := by
    refine eq_nil_of_forall_not_mem (fun X hX => ?_)
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    obtain ⟨hmem, hc⟩ := List.mem_filter.mp hj
    exact absurd hc (by
      rw [not_isCirc_of_gHatAtImp (hΩ X (hStΩ j hmem))]
      exact fun h => Bool.noConfusion h)
  refine ⟨_, .barren, ⟨.joinOr (fun j => d j) hJ1 hJ2 hcirc (keptChainRestrict _ Th)
        ⟨.ups ((E.spec C₁).mpr List.mem_cons_self),
         .ups ((E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self))⟩
        hgoal (CtxEq.refl _)⟩,
    Or.inl rfl, fun X hX => .base (?_)⟩
  by_cases hin : ∃ j, X ∈ St j
  · obtain ⟨j, hj⟩ := hin
    refine List.mem_append_left _ ?_
    by_cases hi : X.isImp
    · exact List.mem_append_right _
        (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hi⟩⟩)
    · refine List.mem_append_left _ (List.mem_append_left _
        (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, ?_⟩⟩))
      have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
      exact (List.mem_filter.mp this).2
  · have hall : ∀ j, X ∈ Th j := by
      intro j
      rcases List.mem_append.mp (hΩSt j hX) with h' | h'
      · exact absurd ⟨j, h'⟩ hin
      · exact h'
    by_cases hi : X.isImp
    · refine List.mem_append_right _ ?_
      match X, hi with
      | .imp A B, _ =>
          refine mem_restrict.mpr ⟨?_, ?_⟩
          · exact List.mem_filter.mpr ⟨mem_interAll.mpr hall, rfl⟩
          · exact (E.spec A).mpr (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_map.mpr
                ⟨.imp A B, List.mem_filter.mpr ⟨hX, rfl⟩, rfl⟩)))
    · refine List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ ?_))
      refine mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, ?_⟩)
      have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
      exact (List.mem_filter.mp this).2

/-- **Lemma 12 (`gbuSuccOr`), W-form.** -/
theorem gbuSuccOr (hsat : WSaturated G D)
    {Ω : List Form} {C₁ C₂ : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → WEvalI D Ω A)
    (h₁ : WEvalI D Ω C₁) (h₂ : WEvalI D Ω C₂) :
    WEvalR D Ω (.or C₁ C₂) :=
  wEvalR_of_refutedCleanly hsat
    (refutedCleanly_or hsat hΩ hgoal himp h₁ h₂)


/-! ## Axiom pins -/

/-- info: 'FRJ.Gbu.W.gbuInv1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gbuInv1

/-- info: 'FRJ.Gbu.W.gbuInv2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv2

/-- info: 'FRJ.Gbu.W.gbuInv9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv9

/-- info: 'FRJ.Gbu.W.gbuInv10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv10

/-- info: 'FRJ.Gbu.W.pledge_of_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pledge_of_le

/-- info: 'FRJ.Gbu.W.wEvalRP_of_refutedCleanly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wEvalRP_of_refutedCleanly

/-- info: 'FRJ.Gbu.W.refutedCleanly_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_at

/-- info: 'FRJ.Gbu.W.refutedCleanly_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_or

/-- info: 'FRJ.Gbu.W.gbuSuccAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuSuccAt

/-- info: 'FRJ.Gbu.W.gbuSuccOr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuSuccOr


end FRJ.Gbu.W
