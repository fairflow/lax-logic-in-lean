/-
# The W-database lemma layer — Lemma 9/11/12 over `WSeq`

The `FRJ/Gbu/DB.lean` layer (F&F Lemmas 9–12) transcribed to the
W-database of `FRJ/Gbu/W/Dichotomy.lean`.  Family-independent
helpers (`finPi`, `finEx`, `keptChainRestrict`, the `Ĝ`-zone facts and
the `enumOf` machinery) are imported from `FRJ/Gbu/DB.lean`, not
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
import FRJ.Gbu.W.Dichotomy
import FRJ.Gbu.DB

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

/-! ## The two irregular database adapters, and the FRJW rule instances

`FRJ.Gbu.irr_of_evalI` / `evalI_of_irr` over `WSeq`: (DB1) turns a
looked-up irregular row into a derivation and (DB2) admits a new one,
repairing the zones of the subsuming row.  Below them, the four
constructor fields the calculus-free cores of `FRJ/Gbu/DB.lean` take as
hypotheses.  `⋈^◯` is the one field that is not alpha-equal across the
families — FRJW's (J2) is the `RefAt`-relaxed
`RefAt true Υ (joinCtxOrVBase Ξs Θs ++ kept) A`, FRJV's the strict
`A ∈ Υ` — and the instance below is where the `RefAt.ups` adapter sits,
the same one the manufacture call site carried before the hoist. -/

/-- (DB1) at an irregular row, W-form. -/
theorem irr_of_evalI (hsat : WSaturated G D) {Ω : List Form} {C : Form}
    (h : WEvalI D Ω C) :
    ∃ Ξ Θ, Nonempty (FRJWi G Ξ Θ C) ∧ Ξ ⊆ Ω ∧ Ω ⊆ Ξ ++ Θ :=
  let ⟨Ξ, Θ, hmem, h₁, h₂⟩ := h
  ⟨Ξ, Θ, hsat.1 _ hmem, h₁, h₂⟩

/-- (DB2) at an irregular row, W-form. -/
theorem evalI_of_irr (hsat : WSaturated G D) {Ω Ξ Θ : List Form} {C : Form}
    (d : Nonempty (FRJWi G Ξ Θ C)) (hΞ : Ξ ⊆ Ω) (hΩ : Ω ⊆ Ξ ++ Θ) :
    WEvalI D Ω C := by
  obtain ⟨s', hs'mem, hsub⟩ := hsat.2 (.irr Ξ Θ C) d
  match s', hsub with
  | .irr Ξ' Θ' _, ⟨rfl, hΞeq, hΘ⟩ =>
      refine ⟨Ξ', Θ', hs'mem, fun X hX => hΞ ((hΞeq X).mpr hX), fun X hX => ?_⟩
      rcases List.mem_append.mp (hΩ hX) with h' | h'
      · exact List.mem_append_left _ ((hΞeq X).mp h')
      · exact List.mem_append_right _ (hΘ h')

def axRRuleW : AxRRule FRJWr := @fun _ F hF hg _ hΓ => FRJWr.axR F hF hg hΓ

def atRuleW : AtRule FRJWi FRJWr :=
  @fun _ _ _ _ _ _ _ p a b c d e f g _ h => FRJWr.joinAt p a b c d e f g h

def orRuleW : OrRule FRJWi FRJWr :=
  @fun _ _ _ _ _ _ _ _ p a b c d e f _ h => FRJWr.joinOr p a b c d e f h

/-- FRJW's `⋈^◯` asks only the `RefAt`-relaxed (J2), so the strict
premise of `CircRule` is weakened here by `RefAt.ups`. -/
def circRuleW : CircRule FRJWi FRJWr :=
  @fun _ _ _ _ _ _ _ p a b c d e f _ h =>
    FRJWr.joinCirc p a (fun A B hm => .ups (b A B hm)) c d e f h

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
  rcases h with h | h
  · obtain ⟨Ξ, Θ, ⟨d⟩, hΞ, hΩ⟩ := irr_of_evalI hsat h
    exact evalI_of_irr hsat ⟨.andI1 d hgoal⟩ hΞ hΩ
  · obtain ⟨Ξ, Θ, ⟨d⟩, hΞ, hΩ⟩ := irr_of_evalI hsat h
    exact evalI_of_irr hsat ⟨.andI2 d hgoal⟩ hΞ hΩ

/-- **(viii)** `Ω →g B` with `A ∈ Cl(Ω)` gives `Ω →g A⊃B`, through
`⊃∈ᵢ`. -/
theorem gbuInv8 (hsat : WSaturated G D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ω A) (h : WEvalI D Ω B) : WEvalI D Ω (.imp A B) := by
  obtain ⟨Ξ₀, Θ₀, ⟨d⟩, hΞ₀, hΩ⟩ := irr_of_evalI hsat h
  obtain ⟨Λ, Θ, hpre, hdisj, hΞΛ, hsplit⟩ := impZoneSplit hΞ₀ hΩ
  have hcl : ∀ X ∈ Ω, Clo (Ξ₀ ++ Λ) X := fun _ hX => .base (hsplit hX)
  exact evalI_of_irr hsat
    ⟨.impInI d hpre hdisj (clo_trans hcl hA) hgoal
      (CtxEq.refl _) (CtxEq.refl _)⟩
    hΞΛ (fun {_} hX => List.mem_append_left _ (hsplit hX))

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
  | .irr Ξ' Θ' _, ⟨rfl, hSteq, hTh'⟩ =>
      refine ⟨Ξ', Θ', hs'mem, fun X hX => ?_, fun X hX => ?_⟩
      · exact absurd ((hSteq X).mpr hX) List.not_mem_nil
      · exact List.mem_append_right _ (hTh' hX)

/-- **(x)** `Ω →g Cₖ` for both `k` gives `Ω →g C₁∨C₂`, through the
`∨` join. -/
theorem gbuInv10 (hsat : WSaturated G D)
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (h₁ : WEvalI D Ω C₁) (h₂ : WEvalI D Ω C₂) : WEvalI D Ω (.or C₁ C₂) := by
  obtain ⟨Ξ₁, Θ₁, ⟨d₁⟩, hΞ₁, hΩ₁⟩ := irr_of_evalI hsat h₁
  obtain ⟨Ξ₂, Θ₂, ⟨d₂⟩, hΞ₂, hΩ₂⟩ := irr_of_evalI hsat h₂
  obtain ⟨hj₁, hj₂, hΞ, hΩ⟩ := orZoneMerge hΞ₁ hΩ₁ hΞ₂ hΩ₂
  exact evalI_of_irr hsat
    ⟨.orI d₁ d₂ hj₁ hj₂ hgoal (CtxEq.refl _) (CtxEq.refl _)⟩ hΞ hΩ

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
    WRefutedCleanly G Ω F :=
  let ⟨Γ, d, hcov⟩ := refutedCleanly_at_core axRRuleW atRuleW hΩ hFp hFgoal hFmem
    (fun A B h => irr_of_evalI hsat (himp A B h))
  ⟨Γ, .barren, d, Or.inl rfl, hcov⟩

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
    WRefutedCleanly G Ω (.or C₁ C₂) :=
  let ⟨Γ, d, hcov⟩ := refutedCleanly_or_core orRuleW hΩ hgoal
    (fun A B h => irr_of_evalI hsat (himp A B h))
    (irr_of_evalI hsat h₁) (irr_of_evalI hsat h₂)
  ⟨Γ, .barren, d, Or.inl rfl, hcov⟩

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

/-- info: 'FRJ.Gbu.W.gbuInv2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gbuInv2

/-- info: 'FRJ.Gbu.W.gbuInv9' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gbuInv9

/-- info: 'FRJ.Gbu.W.gbuInv10' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gbuInv10

/-- info: 'FRJ.Gbu.W.pledge_of_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pledge_of_le

/-- info: 'FRJ.Gbu.W.wEvalRP_of_refutedCleanly' depends on axioms: [propext] -/
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
