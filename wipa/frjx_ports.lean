/-
# FRJX — the port surface

`SaturatedOver (LiftClosure G) D` replaces `Saturated G D` throughout.  The
two helpers below are the whole of the difference: insertion is unchanged
because `FDerivable ⊆ LiftClosure`, and extraction AT A REGULAR ROW is
unchanged because `(Lift)` adds no regular rows (`liftClosure_reg`).
Extraction at an irregular row is the one place that genuinely differs, and
`liftClosure_irr` is where that is handled.
-/
import wipa.frjx_screen

namespace FRJ.Gbu.X

open FRJ FRJ.Gbu

/-- Insertion: unchanged, since every `FDerivable` row is a `LiftClosure`
row. -/
theorem satInsert {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D) (s : FSeq) (h : FDerivable G s) :
    ∃ s', D s' ∧ Subsumes s s' := hsat.2 s (.base h)

/-- Extraction at a regular row: unchanged, by `liftClosure_reg`. -/
theorem satExtractR {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D) {Γ : List Form} {C : Form}
    (h : D (.reg Γ C)) : ∃ t, Nonempty (FRJVr G t Γ C) :=
  liftClosure_reg (hsat.1 _ h)

/-- **(X5)** Extraction at an irregular row: EITHER an FRJV disproof as
before, OR a `(Lift)`ed regular one, in which case the regular disproof and
its `Ĝ`-context bound are available.  This is the one place the change of
base relation is visible, and it is what the nine remaining ports consume. -/
theorem satExtractI {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D) {St Th : List Form} {C : Form}
    (h : D (.irr St Th C)) :
    Nonempty (FRJVi G St Th C) ∨
      (St = [] ∧ ∃ Γ, (∃ t, Nonempty (FRJVr G t Γ C)) ∧
        ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G) := by
  cases hsat.1 _ h with
  | base hb => exact Or.inl hb
  | lift hreg hΘ => exact Or.inr ⟨rfl, _, liftClosure_reg hreg, hΘ⟩

/-- `LiftClosed`, as the ports consume it. -/
abbrev IsLiftClosed (G : Form) (D : FSeq → Prop) : Prop :=
  ∀ (Γ Θ : List Form) (C : Form), D (.reg Γ C) →
    (∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) → D (.irr [] Θ C)

/-- The uniform shape of every lifted case: rebuild the disproof on the
REGULAR side, insert it, and lift it again.  `mk` is the regular
constructor the lemma was using on the irregular side. -/
theorem relift {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D) (hlift : IsLiftClosed G D)
    {Γ Th : List Form} {C C' : Form}
    (hreg : ∃ t, Nonempty (FRJVr G t Γ C))
    (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G)
    (mk : ∀ {t : Tag}, FRJVr G t Γ C → FRJVr G t Γ C') :
    D (.irr [] Th C') := by
  obtain ⟨t, ⟨d⟩⟩ := hreg
  obtain ⟨s', hs'mem, hsub⟩ := satInsert hsat (.reg Γ C') ⟨t, ⟨mk d⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      exact hlift Γ' Th C' hs'mem
        (fun X hX => ⟨clo_mono hΓ (hTh X hX).1, (hTh X hX).2⟩)

/-- Port of `gbuInv2`. -/
theorem gbuInv2' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ψ : List Form} {C₁ C₂ : Form} (hgoal : Form.and C₁ C₂ ∈ sfR G)
    (h : EvalR D Ψ C₁ ∨ EvalR D Ψ C₂) : EvalR D Ψ (.and C₁ C₂) := by
  have step : ∀ {C : Form}, EvalR D Ψ C →
      (∀ {t : Tag} {Γ : List Form}, FRJVr G t Γ C →
        FRJVr G t Γ (.and C₁ C₂)) → EvalR D Ψ (.and C₁ C₂) := by
    rintro C ⟨Γ, hmem, hcl⟩ mk
    obtain ⟨t, ⟨d⟩⟩ := satExtractR hsat hmem
    obtain ⟨s', hs'mem, hsub⟩ := satInsert hsat (.reg Γ (.and C₁ C₂)) ⟨t, ⟨mk d⟩⟩
    match s', hsub with
    | .reg Γ' _, ⟨rfl, hΓ⟩ =>
        exact ⟨Γ', hs'mem, fun X hX => clo_mono hΓ (hcl X hX)⟩
  rcases h with h | h
  · exact step h (fun d => .andR1 d hgoal)
  · exact step h (fun d => .andR2 d hgoal)

/-- Port of `gbuInv5`. -/
theorem gbuInv5' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ψ : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ψ A) (h : EvalR D Ψ B) : EvalR D Ψ (.imp A B) := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  obtain ⟨t, ⟨d⟩⟩ := satExtractR hsat hmem
  have hAΓ : Clo Γ A := clo_trans hcl hA
  obtain ⟨s', hs'mem, hsub⟩ :=
    satInsert hsat (.reg Γ (.imp A B)) ⟨t, ⟨.impIn d hAΓ hgoal⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      exact ⟨Γ', hs'mem, fun X hX => clo_mono hΓ (hcl X hX)⟩

/-- Port of `gbuInv6`. -/
theorem gbuInv6' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ψ : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (h : EvalR D (A :: Ψ) B) : EvalR D Ψ (.imp A B) := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  obtain ⟨t, ⟨d⟩⟩ := satExtractR hsat hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    satInsert hsat (.reg Γ (.imp A B)) ⟨t, ⟨.impIn d (hcl A List.mem_cons_self) hgoal⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      exact ⟨Γ', hs'mem,
        fun X hX => clo_mono hΓ (hcl X (List.mem_cons_of_mem _ hX))⟩

/-- Port of `gbuInv7`. -/
theorem gbuInv7' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : IsLiftClosed G D)
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.and C₁ C₂ ∈ sfR G)
    (h : EvalI D Ω C₁ ∨ EvalI D Ω C₂) : EvalI D Ω (.and C₁ C₂) := by
  have step : ∀ {C : Form}, EvalI D Ω C →
      (∀ {St Th : List Form}, FRJVi G St Th C →
        FRJVi G St Th (.and C₁ C₂)) →
      (∀ {t : Tag} {Γ : List Form}, FRJVr G t Γ C → FRJVr G t Γ (.and C₁ C₂)) →
      EvalI D Ω (.and C₁ C₂) := by
    rintro C ⟨St, Th, hmem, hSt, hΩ⟩ mk mkR
    rcases satExtractI hsat hmem with hd | ⟨rfl, Γ, hreg, hTh⟩
    · obtain ⟨d⟩ := hd
      obtain ⟨s', hs'mem, hsub⟩ :=
        satInsert hsat (.irr St Th (.and C₁ C₂)) ⟨mk d⟩
      match s', hsub with
      | .irr St' Th' _, ⟨rfl, hSteq, hTh'⟩ =>
          refine ⟨St', Th', hs'mem, fun {x} hX => hSt ((hSteq x).mpr hX),
            fun {x} hX => ?_⟩
          rcases List.mem_append.mp (hΩ hX) with hX' | hX'
          · exact List.mem_append_left _ ((hSteq x).mp hX')
          · exact List.mem_append_right _ (hTh' hX')
    · exact ⟨[], Th, relift hsat hlift hreg hTh mkR,
        fun {x} hX => absurd hX List.not_mem_nil, hΩ⟩
  rcases h with h | h
  · exact step h (fun d => .andI1 d hgoal) (fun d => .andR1 d hgoal)
  · exact step h (fun d => .andI2 d hgoal) (fun d => .andR2 d hgoal)

/-- Port of `gbuInv8`.

**CLOSED.**  Two branches.  The `(Lift)`ed one is `relift` with the regular
`impIn`.  The `base` one uses the irregular implication rule `FRJVi.impInI`,
which moves a slice `Λ` of the premise's `Th` zone into the conclusion's
stoup:

    d : FRJVi G St (Th₁ ++ Λ) B    cap Th₁ Λ = []    Clo (St ++ Λ) A
    ─────────────────────────────────────────────────────────────────
                     FRJVi G (St ++ Λ) Th₁ (A ⊃ B)

Take `Λ := Th.filter (· ∈ Ω)`.  Then `Ω ⊆ St ++ Λ ⊆ Ω`, which is exactly
what `Clo (St ++ Λ) A` (from `Clo Ω A`, by `clo_mono`) and both zone
conditions of `EvalI` need. -/
theorem gbuInv8' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : IsLiftClosed G D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ω A) (h : EvalI D Ω B) : EvalI D Ω (.imp A B) := by
  obtain ⟨St, Th, hmem, hSt, hin⟩ := h
  rcases satExtractI hsat hmem with hd | ⟨rfl, Γ, hreg, hTh⟩
  · obtain ⟨d⟩ := hd
    -- The irregular `⊃`-rule moves a slice `Λ` of the premise's `Th` zone into
    -- the conclusion's stoup.  Take `Λ` to be exactly the part of `Th` that
    -- lies in `Ω`: then `St ++ Λ` is sandwiched, `Ω ⊆ St ++ Λ ⊆ Ω`, which is
    -- what both `Clo … A` and the two zone conditions need.
    have hmemΛ : ∀ x : Form,
        x ∈ Th.filter (fun y => decide (y ∈ Ω)) ↔ (x ∈ Th ∧ x ∈ Ω) := by
      intro x; simp [List.mem_filter]
    have hmemTh₁ : ∀ x : Form,
        x ∈ Th.filter (fun y => !decide (y ∈ Ω)) ↔ (x ∈ Th ∧ x ∉ Ω) := by
      intro x; simp [List.mem_filter]
    have hΩsub : Ω ⊆ St ++ Th.filter (fun y => decide (y ∈ Ω)) := by
      intro x hx
      rcases List.mem_append.mp (hin hx) with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ ((hmemΛ x).mpr ⟨h', hx⟩)
    have hsubΩ : St ++ Th.filter (fun y => decide (y ∈ Ω)) ⊆ Ω := by
      intro x hx
      rcases List.mem_append.mp hx with h' | h'
      · exact hSt h'
      · exact ((hmemΛ x).mp h').2
    have hAA : Clo (St ++ Th.filter (fun y => decide (y ∈ Ω))) A := clo_mono hΩsub hA
    have hpre : Th ≐ Th.filter (fun y => !decide (y ∈ Ω))
        ++ Th.filter (fun y => decide (y ∈ Ω)) := by
      intro x
      constructor
      · intro hx
        by_cases hxΩ : x ∈ Ω
        · exact List.mem_append_right _ ((hmemΛ x).mpr ⟨hx, hxΩ⟩)
        · exact List.mem_append_left _ ((hmemTh₁ x).mpr ⟨hx, hxΩ⟩)
      · intro hx
        rcases List.mem_append.mp hx with h' | h'
        · exact ((hmemTh₁ x).mp h').1
        · exact ((hmemΛ x).mp h').1
    have hdisj : cap (Th.filter (fun y => !decide (y ∈ Ω)))
        (Th.filter (fun y => decide (y ∈ Ω))) = [] := by
      simp [cap, List.mem_filter]
    have key : FRJVi G (St ++ Th.filter (fun y => decide (y ∈ Ω)))
        (Th.filter (fun y => !decide (y ∈ Ω))) (.imp A B) := by
      exact FRJVi.impInI d hpre hdisj hAA hgoal (CtxEq.refl _) (CtxEq.refl _)
    obtain ⟨s', hs'mem, hsub⟩ :=
      satInsert hsat (.irr (St ++ Th.filter (fun y => decide (y ∈ Ω)))
        (Th.filter (fun y => !decide (y ∈ Ω))) (.imp A B)) ⟨key⟩
    match s', hsub with
    | .irr St' Th' _, ⟨rfl, hSteq, hTh'⟩ =>
        exact ⟨St', Th', hs'mem, fun {x} hX => hsubΩ ((hSteq x).mpr hX),
          fun {x} hX => List.mem_append_left _ ((hSteq x).mp (hΩsub hX))⟩
  · have hΩTh : ∀ x ∈ Ω, x ∈ Th := by
      intro x hx
      rcases List.mem_append.mp (hin hx) with h' | h'
      · exact absurd h' List.not_mem_nil
      · exact h'
    have hAΓ : Clo Γ A := clo_trans (fun X hX => (hTh X (hΩTh X hX)).1) hA
    exact ⟨[], Th, relift hsat hlift hreg hTh (fun d => .impIn d hAΓ hgoal),
      fun {x} hX => absurd hX List.not_mem_nil, hin⟩

/-- Port of `gbuInv9`. -/
theorem gbuInv9' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (hAnot : ¬ Clo Ω A)
    (h : EvalR D (A :: Ω) B) : EvalI D Ω (.imp A B) := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  obtain ⟨t, ⟨d⟩⟩ := satExtractR hsat hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    satInsert hsat (.irr [] Ω (.imp A B))
      ⟨.impNotIn d
        (fun X hX => ⟨hcl X (List.mem_cons_of_mem _ hX), hΩ X hX⟩)
        (hcl A List.mem_cons_self) hAnot hgoal⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSteq, hTh'⟩ =>
      refine ⟨St', Th', hs'mem, fun X hX => ?_, fun X hX => ?_⟩
      · exact absurd ((hSteq X).mpr hX) List.not_mem_nil
      · exact List.mem_append_right _ (hTh' hX)

/-- Port of `gbuInv10`.

**PARTIAL — base/base branch CLOSED, the two `(Lift)`ed branches OPEN.**

The join is `FRJVi.orI`:

    d₁ : FRJVi G St₁ Th₁ C₁   d₂ : FRJVi G St₂ Th₂ C₂
    St₁ ⊆ St₂ ++ Th₂          St₂ ⊆ St₁ ++ Th₁
    ──────────────────────────────────────────────────
        FRJVi G (St₁ ++ St₂) (cap Th₁ Th₂) (C₁ ∨ C₂)

and both side conditions follow from `Stᵢ ⊆ Ω ⊆ Stⱼ ++ Thⱼ`.

The remaining two branches are the ones where at least one premise row is a
`(Lift)`ed one, so only a REGULAR disproof over some `Γᵢ` is available and
no `FRJVi` term is.  There is no route from the material to hand: joining
needs two irregular premises, `(Lift)` needs a regular row for the
CONCLUSION `C₁ ∨ C₂`, and the two regular premises live over different
contexts `Γ₁ ≠ Γ₂`, so `relift` has no single `Γ` to rebuild over.  This may
be a defect of the statement rather than of the proof; it is recorded as
OPEN, not refuted — no countermodel was constructed.  Residual goal in both
branches: `⊢ EvalI D Ω (C₁.or C₂)`. -/
theorem gbuInv10' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : IsLiftClosed G D)
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (h₁ : EvalI D Ω C₁) (h₂ : EvalI D Ω C₂) : EvalI D Ω (.or C₁ C₂) := by
  obtain ⟨St₁, Th₁, hmem₁, hSt₁, hin₁⟩ := h₁
  obtain ⟨St₂, Th₂, hmem₂, hSt₂, hin₂⟩ := h₂
  rcases satExtractI hsat hmem₁ with hd₁ | hL₁
  · rcases satExtractI hsat hmem₂ with hd₂ | hL₂
    · obtain ⟨d₁⟩ := hd₁
      obtain ⟨d₂⟩ := hd₂
      have hmemcap : ∀ x : Form, x ∈ cap Th₁ Th₂ ↔ (x ∈ Th₁ ∧ x ∈ Th₂) := by
        intro x; simp [cap, List.mem_filter]
      have hj₁ : St₁ ⊆ St₂ ++ Th₂ := by intro x hx; exact hin₂ (hSt₁ hx)
      have hj₂ : St₂ ⊆ St₁ ++ Th₁ := by intro x hx; exact hin₁ (hSt₂ hx)
      have key : FRJVi G (St₁ ++ St₂) (cap Th₁ Th₂) (.or C₁ C₂) := by
        first
          | exact FRJVi.orI d₁ d₂ hj₁ hj₂ hgoal (CtxEq.refl _) (CtxEq.refl _)
          | exact FRJVi.orIJ d₁ d₂ hj₁ hj₂ hgoal (CtxEq.refl _) (CtxEq.refl _)
          | exact FRJVi.orJoin d₁ d₂ hj₁ hj₂ hgoal (CtxEq.refl _) (CtxEq.refl _)
          | exact FRJVi.orIn d₁ d₂ hj₁ hj₂ hgoal (CtxEq.refl _) (CtxEq.refl _)
          | exact FRJVi.orBoth d₁ d₂ hj₁ hj₂ hgoal (CtxEq.refl _) (CtxEq.refl _)
      obtain ⟨s', hs'mem, hsub⟩ :=
        satInsert hsat (.irr (St₁ ++ St₂) (cap Th₁ Th₂) (.or C₁ C₂)) ⟨key⟩
      match s', hsub with
      | .irr St' Th' _, ⟨rfl, hSteq, hTh'⟩ =>
          refine ⟨St', Th', hs'mem, ?_, ?_⟩
          · intro x hx
            rcases List.mem_append.mp ((hSteq x).mpr hx) with h' | h'
            · exact hSt₁ h'
            · exact hSt₂ h'
          · intro x hx
            by_cases hx1 : x ∈ St₁
            · exact List.mem_append_left _ ((hSteq x).mp (List.mem_append_left _ hx1))
            · by_cases hx2 : x ∈ St₂
              · exact List.mem_append_left _ ((hSteq x).mp (List.mem_append_right _ hx2))
              · have e1 : x ∈ Th₁ := (List.mem_append.mp (hin₁ hx)).resolve_left hx1
                have e2 : x ∈ Th₂ := (List.mem_append.mp (hin₂ hx)).resolve_left hx2
                exact List.mem_append_right _ (hTh' ((hmemcap x).mpr ⟨e1, e2⟩))
    · sorry
  · sorry

/-- Port of `refutedCleanly_at`.

**OPEN.**  `refine ⟨?_, ?_, ?_, ?_, ?_⟩` exposes the target as

    ∃ Γ t, Nonempty (FRJVr G t Γ F)
         ∧ (t = Tag.barren ∨ ∃ W, t = Tag.chain W ∧ Covers Γ W F)
         ∧ ∀ X ∈ Ω, Clo Γ X

`axR` forces `Γ ≐ rm (gAt G) F`, and then the last component fails for the
IMPLICATIONS of `Ω`: `Clo` (constructors visible here: `base`, `imp` with
`Clo Γ B → Clo Γ (A ⊃ B)`) cannot reach `A ⊃ B ∈ gImp G` from
`rm (gAt G) F`.  The real construction must join the `himp` witnesses into
`Γ`, and that join is not nameable from this file set. -/
theorem refutedCleanly_at' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : IsLiftClosed G D)
    {Ω : List Form} {F : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hFp : F.isPrime) (hFgoal : F ∈ sfR G) (hFmem : F ∉ Ω)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A) :
    RefutedCleanly G Ω F := by
  sorry

/-- Port of `refutedCleanly_or`.

**OPEN.**  Same target shape as `refutedCleanly_at'` at the goal `C₁ ∨ C₂`;
needs both the `∨`-join of `gbuInv10'` and the `himp` join of
`refutedCleanly_at'`. -/
theorem refutedCleanly_or' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : IsLiftClosed G D)
    {Ω : List Form} {C₁ C₂ : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (h₁ : EvalI D Ω C₁) (h₂ : EvalI D Ω C₂) :
    RefutedCleanly G Ω (.or C₁ C₂) := by
  sorry

/-- Port of `evalR_of_refutedCleanly`. -/
theorem evalR_of_refutedCleanly' {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D) {Ω : List Form} {C : Form}
    (h : RefutedCleanly G Ω C) : EvalR D Ω C := by
  obtain ⟨Γ, t, ⟨d⟩, _, hcov⟩ := h
  obtain ⟨s', hs'mem, hsub⟩ := satInsert hsat (.reg Γ C) ⟨t, ⟨d⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      exact ⟨Γ', hs'mem, fun X hX => clo_mono hΓ (hcov X hX)⟩

/-- Port of `evalI_axI`. -/
theorem evalI_axI' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {F : Form} (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hFp : F.isPrime = true) (hF : F ∈ sfR G) (hFn : F ∉ Ω) : EvalI D Ω F := by
  obtain ⟨s', hs'mem, hsub⟩ :=
    satInsert hsat (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F)
      ⟨.axI F hFp hF (CtxEq.refl _)⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSt, hTh⟩ =>
      refine ⟨St', Th', hs'mem, fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil, ?_⟩
      intro x hx
      refine List.mem_append_right _ (hTh ?_)
      rcases List.mem_append.mp (hΩ x hx) with h | h
      · refine List.mem_append_left _ (List.mem_append_left _ (mem_rm.mpr ⟨?_, h⟩))
        intro he
        exact hFn (he ▸ hx)
      · exact List.mem_append_left _ (List.mem_append_right _ h)

/-- Port of `refutedCleanly_circ`.

**OPEN.**  Target (from `refine ⟨?_, ?_, ?_, ?_, ?_⟩`):

    ∃ Γ t, Nonempty (FRJVr G t Γ (◯Z))
         ∧ (t = Tag.barren ∨ ∃ W, t = Tag.chain W ∧ Covers Γ W (◯Z))
         ∧ ∀ X ∈ Ω, Clo Γ X

The only `◯`-introduction visible in this file set is the REGULAR
`FRJVr.circIn`, whose premise is a cleanly-tagged REGULAR disproof of `Z`;
the hypothesis here is the IRREGULAR `hz : EvalI D Ω Z`.  The rule that
takes an irregular premise to a regular `◯`-conclusion is not nameable from
this file set. -/
theorem refutedCleanly_circ' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : IsLiftClosed G D)
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (hz : EvalI D Ω Z) :
    RefutedCleanly G Ω (.circ Z) := by
  sorry

/-- Port of `gbuSuccCirc`.

**COMPLETE RELATIVE TO `refutedCleanly_circ'`** — no new content: it is
`evalR_of_refutedCleanly'` applied to it.  It therefore inherits that
lemma's `sorry` and is NOT closed. -/
theorem gbuSuccCirc' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : IsLiftClosed G D)
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (hz : EvalI D Ω Z) :
    EvalR D Ω (.circ Z) :=
  evalR_of_refutedCleanly' hsat (refutedCleanly_circ' hsat hlift hΩ hgoal himp hz)

/-- Port of `unrefutedBelow_of_gHat`. -/
theorem unrefutedBelow_of_gHat' {G : Form} {D : FSeq → Prop} {Ω : List Form}
    {C : Form} (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (h : ¬ EvalI D Ω C) :
    UnrefutedBelow G D Ω C :=
  ⟨h, Ω, hΩ, fun X hX => .base hX, h⟩

/-- Port of `gbuInv14`.

**PARTIAL.**  The `(Lift)`ed branch is complete: the lifted row hands back a
regular disproof over `Γ` with `Ω' ⊆ Cl(Γ)`, so `Ω ⊆ Cl(Ω') ⊆ Cl(Γ)` by
`clo_trans` and `relift` (with `mk := id`) re-lifts it at `Θ := Ω`.  The
`base` branch is OPEN: from `d : FRJVi G St Th (◯Z)` with `St ⊆ Ω'` and
`Ω' ⊆ St ++ Th` one must produce an irregular row whose stoup is inside `Ω`,
and the zone-changing lemma for `◯`-goals is not nameable from this file
set.  Residual goal: `⊢ EvalI D Ω Z.circ`.

(Moved ahead of `unrefutedBelow_step'`, which uses it; no statement
changed.) -/
theorem gbuInv14' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : IsLiftClosed G D)
    {Ω Ω' : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (hcl : ∀ X ∈ Ω, Clo Ω' X)
    (h : EvalI D Ω' (.circ Z)) : EvalI D Ω (.circ Z) := by
  obtain ⟨St, Th, hmem, hSt, hin⟩ := h
  rcases satExtractI hsat hmem with hd | ⟨rfl, Γ, hreg, hTh⟩
  · sorry
  · have hΩTh : ∀ x ∈ Ω', x ∈ Th := by
      intro x hx
      rcases List.mem_append.mp (hin hx) with h' | h'
      · exact absurd h' List.not_mem_nil
      · exact h'
    have hcloΓ : ∀ X ∈ Ω, Clo Γ X :=
      fun X hX => clo_trans (fun Y hY => (hTh Y (hΩTh Y hY)).1) (hcl X hX)
    exact ⟨[], Ω,
      relift hsat hlift hreg (fun X hX => ⟨hcloΓ X hX, hΩ X hX⟩) (fun d => d),
      fun {x} hx => absurd hx List.not_mem_nil,
      fun {x} hx => List.mem_append_right _ hx⟩

/-- Port of `unrefutedBelow_step`.

**COMPLETE RELATIVE TO `gbuInv14'`** — the proof below is finished; it
inherits that lemma's `sorry` and is therefore NOT closed. -/
theorem unrefutedBelow_step' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : IsLiftClosed G D)
    {Ω Ω' : List Form} {Z : Form} (hcl : ∀ X ∈ Ω, Clo Ω' X)
    (h : UnrefutedBelow G D Ω (.circ Z)) : UnrefutedBelow G D Ω' (.circ Z) := by
  obtain ⟨hne, Ω₀, hhat, hcl₀, hne₀⟩ := h
  have hcl₀' : ∀ X ∈ Ω₀, Clo Ω' X := fun X hX => clo_trans hcl (hcl₀ X hX)
  refine ⟨?_, Ω₀, hhat, hcl₀', hne₀⟩
  intro hE
  exact hne₀ (gbuInv14' hsat hlift hhat hcl₀' hE)


/-- info: 'FRJ.Gbu.X.gbuInv8'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv8'
