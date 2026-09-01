/-
# FRJX — the port surface

`SaturatedOver (LiftClosure G) D` replaces `Saturated G D` throughout.  The
two helpers below are the whole of the difference: insertion is unchanged
because `FDerivable ⊆ LiftClosure`, and extraction AT A REGULAR ROW is
unchanged because `(Lift)` adds no regular rows (`liftClosure_reg`).
Extraction at an irregular row is the one place that genuinely differs, and
`liftClosure_irr` is where that is handled.
-/
import wip.frjx_screen

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
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.and C₁ C₂ ∈ sfR G)
    (h : EvalI D Ω C₁ ∨ EvalI D Ω C₂) : EvalI D Ω (.and C₁ C₂) := by
  sorry

/-- Port of `gbuInv8`. -/
theorem gbuInv8' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ω A) (h : EvalI D Ω B) : EvalI D Ω (.imp A B) := by
  sorry

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

/-- Port of `gbuInv10`. -/
theorem gbuInv10' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (h₁ : EvalI D Ω C₁) (h₂ : EvalI D Ω C₂) : EvalI D Ω (.or C₁ C₂) := by
  sorry

/-- Port of `refutedCleanly_at`. -/
theorem refutedCleanly_at' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {F : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hFp : F.isPrime) (hFgoal : F ∈ sfR G) (hFmem : F ∉ Ω)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A) :
    RefutedCleanly G Ω F := by
  sorry

/-- Port of `refutedCleanly_or`. -/
theorem refutedCleanly_or' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
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

/-- Port of `refutedCleanly_circ`. -/
theorem refutedCleanly_circ' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (hz : EvalI D Ω Z) :
    RefutedCleanly G Ω (.circ Z) := by
  sorry

/-- Port of `gbuSuccCirc`. -/
theorem gbuSuccCirc' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (hz : EvalI D Ω Z) :
    EvalR D Ω (.circ Z) := by
  sorry

/-- Port of `unrefutedBelow_of_gHat`. -/
theorem unrefutedBelow_of_gHat' {G : Form} {D : FSeq → Prop} {Ω : List Form}
    {C : Form} (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (h : ¬ EvalI D Ω C) :
    UnrefutedBelow G D Ω C :=
  ⟨h, Ω, hΩ, fun X hX => .base hX, h⟩

/-- Port of `unrefutedBelow_step`. -/
theorem unrefutedBelow_step' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ω Ω' : List Form} {Z : Form} (hcl : ∀ X ∈ Ω, Clo Ω' X)
    (h : UnrefutedBelow G D Ω (.circ Z)) : UnrefutedBelow G D Ω' (.circ Z) := by
  sorry

/-- Port of `gbuInv14`. -/
theorem gbuInv14' {G : Form} {D : FSeq → Prop} (hsat : SaturatedOver (LiftClosure G) D)
    {Ω Ω' : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (hcl : ∀ X ∈ Ω, Clo Ω' X)
    (h : EvalI D Ω' (.circ Z)) : EvalI D Ω (.circ Z) := by
  sorry
