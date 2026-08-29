/-
# §4: saturated databases, and Lemma 9 — the bridge from `FRJ` to `Gbu`

Stage 3 of `docs/gbu-adoption-plan.md`, continuing `wip/gbu.lean`.
Source lines are `LaxLogic/papers/frj-corr-arxiv-1804.06689.tex`.

The three §4 notions (source 2660, 2827, 2830) and the EVALUATION
RELATION `▷` (source 3287), which is where the two calculi meet:

    D ▷ (Ψ ⇒g C)   iff  ∃ (Γ ⇒ C) ∈ D  with  Ψ ⊆ Cl(Γ)
    D ▷ (Ω →g C)   iff  ∃ (Σ ; Θ → C) ∈ D  with  Σ ⊆ Ω ⊆ Σ ∪ Θ

`▷` is a NEGATIVE fact about a `Gbu`-sequent: the database holds an
`FRJ` REFUTATION covering it.  Lemma 9's nine clauses say `▷` is closed
under the shape-moves `Search` makes, and each one is proved the same
way — take the witness, apply ONE `FRJ` rule, use (DB2) to find a member
subsuming the result, and transport the `Cl`-condition along the
subsumption.

**Divergence D6**: derivability is taken in the REPAIRED family
`FRJVr`/`FRJVi`, not the paper's `FRJr`/`FRJi`, with the tag
existentially quantified.  The paper's `FRJ(G)` is the IPC calculus and
carries no tag; `FRJV` is the calculus this campaign is actually about,
and Lemma 9's proofs use only rules the two families share.
-/
import wip.gbu
import FRJ.CalculusV

namespace FRJ.Gbu

open Form

/-! ## Sequents as data, and subsumption (source 2660) -/

/-- An `FRJ(G)`-sequent, as data. -/
inductive FSeq where
  | reg (Γ : List Form) (C : Form)
  | irr (St Th : List Form) (C : Form)

/-- `s₁ ⊑ s₂`: `s₂` subsumes `s₁` (source 2664–2669).  Regular sequents
compare by context inclusion at a common goal; irregular ones by the
`Θ`-zone alone, the `Σ`-zone being fixed. -/
def Subsumes : FSeq → FSeq → Prop
  | .reg Γ₁ C₁, .reg Γ₂ C₂ => C₁ = C₂ ∧ Γ₁ ⊆ Γ₂
  | .irr St₁ Th₁ C₁, .irr St₂ Th₂ C₂ => C₁ = C₂ ∧ St₁ ≐ St₂ ∧ Th₁ ⊆ Th₂
  | _, _ => False

/-- Derivability of a sequent in the repaired family (divergence D6). -/
def FDerivable (G : Form) : FSeq → Prop
  | .reg Γ C => ∃ t, Nonempty (FRJVr G t Γ C)
  | .irr St Th C => Nonempty (FRJVi G St Th C)

/-- **(DB1)** (source 2827): every member is derivable. -/
def IsDatabase (G : Form) (D : FSeq → Prop) : Prop :=
  ∀ s, D s → FDerivable G s

/-- **(DB2)** (source 2830): every derivable sequent is subsumed by a
member. -/
def Saturated (G : Form) (D : FSeq → Prop) : Prop :=
  IsDatabase G D ∧ ∀ s, FDerivable G s → ∃ s', D s' ∧ Subsumes s s'

/-! ## The evaluation relation `▷` (source 3287) -/

/-- `D ▷ (Ψ ⇒g C)`. -/
def EvalR (D : FSeq → Prop) (Ψ : List Form) (C : Form) : Prop :=
  ∃ Γ, D (.reg Γ C) ∧ ∀ X ∈ Ψ, Clo Γ X

/-- `D ▷ (Ω →g C)`. -/
def EvalI (D : FSeq → Prop) (Ω : List Form) (C : Form) : Prop :=
  ∃ St Th, D (.irr St Th C) ∧ St ⊆ Ω ∧ Ω ⊆ St ++ Th

/-! ## Lemma 9 (`lemma:gbuInv`, source 3828) — nine clauses

Clauses (i), (iii) and (iv) need no rule at all: they are `Clo`'s own
closure conditions, which is why the paper calls them inversions. -/

/-- **(i)** `A,B,Ψ ⇒g C` gives `A∧B,Ψ ⇒g C`. -/
theorem gbuInv1 {D : FSeq → Prop} {Ψ : List Form} {A B C : Form}
    (h : EvalR D (A :: B :: Ψ) C) : EvalR D (.and A B :: Ψ) C := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  refine ⟨Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .and (hcl A List.mem_cons_self)
      (hcl B (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact hcl X (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hX'))

/-- **(iii)** `Aₖ,Ψ ⇒g C` gives `A₁∨A₂,Ψ ⇒g C`. -/
theorem gbuInv3L {D : FSeq → Prop} {Ψ : List Form} {A₁ A₂ C : Form}
    (h : EvalR D (A₁ :: Ψ) C) : EvalR D (.or A₁ A₂ :: Ψ) C := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  refine ⟨Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .orL (hcl A₁ List.mem_cons_self)
  · exact hcl X (List.mem_cons_of_mem _ hX')

theorem gbuInv3R {D : FSeq → Prop} {Ψ : List Form} {A₁ A₂ C : Form}
    (h : EvalR D (A₂ :: Ψ) C) : EvalR D (.or A₁ A₂ :: Ψ) C := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  refine ⟨Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .orR (hcl A₂ List.mem_cons_self)
  · exact hcl X (List.mem_cons_of_mem _ hX')

/-- **(iv)** `B,Ψ ⇒g C` gives `A⊃B,Ψ ⇒g C`. -/
theorem gbuInv4 {D : FSeq → Prop} {Ψ : List Form} {A B C : Form}
    (h : EvalR D (B :: Ψ) C) : EvalR D (.imp A B :: Ψ) C := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  refine ⟨Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .imp (hcl B List.mem_cons_self)
  · exact hcl X (List.mem_cons_of_mem _ hX')

/-! The remaining clauses apply one `FRJ` rule and then (DB2). -/

/-- **(ii)** `Ψ ⇒g Cₖ` gives `Ψ ⇒g C₁∧C₂`. -/
theorem gbuInv2 {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ψ : List Form} {C₁ C₂ : Form} (hgoal : Form.and C₁ C₂ ∈ sfR G)
    (h : EvalR D Ψ C₁ ∨ EvalR D Ψ C₂) : EvalR D Ψ (.and C₁ C₂) := by
  have step : ∀ {C : Form}, EvalR D Ψ C →
      (∀ {t : Tag} {Γ : List Form}, FRJVr G t Γ C →
        FRJVr G t Γ (.and C₁ C₂)) → EvalR D Ψ (.and C₁ C₂) := by
    rintro C ⟨Γ, hmem, hcl⟩ mk
    obtain ⟨t, ⟨d⟩⟩ := hsat.1 _ hmem
    obtain ⟨s', hs'mem, hsub⟩ := hsat.2 (.reg Γ (.and C₁ C₂)) ⟨t, ⟨mk d⟩⟩
    match s', hsub with
    | .reg Γ' _, ⟨rfl, hΓ⟩ =>
        exact ⟨Γ', hs'mem, fun X hX => clo_mono hΓ (hcl X hX)⟩
  rcases h with h | h
  · exact step h (fun d => .andR1 d hgoal)
  · exact step h (fun d => .andR2 d hgoal)

/-- **(v)** and **(vi)**: `Ψ ⇒g B` with `A ∈ Cl(Ψ)`, and `A,Ψ ⇒g B`,
both give `Ψ ⇒g A⊃B`.  Both go through `⊃∈`, which needs only that `A`
lies in the closure of the witness context. -/
theorem gbuInv5 {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ψ : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ψ A) (h : EvalR D Ψ B) : EvalR D Ψ (.imp A B) := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  obtain ⟨t, ⟨d⟩⟩ := hsat.1 _ hmem
  have hAΓ : Clo Γ A := clo_trans hcl hA
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg Γ (.imp A B)) ⟨t, ⟨.impIn d hAΓ hgoal⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      exact ⟨Γ', hs'mem, fun X hX => clo_mono hΓ (hcl X hX)⟩

theorem gbuInv6 {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ψ : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (h : EvalR D (A :: Ψ) B) : EvalR D Ψ (.imp A B) := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  obtain ⟨t, ⟨d⟩⟩ := hsat.1 _ hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg Γ (.imp A B)) ⟨t, ⟨.impIn d (hcl A List.mem_cons_self) hgoal⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      exact ⟨Γ', hs'mem,
        fun X hX => clo_mono hΓ (hcl X (List.mem_cons_of_mem _ hX))⟩

/-- **(vii)** `Ω →g Cₖ` gives `Ω →g C₁∧C₂`. -/
theorem gbuInv7 {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.and C₁ C₂ ∈ sfR G)
    (h : EvalI D Ω C₁ ∨ EvalI D Ω C₂) : EvalI D Ω (.and C₁ C₂) := by
  have step : ∀ {C : Form}, EvalI D Ω C →
      (∀ {St Th : List Form}, FRJVi G St Th C →
        FRJVi G St Th (.and C₁ C₂)) → EvalI D Ω (.and C₁ C₂) := by
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
`⊃∉ᵢ`.  The rule splits the witness's `Θ`-zone into the part `Lam` that
`Ω` actually uses and the rest; `Lam` is exactly `Ω \ Σ`, which lands in
`Θ` because `Ω ⊆ Σ ∪ Θ`. -/
theorem gbuInv8 {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ω A) (h : EvalI D Ω B) : EvalI D Ω (.imp A B) := by
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

/-- **(ix)** `A,Ω ⇒g B` with `A ∉ Cl(Ω)` gives `Ω →g A⊃B`, through `⊃∉`
— the rule that turns a REGULAR premise into an irregular conclusion.
The paper's blanket `Ω ⊆ Γ̂` appears here as `hΩ`: the `Θ`-zone the rule
builds must lie in `Ĝ`. -/
theorem gbuInv9 {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (hAnot : ¬ Clo Ω A)
    (h : EvalR D (A :: Ω) B) : EvalI D Ω (.imp A B) := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  obtain ⟨t, ⟨d⟩⟩ := hsat.1 _ hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] Ω (.imp A B))
      ⟨.impNotIn d
        (fun X hX => ⟨hcl X (List.mem_cons_of_mem _ hX), hΩ X hX⟩)
        (hcl A List.mem_cons_self) hAnot hgoal⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSteq, hTh'⟩ =>
      refine ⟨St', Th', hs'mem, fun X hX => ?_, fun X hX => ?_⟩
      · exact absurd ((hSteq X).mpr hX) List.not_mem_nil
      · exact List.mem_append_right _ (hTh' hX)

/-! ## Axiom pins -/

/-- info: 'FRJ.Gbu.gbuInv1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gbuInv1

/-- info: 'FRJ.Gbu.gbuInv2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv2

/-- info: 'FRJ.Gbu.gbuInv5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv5

/-- info: 'FRJ.Gbu.gbuInv7' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv7

/-- info: 'FRJ.Gbu.gbuInv8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv8

/-- info: 'FRJ.Gbu.gbuInv9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv9

end FRJ.Gbu
