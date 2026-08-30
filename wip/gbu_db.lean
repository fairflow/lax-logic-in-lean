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
import FRJ.Minimal

namespace FRJ.Gbu

open Form

/-! ## Sequents as data, and subsumption (source 2660) -/

/-- An `FRJ(G)`-sequent, as data. -/
inductive FSeq where
  | reg (Γ : List Form) (C : Form)
  /-- the CLEAN regular stratum (divergence D9): a row whose derivation
  carries a tag `◯∈`/`◯∉` can lift.  A SEPARATE clause, not a flag on
  `reg`, because tag-preserving weakening is refuted
  (`tag_weakening_refuted`): `[] ⇒ p` is barren, `[◯p] ⇒ p` is derivable
  only at `blocked`, and `[] ⊆ [◯p]`.  So cleanliness is not inherited
  along subsumption and the clean rows must be kept in their own
  stratum, subsumed only by clean rows. -/
  | regC (Γ : List Form) (C : Form)
  | irr (St Th : List Form) (C : Form)

/-- `s₁ ⊑ s₂`: `s₂` subsumes `s₁` (source 2664–2669).  Regular sequents
compare by context inclusion at a common goal; irregular ones by the
`Θ`-zone alone, the `Σ`-zone being fixed. -/
def Subsumes : FSeq → FSeq → Prop
  | .reg Γ₁ C₁, .reg Γ₂ C₂ => C₁ = C₂ ∧ Γ₁ ⊆ Γ₂
  | .regC Γ₁ C₁, .regC Γ₂ C₂ => C₁ = C₂ ∧ Γ₁ ⊆ Γ₂
  | .irr St₁ Th₁ C₁, .irr St₂ Th₂ C₂ => C₁ = C₂ ∧ St₁ ≐ St₂ ∧ Th₁ ⊆ Th₂
  | _, _ => False

/-- Derivability of a sequent in the repaired family (divergence D6). -/
def FDerivable (G : Form) : FSeq → Prop
  | .reg Γ C => ∃ t, Nonempty (FRJVr G t Γ C)
  | .regC Γ C => ∃ t, Nonempty (FRJVr G t Γ C) ∧
      (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C)
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

/-- `D ▷ᶜ (Ψ ⇒g C)` — the CLEAN regular lookup.  Same shape as `EvalR`,
one stratum down. -/
def EvalRC (D : FSeq → Prop) (Ψ : List Form) (C : Form) : Prop :=
  ∃ Γ, D (.regC Γ C) ∧ ∀ X ∈ Ψ, Clo Γ X

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

/-! ## Lemma 10 (`lemma:gbuiOr`, source 4057)

The `∨`-closure of `▷` on the focused judgment.  `▷` is a REFUTATION
fact, so a disjunction needs BOTH disjuncts — this is FRJ's `∨` join,
whose two side conditions `Σ₁ ⊆ Σ₂ ∪ Θ₂` and `Σ₂ ⊆ Σ₁ ∪ Θ₁` come free
from `Σₖ ⊆ Ω ⊆ Σₖ ∪ Θₖ`. -/

theorem gbuInv10 {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (h₁ : EvalI D Ω C₁) (h₂ : EvalI D Ω C₂) : EvalI D Ω (.or C₁ C₂) := by
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

/-! ## Lemma 11 (`lemma:gbuSuccAt`, source 4118) — the prime success lemma

The first place `▷` is ESTABLISHED rather than propagated: under
saturation, a prime goal `F` not in `Ω`, all of whose left implications
have `▷`-refuted antecedents, is itself `▷`-refuted.  The paper's proof
splits on whether `Ω` has implications: none, and the `Ax^R` cell does
it; some, and the `⋈^At` JOIN over their antecedents does.

Note what does NOT appear: any `◯`-freeness hypothesis.  `Ω ⊆ Γ̂` and
`Γ̂ = Ĝ_at ∪ Ĝ_imp` already exclude top-level `◯`, so the V-join's
`hcirc` side condition is discharged from the paper's own hypothesis.
The `◯`-extension's obligation therefore does not sit here. -/

/-- Finite choice over `Fin (n+1)`: needed to turn the database's
`Nonempty` derivations into the join's premise FAMILY, and provable by
induction because the index type is finite — `Classical.choice` is not
required and must not be used. -/
theorem finPi : ∀ {n : Nat} {X : Fin (n + 1) → Type},
    (∀ j, Nonempty (X j)) → Nonempty (∀ j, X j)
  | 0, X, h =>
      (h 0).elim (fun x0 => ⟨fun j => Fin.cases x0 (fun i => i.elim0) j⟩)
  | _ + 1, X, h =>
      (h 0).elim (fun x0 =>
        (finPi (X := fun j => X j.succ) (fun j => h j.succ)).elim
          (fun xs => ⟨fun j => Fin.cases x0 xs j⟩))

/-- The paper's `Θ^⊃∩` retention zone as a `KeptChain` certificate.
Inlined from `wip/minmodv.lean`'s `keptChain_restrict` so that this
development does not depend on the `minmodv` campaign. -/
theorem keptChainRestrict {n : Nat} {rhs : Fin (n + 1) → Form}
    (base : List Form) (th : Fin (n + 1) → List Form) :
    KeptChain (upsilon rhs) base (thPool th)
      (restrict (thPool th) (upsilon rhs)) :=
  keptChain_of_ups (fun _ hX => restrict_subset hX)
    (fun h => (mem_restrict.mp h).2)
    (fun _ hX => (List.mem_filter.mp (restrict_subset hX)).2)

/-- Finite choice for existentials, the `∃`-form of `finPi`.  `choose`
would do this but pulls `Classical.choice`; over a finite index type it
is a theorem. -/
theorem finEx : ∀ {n : Nat} {α : Type} {P : Fin (n + 1) → α → Prop},
    (∀ j, ∃ x, P j x) → ∃ g : Fin (n + 1) → α, ∀ j, P j (g j)
  | 0, _, _, h => by
      obtain ⟨x0, hx0⟩ := h 0
      exact ⟨fun _ => x0, fun j => Fin.cases hx0 (fun i => i.elim0) j⟩
  | _ + 1, _, _, h => by
      obtain ⟨x0, hx0⟩ := h 0
      obtain ⟨g, hg⟩ := finEx (fun j => h j.succ)
      exact ⟨Fin.cases x0 g, fun j => Fin.cases hx0 hg j⟩

theorem not_isCirc_of_gHatAtImp {G X : Form}
    (h : X ∈ gAt G ++ gImp G) : X.isCirc = false := by
  rcases List.mem_append.mp h with h' | h'
  · have := (List.mem_filter.mp h').2
    cases X <;> simp_all [Form.isPV, Form.isCirc]
  · have := (List.mem_filter.mp h').2
    cases X <;> simp_all [Form.isImp, Form.isCirc]

theorem mem_gAt_of_not_imp {G X : Form}
    (h : X ∈ gAt G ++ gImp G) (himp : X.isImp = false) : X ∈ gAt G := by
  rcases List.mem_append.mp h with h' | h'
  · exact h'
  · exact absurd (List.mem_filter.mp h').2 (by simp [himp])

/-! ## §10a′  Clean refutations, and Lemma 14 — the irregular `◯` goal

Obstruction 1 was that `Ω →g ◯Z` had no success lemma.  Its root cause
is in the DATABASE model, not the calculus: `FDerivable (.reg Γ C)` is
`∃ t, Nonempty (FRJVr G t Γ C)` — the tag is quantified away — and (DB2)
returns a SUBSUMING row whose tag is then unknown.  `◯∈`/`◯∉` need a
tag they can lift, so the query has to be made before the database
forgets it.

`RefutedCleanly` is that query, localised to one derivation rather than
imposed on the whole database as `TagClean` was: a derivation of
`Γ ⇒ C` with a liftable tag, `Γ` covering `Ω`.  It is what the BARREN
joins produce — `⋈^At`, `⋈^∨` and `⋈^◯` all conclude at `barren` — and
what the fallible ones do not.

With it, Lemma 14 is short, and needs no query on `Υ` at all. -/

/-- An `FRJV` derivation of `Γ ⇒ C` whose tag `◯∈`/`◯∉` can lift, with
`Γ` covering `Ω`.  Strictly stronger than `EvalR D Ω C`. -/
def RefutedCleanly (G : Form) (Ω : List Form) (C : Form) : Prop :=
  ∃ (Γ : List Form) (t : Tag), Nonempty (FRJVr G t Γ C) ∧
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C) ∧ (∀ X ∈ Ω, Clo Γ X)

/-- A clean refutation is in particular a refutation. -/
theorem evalR_of_refutedCleanly {G : Form} {D : FSeq → Prop}
    (hsat : Saturated G D) {Ω : List Form} {C : Form}
    (h : RefutedCleanly G Ω C) : EvalR D Ω C := by
  obtain ⟨Γ, t, ⟨d⟩, _, hcov⟩ := h
  obtain ⟨s', hs'mem, hsub⟩ := hsat.2 (.reg Γ C) ⟨t, ⟨d⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      exact ⟨Γ', hs'mem, fun X hX => clo_mono hΓ (hcov X hX)⟩

/-- **The clean lookup IS the clean-refutation predicate**, under (DB1)
and (DB2).  This is what makes divergence D9 pay: `RefutedCleanly`
quantifies over derivations, `EvalRC` is a database lookup, and on a
saturated database they coincide — so Gbu◯ keeps the paper's
backtracking-free character at the modal rules too. -/
theorem evalRC_iff_refutedCleanly {G : Form} {D : FSeq → Prop}
    (hsat : Saturated G D) {Ψ : List Form} {C : Form} :
    EvalRC D Ψ C ↔ RefutedCleanly G Ψ C := by
  constructor
  · rintro ⟨Γ, hmem, hcov⟩
    obtain ⟨t, hd, htag⟩ := hsat.1 (.regC Γ C) hmem
    exact ⟨Γ, t, hd, htag, hcov⟩
  · rintro ⟨Γ, t, hd, htag, hcov⟩
    obtain ⟨s', hs'mem, hsub⟩ := hsat.2 (.regC Γ C) ⟨t, hd, htag⟩
    match s', hsub with
    | .regC Γ' _, ⟨rfl, hΓ⟩ =>
        exact ⟨Γ', hs'mem, fun X hX => clo_mono hΓ (hcov X hX)⟩

/-- Clean refutation is antitone in the context it covers — the same
monotonicity `EvalR` has, and for the same reason. -/
theorem refutedCleanly_mono {G : Form} {Ω Ω' : List Form} {C : Form}
    (h : Ω ⊆ Ω') (hr : RefutedCleanly G Ω' C) : RefutedCleanly G Ω C :=
  let ⟨Γ, t, d, htag, hcov⟩ := hr
  ⟨Γ, t, d, htag, fun X hX => hcov X (h hX)⟩

/-- …and closed under `Clo`, since the covering is a `Clo` already. -/
theorem refutedCleanly_clo {G : Form} {Ω Ω' : List Form} {C : Form}
    (h : ∀ X ∈ Ω, Clo Ω' X) (hr : RefutedCleanly G Ω' C) :
    RefutedCleanly G Ω C :=
  let ⟨Γ, t, d, htag, hcov⟩ := hr
  ⟨Γ, t, d, htag, fun X hX => clo_trans hcov (h X hX)⟩

theorem refutedCleanly_at {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {F : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hFp : F.isPrime) (hFgoal : F ∈ sfR G) (hFmem : F ∉ Ω)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A) :
    RefutedCleanly G Ω F := by
  by_cases hne : (impPart Ω).map ante = []
  · -- no left implications: the `Ax^R` cell
    have hnoimp : ∀ X ∈ Ω, X.isImp = false := by
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
  · -- the `⋈^At` join over the antecedents of `Ω`'s implications
    let E := enumOf ((impPart Ω).map ante) hne
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
    have hder : ∀ j, Nonempty (FRJVi G (St j) (Th j) (f j)) :=
      fun j => hsat.1 _ (hStTh j)
    obtain ⟨d⟩ := finPi hder
    -- the join's side conditions
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
    -- `Ω ⊆ Γ`: in some `Σ`, or in every `Θ`
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


theorem gbuSuccAt {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {F : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hFp : F.isPrime) (hFgoal : F ∈ sfR G) (hFmem : F ∉ Ω)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A) :
    EvalR D Ω F :=
  evalR_of_refutedCleanly hsat (refutedCleanly_at hsat hΩ hFp hFgoal hFmem himp)

/-! ## Lemma 12 (`lemma:gbuSuccOr`, source 4193) — the `∨` success lemma

"In a similar way" (source 4191), with `⋈^∨` in place of `⋈^At`.  Two
differences.  The premise family carries the two DISJUNCTS as well as
the antecedents, so it is never empty and there is no `Ax^R` case; and
the V-join's `RefAt` disjunct condition is discharged by its base clause
`RefAt.ups`, membership in `Υ`, which is exactly why the disjuncts have
to be in the family. -/

theorem refutedCleanly_or {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {C₁ C₂ : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (h₁ : EvalI D Ω C₁) (h₂ : EvalI D Ω C₂) :
    RefutedCleanly G Ω (.or C₁ C₂) := by
  let U := C₁ :: C₂ :: (impPart Ω).map ante
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : EvalI D Ω (f j) := by
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


theorem gbuSuccOr {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {C₁ C₂ : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (h₁ : EvalI D Ω C₁) (h₂ : EvalI D Ω C₂) :
    EvalR D Ω (.or C₁ C₂) :=
  evalR_of_refutedCleanly hsat (refutedCleanly_or hsat hΩ hgoal himp h₁ h₂)

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

/-- info: 'FRJ.Gbu.gbuInv10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv10

/-- info: 'FRJ.Gbu.gbuSuccAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuSuccAt

/-- info: 'FRJ.Gbu.gbuSuccOr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuSuccOr

/-- info: 'FRJ.Gbu.evalR_of_refutedCleanly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evalR_of_refutedCleanly

/-- info: 'FRJ.Gbu.evalRC_iff_refutedCleanly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evalRC_iff_refutedCleanly

/-- info: 'FRJ.Gbu.refutedCleanly_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_mono

/-- info: 'FRJ.Gbu.refutedCleanly_clo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_clo

/-- info: 'FRJ.Gbu.refutedCleanly_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_at

/-- info: 'FRJ.Gbu.refutedCleanly_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_or

end FRJ.Gbu
