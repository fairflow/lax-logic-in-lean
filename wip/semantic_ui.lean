import LaxLogic.PLLKripke
import LaxLogic.PLLCompleteness
import LaxLogic.PLLG4Space

/-!
# The semantic route to uniform interpolation: bisimulation quantifiers

Ghilardi-style plan, adapted to constraint models.  The syntactic route
(task #9) builds ∃p/∀p by recursion over the calculus; this file instead
characterises them SEMANTICALLY, via bisimulation:

    w ⊨ ∃p.φ   iff   some p-variant of w forces φ
    w ⊨ ∀p.φ   iff   every p-variant of every Rᵢ-future of w forces φ

where a *p-variant* is a world related by a bisimulation protecting every
atom except p.  This file proves, over the full class of constraint
models (matching the library's `soundness`/`completeness`):

* `force_iff_of_bisim` — forcing is invariant under A-bisimulation, for
  formulas whose atoms lie in the protected alphabet A.  The ◯-case
  needs zigzag for BOTH relations; the ⊥-case needs matching
  fallibility.  PROVED.
* `ABisim.id` — the identity is an A-bisimulation.  PROVED.
* `semEx_upper`, `semEx_adjunction`, `semAll_lower`, `semAll_adjunction`
  — ANY formula satisfying the semantic spec has exactly the
  Pitts/Ghilardi universal property of the uniform interpolant.  PROVED
  (via `soundness` + `completeness`).

Consequently the whole of uniform interpolation for PLL compresses into
ONE open statement per quantifier: DEFINABILITY (`semEx_definable`,
`semAll_definable`) — the existence of a p-free formula meeting the
spec.  That is where Ghilardi's method must survive the ∀∃ ◯-clause and
the fallible worlds, and where the finite canonical model
(`PLLFinComp.lean`, choice-free) is the intended engine: its worlds are
closure-total triples (Γ, Δ, Θ), finitely many per closure, and the
candidate interpolant is a disjunction of promise-aware world
descriptions.  See docs/semantic-ui-route.md for the full plan and the
relation to the realisability semantics.
-/

open PLLFormula
namespace PLLND
namespace SemUI

/-- **A-bisimulation** between constraint models: zigzag for both
relations, matching fallibility, matching atoms in the protected
alphabet `A`. -/
structure ABisim (A : String → Prop) (M N : ConstraintModel) where
  Z : M.W → N.W → Prop
  atoms : ∀ {w w'}, Z w w' → ∀ a, A a → (w ∈ M.V a ↔ w' ∈ N.V a)
  fall  : ∀ {w w'}, Z w w' → (w ∈ M.F ↔ w' ∈ N.F)
  iforth : ∀ {w w'}, Z w w' → ∀ {v}, M.Ri w v → ∃ v', N.Ri w' v' ∧ Z v v'
  iback  : ∀ {w w'}, Z w w' → ∀ {v'}, N.Ri w' v' → ∃ v, M.Ri w v ∧ Z v v'
  mforth : ∀ {w w'}, Z w w' → ∀ {u}, M.Rm w u → ∃ u', N.Rm w' u' ∧ Z u u'
  mback  : ∀ {w w'}, Z w w' → ∀ {u'}, N.Rm w' u' → ∃ u, M.Rm w u ∧ Z u u'

/-- **Forcing is invariant under A-bisimulation** for formulas over the
protected alphabet.  The ⊃-case uses i-zigzag; the ◯-case uses i-zigzag
to move the future and m-zigzag to move the constraint witness. -/
theorem force_iff_of_bisim {A : String → Prop} {M N : ConstraintModel}
    (B : ABisim A M N) :
    ∀ {φ : PLLFormula}, (∀ a ∈ φ.atoms, A a) →
    ∀ {w : M.W} {w' : N.W}, B.Z w w' → (M.force w φ ↔ N.force w' φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro hA w w' hZ
      simpa [ConstraintModel.force] using B.atoms hZ a (hA a (by simp))
  | falsePLL =>
      intro _ w w' hZ
      simpa [ConstraintModel.force] using B.fall hZ
  | and φ ψ ihφ ihψ =>
      intro hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact and_congr (ihφ h1 hZ) (ihψ h2 hZ)
  | or φ ψ ihφ ihψ =>
      intro hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact or_congr (ihφ h1 hZ) (ihψ h2 hZ)
  | ifThen φ ψ ihφ ihψ =>
      intro hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      constructor
      · intro hf v' hv' hφ'
        obtain ⟨v, hv, hZv⟩ := B.iback hZ hv'
        exact (ihψ h2 hZv).mp (hf v hv ((ihφ h1 hZv).mpr hφ'))
      · intro hf v hv hφv
        obtain ⟨v', hv', hZv⟩ := B.iforth hZ hv
        exact (ihψ h2 hZv).mpr (hf v' hv' ((ihφ h1 hZv).mp hφv))
  | somehow φ ihφ =>
      intro hA w w' hZ
      simp only [ConstraintModel.force]
      constructor
      · intro hf v' hv'
        obtain ⟨v, hv, hZv⟩ := B.iback hZ hv'
        obtain ⟨u, hu, hφu⟩ := hf v hv
        obtain ⟨u', hu', hZu⟩ := B.mforth hZv hu
        exact ⟨u', hu', (ihφ hA hZu).mp hφu⟩
      · intro hf v hv
        obtain ⟨v', hv', hZv⟩ := B.iforth hZ hv
        obtain ⟨u', hu', hφu'⟩ := hf v' hv'
        obtain ⟨u, hu, hZu⟩ := B.mback hZv hu'
        exact ⟨u, hu, (ihφ hA hZu).mpr hφu'⟩

/-- The identity bisimulation (any alphabet). -/
def ABisim.id (A : String → Prop) (M : ConstraintModel) : ABisim A M M where
  Z := fun w w' => w = w'
  atoms := by rintro w _ rfl a _; exact Iff.rfl
  fall := by rintro w _ rfl; exact Iff.rfl
  iforth := by rintro w _ rfl v hv; exact ⟨v, hv, rfl⟩
  iback := by rintro w _ rfl v' hv'; exact ⟨v', hv', rfl⟩
  mforth := by rintro w _ rfl u hu; exact ⟨u, hu, rfl⟩
  mback := by rintro w _ rfl u' hu'; exact ⟨u', hu', rfl⟩

/-- Bisimulation protecting every atom except `p`: its related worlds
are each other's *p-variants*. -/
abbrev PBisim (p : String) := ABisim (fun a => a ≠ p)

/-! ## The semantic specifications of the two quantifiers -/

/-- `ψ` is a **semantic ∃p-quantifier** for `φ`: p-free, and forced
exactly at the worlds having a p-variant forcing `φ`.  (Persistence of
the right-hand side follows from i-forth, so the spec is coherent.) -/
def IsSemEx (p : String) (φ ψ : PLLFormula) : Prop :=
  p ∉ ψ.atoms ∧
  ∀ (M : ConstraintModel) (w : M.W),
    M.force w ψ ↔
      ∃ (N : ConstraintModel) (B : PBisim p M N) (w' : N.W),
        B.Z w w' ∧ N.force w' φ

/-- `ψ` is a **semantic ∀p-quantifier** for `φ`: p-free, and forced
exactly at the worlds ALL of whose futures' p-variants force `φ` (the
Rᵢ-guard makes the right-hand side hereditary). -/
def IsSemAll (p : String) (φ ψ : PLLFormula) : Prop :=
  p ∉ ψ.atoms ∧
  ∀ (M : ConstraintModel) (w : M.W),
    M.force w ψ ↔
      ∀ v, M.Ri w v →
        ∀ (N : ConstraintModel) (B : PBisim p M N) (v' : N.W),
          B.Z v v' → N.force v' φ

/-! ## The universal properties (PROVED): a spec-satisfier IS the
uniform interpolant -/

/-- `φ ⊢ ∃p.φ`. -/
theorem semEx_upper {p : String} {φ ψ : PLLFormula} (h : IsSemEx p φ ψ) :
    Nonempty (LaxND [φ] ψ) := by
  refine completeness ?_
  intro M w hw
  exact (h.2 M w).mpr ⟨M, ABisim.id _ M, w, rfl, hw φ (by simp)⟩

/-- **The ∃p adjunction**: for p-free `χ`,  `φ ⊢ χ  iff  ∃p.φ ⊢ χ`. -/
theorem semEx_adjunction {p : String} {φ ψ : PLLFormula}
    (h : IsSemEx p φ ψ) {χ : PLLFormula} (hχ : p ∉ χ.atoms) :
    Nonempty (LaxND [φ] χ) ↔ Nonempty (LaxND [ψ] χ) := by
  have hAχ : ∀ a ∈ χ.atoms, a ≠ p := fun a ha he => hχ (he ▸ ha)
  constructor
  · rintro ⟨d⟩
    refine completeness ?_
    intro M w hw
    obtain ⟨N, B, w', hZ, hφ'⟩ := (h.2 M w).mp (hw ψ (by simp))
    have hχ' : N.force w' χ := by
      refine soundness d N w' ?_
      intro ξ hξ
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hφ'
    exact (force_iff_of_bisim B hAχ hZ).mpr hχ'
  · rintro ⟨d⟩
    refine completeness ?_
    intro M w hw
    have hψw : M.force w ψ :=
      (h.2 M w).mpr ⟨M, ABisim.id _ M, w, rfl, hw φ (by simp)⟩
    refine soundness d M w ?_
    intro ξ hξ
    simp only [List.mem_singleton] at hξ
    exact hξ ▸ hψw

/-- `∀p.φ ⊢ φ`. -/
theorem semAll_lower {p : String} {φ ψ : PLLFormula} (h : IsSemAll p φ ψ) :
    Nonempty (LaxND [ψ] φ) := by
  refine completeness ?_
  intro M w hw
  exact (h.2 M w).mp (hw ψ (by simp)) w (M.refl_i w) M (ABisim.id _ M) w rfl

/-- **The ∀p adjunction**: for p-free `χ`,  `χ ⊢ φ  iff  χ ⊢ ∀p.φ`. -/
theorem semAll_adjunction {p : String} {φ ψ : PLLFormula}
    (h : IsSemAll p φ ψ) {χ : PLLFormula} (hχ : p ∉ χ.atoms) :
    Nonempty (LaxND [χ] φ) ↔ Nonempty (LaxND [χ] ψ) := by
  have hAχ : ∀ a ∈ χ.atoms, a ≠ p := fun a ha he => hχ (he ▸ ha)
  constructor
  · rintro ⟨d⟩
    refine completeness ?_
    intro M w hw
    refine (h.2 M w).mpr ?_
    intro v hv N B v' hZ
    have hχv : M.force v χ := M.force_hered hv (hw χ (by simp))
    have hχv' : N.force v' χ := (force_iff_of_bisim B hAχ hZ).mp hχv
    refine soundness d N v' ?_
    intro ξ hξ
    simp only [List.mem_singleton] at hξ
    exact hξ ▸ hχv'
  · rintro ⟨d⟩
    refine completeness ?_
    intro M w hw
    have hψw : M.force w ψ := by
      refine soundness d M w ?_
      intro ξ hξ
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hw χ (by simp)
    exact (h.2 M w).mp hψw w (M.refl_i w) M (ABisim.id _ M) w rfl

/-! ## The single open target per quantifier: DEFINABILITY

This is the Ghilardi step, and the whole of uniform interpolation for
PLL now rests on it.  Intended engine: the finite canonical model of
`PLLFinComp.lean` — worlds are closure-total triples (Γ, Δ, Θ),
finitely many per subformula closure, so the candidate ∃p-interpolant
is a finite disjunction of *promise-aware world descriptions* over the
closure of φ with p removed.  The two PLL-specific hazards, in order of
expected difficulty:
  (i) the ∀∃ ◯-clause: amalgamating two p-variants must complete
      Rm-witnesses coherently (this is where S4-style failure would
      enter; PLL's full heredity is the counter-pressure);
  (ii) fallible worlds: every formula is forced there, so descriptions
      must carry the Θ-promises (the ¬◯⋁Θ shape of the consistency
      formula) to pin the ◯-behaviour.
The 1-pv evidence (five-class state spaces, stabilisation far below
threshold) suggests the finite type structure is very tame. -/

/-- OPEN (Ghilardi step, ∃-side). -/
theorem semEx_definable (p : String) (φ : PLLFormula) :
    ∃ ψ, IsSemEx p φ ψ := by
  sorry

/-- OPEN (Ghilardi step, ∀-side). -/
theorem semAll_definable (p : String) (φ : PLLFormula) :
    ∃ ψ, IsSemAll p φ ψ := by
  sorry

/-! ## Base and compositional cases of definability (PROVED)

The definability induction begins here.  The atomic and ⊥ cases and the
"pointwise" compositional cases (∃ through ∨, ∀ through ∧) are proved
outright; the genuinely quantificational content is confined to what is
NOT here — ∃ through ∧/⊃/◯ and ∀ through ∨/⊃/◯ — exactly the cases
where the canonical-model descriptions must enter. -/

/-- **The universal p-variant constructor**: redecorate the atom `p`
with an arbitrary hereditary, fallibility-respecting set of worlds;
frame and all other atoms unchanged. -/
def redecorate (M : ConstraintModel) (p : String) (S : Set M.W)
    (hh : ∀ {w v}, M.Ri w v → w ∈ S → v ∈ S)
    (hf : ∀ {w}, w ∈ M.F → w ∈ S) : ConstraintModel where
  W := M.W
  Ri := M.Ri
  Rm := M.Rm
  F := M.F
  V := fun a => if a = p then S else M.V a
  refl_i := M.refl_i
  trans_i := M.trans_i
  refl_m := M.refl_m
  trans_m := M.trans_m
  sub_mi := M.sub_mi
  hered_F := M.hered_F
  hered_V := by
    intro a w v h hw
    have hw' : w ∈ (if a = p then S else M.V a) := hw
    show v ∈ (if a = p then S else M.V a)
    by_cases ha : a = p
    · rw [if_pos ha] at hw' ⊢
      exact hh h hw'
    · rw [if_neg ha] at hw' ⊢
      exact M.hered_V h hw'
  full_F := by
    intro a w hw
    show w ∈ (if a = p then S else M.V a)
    by_cases ha : a = p
    · rw [if_pos ha]
      exact hf hw
    · rw [if_neg ha]
      exact M.full_F hw

/-- Redecoration is a p-variant: the identity carrier is a `PBisim p`. -/
def redecorate_pbisim (M : ConstraintModel) (p : String) (S : Set M.W)
    (hh : ∀ {w v}, M.Ri w v → w ∈ S → v ∈ S)
    (hf : ∀ {w}, w ∈ M.F → w ∈ S) :
    PBisim p M (redecorate M p S hh hf) where
  Z := fun w w' => w = w'
  atoms := by
    rintro w _ rfl a ha
    show w ∈ M.V a ↔ w ∈ (if a = p then S else M.V a)
    rw [if_neg ha]
  fall := by rintro w _ rfl; exact Iff.rfl
  iforth := by rintro w _ rfl v hv; exact ⟨v, hv, rfl⟩
  iback := by rintro w _ rfl v' hv'; exact ⟨v', hv', rfl⟩
  mforth := by rintro w _ rfl u hu; exact ⟨u, hu, rfl⟩
  mback := by rintro w _ rfl u' hu'; exact ⟨u', hu', rfl⟩

/-- `∃p.p = ⊤` — every world has a p-variant forcing p (redecorate with
the universal set). -/
theorem semEx_prop_self (p : String) : IsSemEx p (.prop p) truePLL := by
  refine ⟨by simp [truePLL], ?_⟩
  intro M w
  constructor
  · intro _
    refine ⟨redecorate M p Set.univ (fun _ _ => trivial) (fun _ => trivial),
            redecorate_pbisim M p Set.univ (fun _ _ => trivial) (fun _ => trivial),
            w, rfl, ?_⟩
    show w ∈ (if p = p then Set.univ else M.V p)
    rw [if_pos rfl]
    trivial
  · intro _
    exact fun v _ h => h

/-- `∀p.p = ⊥` — only fallible worlds have p forced by ALL p-variants
(redecorate with the fallible set). -/
theorem semAll_prop_self (p : String) : IsSemAll p (.prop p) falsePLL := by
  refine ⟨by simp, ?_⟩
  intro M w
  constructor
  · intro hw v hv N B v' hZ
    have hvF : v ∈ M.F := M.hered_F hv hw
    exact N.full_F ((B.fall hZ).mp hvF)
  · intro h
    have := h w (M.refl_i w)
      (redecorate M p M.F (fun hri hF => M.hered_F hri hF) (fun hF => hF))
      (redecorate_pbisim M p M.F (fun hri hF => M.hered_F hri hF) (fun hF => hF))
      w rfl
    have hw : w ∈ (if p = p then M.F else M.V p) := this
    rwa [if_pos rfl] at hw

/-- `∃p.q = q` for `q ≠ p`. -/
theorem semEx_prop_ne {p q : String} (h : q ≠ p) :
    IsSemEx p (.prop q) (.prop q) := by
  refine ⟨by simpa using fun hp => h hp.symm, ?_⟩
  intro M w
  constructor
  · intro hw
    exact ⟨M, ABisim.id _ M, w, rfl, hw⟩
  · rintro ⟨N, B, w', hZ, hq⟩
    exact (B.atoms hZ q h).mpr hq

/-- `∀p.q = q` for `q ≠ p`. -/
theorem semAll_prop_ne {p q : String} (h : q ≠ p) :
    IsSemAll p (.prop q) (.prop q) := by
  refine ⟨by simpa using fun hp => h hp.symm, ?_⟩
  intro M w
  constructor
  · intro hw v hv N B v' hZ
    exact (B.atoms hZ q h).mp (M.hered_V hv hw)
  · intro h'
    exact h' w (M.refl_i w) M (ABisim.id _ M) w rfl

/-- `∃p.⊥ = ⊥`. -/
theorem semEx_false (p : String) : IsSemEx p .falsePLL .falsePLL := by
  refine ⟨by simp, ?_⟩
  intro M w
  constructor
  · intro hw
    exact ⟨M, ABisim.id _ M, w, rfl, hw⟩
  · rintro ⟨N, B, w', hZ, hF⟩
    exact (B.fall hZ).mpr hF

/-- `∀p.⊥ = ⊥`. -/
theorem semAll_false (p : String) : IsSemAll p .falsePLL .falsePLL := by
  refine ⟨by simp, ?_⟩
  intro M w
  constructor
  · intro hw v hv N B v' hZ
    exact (B.fall hZ).mp (M.hered_F hv hw)
  · intro h'
    exact h' w (M.refl_i w) M (ABisim.id _ M) w rfl

/-- ∃p commutes with ∨ (the SAME p-variant serves whichever disjunct). -/
theorem semEx_or {p : String} {φ₁ φ₂ ψ₁ ψ₂ : PLLFormula}
    (h₁ : IsSemEx p φ₁ ψ₁) (h₂ : IsSemEx p φ₂ ψ₂) :
    IsSemEx p (φ₁.or φ₂) (ψ₁.or ψ₂) := by
  refine ⟨fun hp => (mem_atoms_or.mp hp).elim h₁.1 h₂.1, ?_⟩
  intro M w
  show M.force w ψ₁ ∨ M.force w ψ₂ ↔ _
  rw [h₁.2 M w, h₂.2 M w]
  constructor
  · rintro (⟨N, B, w', hZ, hφ⟩ | ⟨N, B, w', hZ, hφ⟩)
    · exact ⟨N, B, w', hZ, Or.inl hφ⟩
    · exact ⟨N, B, w', hZ, Or.inr hφ⟩
  · rintro ⟨N, B, w', hZ, hφ | hφ⟩
    · exact Or.inl ⟨N, B, w', hZ, hφ⟩
    · exact Or.inr ⟨N, B, w', hZ, hφ⟩

/-- ∀p commutes with ∧. -/
theorem semAll_and {p : String} {φ₁ φ₂ ψ₁ ψ₂ : PLLFormula}
    (h₁ : IsSemAll p φ₁ ψ₁) (h₂ : IsSemAll p φ₂ ψ₂) :
    IsSemAll p (φ₁.and φ₂) (ψ₁.and ψ₂) := by
  refine ⟨fun hp => (mem_atoms_and.mp hp).elim h₁.1 h₂.1, ?_⟩
  intro M w
  show M.force w ψ₁ ∧ M.force w ψ₂ ↔ _
  rw [h₁.2 M w, h₂.2 M w]
  constructor
  · rintro ⟨ha, hb⟩ v hv N B v' hZ
    exact ⟨ha v hv N B v' hZ, hb v hv N B v' hZ⟩
  · intro h'
    exact ⟨fun v hv N B v' hZ => (h' v hv N B v' hZ).1,
           fun v hv N B v' hZ => (h' v hv N B v' hZ).2⟩

/-! What is deliberately NOT here — the quantificational core, where the
canonical-model descriptions must enter:
* ∃ through ∧ (two variants must be AMALGAMATED into one),
* ∃ through ⊃ and ◯ (variant construction against ∀-clauses),
* ∀ through ∨ (a disjunction of ∀'s under-approximates).
These are the ⊃/◯/amalgamation cases of `semEx_definable`/
`semAll_definable`, and the reason the general theorem needs the finite
canonical model rather than a structural recursion. -/

/-! ## The amalgamation case at one variable (PROVED)

Two halves.  NEGATIVE: the pointwise ∧-candidate is provably wrong —
`∃p.p = ⊤` and `∃p.¬p = ⊤` (witnessing decorations: p everywhere,
p exactly on the fallible set), yet `∃p.(p ∧ ¬p) = ⊥`: the two
witnesses decorate p INCOMPATIBLY (⊤-decoration vs F-decoration), and
no single p-variant serves both conjuncts at a non-fallible world.
`semEx_and_pointwise_fails` machine-checks this on a one-world model.
This is the amalgamation obstruction in miniature: it is exactly what
the canonical-model descriptions must negotiate.

POSITIVE: the first genuinely modal quantifier values, matching the
{⊥, ◯⊥, ⊤} landscape the one-variable descent probe observed:

    ∃p.¬p = ⊤     ∀p.¬p = ⊥     ∃p.◯p = ⊤     **∀p.◯p = ◯⊥**

The last is the interesting one: the strongest legal p-decoration is
p := F (the fallible set), under which ◯p becomes literally ◯⊥ — and
against ALL variants, full_F pins the value.  ◯⊥, the free generator of
the closed fragment, is the ∀p-shadow of the modality itself. -/

/-- `∃p.¬p = ⊤`: decorate p by the fallible set; then p ⊃ ⊥ holds
everywhere. -/
theorem semEx_neg_p (p : String) : IsSemEx p ((PLLFormula.prop p).ifThen .falsePLL) truePLL := by
  refine ⟨by simp [truePLL], ?_⟩
  intro M w
  constructor
  · intro _
    refine ⟨redecorate M p M.F (fun h hw => M.hered_F h hw) (fun hw => hw),
            redecorate_pbisim M p M.F (fun h hw => M.hered_F h hw) (fun hw => hw),
            w, rfl, ?_⟩
    intro v _ hp
    have hv : v ∈ (if p = p then M.F else M.V p) := hp
    rwa [if_pos rfl] at hv
  · intro _
    exact fun v _ h => h

/-- `∀p.¬p = ⊥`: against the ⊤-decoration, ¬p forces only where
everything ahead is fallible — i.e. exactly on F. -/
theorem semAll_neg_p (p : String) : IsSemAll p ((PLLFormula.prop p).ifThen .falsePLL) .falsePLL := by
  refine ⟨by simp, ?_⟩
  intro M w
  constructor
  · intro hw v hv N B v' hZ
    have hvF' : v' ∈ N.F := (B.fall hZ).mp (M.hered_F hv hw)
    intro u' hu' _
    exact N.hered_F hu' hvF'
  · intro h'
    have h'' := h' w (M.refl_i w)
      (redecorate M p Set.univ (fun _ _ => trivial) (fun _ => trivial))
      (redecorate_pbisim M p Set.univ (fun _ _ => trivial) (fun _ => trivial))
      w rfl
    exact h'' w (M.refl_i w)
      (by show w ∈ (if p = p then Set.univ else M.V p); rw [if_pos rfl]; trivial)

/-- `∃p.◯p = ⊤`: under the ⊤-decoration every world Rₘ-reaches itself
forcing p. -/
theorem semEx_box_p (p : String) : IsSemEx p (PLLFormula.prop p).somehow truePLL := by
  refine ⟨by simp [truePLL], ?_⟩
  intro M w
  constructor
  · intro _
    refine ⟨redecorate M p Set.univ (fun _ _ => trivial) (fun _ => trivial),
            redecorate_pbisim M p Set.univ (fun _ _ => trivial) (fun _ => trivial),
            w, rfl, ?_⟩
    intro v _
    refine ⟨v, M.refl_m v, ?_⟩
    show v ∈ (if p = p then Set.univ else M.V p)
    rw [if_pos rfl]
    trivial
  · intro _
    exact fun v _ h => h

/-- **`∀p.◯p = ◯⊥`** — the first genuinely modal quantifier value.
Forward: ◯⊥ is p-free, so it crosses any p-bisimulation, and `full_F`
turns its fallible witnesses into p-witnesses.  Backward: the
F-decoration is a legal p-variant on which ◯p IS ◯⊥. -/
theorem semAll_box_p (p : String) :
    IsSemAll p (PLLFormula.prop p).somehow PLLFormula.falsePLL.somehow := by
  refine ⟨by simp, ?_⟩
  intro M w
  constructor
  · intro hw v hv N B v' hZ
    have hvbox : M.force v (PLLFormula.falsePLL.somehow) := M.force_hered hv hw
    have hA : ∀ a ∈ (PLLFormula.falsePLL.somehow).atoms, a ≠ p := by simp
    have hvbox' : N.force v' (PLLFormula.falsePLL.somehow) :=
      (force_iff_of_bisim B hA hZ).mp hvbox
    intro v₂' hv₂'
    obtain ⟨u', hu', hF⟩ := hvbox' v₂' hv₂'
    exact ⟨u', hu', N.full_F hF⟩
  · intro h'
    have h'' := h' w (M.refl_i w)
      (redecorate M p M.F (fun h hw => M.hered_F h hw) (fun hw => hw))
      (redecorate_pbisim M p M.F (fun h hw => M.hered_F h hw) (fun hw => hw))
      w rfl
    intro v hv
    obtain ⟨u, hu, hp⟩ := h'' v hv
    refine ⟨u, hu, ?_⟩
    have hu' : u ∈ (if p = p then M.F else M.V p) := hp
    rwa [if_pos rfl] at hu'

/-- `∃p.(p ∧ ¬p) = ⊥`: a p-variant forcing both p and ¬p is fallible,
and fallibility crosses the bisimulation. -/
theorem semEx_p_and_neg_p (p : String) :
    IsSemEx p ((PLLFormula.prop p).and ((PLLFormula.prop p).ifThen .falsePLL)) .falsePLL := by
  refine ⟨by simp, ?_⟩
  intro M w
  constructor
  · intro hw
    refine ⟨M, ABisim.id _ M, w, rfl, M.full_F hw, ?_⟩
    intro v hv _
    exact M.hered_F hv hw
  · rintro ⟨N, B, w', hZ, hp, hnp⟩
    exact (B.fall hZ).mpr (hnp w' (N.refl_i w') hp)

/-! ## The quantifiers fix the p-free fragment; surjectivity onto RN(◯,{})

Matthew's conjecture (2026-07-18): every element of the closed lax
fragment RN(◯,{}) is the value of ∀p.M for some one-variable M.  TRUE —
and by a short route: the quantifiers FIX every p-free formula
(`semAll_pfree_fixpoint`, `semEx_pfree_fixpoint`), so a closed ξ is its
own ∀p-value (and ∃p-value).  Surjectivity is therefore immediate
(`semAll_hits_every_closed`); the non-trivial content moves to the
FIBRES of ∀p — which one-variable formulas map to which closed value —
where the lattice-height induction over RN(◯,{}) belongs.  Structurally
(modulo definability) the two adjunctions + these fixpoints say:
∃p ⊣ inclusion ⊣ ∀p, a retraction triple — incl∘∀p is an interior
(meet-preserving, cf. `semAll_and`) comonad and incl∘∃p a closure
(join-preserving, cf. `semEx_or`) monad on the free one-variable lax
algebra, both with fixpoint set exactly RN(◯,{}). -/

/-- ∀p fixes every p-free formula. -/
theorem semAll_pfree_fixpoint {p : String} {ψ : PLLFormula}
    (hp : p ∉ ψ.atoms) : IsSemAll p ψ ψ := by
  have hA : ∀ a ∈ ψ.atoms, a ≠ p := fun a ha he => hp (he ▸ ha)
  refine ⟨hp, ?_⟩
  intro M w
  constructor
  · intro hw v hv N B v' hZ
    exact (force_iff_of_bisim B hA hZ).mp (M.force_hered hv hw)
  · intro h'
    exact h' w (M.refl_i w) M (ABisim.id _ M) w rfl

/-- ∃p fixes every p-free formula. -/
theorem semEx_pfree_fixpoint {p : String} {ψ : PLLFormula}
    (hp : p ∉ ψ.atoms) : IsSemEx p ψ ψ := by
  have hA : ∀ a ∈ ψ.atoms, a ≠ p := fun a ha he => hp (he ▸ ha)
  refine ⟨hp, ?_⟩
  intro M w
  constructor
  · intro hw
    exact ⟨M, ABisim.id _ M, w, rfl, hw⟩
  · rintro ⟨N, B, w', hZ, hφ⟩
    exact (force_iff_of_bisim B hA hZ).mpr hφ

/-- **Every closed formula is a ∀p-value** (Matthew's conjecture,
2026-07-18): the ∀p-image covers all of RN(◯,{}). -/
theorem semAll_hits_every_closed (p : String) {ξ : PLLFormula}
    (h : ξ.atoms = ∅) : ∃ M, IsSemAll p M ξ :=
  ⟨ξ, semAll_pfree_fixpoint (by simp [h])⟩

/-- Dually for ∃p. -/
theorem semEx_hits_every_closed (p : String) {ξ : PLLFormula}
    (h : ξ.atoms = ∅) : ∃ M, IsSemEx p M ξ :=
  ⟨ξ, semEx_pfree_fixpoint (by simp [h])⟩

/-- The trivial one-world, nowhere-fallible model. -/
def oneW : ConstraintModel where
  W := Unit
  Ri := fun _ _ => True
  Rm := fun _ _ => True
  F := ∅
  V := fun _ => ∅
  refl_i := fun _ => trivial
  trans_i := fun _ _ => trivial
  refl_m := fun _ => trivial
  trans_m := fun _ _ => trivial
  sub_mi := fun _ => trivial
  hered_F := fun _ hw => hw.elim
  hered_V := fun _ hw => hw.elim
  full_F := fun hw => hw.elim

/-- **The amalgamation obstruction, machine-checked**: ∃p does NOT
commute with ∧.  The pointwise candidate for `∃p.(p ∧ ¬p)` from
`semEx_prop_self` and `semEx_neg_p` is `⊤ ∧ ⊤`; it fails the spec,
because at the non-fallible world of `oneW` the two conjuncts demand
INCOMPATIBLE p-decorations (everywhere vs nowhere-but-F). -/
theorem semEx_and_pointwise_fails (p : String) :
    ¬ IsSemEx p ((PLLFormula.prop p).and ((PLLFormula.prop p).ifThen .falsePLL))
        (truePLL.and truePLL) := by
  rintro ⟨-, hspec⟩
  have htop : oneW.force () (truePLL.and truePLL) :=
    ⟨fun _ _ h => h, fun _ _ h => h⟩
  obtain ⟨N, B, w', hZ, hp, hnp⟩ := (hspec oneW ()).mp htop
  have hF' : w' ∈ N.F := hnp w' (N.refl_i w') hp
  exact ((B.fall hZ).mpr hF').elim

/-! ## The essential fibre of the quantifiers

Call `p` **inessential** in `M` when `M` is PLL-equivalent to some p-free
formula, **essential** otherwise.  The quantifiers hit every p-free value
(`semAll_hits_every_closed`), but only because p-free formulas are their
own values; the essential fibre asks which values are attained by
formulas in which `p` genuinely matters.  The answer
(`essential_semAll_image`, `essential_semEx_image` below):

    { ξ p-free : ξ = ∀p.M for some M with p essential }  =  { ξ : ⊬ ξ }
    { ξ p-free : ξ = ∃p.M for some M with p essential }  =  { ξ : ξ ⊬ ⊥ }

— on the closed fragment RN(◯,{}): the essential ∀p-image is everything
except ⊤, and the essential ∃p-image is everything except ⊥. -/

/-- `p` is inessential in `M`: `M` is interderivable with some p-free
formula.  (*Essential* = the negation.) -/
def Inessential (p : String) (M : PLLFormula) : Prop :=
  ∃ ψ, p ∉ ψ.atoms ∧ Nonempty (LaxND [M] ψ) ∧ Nonempty (LaxND [ψ] M)

/-- If ⊤ meets the ∀p-spec for `M`, then `⊢ M`: instantiate the spec's
right-hand side at the world itself and the identity bisimulation. -/
theorem semAll_true_derivable {p : String} {M : PLLFormula}
    (h : IsSemAll p M truePLL) : Nonempty (LaxND [] M) := by
  refine completeness ?_
  intro C w _
  exact (h.2 C w).mp (fun v _ hv => hv) w (C.refl_i w) C (ABisim.id _ C) w rfl

/-- **⊤ is never an essential ∀p-value**: `∀p.M = ⊤` forces `M ≡ ⊤`. -/
theorem inessential_of_semAll_true {p : String} {M : PLLFormula}
    (h : IsSemAll p M truePLL) : Inessential p M := by
  obtain ⟨d⟩ := semAll_true_derivable h
  exact ⟨truePLL, by simp [truePLL],
    ⟨.impIntro (.iden (by simp))⟩, ⟨d.rename (by simp)⟩⟩

/-- If ⊥ meets the ∃p-spec for `M`, then `M ⊢ ⊥`: the world itself is a
p-variant of itself forcing `M`. -/
theorem semEx_false_refutes {p : String} {M : PLLFormula}
    (h : IsSemEx p M .falsePLL) : Nonempty (LaxND [M] .falsePLL) := by
  refine completeness ?_
  intro C w hw
  exact (h.2 C w).mpr ⟨C, ABisim.id _ C, w, rfl, hw M (by simp)⟩

/-- **⊥ is never an essential ∃p-value**: `∃p.M = ⊥` forces `M ≡ ⊥`. -/
theorem inessential_of_semEx_false {p : String} {M : PLLFormula}
    (h : IsSemEx p M .falsePLL) : Inessential p M := by
  obtain ⟨d⟩ := semEx_false_refutes h
  exact ⟨.falsePLL, by simp, ⟨d⟩, ⟨.falsoElim M (.iden (by simp))⟩⟩

/-! ## Substitution and truth-set decorations

`substP p χ M` substitutes `χ` for the atom `p`.  Decorating `p` by the
truth set of `χ` is a legal redecoration (heredity is `force_hered`,
F-fullness is `force_of_fallible`), and forcing in the redecorated model
is forcing of the substituted formula — the bridge between the spec's
quantification over p-variants and the syntactic instances `M[p:=χ]`. -/

/-- Substitute `χ` for the atom `p`. -/
def substP (p : String) (χ : PLLFormula) : PLLFormula → PLLFormula
  | .prop a     => if a = p then χ else .prop a
  | .falsePLL   => .falsePLL
  | .and A B    => .and (substP p χ A) (substP p χ B)
  | .or A B     => .or (substP p χ A) (substP p χ B)
  | .ifThen A B => .ifThen (substP p χ A) (substP p χ B)
  | .somehow A  => .somehow (substP p χ A)

/-- Substitution is vacuous on p-free formulas. -/
theorem substP_of_not_mem {p : String} {χ M : PLLFormula} (h : p ∉ M.atoms) :
    substP p χ M = M := by
  induction M with
  | prop a =>
      have ha : a ≠ p := by rintro rfl; exact h (by simp)
      simp [substP, ha]
  | falsePLL => rfl
  | and A B ihA ihB =>
      simp only [substP]
      rw [ihA (fun hx => h (mem_atoms_and.mpr (.inl hx))),
          ihB (fun hx => h (mem_atoms_and.mpr (.inr hx)))]
  | or A B ihA ihB =>
      simp only [substP]
      rw [ihA (fun hx => h (mem_atoms_or.mpr (.inl hx))),
          ihB (fun hx => h (mem_atoms_or.mpr (.inr hx)))]
  | ifThen A B ihA ihB =>
      simp only [substP]
      rw [ihA (fun hx => h (mem_atoms_ifThen.mpr (.inl hx))),
          ihB (fun hx => h (mem_atoms_ifThen.mpr (.inr hx)))]
  | somehow A ihA =>
      simp only [substP]
      rw [ihA (fun hx => h hx)]

/-- The truth-set decoration: `p` re-decorated to hold exactly where `χ`
is forced. -/
def truthDeco (C : ConstraintModel) (p : String) (χ : PLLFormula) :
    ConstraintModel :=
  redecorate C p {w | C.force w χ}
    (fun h hw => C.force_hered h hw) (fun hw => C.force_of_fallible hw)

/-- The truth-set decoration is a p-variant of the original model. -/
def truthDeco_pbisim (C : ConstraintModel) (p : String) (χ : PLLFormula) :
    PBisim p C (truthDeco C p χ) :=
  redecorate_pbisim C p {w | C.force w χ}
    (fun h hw => C.force_hered h hw) (fun hw => C.force_of_fallible hw)

/-- **Forcing a substitution instance = forcing under the truth-set
decoration.** -/
theorem force_truthDeco (C : ConstraintModel) (p : String) (χ : PLLFormula) :
    ∀ (M : PLLFormula) (w : C.W),
      (truthDeco C p χ).force w M ↔ C.force w (substP p χ M) := by
  intro M
  induction M with
  | prop a =>
      intro w
      show w ∈ (if a = p then {w | C.force w χ} else C.V a) ↔
        C.force w (substP p χ (.prop a))
      by_cases ha : a = p
      · rw [if_pos ha]
        simp only [substP, if_pos ha]
        exact Iff.rfl
      · rw [if_neg ha]
        simp only [substP, if_neg ha]
        exact Iff.rfl
  | falsePLL => exact fun w => Iff.rfl
  | and A B ihA ihB =>
      intro w
      simp only [ConstraintModel.force, substP]
      exact and_congr (ihA w) (ihB w)
  | or A B ihA ihB =>
      intro w
      simp only [ConstraintModel.force, substP]
      exact or_congr (ihA w) (ihB w)
  | ifThen A B ihA ihB =>
      intro w
      simp only [ConstraintModel.force, substP]
      constructor
      · intro hf v hv hA
        exact (ihB v).mp (hf v hv ((ihA v).mpr hA))
      · intro hf v hv hA
        exact (ihB v).mpr (hf v hv ((ihA v).mp hA))
  | somehow A ihA =>
      intro w
      simp only [ConstraintModel.force, substP]
      constructor
      · intro hf v hv
        obtain ⟨u, hu, hA⟩ := hf v hv
        exact ⟨u, hu, (ihA u).mp hA⟩
      · intro hf v hv
        obtain ⟨u, hu, hA⟩ := hf v hv
        exact ⟨u, hu, (ihA u).mpr hA⟩

/-! ## Certificate criteria: derivability facts ⇒ the spec

Sound (deliberately not complete) criteria reducing the spec to
derivability facts — each oracle-checkable, and each directly a Lean
proof obligation.  The ∃-side needs one substitution instance, the
∀-side a finite family.  They capture exactly the p-variants that are
redecorations of the *same* model; `semAll_em_p` below exhibits a value
that needs a frame-changing variant, so the criteria are provably not
complete. -/

/-- **∃-side certificate criterion**: if `ψ` is p-free, `M ⊢ ψ`, and
`ψ ⊢ M[p:=χ]` for some formula `χ`, then `ψ` is the ∃p-value of `M`. -/
theorem isSemEx_of_certificates {p : String} {M ψ χ : PLLFormula}
    (hp : p ∉ ψ.atoms) (d₁ : LaxND [M] ψ) (d₂ : LaxND [ψ] (substP p χ M)) :
    IsSemEx p M ψ := by
  have hAψ : ∀ a ∈ ψ.atoms, a ≠ p := fun a ha he => hp (he ▸ ha)
  refine ⟨hp, ?_⟩
  intro C w
  constructor
  · intro hw
    have hMχ : C.force w (substP p χ M) := soundness d₂ C w (fun ξ hξ => by
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hw)
    exact ⟨truthDeco C p χ, truthDeco_pbisim C p χ, w, rfl,
      (force_truthDeco C p χ M w).mpr hMχ⟩
  · rintro ⟨N, B, w', hZ, hM'⟩
    have hψ' : N.force w' ψ := soundness d₁ N w' (fun ξ hξ => by
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hM')
    exact (force_iff_of_bisim B hAψ hZ).mpr hψ'

/-- **∀-side certificate criterion**: if `ψ` is p-free, `ψ ⊢ M`, and some
finite family of substitution instances derives it back,
`M[p:=χ₁], …, M[p:=χₖ] ⊢ ψ`, then `ψ` is the ∀p-value of `M`. -/
theorem isSemAll_of_certificates {p : String} {M ψ : PLLFormula}
    {χs : List PLLFormula} (hp : p ∉ ψ.atoms) (d₁ : LaxND [ψ] M)
    (d₂ : LaxND (χs.map (fun χ => substP p χ M)) ψ) :
    IsSemAll p M ψ := by
  have hAψ : ∀ a ∈ ψ.atoms, a ≠ p := fun a ha he => hp (he ▸ ha)
  refine ⟨hp, ?_⟩
  intro C w
  constructor
  · intro hw v hv N B v' hZ
    have hψ' : N.force v' ψ :=
      (force_iff_of_bisim B hAψ hZ).mp (C.force_hered hv hw)
    exact soundness d₁ N v' (fun ξ hξ => by
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hψ')
  · intro h'
    refine soundness d₂ C w ?_
    intro ξ hξ
    obtain ⟨χ, -, rfl⟩ := List.mem_map.mp hξ
    exact (force_truthDeco C p χ M w).mp
      (h' w (C.refl_i w) (truthDeco C p χ) (truthDeco_pbisim C p χ) w rfl)

/-- Substitution instances of a formula interderivable with a p-free `ψ`
force exactly like `ψ` — semantic substitution-admissibility, via the
truth-set decoration; no proof-theoretic substitution lemma is needed. -/
theorem force_subst_iff_of_pfree_equiv {p : String} {M ψ : PLLFormula}
    (hp : p ∉ ψ.atoms) (d₁ : LaxND [M] ψ) (d₂ : LaxND [ψ] M)
    (χ : PLLFormula) (C : ConstraintModel) (w : C.W) :
    C.force w (substP p χ M) ↔ C.force w ψ := by
  have hAψ : ∀ a ∈ ψ.atoms, a ≠ p := fun a ha he => hp (he ▸ ha)
  have hbis := force_iff_of_bisim (truthDeco_pbisim C p χ) hAψ
    (show (truthDeco_pbisim C p χ).Z w w from rfl)
  constructor
  · intro h
    have hM : (truthDeco C p χ).force w M := (force_truthDeco C p χ M w).mpr h
    have hψ : (truthDeco C p χ).force w ψ := soundness d₁ (truthDeco C p χ) w
      (fun ξ hξ => by simp only [List.mem_singleton] at hξ; exact hξ ▸ hM)
    exact hbis.mpr hψ
  · intro h
    have hM : (truthDeco C p χ).force w M := soundness d₂ (truthDeco C p χ) w
      (fun ξ hξ => by simp only [List.mem_singleton] at hξ; exact hξ ▸ hbis.mp h)
    exact (force_truthDeco C p χ M w).mp hM

/-- **Separation criterion for essentiality**: if two substitution
instances of `M` disagree at a single world of a single model, then `M`
is equivalent to no p-free formula. -/
theorem essential_of_separation {p : String} {M χ₁ χ₂ : PLLFormula}
    (C : ConstraintModel) (w : C.W)
    (h₁ : C.force w (substP p χ₁ M)) (h₂ : ¬ C.force w (substP p χ₂ M)) :
    ¬ Inessential p M := by
  rintro ⟨ψ, hp, ⟨d₁⟩, ⟨d₂⟩⟩
  exact h₂ ((force_subst_iff_of_pfree_equiv hp d₁ d₂ χ₂ C w).mpr
    ((force_subst_iff_of_pfree_equiv hp d₁ d₂ χ₁ C w).mp h₁))

/-- Classically, non-derivability yields a countermodel (contrapositive
of `completeness`). -/
theorem exists_countermodel {Γ : List PLLFormula} {φ : PLLFormula}
    (h : ¬ Nonempty (LaxND Γ φ)) :
    ∃ (C : ConstraintModel) (w : C.W),
      (∀ ψ ∈ Γ, C.force w ψ) ∧ ¬ C.force w φ := by
  by_contra hn
  push Not at hn
  exact h (completeness (fun C w hw => hn C w hw))

/-! ## The essential fibre theorems

The fibre construction: for p-free ξ, the formula `ξ ∨ p` has ∀p-value
ξ (one substitution instance, `p := ⊥`, certifies it), and `ξ ∧ p` has
∃p-value ξ (instance `p := ⊤`).  Essentiality comes from separating the
instances `p := ⊤` and `p := ⊥`, at the countermodel that classical
completeness extracts from the value's non-derivability. -/

/-- `∀p.(ξ ∨ p) = ξ` for p-free ξ. -/
theorem semAll_or_p (p : String) {ξ : PLLFormula} (hp : p ∉ ξ.atoms) :
    IsSemAll p (ξ.or (.prop p)) ξ := by
  have hsub : substP p .falsePLL (ξ.or (.prop p)) = ξ.or .falsePLL := by
    simp [substP, substP_of_not_mem hp]
  refine isSemAll_of_certificates (χs := [.falsePLL]) hp
    (.orIntro1 (.iden (List.mem_singleton.mpr rfl))) ?_
  rw [List.map_cons, List.map_nil, hsub]
  exact .orElim (.iden (List.mem_singleton.mpr rfl))
    (.iden (List.mem_cons_self ..))
    (.falsoElim ξ (.iden (List.mem_cons_self ..)))

/-- For underivable p-free ξ, `p` is essential in `ξ ∨ p`: the instances
`p := ⊤` and `p := ⊥` are separated at any countermodel to ξ. -/
theorem essential_or_p (p : String) {ξ : PLLFormula} (hp : p ∉ ξ.atoms)
    (hξ : ¬ Nonempty (LaxND [] ξ)) : ¬ Inessential p (ξ.or (.prop p)) := by
  obtain ⟨C, w, -, hnf⟩ := exists_countermodel hξ
  refine essential_of_separation (χ₁ := truePLL) (χ₂ := .falsePLL) C w ?_ ?_
  · rw [show substP p truePLL (ξ.or (.prop p)) = ξ.or truePLL from by
      simp [substP, substP_of_not_mem hp]]
    exact Or.inr (fun v _ hv => hv)
  · rw [show substP p .falsePLL (ξ.or (.prop p)) = ξ.or .falsePLL from by
      simp [substP, substP_of_not_mem hp]]
    rintro (hξw | hF)
    · exact hnf hξw
    · exact hnf (C.force_of_fallible hF)

/-- `∃p.(ξ ∧ p) = ξ` for p-free ξ. -/
theorem semEx_and_p (p : String) {ξ : PLLFormula} (hp : p ∉ ξ.atoms) :
    IsSemEx p (ξ.and (.prop p)) ξ := by
  have hsub : substP p truePLL (ξ.and (.prop p)) = ξ.and truePLL := by
    simp [substP, substP_of_not_mem hp]
  refine isSemEx_of_certificates (χ := truePLL) hp
    (.andElim1 (.iden (List.mem_singleton.mpr rfl))) ?_
  rw [hsub]
  exact .andIntro (.iden (List.mem_singleton.mpr rfl))
    (.impIntro (.iden (List.mem_cons_self ..)))

/-- For p-free ξ with `ξ ⊬ ⊥`, `p` is essential in `ξ ∧ p`. -/
theorem essential_and_p (p : String) {ξ : PLLFormula} (hp : p ∉ ξ.atoms)
    (hξ : ¬ Nonempty (LaxND [ξ] .falsePLL)) :
    ¬ Inessential p (ξ.and (.prop p)) := by
  obtain ⟨C, w, hfor, hnf⟩ := exists_countermodel hξ
  have hξw : C.force w ξ := hfor ξ (List.mem_singleton.mpr rfl)
  refine essential_of_separation (χ₁ := truePLL) (χ₂ := .falsePLL) C w ?_ ?_
  · rw [show substP p truePLL (ξ.and (.prop p)) = ξ.and truePLL from by
      simp [substP, substP_of_not_mem hp]]
    exact ⟨hξw, fun v _ hv => hv⟩
  · rw [show substP p .falsePLL (ξ.and (.prop p)) = ξ.and .falsePLL from by
      simp [substP, substP_of_not_mem hp]]
    rintro ⟨-, hF⟩
    exact hnf hF

/-- **The essential ∀p-image theorem**: a p-free ξ is the ∀p-value of a
formula in which `p` is essential  iff  ξ is not derivable.  On the
closed fragment: the essential ∀p-image is RN(◯,{}) ∖ {⊤}. -/
theorem essential_semAll_image {p : String} {ξ : PLLFormula}
    (hp : p ∉ ξ.atoms) :
    (∃ M, IsSemAll p M ξ ∧ ¬ Inessential p M) ↔ ¬ Nonempty (LaxND [] ξ) := by
  constructor
  · rintro ⟨M, hall, hess⟩ ⟨d⟩
    exact hess ⟨ξ, hp, ⟨d.rename (by simp)⟩, semAll_lower hall⟩
  · intro hξ
    exact ⟨ξ.or (.prop p), semAll_or_p p hp, essential_or_p p hp hξ⟩

/-- **The essential ∃p-image theorem**: a p-free ξ is the ∃p-value of a
formula in which `p` is essential  iff  `ξ ⊬ ⊥`.  On the closed
fragment: the essential ∃p-image is RN(◯,{}) ∖ {⊥}. -/
theorem essential_semEx_image {p : String} {ξ : PLLFormula}
    (hp : p ∉ ξ.atoms) :
    (∃ M, IsSemEx p M ξ ∧ ¬ Inessential p M) ↔
      ¬ Nonempty (LaxND [ξ] .falsePLL) := by
  constructor
  · rintro ⟨M, hex, hess⟩ ⟨d⟩
    exact hess ⟨ξ, hp, semEx_upper hex, ⟨.falsoElim M d⟩⟩
  · intro hξ
    exact ⟨ξ.and (.prop p), semEx_and_p p hp, essential_and_p p hp hξ⟩

/-! ## Beyond redecoration: the doubled model, and `∀p.(p ∨ ¬p) = ⊥`

Redecorating the SAME frame realises exactly the substitution instances
`M[p:=χ]`; the spec's p-variants are richer.  The *doubling* below —
two copies of the model stacked along the 2-chain, the projection a
total p-bisimulation — is the first genuinely frame-changing variant:
decorating `p` on the upper copy only refutes `p ∨ ¬p` at every
non-fallible world.  Together with `em_p_no_certificate` (every
substitution instance of `p ∨ ¬p` is an excluded-middle instance, forced
at the one-world classical model) this shows `∀p.(p ∨ ¬p) = ⊥` is a
quantifier value the certificate criteria provably cannot reach. -/

/-- The doubled model: worlds `W × Bool`, both relations required to be
monotone into the upper copy, fallibility and valuation inherited from
the first coordinate. -/
def double (C : ConstraintModel) : ConstraintModel where
  W := C.W × Bool
  Ri := fun a b => C.Ri a.1 b.1 ∧ (a.2 = true → b.2 = true)
  Rm := fun a b => C.Rm a.1 b.1 ∧ (a.2 = true → b.2 = true)
  F := {a | a.1 ∈ C.F}
  V := fun q => {a | a.1 ∈ C.V q}
  refl_i := fun a => ⟨C.refl_i a.1, fun h => h⟩
  trans_i := fun h₁ h₂ => ⟨C.trans_i h₁.1 h₂.1, fun h => h₂.2 (h₁.2 h)⟩
  refl_m := fun a => ⟨C.refl_m a.1, fun h => h⟩
  trans_m := fun h₁ h₂ => ⟨C.trans_m h₁.1 h₂.1, fun h => h₂.2 (h₁.2 h)⟩
  sub_mi := fun h => ⟨C.sub_mi h.1, h.2⟩
  hered_F := fun h hw => C.hered_F h.1 hw
  hered_V := fun h hw => C.hered_V h.1 hw
  full_F := fun hw => C.full_F hw

/-- The upper-copy decoration over `w₀`: the upper copy of the cone over
`w₀`, plus the fallible worlds. -/
def emSet (C : ConstraintModel) (w₀ : C.W) : Set (C.W × Bool) :=
  {a | (a.2 = true ∧ C.Ri w₀ a.1) ∨ a.1 ∈ C.F}

/-- The doubled model with `p` decorated on the upper copy over `w₀`. -/
def emVariant (C : ConstraintModel) (p : String) (w₀ : C.W) :
    ConstraintModel :=
  redecorate (double C) p (emSet C w₀)
    (by rintro a b hab (⟨h2, hw⟩ | hF)
        · exact Or.inl ⟨hab.2 h2, C.trans_i hw hab.1⟩
        · exact Or.inr (C.hered_F hab.1 hF))
    (fun hF => Or.inr hF)

/-- Projection to the first coordinate is a p-bisimulation onto the
decorated double: each `(x, i)` is a p-variant of `x`. -/
def emVariant_pbisim (C : ConstraintModel) (p : String) (w₀ : C.W) :
    PBisim p C (emVariant C p w₀) where
  Z := fun x a => a.1 = x
  atoms := by
    rintro x a rfl q hq
    show a.1 ∈ C.V q ↔ a ∈ (if q = p then emSet C w₀ else (double C).V q)
    rw [if_neg hq]
    exact Iff.rfl
  fall := by rintro x a rfl; exact Iff.rfl
  iforth := by
    rintro x a rfl v hv
    exact ⟨(v, a.2), ⟨hv, fun h => h⟩, rfl⟩
  iback := by
    rintro x a rfl v' hv'
    exact ⟨v'.1, hv'.1, rfl⟩
  mforth := by
    rintro x a rfl u hu
    exact ⟨(u, a.2), ⟨hu, fun h => h⟩, rfl⟩
  mback := by
    rintro x a rfl u' hu'
    exact ⟨u'.1, hu'.1, rfl⟩

/-- **`∀p.(p ∨ ¬p) = ⊥`** — the first quantifier value requiring a
frame-changing p-variant.  A non-fallible world of the lower copy
forces neither `p` (it is not in the decoration) nor `¬p` (its upper
twin is), so only fallible worlds survive the spec. -/
theorem semAll_em_p (p : String) :
    IsSemAll p ((PLLFormula.prop p).or ((PLLFormula.prop p).ifThen .falsePLL))
      .falsePLL := by
  refine ⟨by simp, ?_⟩
  intro C w
  constructor
  · intro hw v hv N B v' hZ
    exact N.force_of_fallible ((B.fall hZ).mp (C.hered_F hv hw))
  · intro h'
    have hforce := h' w (C.refl_i w) (emVariant C p w) (emVariant_pbisim C p w)
      (w, false) rfl
    rcases hforce with hmem | hnp
    · have hmem' : (w, false) ∈ emSet C w := by
        have h0 : (w, false) ∈ (if p = p then emSet C w else (double C).V p) :=
          hmem
        rwa [if_pos rfl] at h0
      rcases hmem' with ⟨h2, -⟩ | hF
      · exact (Bool.false_ne_true h2).elim
      · exact hF
    · have hup : (emVariant C p w).Ri (w, false) (w, true) :=
        ⟨C.refl_i w, fun _ => rfl⟩
      have hptop : (emVariant C p w).force (w, true) (.prop p) := by
        show (w, true) ∈ (if p = p then emSet C w else (double C).V p)
        rw [if_pos rfl]
        exact Or.inl ⟨rfl, C.refl_i w⟩
      exact hnp (w, true) hup hptop

/-- At the one-world irrefutable model, excluded middle holds for every
formula (classically). -/
theorem oneW_em (A : PLLFormula) :
    oneW.force () (A.or (A.ifThen .falsePLL)) := by
  by_cases h : oneW.force () A
  · exact Or.inl h
  · refine Or.inr ?_
    intro v _ hv
    cases v
    exact (h hv).elim

/-- **No substitution certificate reaches `∀p.(p ∨ ¬p)`**: every
substitution instance of `p ∨ ¬p` is an excluded-middle instance, forced
at the one-world model, so no finite family of instances derives ⊥.
The ∀-criterion provably cannot establish `semAll_em_p`: the doubling
is necessary. -/
theorem em_p_no_certificate (p : String) (χs : List PLLFormula) :
    ¬ Nonempty (LaxND (χs.map (fun χ =>
        substP p χ
          ((PLLFormula.prop p).or ((PLLFormula.prop p).ifThen .falsePLL))))
      .falsePLL) := by
  rintro ⟨d⟩
  have hval := soundness d oneW () (fun ξ hξ => by
    obtain ⟨χ, -, rfl⟩ := List.mem_map.mp hξ
    rw [show substP p χ
        ((PLLFormula.prop p).or ((PLLFormula.prop p).ifThen .falsePLL))
        = χ.or (χ.ifThen .falsePLL) from by simp [substP]]
    exact oneW_em χ)
  exact hval

/-! ## Concrete fibre data

The conjecture's data points, now instances of the image theorems.  Two
underivability facts feed them: `⊬ ◯⊥` (countermodel `oneW`) and
`⊬ ¬◯⊥` (countermodel: the two-element chain with fallible top, where
◯⊥ holds at the non-fallible root).  With these:

    ⊥   = ∀p.(⊥ ∨ p)  = ∀p.p     (p essential)
    ◯⊥  = ∀p.(◯⊥ ∨ p) = ∀p.◯p    (p essential)
    ¬◯⊥ = ∀p.(¬◯⊥ ∨ p)           (p essential)

and dually on the ∃-side every closed ξ ≢ ⊥ is an essential ∃p-value. -/

/-- The two-element chain with fallible top: `◯⊥` holds at the
non-fallible root (the constraint relation reaches the fallible top). -/
def twoChain : ConstraintModel where
  W := Bool
  Ri := fun x y => x = true → y = true
  Rm := fun x y => x = true → y = true
  F := {x | x = true}
  V := fun _ => {x | x = true}
  refl_i := fun _ h => h
  trans_i := fun h₁ h₂ h => h₂ (h₁ h)
  refl_m := fun _ h => h
  trans_m := fun h₁ h₂ h => h₂ (h₁ h)
  sub_mi := fun h => h
  hered_F := fun h hw => h hw
  hered_V := fun h hw => h hw
  full_F := fun hw => hw

/-- `⊬ ◯⊥`: at the one-world irrefutable model, no constraint witness is
fallible. -/
theorem not_derivable_boxFalse :
    ¬ Nonempty (LaxND [] PLLFormula.falsePLL.somehow) := by
  rintro ⟨d⟩
  obtain ⟨u, -, hu⟩ := soundness d oneW () (by simp) () (oneW.refl_i ())
  exact hu

/-- `⊬ ¬◯⊥`: at the root of `twoChain`, `◯⊥` holds non-fallibly. -/
theorem not_derivable_neg_boxFalse :
    ¬ Nonempty (LaxND [] (PLLFormula.falsePLL.somehow.ifThen .falsePLL)) := by
  rintro ⟨d⟩
  have hval := soundness d twoChain false (by simp) false (fun h => h)
  have hbox : twoChain.force false PLLFormula.falsePLL.somehow := by
    intro v _
    exact ⟨true, fun _ => rfl, rfl⟩
  exact Bool.false_ne_true (hval hbox)

/-- `◯⊥` is an essential ∀p-value: `∀p.(◯⊥ ∨ p) = ◯⊥` with `p`
essential. -/
theorem essential_fibre_boxFalse (p : String) :
    ∃ M, IsSemAll p M PLLFormula.falsePLL.somehow ∧ ¬ Inessential p M :=
  (essential_semAll_image (by simp)).mpr not_derivable_boxFalse

/-- `¬◯⊥` is an essential ∀p-value: `∀p.(¬◯⊥ ∨ p) = ¬◯⊥` with `p`
essential. -/
theorem essential_fibre_neg_boxFalse (p : String) :
    ∃ M, IsSemAll p M (PLLFormula.falsePLL.somehow.ifThen .falsePLL) ∧
      ¬ Inessential p M :=
  (essential_semAll_image (by simp)).mpr not_derivable_neg_boxFalse

/-- `p` is essential in `p` itself: the instances `⊤` and `⊥` are
separated at the one-world model. -/
theorem essential_prop_self (p : String) :
    ¬ Inessential p (.prop p) := by
  refine essential_of_separation (χ₁ := truePLL) (χ₂ := .falsePLL) oneW () ?_ ?_
  · show oneW.force () (if p = p then truePLL else .prop p)
    rw [if_pos rfl]
    exact fun v _ hv => hv
  · show ¬ oneW.force () (if p = p then .falsePLL else .prop p)
    rw [if_pos rfl]
    exact fun h => h

/-- `p` is essential in `◯p`: the instances `◯⊤` and `◯⊥` are separated
at the one-world model.  With `semAll_box_p`, the original data point
`∀p.◯p = ◯⊥` is essential in full. -/
theorem essential_box_p (p : String) :
    ¬ Inessential p (PLLFormula.prop p).somehow := by
  refine essential_of_separation (χ₁ := truePLL) (χ₂ := .falsePLL) oneW () ?_ ?_
  · show oneW.force () ((if p = p then truePLL else PLLFormula.prop p).somehow)
    rw [if_pos rfl]
    intro v _
    exact ⟨v, oneW.refl_m v, fun u _ hu => hu⟩
  · show ¬ oneW.force () ((if p = p then .falsePLL else PLLFormula.prop p).somehow)
    rw [if_pos rfl]
    intro h
    obtain ⟨u, -, hu⟩ := h () (oneW.refl_i ())
    exact hu

end SemUI
end PLLND
