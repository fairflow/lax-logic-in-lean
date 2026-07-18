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

end SemUI
end PLLND
