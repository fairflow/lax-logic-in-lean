import LaxLogic.PLLSemUILayered

/-!
# The witnessing-triple amalgam for PLL (Lemma 5.4 scaffold)

The PLL form of the Litak–Visser/Visser amalgamation construction,
with the finite canonical model `canonFin cl` in the role of the
pre-Henkin model.  Everything structural is PROVED here — the depth
function and its strict drop, the witnessing triples, the amalgam
model with all frame legality, the assembly of the amalgamation
theorem from its two claims, with the root pair admissible and
forcing at the root converted through the descriptions functor.  The
two claims that carry the mathematics are stated as named `sorry`s:

* `wit_pbisim` (their Claim 1): the projection ⟨Δ, m⟩ ↦ m is an
  unbounded bisimulation off p — the zigzags maintain witnessing
  triples by the two-case budget argument (same theory: reuse the
  triple, transported along the move; strictly larger theory: the
  depth drops, so the spare budget 2·d(Δ′)+1 ≤ 2·d(Δ)−1 finances a
  fresh triple).  The Henkin-side moves are supplied by the PROVED
  functor clauses `trace_iforth` and `trace_mforth` — the promise
  component moves along Rₘ exactly as required.
* `wit_force` (their Claim 2): a pair forces φ ∈ cl iff φ ∈ Δ.val —
  induction on the adequate set with the same budget bookkeeping; the
  ⊃-case spends one i-zigzag, the ◯-case an i-zigzag and an m-zigzag
  (hence ◯'s crank of 2); fallible escapes absorb as in
  `descGraft_force_iff`.

Budget calibration: depth is measured by missing `val`-cardinality
(`canonDepth`), so the entry budget is `2·cl.card + 1` — coarser than
Litak–Visser's count of variables/implications/arrows, sound for the
same reason (every strict theory-extension adds a closure formula to
`val`).
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp

/-! ## Depth in the finite canonical model -/

/-- Depth of a canonical theory: how many closure formulas its `val`
is still missing.  The budget financier: strict extensions strictly
drop it. -/
def canonDepth (cl : Finset PLLFormula) (T : (canonFin cl).W) : Nat :=
  cl.card - T.1.val.card

theorem canonDepth_le (cl : Finset PLLFormula) (T : (canonFin cl).W) :
    canonDepth cl T ≤ cl.card :=
  Nat.sub_le _ _

/-- **Strict extensions strictly drop the depth**: a proper
`val`-inclusion between canonical theories loses at least one unit of
budget. -/
theorem canonDepth_lt {cl : Finset PLLFormula} {T T' : (canonFin cl).W}
    (hsub : T.1.val ⊆ T'.1.val) (hne : T.1.val ≠ T'.1.val) :
    canonDepth cl T' < canonDepth cl T := by
  have hlt : T.1.val.card < T'.1.val.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hle : T'.1.val.card ≤ cl.card :=
    Finset.card_le_card T'.2.2.1.1
  unfold canonDepth
  omega

/-! ## Witnessing triples -/

variable {p : String} {K M : ConstraintModel}

/-- **Witnessing triple** for a pair ⟨Δ, m⟩ (Litak–Visser Lemma 5.4):
worlds k′ ≼ k of K both describing Δ, a shadow m′ ≼ m, with the
layered links k′ Z_{2d+1} m′ and k Z_{2d} m, d the canonical depth of
Δ. -/
structure WitTriple (cl : Finset PLLFormula)
    (B : LayeredBisim (fun a => a ≠ p) K M)
    (Δ : (canonFin cl).W) (m : M.W) where
  k' : K.W
  k : K.W
  m' : M.W
  hΔk : (traceT K cl k) = Δ.1
  hΔk' : (traceT K cl k') = Δ.1
  hik : K.Ri k' k
  him : M.Ri m' m
  hZ' : B.Z (2 * canonDepth cl Δ + 1) k' m'
  hZ : B.Z (2 * canonDepth cl Δ) k m

/-! ## The amalgam model -/

variable (cl : Finset PLLFormula) (B : LayeredBisim (fun a => a ≠ p) K M)

/-- The amalgam: admissible pairs ⟨Δ, m⟩, relations componentwise
(the canonical side carries the promise-aware `Rₘ`).  Valuation in
the `descGraft` discipline rather than Litak–Visser's union clause:
atoms other than `p` and fallibility read the M-COORDINATE (the
canonical model forces every out-of-closure atom — the filtration
convention — so a union valuation would break the p-variant claim on
untracked atoms); `p` reads the theory coordinate, with the
M-fallibility disjunct restoring fullness on F. -/
def witAmalgam : ConstraintModel where
  W := {q : (canonFin cl).W × M.W // Nonempty (WitTriple cl B q.1 q.2)}
  Ri := fun a b => (canonFin cl).Ri a.1.1 b.1.1 ∧ M.Ri a.1.2 b.1.2
  Rm := fun a b => (canonFin cl).Rm a.1.1 b.1.1 ∧ M.Rm a.1.2 b.1.2
  F := fun a => a.1.2 ∈ M.F
  V := fun x a =>
    if x = p then a.1.1 ∈ (canonFin cl).V x ∨ a.1.2 ∈ M.F
    else a.1.2 ∈ M.V x
  refl_i := fun a => ⟨(canonFin cl).refl_i _, M.refl_i _⟩
  trans_i := fun h₁ h₂ =>
    ⟨(canonFin cl).trans_i h₁.1 h₂.1, M.trans_i h₁.2 h₂.2⟩
  refl_m := fun a => ⟨(canonFin cl).refl_m _, M.refl_m _⟩
  trans_m := fun h₁ h₂ =>
    ⟨(canonFin cl).trans_m h₁.1 h₂.1, M.trans_m h₁.2 h₂.2⟩
  sub_mi := fun h => ⟨(canonFin cl).sub_mi h.1, M.sub_mi h.2⟩
  hered_F := fun h hF => M.hered_F h.2 hF
  hered_V := by
    intro x a b h hv
    have hv' : (if x = p then a.1.1 ∈ (canonFin cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x) := hv
    show (if x = p then b.1.1 ∈ (canonFin cl).V x ∨ b.1.2 ∈ M.F
        else b.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx] at hv' ⊢
      rcases hv' with hΔ | hm
      · exact Or.inl ((canonFin cl).hered_V h.1 hΔ)
      · exact Or.inr (M.hered_F h.2 hm)
    · rw [if_neg hx] at hv' ⊢
      exact M.hered_V h.2 hv'
  full_F := by
    intro x a hF
    show (if x = p then a.1.1 ∈ (canonFin cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx]
      exact Or.inr hF
    · rw [if_neg hx]
      exact M.full_F hF

/-! ## The two claims (the open mathematics) -/

/-- **Claim 1 (their proof of Lemma 5.4; OPEN)**: the projection to
the M-coordinate is an unbounded bisimulation off p — the amalgam is
a p-variant of M.  Proof shape: Z := graph of the projection; zig is
componentwise; zag maintains a witnessing triple for the moved pair
by the two-case budget argument, with the Henkin-side move supplied
by `trace_iforth` (Rᵢ) resp. `trace_mforth` (Rₘ, promises included)
and the depth drop `canonDepth_lt` paying for the fresh triple in the
strictly-up case.  Atoms off p: for a ≠ p tracked in the pair, the
theory coordinate and the M-coordinate agree through the triple's
links (their displayed "Δ ⊩ p ⇔ k ⊩ p ⇔ m ⊩ p"); fallibility: the
links match fallibility at every level. -/
theorem wit_pbisim :
    ∃ C : PBisim p M (witAmalgam cl B),
      ∀ (q : (witAmalgam cl B).W), C.Z q.1.2 q := by
  sorry

/-- **Claim 2 (their proof of Lemma 5.4; OPEN)**: a pair forces a
closure formula iff its theory coordinate contains it.  Induction on
the adequate set; ⊃ spends one i-zigzag, ◯ an i-zigzag and an
m-zigzag; the truth-lemma infrastructure of `canonFin` bridges
membership and canonical forcing; fallible escapes absorb as in
`descGraft_force_iff`. -/
theorem wit_force (hcl : SubClosed cl) :
    ∀ (q : (witAmalgam cl B).W) (φ : PLLFormula), φ ∈ cl →
      ((witAmalgam cl B).force q φ ↔ φ ∈ q.1.1.1.val) := by
  sorry

/-! ## The assembly (PROVED modulo the claims) -/

/-- **The amalgamation theorem, assembled**: from a layered link of
budget `2·cl.card + 1` between k₀ and m₀, a p-variant of M whose
distinguished world agrees with k₀ on the whole closure.  The root
pair is ⟨description of k₀, m₀⟩, admissible by the degenerate
witnessing triple (k₀, k₀, m₀) after stepping the budget down to the
root theory's depth; forcing at the root converts through the
descriptions functor. -/
theorem amalgamation_assembled (hcl : SubClosed cl)
    (k₀ : K.W) (m₀ : M.W)
    (hB : B.Z (2 * cl.card + 1) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) := by
  classical
  -- the root theory and its admissibility
  set Δ₀ : (canonFin cl).W := trace K cl k₀ with hΔ₀
  have hbudget : 2 * canonDepth cl Δ₀ + 1 ≤ 2 * cl.card + 1 := by
    have := canonDepth_le cl Δ₀; omega
  have htrip : Nonempty (WitTriple cl B Δ₀ m₀) := by
    refine ⟨⟨k₀, k₀, m₀, rfl, rfl, K.refl_i _, M.refl_i _, ?_, ?_⟩⟩
    · exact B.mono_le hbudget hB
    · exact B.mono_le (by omega) hB
  obtain ⟨C, hC⟩ := wit_pbisim cl B
  refine ⟨witAmalgam cl B, C, ⟨(Δ₀, m₀), htrip⟩,
    hC ⟨(Δ₀, m₀), htrip⟩, ?_⟩
  intro φ hφ
  rw [wit_force cl B hcl _ φ hφ]
  -- membership in the root theory is forcing at k₀, by the functor
  constructor
  · intro h
    exact (mem_traceT_val.mp h).2
  · intro h
    exact mem_traceT_val.mpr ⟨hφ, h⟩

/-! ## Axiom audit (assembly only; the claims are sorried) -/

/--
info: 'PLLND.SemUI.canonDepth_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms canonDepth_lt

end SemUI
end PLLND
