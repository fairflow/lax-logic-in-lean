import wip.bandStabilise

/-!
# The m-clauses: the infallible collapse, and the positive half

Branch `ui-confluence`.  Two results locating the m-clause difficulty
exactly at fallibility-grading (Matthew's observation, 2026-07-26: over
infallible models `◯⊥ ≡ ⊥` and RN(◯,{}) collapses to `{⊥, ⊤}`, so no
uniform-interpolation argument there can depend on tower structure).

1. `infallible_amalgamation` (PROVED, UNCONDITIONAL): between p-pure
   INFALLIBLE models the total link is a lawful `LayeredBisimE` — all
   eight clauses, the two m-clauses included, hold trivially — so the
   full one-variable amalgamation drops out with no agreement
   hypothesis at all.  This is the semantic form of the RN(◯,{})
   collapse under `¬◯⊥`: over infallible p-pure models, every
   variable-free formula is pointwise constant, p-blind bisimilarity
   says nothing, and any realisable p-theory rides any base model.  It
   is also a constructive non-vacuity certificate for the whole
   amalgamation tower (`witTripleC` → `stabilise` → `bandStabilise`):
   the machinery applies outright somewhere.

2. `band_mforth_positive` (PROVED): in the general fallible case, the
   POSITIVE half of the banded m-forth clause — an `Rₘ`-move `k ⟶ u`
   is answered by `m ⟶Rₘ u′` with `u′` forcing EVERY variable-free
   formula of crank ≤ α that `u` forces — by the character argument:
   `u` witnesses `◯(charPos u)` at `k` (bare possibility in K), the box
   crosses the link at rank `α + 3 ≤ R`, and bare possibility in M
   produces the witness.  What is NOT delivered is the negative half
   (`u′` may overshoot); that residue is the entire remaining content
   of `BandMforth`/`BandMback`, and by result 1 it is a phenomenon of
   fallible models only.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-! ## 1. The infallible collapse -/

/-- No fallible worlds. -/
def FFree (C : ConstraintModel) : Prop := ∀ w : C.W, w ∉ C.F

/-- **The total link**: between p-pure infallible models, the constant
total family satisfies every clause of `LayeredBisimE` — the m-clauses
answer every move reflexively.  The m-clause difficulty is a
fallibility phenomenon. -/
def totalB (hPK : PPure p K) (hPM : PPure p M)
    (hFK : FFree K) (hFM : FFree M) :
    LayeredBisimWit (fun a => a ≠ p) K M where
  Z := fun _ _ _ => True
  mono := fun _ => trivial
  atoms := by
    intro n k m _ a ha
    exact iff_of_false (hPK a ha k) (hPM a ha m)
  fall := by
    intro n k m _
    exact iff_of_false (hFK k) (hFM m)
  iforth := by
    intro n k m _ v _
    exact .inl ⟨m, M.refl_i m, trivial⟩
  iback := by
    intro n k m _ v' _
    exact .inl ⟨k, K.refl_i k, trivial⟩
  mwit := by
    intro n k m _ ψ hex
    obtain ⟨κ, hkκ, hκψ⟩ := hex
    exact ⟨κ, m, hkκ, hκψ, M.refl_m m, .inl trivial⟩
  mback := by
    intro n k m _ u' _
    exact ⟨k, K.refl_m k, .inl trivial⟩

/-- **The unconditional infallible amalgamation**: between p-pure
infallible models (K mutually confluent), the full p-variant conclusion
holds with NO agreement hypothesis — the semantic image of
RN(◯,{}) ≡ {⊥, ⊤} under `¬◯⊥`. -/
theorem infallible_amalgamation (cl : Finset PLLFormula)
    (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hPK : PPure p K) (hPM : PPure p M)
    (hFK : FFree K) (hFM : FFree M) (k₀ : K.W) (m₀ : M.W) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) :=
  amalgamation_assembledC cl (totalB hPK hPM hFK hFM) hcl hadeq hK
    (mforthResidue_of_stabilised cl (totalB hPK hPM hFK hFM) (fun h => h))
    k₀ m₀ trivial

/-! ## 2. The positive half of the banded m-clause -/

/-- **The m-forth clause, positive half** (general fallible case): over
mutually confluent `K` and `M`, an `Rₘ`-move `k ⟶ u` is answered by
`m ⟶Rₘ u′` preserving every variable-free formula of crank ≤ α that
`u` forces, provided the band floor covers the boxed positive
character (`α + 3 ≤ R`).  The proof: `u` forces its positive character
over the rank-α representatives (`force_charPos`); bare possibility in
`K` puts `◯(charPos u)` at `k`; the band link transfers it; bare
possibility in `M` produces the witness; `force_bigAnd_iff` unpacks it
on representatives, and interderivability carries it to every rank-α
formula.  The NEGATIVE half — that `u′` need not overshoot — is the
open remainder of `BandMforth`. -/
theorem band_mforth_positive {R α : Nat}
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hcr : α + 3 ≤ R)
    {k : K.W} {m : M.W} (hZ : bandAgree R K M k m)
    {u : K.W} (hu : K.Rm k u) :
    ∃ u', M.Rm m u' ∧ ∀ ρ : PLLFormula, ρ.atoms = ∅ → crank ρ ≤ α →
      K.force u ρ → M.force u' ρ := by
  classical
  obtain ⟨L, hL, hrep⟩ := frag_reps_exist' (∅ : Finset String) α
  set χ : PLLFormula := charPos K u L with hχ
  have hχatoms : χ.atoms = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => ?_)
    exact Finset.notMem_empty a
      (atoms_charPos (fun D hD => (hL D hD).2) a ha)
  have hχcrank : crank χ ≤ α + 1 :=
    crank_charPos_le (fun D hD => (hL D hD).1)
  -- k forces ◯χ: u is the bare-possibility witness
  have hkbox : K.force k (PLLFormula.somehow χ) := by
    rw [force_somehow_iff_of_confluent hK]
    exact ⟨u, hu, force_charPos K u L⟩
  -- the box crosses the band link
  have hmbox : M.force m (PLLFormula.somehow χ) := by
    refine (hZ (PLLFormula.somehow χ) ?_ ?_).mp hkbox
    · show χ.atoms = ∅
      exact hχatoms
    · show crank χ + 2 ≤ R
      omega
  -- bare possibility in M produces the witness
  rw [force_somehow_iff_of_confluent hM] at hmbox
  obtain ⟨u', hmu', hχu'⟩ := hmbox
  refine ⟨u', hmu', fun ρ hρa hρc hρu => ?_⟩
  -- collapse ρ to a representative D forced by u
  obtain ⟨D, hDL, hd₁, hd₂⟩ := hrep ρ hρc
    (fun a ha => by rw [hρa] at ha; exact absurd ha (Finset.notMem_empty a))
  have hInterd : Interd ρ D := ⟨hd₁, hd₂⟩
  have hDu : K.force u D := (interd_force_iff hInterd K u).mp hρu
  -- D is in the character's conjunction, so u′ forces it
  have hDu' : M.force u' D := by
    have := (force_bigAnd_iff M u' _).mp hχu'
    exact this D (List.mem_filter.mpr ⟨hDL, decide_eq_true hDu⟩)
  exact (interd_force_iff hInterd M u').mpr hDu'

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.infallible_amalgamation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms infallible_amalgamation

/--
info: 'PLLND.SemUI.band_mforth_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms band_mforth_positive

end SemUI
end PLLND
