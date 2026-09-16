/-
# The cube embedding — a theorem of distributive-lattice algebra

In any distributive lattice (with `⊥`, used only to form finite
suprema), if `U` is a finite set of covers of `n`, then

    S ⊆ U  ⟼  n ⊔ ⋁S

is an order-embedding of the Boolean lattice `2^U`.

The proof is the interval collapse: for a cover `n ⋖ y` and any `t` with
`n ≤ t`, the meet `y ⊓ t` lies in the two-element interval `[n, y]`, so
it is `n` or `y` — and `y ⊓ t = y` forces `y = t` when `t` is itself a
cover.  Distributing `y` over `n ⊔ ⋁T` then leaves no room: either some
disjunct equals `y` (so `y ∈ T`) or all equal `n` (so `y = n`,
contradicting strictness).

No conditions on `n` and none on the covers beyond finiteness.  This is
the algebraic home of the ρ-catalogue's cube patterns: once a set of
GENUINE fragment covers over a node is certified, the Boolean cube above
that node is free — the entire empirical content relocates to the
per-edge question "is this scoped cover a genuine cover?".
-/
import Mathlib.Order.Cover
import Mathlib.Data.Finset.Lattice.Fold

namespace CubeEmbedding

variable {α : Type*} [DistribLattice α] [OrderBot α]

omit [OrderBot α] in
/-- Distinct covers of the same element are incomparable. -/
theorem eq_of_covBy_of_covBy_of_le {n y t : α} (hy : n ⋖ y) (ht : n ⋖ t)
    (hle : y ≤ t) : y = t := by
  rcases ht.eq_or_eq hy.lt.le hle with h | h
  · exact absurd h hy.lt.ne'
  · exact h

/-- The cube map: `S ⟼ n ⊔ ⋁S`. -/
def cube (n : α) (S : Finset α) : α := n ⊔ S.sup id

theorem le_cube (n : α) (S : Finset α) : n ≤ cube n S := le_sup_left

theorem mem_le_cube {n y : α} {S : Finset α} (hy : y ∈ S) : y ≤ cube n S :=
  le_sup_of_le_right (Finset.le_sup (f := id) hy)

theorem cube_mono {n : α} {S T : Finset α} (h : S ⊆ T) : cube n S ≤ cube n T :=
  sup_le_sup_left (Finset.sup_mono h) n

/-- The reflection half: a cover below `n ⊔ ⋁T` is a member of `T`. -/
theorem mem_of_le_cube {n : α} {U T : Finset α} (hcov : ∀ y ∈ U, n ⋖ y)
    (hT : T ⊆ U) {y : α} (hyU : y ∈ U) (hy : y ≤ cube n T) : y ∈ T := by
  have hcy := hcov y hyU
  -- distribute `y` over `n ⊔ ⋁T`
  have hy_eq : y = (y ⊓ n) ⊔ T.sup fun t => y ⊓ t := by
    conv_lhs => rw [← inf_eq_left.mpr hy]
    rw [cube, inf_sup_left, Finset.sup_inf_distrib_left]
    simp only [id]
  by_cases hex : ∃ t ∈ T, y ≤ t
  · obtain ⟨t, htT, hyt⟩ := hex
    exact eq_of_covBy_of_covBy_of_le hcy (hcov t (hT htT)) hyt ▸ htT
  · push Not at hex
    -- every disjunct collapses to `n`, so `y ≤ n`, contradicting `n ⋖ y`
    exfalso
    have hsup : (T.sup fun t => y ⊓ t) ≤ n := by
      refine Finset.sup_le fun t htT => ?_
      rcases hcy.eq_or_eq (le_inf hcy.lt.le (hcov t (hT htT)).lt.le)
        inf_le_left with h | h
      · exact h.le
      · exact absurd (h ▸ inf_le_right) (hex t htT)
    exact hcy.lt.not_ge <| hy_eq ▸ sup_le inf_le_right hsup

/-- **The cube embedding** (order form).  For `U` a finite set of covers
of `n` and `S, T ⊆ U`:

    n ⊔ ⋁S ≤ n ⊔ ⋁T  ⟺  S ⊆ T

so `S ⟼ n ⊔ ⋁S` order-embeds `2^U`. -/
theorem cube_le_iff {n : α} {U : Finset α} (hcov : ∀ y ∈ U, n ⋖ y)
    {S T : Finset α} (hS : S ⊆ U) (hT : T ⊆ U) :
    cube n S ≤ cube n T ↔ S ⊆ T := by
  constructor
  · intro h y hyS
    exact mem_of_le_cube hcov hT (hS hyS) ((mem_le_cube hyS).trans h)
  · exact cube_mono

/-- Injectivity: distinct subsets of `U` give distinct cube points. -/
theorem cube_inj {n : α} {U : Finset α} (hcov : ∀ y ∈ U, n ⋖ y)
    {S T : Finset α} (hS : S ⊆ U) (hT : T ⊆ U)
    (h : cube n S = cube n T) : S = T :=
  Finset.Subset.antisymm
    ((cube_le_iff hcov hS hT).mp h.le)
    ((cube_le_iff hcov hT hS).mp h.ge)

end CubeEmbedding

/-! ## Pins -/

/-- info: 'CubeEmbedding.cube_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CubeEmbedding.cube_le_iff

/-- info: 'CubeEmbedding.cube_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CubeEmbedding.cube_inj
