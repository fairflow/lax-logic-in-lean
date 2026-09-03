/-
THE HEIGHT MEASURE — what T2's induction runs on.

FRJ's completeness proof (Lemma 4) inducts on `h(α)`, the height of a
world.  Two adaptations, both deliberate:

* **The measure is the UP-SET CARDINALITY**, `|{z | w Rᵢ z ∧ w ≠ z}|`,
  not the longest ascending path.  The two differ in value; they agree
  in everything the induction uses, namely that a strict `Rᵢ`-step
  strictly decreases them.  Cardinality is a `Set.ncard`, so the
  decrease is a proper-subset argument and no well-founded recursion
  is needed to DEFINE it.
* **Reducedness is exactly the hypothesis.**  It is not a convenience:
  `lean_exe t2screen` §A′ measures it — on all 2,588 reduced models of
  the ≤3-world battery the decrease holds, and on all 1,826
  NON-reduced ones it FAILS, smallest certificate the two-world
  `Rᵢ`-cycle `{n := 2, ri := [(0,1),(1,0)]}`.  So this is the second
  place reducedness is load-bearing, exactly as docs/frj-lifting.md §5
  predicted (the first being the unary arity of the ◯-rule).

`height_induction` is the form T2 consumes: to prove `P` everywhere it
suffices to prove `P w` from `P` at every world STRICTLY above `w`.
-/
import Reject.Join
import Mathlib.Data.Set.Card
import Mathlib

namespace Reject

open PLLND

variable {N : ConstraintModel}

/-! ## 1. The measure -/

/-- The worlds STRICTLY above `x`. -/
def upSet (N : ConstraintModel) (x : N.W) : Set N.W := {z | N.Ri x z ∧ x ≠ z}

/-- **The height of a world**: how many worlds lie strictly above it. -/
noncomputable def height (N : ConstraintModel) (x : N.W) : Nat :=
  (upSet N x).ncard

/-- A strict `Rᵢ`-step shrinks the up-set PROPERLY.  Reducedness is
used exactly once, to rule out `z = x` in the inclusion. -/
theorem upSet_ssubset (hr : Reduced N) {x y : N.W}
    (hxy : N.Ri x y) (hne : x ≠ y) : upSet N y ⊂ upSet N x := by
  refine ⟨fun z hz => ⟨N.trans_i hxy hz.1, ?_⟩, fun hsub => ?_⟩
  · intro hxz
    subst hxz
    exact hne (hr hxy hz.1)
  · exact absurd rfl (hsub ⟨hxy, hne⟩).2

/-- **The measure decreases along a strict `Rᵢ`-step.** -/
theorem height_lt_of_ri [Finite N.W] (hr : Reduced N) {x y : N.W}
    (hxy : N.Ri x y) (hne : x ≠ y) : height N y < height N x :=
  Set.ncard_lt_ncard (upSet_ssubset hr hxy hne) (Set.toFinite _)

/-- **And along a strict `Rₘ`-step**, since `Rₘ ⊆ Rᵢ`.  This is the
clause that would fail without reducedness: an `Rₘ`-successor could be
`Rᵢ`-equivalent to its source and the measure would stall. -/
theorem height_lt_of_rm [Finite N.W] (hr : Reduced N) {x y : N.W}
    (hxy : N.Rm x y) (hne : x ≠ y) : height N y < height N x :=
  height_lt_of_ri hr (N.sub_mi hxy) hne

/-- **The induction principle T2 runs on**: to prove `P` at every
world it suffices to prove it at `x` given it at every world STRICTLY
above `x`.  (Maximal worlds are the base case, discharged by the
hypothesis with a vacuous premise.) -/
theorem height_induction [Finite N.W] (hr : Reduced N) {P : N.W → Prop}
    (step : ∀ x, (∀ y, N.Ri x y → x ≠ y → P y) → P x) : ∀ x, P x := by
  have key : ∀ n (x : N.W), height N x ≤ n → P x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        refine step x (fun y hy hne => ?_)
        exact absurd (height_lt_of_ri hr hy hne) (by omega)
    | succ n ih =>
        intro x hx
        refine step x (fun y hy hne => ih y ?_)
        have := height_lt_of_ri hr hy hne
        omega
  exact fun x => key (height N x) x le_rfl

/-! ## 1b. Covers

The completeness construction indexes a join's components by worlds
above `w`.  Taking ALL strictly greater worlds makes the extracted
model EXPONENTIAL — on a chain of `n` worlds it has `2^(n-1)` worlds,
because every world is re-expanded once per path reaching it
(`lean_exe t2screen` §G).  Indexing by the COVERS instead makes the
chain case linear, and it is still exhaustive: every world above `w`
lies above some cover of `w`.  That is the lemma. -/

/-- `v` COVERS `w`: strictly above, with nothing strictly between. -/
def Covers (N : ConstraintModel) (w v : N.W) : Prop :=
  N.Ri w v ∧ w ≠ v ∧ ∀ z, N.Ri w z → N.Ri z v → z = w ∨ z = v

/-- **Every world strictly above `w` lies above a COVER of `w`.**  The
witness is a world of maximal height in the interval — maximal height
means minimal position, and minimal-above-`w` is exactly a cover. -/
theorem exists_cover_below [Finite N.W] (hr : Reduced N) {w y : N.W}
    (hwy : N.Ri w y) (hne : w ≠ y) : ∃ v, Covers N w v ∧ N.Ri v y := by
  classical
  obtain ⟨z, hz, hmax⟩ :=
    Set.exists_max_image {u | N.Ri w u ∧ N.Ri u y ∧ w ≠ u} (height N)
      (Set.toFinite _) ⟨y, hwy, N.refl_i y, hne⟩
  refine ⟨z, ⟨hz.1, hz.2.2, fun u hwu huz => ?_⟩, hz.2.1⟩
  by_cases hu : w = u
  · exact .inl hu.symm
  · right
    by_contra hne'
    have hlt : height N z < height N u := height_lt_of_ri hr huz hne'
    have := hmax u ⟨hwu, N.trans_i huz hz.2.1, hu⟩
    omega

/-! ## 2. The measure under the join

The join is the only constructor that creates a world, so these are
the only facts T2's induction needs about the construction. -/

variable {ι : Type} {Mods : ι → ConstraintModel}

/-- The disjoint union is reduced exactly when every premise is. -/
theorem union_reduced (h : ∀ i, Reduced (Mods i)) : Reduced (union Mods) := by
  rintro x y ⟨h1⟩ h2
  cases h2 with
  | mk h2 => exact congrArg _ (h _ h1 h2)

/-- **A join of reduced premises is reduced** — so the constructions
carry the hypothesis the measure needs, at every step. -/
theorem join_reduced (D : RootData (union Mods)) (h : ∀ i, Reduced (Mods i)) :
    Reduced (join Mods D) :=
  addRoot_reduced D (union_reduced h)

/-- **The root is strictly below every component world**, so its
height strictly exceeds theirs: the measure is safe under the join,
and the induction may descend from a join to its premises. -/
theorem height_root_gt (D : RootData (union Mods)) [Finite (join Mods D).W]
    (hr : Reduced (join Mods D)) (i : ι) (a : (Mods i).W) :
    height (join Mods D) (some ⟨i, a⟩) < height (join Mods D) none :=
  height_lt_of_ri hr True.intro (by simp)

/-- Distinct components are mutually `Rᵢ`-incomparable — the other
half of "the measure is safe": a join adds no relation between
premises, so their heights are computed independently. -/
theorem join_comp_incomparable (D : RootData (union Mods)) {i j : ι} (hij : i ≠ j)
    (a : (Mods i).W) (b : (Mods j).W) :
    ¬ (join Mods D).Ri (some ⟨i, a⟩) (some ⟨j, b⟩) :=
  fun h => hij (Lift.fst_eq h)

/-! ## 3. Finiteness of a join -/

theorem union_finite [Finite ι] [∀ i, Finite (Mods i).W] :
    Finite (union Mods).W := by
  show Finite (Σ i, (Mods i).W)
  infer_instance

theorem join_finite [Finite ι] [∀ i, Finite (Mods i).W]
    (D : RootData (union Mods)) : Finite (join Mods D).W := by
  show Finite (Option (Σ i, (Mods i).W))
  infer_instance

/-! ## 4. Pins -/

/--
info: 'Reject.upSet_ssubset' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms upSet_ssubset

/--
info: 'Reject.height_lt_of_ri' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms height_lt_of_ri

/--
info: 'Reject.height_lt_of_rm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms height_lt_of_rm

/--
info: 'Reject.height_induction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms height_induction

/--
info: 'Reject.union_reduced' does not depend on any axioms
-/
#guard_msgs in
#print axioms union_reduced

/--
info: 'Reject.join_reduced' does not depend on any axioms
-/
#guard_msgs in
#print axioms join_reduced

/--
info: 'Reject.height_root_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms height_root_gt

/--
info: 'Reject.join_comp_incomparable' does not depend on any axioms
-/
#guard_msgs in
#print axioms join_comp_incomparable

/--
info: 'Reject.exists_cover_below' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_cover_below

end Reject
