/-
T2 — COMPLETENESS: every countermodel is a construction.

T1 proved the constructors SOUND: what they build is a real model, and
its root certifies underivability.  T2 is the converse, and it is the
step that turns a certificate format into a calculus: if a sequent has
a countermodel at all, the calculus can BUILD one.

**What the constructors generate.**  `Built M` says `M` is assembled
by `solo` and `join` and nothing else.  Unfolded, that is the finite
`Rᵢ`-TREES, with fallible worlds only at leaves (`join` sets the new
root's `F` to `False` unconditionally, so fallibility can enter only
through `solo`).  `lean_exe t2screen` §D tests the claim extensionally
before it is proved: over the ≤3-world battery with two atoms (30,424
well-formed frames, 1,430 of them trees), every corpus formula refuted
anywhere is refuted AT THE ROOT of some tree — 0 gaps in 22 cells,
with a non-vacuity control (6 formulas refuted at no tree root).

**The induction is on HEIGHT** (`Reject/Height.lean`), and reducedness
is what makes it descend.  §A′ of the same screen measures the
necessity: the decrease holds on all 2,588 reduced models of the
battery and FAILS on all 1,826 non-reduced ones.

**Why bisimulation and not isomorphism.**  The tree duplicates worlds
that the countermodel shares between branches, and collapses whole
`Rᵢ`-equivalence classes into one node, so the two models are never
isomorphic.  `Bisim.force` is the transfer lemma; its `◯` case is why
the zig-zag has to be simultaneous in `Rᵢ` and `Rₘ`.
-/
import Reject.Bisim

namespace Reject

open PLLND

/-! ## 1. The class the calculus generates -/

/-- **`Built M`**: `M` is assembled by the calculus's own constructors
— a `solo` world, or a `join` of already-built premises. -/
inductive Built : ConstraintModel → Prop
  | solo (V₀ : String → Prop) (fal : Prop) (hfull : fal → ∀ a, V₀ a) :
      Built (Reject.solo V₀ fal hfull)
  | join {ι : Type} (Mods : ι → ConstraintModel) (D : RootData (union Mods)) :
      (∀ i, Built (Mods i)) → Built (Reject.join Mods D)

/-- The induction's carrier: a built model bisimilar to `N` at `w`,
with the two invariants the step needs — everything the bisimulation
reaches lies `Rᵢ`-above `w`, and every world of the built model is
reached. -/
structure Gen (N : ConstraintModel) (w : N.W) where
  M : ConstraintModel
  built : Built M
  B : Bisim M N
  root : M.W
  root_rel : B.Z root w
  above : ∀ {x y}, B.Z x y → N.Ri w y
  total : ∀ x, ∃ y, B.Z x y

/-! ## 2. The base case: a fallible world

A fallible world forces everything, so a single `solo` fallible world
is bisimilar to it — and this is the ONLY way fallibility can enter a
construction, `join` always producing an infallible root. -/

def genSolo {N : ConstraintModel} (w : N.W) (hw : w ∈ N.F) : Gen N w where
  M := solo (fun _ => True) True (fun _ _ => True.intro)
  built := .solo _ _ _
  B :=
    { Z := fun _ y => N.Ri w y ∧ y ∈ N.F
      atoms := by intro x y h a _; exact ⟨fun _ => N.full_F h.2, fun _ => True.intro⟩
      fall := by intro x y h; exact ⟨fun _ => h.2, fun _ => True.intro⟩
      iforth := by intro x y h v _; exact ⟨y, N.refl_i y, h⟩
      iback := by
        intro x y h y' hy
        exact ⟨(), True.intro, N.trans_i h.1 hy, N.hered_F hy h.2⟩
      mforth := by intro x y h u _; exact ⟨y, N.refl_m y, h⟩
      mback := by
        intro x y h y' hy
        exact ⟨(), True.intro, N.trans_i h.1 (N.sub_mi hy),
          N.hered_F (N.sub_mi hy) h.2⟩ }
  root := ()
  root_rel := ⟨N.refl_i w, hw⟩
  above := fun h => h.1
  total := fun _ => ⟨w, N.refl_i w, hw⟩

/-! ## 3. The step: an infallible world becomes a join

Components are indexed by the STRICTLY greater worlds, each supplied
by the induction hypothesis.  The root's modal cone collects exactly
the component worlds that stand for an `Rₘ`-successor of `w`. -/

/-- The index type of the join step: the worlds STRICTLY above `w`. -/
abbrev Succ {N : ConstraintModel} (w : N.W) : Type := {v : N.W // N.Ri w v ∧ w ≠ v}

variable {N : ConstraintModel}

/-- The premise family: one built model per strictly greater world. -/
def genMods (w : N.W) (g : ∀ v : Succ w, Gen N v.1) : Succ w → ConstraintModel :=
  fun v => (g v).M

/-- The root data.  The modal cone collects exactly the component
worlds standing for an `Rₘ`-successor of `w`; the root's atoms are
`w`'s.  Both side conditions are discharged from the premises. -/
def genData (w : N.W) (g : ∀ v : Succ w, Gen N v.1) :
    RootData (union (genMods w g)) where
  S x := ∃ u, (g x.1).B.Z x.2 u ∧ N.Rm w u
  S_up := by
    rintro ⟨v, a⟩ y ⟨u, hru, hwu⟩ hm
    cases hm with
    | mk hab =>
        obtain ⟨u', hu', hr'⟩ := (g v).B.mforth hru hab
        exact ⟨u', hr', N.trans_m hwu hu'⟩
  At a := w ∈ N.V a
  At_hered := by
    rintro a ha ⟨v, x⟩
    obtain ⟨y, hy⟩ := (g v).total x
    exact ((g v).B.atoms hy a trivial).mpr
      (N.hered_V (N.trans_i v.2.1 ((g v).above hy)) ha)

/-- The model built at `w`. -/
def genModel (w : N.W) (g : ∀ v : Succ w, Gen N v.1) : ConstraintModel :=
  join (genMods w g) (genData w g)

/-- The bisimulation: the new root stands for `w`, and a component
world stands for whatever it stood for in its premise. -/
def genRel (w : N.W) (g : ∀ v : Succ w, Gen N v.1) :
    (genModel w g).W → N.W → Prop :=
  fun x y => match x with
    | none => y = w
    | some z => (g z.1).B.Z z.2 y

theorem genRel_root (w : N.W) (g : ∀ v : Succ w, Gen N v.1) :
    genRel w g none w := rfl

theorem genRel_above (w : N.W) (g : ∀ v : Succ w, Gen N v.1) :
    ∀ {x y}, genRel w g x y → N.Ri w y := by
  rintro (_ | ⟨v, x⟩) y h
  · exact h ▸ N.refl_i w
  · exact N.trans_i v.2.1 ((g v).above h)

theorem genRel_total (w : N.W) (g : ∀ v : Succ w, Gen N v.1) :
    ∀ x, ∃ y, genRel w g x y := by
  rintro (_ | ⟨v, x⟩)
  · exact ⟨w, rfl⟩
  · obtain ⟨y, hy⟩ := (g v).total x
    exact ⟨y, hy⟩

/-- The zig-zag conditions.  Every ROOT clause is a small case split
on whether the `N`-world in play is `w` itself or strictly above it —
strictly above means it is an index, and its component's root already
stands for it.  Every COMPONENT clause is the premise's own clause. -/
def genBisim (w : N.W) (hw : w ∉ N.F) (g : ∀ v : Succ w, Gen N v.1) :
    Bisim (genModel w g) N := by
  classical
  exact
  { Z := genRel w g
    atoms := by
      rintro (_ | ⟨v, x⟩) y h a _
      · rw [h]; exact Iff.rfl
      · exact (g v).B.atoms h a trivial
    fall := by
      rintro (_ | ⟨v, x⟩) y h
      · rw [h]
        exact ⟨fun k => absurd k not_false, fun k => absurd k hw⟩
      · exact (g v).B.fall h
    iforth := by
      rintro (_ | ⟨v, x⟩) y h (_ | ⟨v', x'⟩) hi
      · exact ⟨y, N.refl_i y, h⟩
      · obtain ⟨y', hy'⟩ := (g v').total x'
        exact ⟨y', h ▸ N.trans_i v'.2.1 ((g v').above hy'), hy'⟩
      · exact absurd hi not_false
      · cases hi with
        | mk hab =>
            obtain ⟨y', hy', hr⟩ := (g v).B.iforth h hab
            exact ⟨y', hy', hr⟩
    iback := by
      rintro (_ | ⟨v, x⟩) y h y' hi
      · have hi' : N.Ri w y' := h ▸ hi
        by_cases he : w = y'
        · exact ⟨none, True.intro, he ▸ rfl⟩
        · exact ⟨some ⟨⟨y', hi', he⟩, (g ⟨y', hi', he⟩).root⟩, True.intro,
            (g ⟨y', hi', he⟩).root_rel⟩
      · obtain ⟨x', hx', hr⟩ := (g v).B.iback h hi
        exact ⟨some ⟨v, x'⟩, .mk hx', hr⟩
    mforth := by
      rintro (_ | ⟨v, x⟩) y h (_ | ⟨v', x'⟩) hm
      · exact ⟨y, N.refl_m y, h⟩
      · obtain ⟨u, hru, hwu⟩ := hm
        exact ⟨u, h ▸ hwu, hru⟩
      · exact absurd hm not_false
      · cases hm with
        | mk hab =>
            obtain ⟨y', hy', hr⟩ := (g v).B.mforth h hab
            exact ⟨y', hy', hr⟩
    mback := by
      rintro (_ | ⟨v, x⟩) y h y' hm
      · have hm' : N.Rm w y' := h ▸ hm
        by_cases he : w = y'
        · exact ⟨none, True.intro, he ▸ rfl⟩
        · exact ⟨some ⟨⟨y', N.sub_mi hm', he⟩, (g ⟨y', N.sub_mi hm', he⟩).root⟩,
            ⟨y', (g ⟨y', N.sub_mi hm', he⟩).root_rel, hm'⟩,
            (g ⟨y', N.sub_mi hm', he⟩).root_rel⟩
      · obtain ⟨x', hx', hr⟩ := (g v).B.mback h hm
        exact ⟨some ⟨v, x'⟩, .mk hx', hr⟩ }

/-- **The join step of the induction.** -/
def genJoin (w : N.W) (hw : w ∉ N.F) (g : ∀ v : Succ w, Gen N v.1) : Gen N w where
  M := genModel w g
  built := .join (genMods w g) (genData w g) (fun v => (g v).built)
  B := genBisim w hw g
  root := none
  root_rel := genRel_root w g
  above := genRel_above w g
  total := genRel_total w g

/-! ## 4. The theorem -/

/-- **T2, model-generation form**: every world of a finite reduced
constraint model is bisimilar to the root of a model the calculus
BUILDS.  The induction is `height_induction`; the two cases are
`genSolo` (a fallible world) and `genJoin` (an infallible one). -/
theorem gen_of_reduced {N : ConstraintModel} [Finite N.W] (hr : Reduced N) :
    ∀ w : N.W, Nonempty (Gen N w) := by
  classical
  refine height_induction hr (fun w ih => ?_)
  by_cases hw : w ∈ N.F
  · exact ⟨genSolo w hw⟩
  · exact ⟨genJoin w hw (fun v => Classical.choice (ih v.1 v.2.1 v.2.2))⟩

/-- **T2, calculus form**: a finite reduced countermodel yields a
BUILT countermodel — a construction of the calculus whose root forces
the same hypotheses and refutes the same conclusion. -/
theorem built_countermodel_of_reduced {N : ConstraintModel} [Finite N.W]
    (hr : Reduced N) {w : N.W} {Γ : List PLLFormula} {ψ : PLLFormula}
    (hΓ : ∀ χ ∈ Γ, N.force w χ) (hψ : ¬ N.force w ψ) :
    ∃ (M : ConstraintModel) (r : M.W),
      Built M ∧ (∀ χ ∈ Γ, M.force r χ) ∧ ¬ M.force r ψ := by
  obtain ⟨G⟩ := gen_of_reduced hr w
  exact ⟨G.M, G.root, G.built,
    fun χ hχ => (G.B.force χ G.root_rel).mpr (hΓ χ hχ),
    fun h => hψ ((G.B.force ψ G.root_rel).mp h)⟩

/-- **The calculus is complete for every sequent that has a finite
reduced countermodel** — and `not_laxND_of_root` is the converse, so
on that class underivability and constructibility coincide. -/
theorem built_iff_of_reduced {Γ : List PLLFormula} {ψ : PLLFormula}
    (hcm : ∃ (N : ConstraintModel) (_ : Finite N.W), Reduced N ∧
      ∃ w : N.W, (∀ χ ∈ Γ, N.force w χ) ∧ ¬ N.force w ψ) :
    ∃ (M : ConstraintModel) (r : M.W),
      Built M ∧ (∀ χ ∈ Γ, M.force r χ) ∧ ¬ M.force r ψ := by
  obtain ⟨N, _, hr, w, hΓ, hψ⟩ := hcm
  exact built_countermodel_of_reduced hr hΓ hψ

/-- Soundness of the class, for the record: a built countermodel
certifies underivability, by `not_laxND_of_root`.  With
`built_countermodel_of_reduced` this is the two-way statement T2 was
after. -/
theorem not_laxND_of_built {M : ConstraintModel} {r : M.W}
    {Γ : List PLLFormula} {ψ : PLLFormula}
    (hΓ : ∀ χ ∈ Γ, M.force r χ) (hψ : ¬ M.force r ψ) :
    ¬ Nonempty (LaxND Γ ψ) :=
  not_laxND_of_root hΓ hψ

end Reject
