/-
(R) — EVERY FINITE COUNTERMODEL CAN BE MADE REDUCED.

`Reject/Complete.lean` proves completeness for finite REDUCED
countermodels, and neither of the repo's finite-countermodel sources
supplies reducedness: the filtration and the emitter both order worlds
by inclusion on theories while distinguishing them by a modal
component, so same-theory/different-modal-part worlds are
`Rᵢ`-equivalent and distinct.  This file closes the gap, by the route
`lake exe rscreen` found:

  STEP 1  quotient by `Rₘ`-EQUIVALENCE.  `Rₘ`-equivalent worlds have
          equal `Rᵢ`-up-sets and equal `Rₘ`-cones, so the equivalence
          is a BISIMULATION and forcing is untouched.  The quotient is
          `Rₘ`-antisymmetric.
  STEP 2  REFINE `Rᵢ`: keep `x Rᵢ y` unless `x` and `y` are
          `Rᵢ`-equivalent, in which case keep it only when
          `Fm x ⊆ Fm y`, with `Rₘ`-RANK and then an arbitrary linear
          order breaking the tie.  `Fm x` is the set of formulas
          refuted at EVERY `Rₘ`-successor of `x` — the emitter's
          `mfal`, semantically.

Screened first (`wip/r_screen.lean`, 1,826 non-reduced frames): pure
`Fm`-inclusion preserves forcing everywhere but reduces only 60 of
1,826; an arbitrary linear order reduces everything but costs forcing;
`Fm` + rank + order does all three, 1444/1444 on the `Rₘ`-acyclic
stratum, which is what step 1 delivers.

**The one non-obvious step** is that shrinking `Rᵢ` cannot make `◯A`
become true.  It cannot, because a witness can always be PUSHED UP:
if `y` witnesses `x ⊮ ◯A` but the refinement drops `x Rᵢ y`, take a
world of maximal `Rₘ`-rank in `{v ≥ᵢ x | A ∈ Fm v}`.  That world's
only `Rₘ`-successor is itself, so its `Fm` is exactly what it refutes,
which forces `Fm x ⊊ Fm m` — and the refinement KEEPS `x Rᵢ m`.
`exists_refined_witness` is that argument.
-/
import Reject.Complete
import LaxLogic.PLLFinComp
import Mathlib.Data.Set.Card

namespace Reject

open PLLND

/-! ## The modal fingerprint -/

/-- `Fm x` — the formulas refuted at EVERY `Rₘ`-successor of `x`.  The
semantic form of the emitter's `mfal` component. -/
def Fm (N : ConstraintModel) (x : N.W) : Set PLLFormula :=
  {A | ∀ u, N.Rm x u → ¬ N.force u A}

variable {N : ConstraintModel}

/-- An `Rₘ`-step can only ENLARGE the fingerprint: the successor's cone
is contained in the source's. -/
theorem Fm_mono {x y : N.W} (h : N.Rm x y) : Fm N x ⊆ Fm N y :=
  fun _ hA u hu => hA u (N.trans_m h hu)

/-- `Rᵢ`-equivalent worlds force the same formulas — one line, from
heredity in both directions.  Used throughout. -/
theorem force_iff_of_ri_equiv {x y : N.W} (h1 : N.Ri x y) (h2 : N.Ri y x)
    (φ : PLLFormula) : N.force x φ ↔ N.force y φ :=
  ⟨N.force_hered h1, N.force_hered h2⟩

/-- The `Rₘ`-down-set, and its size — a linear extension of `Rₘ`. -/
def rdown (N : ConstraintModel) (x : N.W) : Set N.W := {v | N.Rm v x}

noncomputable def rrank (N : ConstraintModel) (x : N.W) : Nat := (rdown N x).ncard

theorem rdown_mono {x y : N.W} (h : N.Rm x y) : rdown N x ⊆ rdown N y :=
  fun _ hv => N.trans_m hv h

theorem rrank_le [Finite N.W] {x y : N.W} (h : N.Rm x y) :
    rrank N x ≤ rrank N y :=
  Set.ncard_le_ncard (rdown_mono h) (Set.toFinite _)

/-- On an `Rₘ`-ANTISYMMETRIC model, equal rank along an `Rₘ`-step forces
equality: rank is a strict linear extension. -/
theorem eq_of_rm_of_rrank_eq [Finite N.W]
    (hanti : ∀ {x y : N.W}, N.Rm x y → N.Rm y x → x = y)
    {x y : N.W} (h : N.Rm x y) (he : rrank N x = rrank N y) : x = y := by
  have hsub : rdown N x ⊆ rdown N y := rdown_mono h
  have : rdown N y ⊆ rdown N x :=
    (Set.eq_of_subset_of_ncard_le hsub (le_of_eq he.symm) (Set.toFinite _)).symm.subset
  exact hanti h (this (N.refl_m y))

/-! ## Step 1: the `Rₘ`-quotient

`Rₘ`-equivalent worlds are `Rᵢ`-equivalent (`Rm ⊆ Ri`), hence force the
same formulas, and have the SAME `Rₘ`-cone.  So collapsing them is a
bisimulation, and it removes exactly the `Rₘ`-cycles that no refinement
of `Rᵢ` could survive — an `Rᵢ` containing `Rₘ` cannot be antisymmetric
while `Rₘ` has a proper cycle. -/

/-- `Rₘ`-equivalence. -/
def RmEq (N : ConstraintModel) (x y : N.W) : Prop := N.Rm x y ∧ N.Rm y x

def rmSetoid (N : ConstraintModel) : Setoid N.W where
  r := RmEq N
  iseqv :=
    ⟨fun x => ⟨N.refl_m x, N.refl_m x⟩, fun h => ⟨h.2, h.1⟩,
     fun h1 h2 => ⟨N.trans_m h1.1 h2.1, N.trans_m h2.2 h1.2⟩⟩

theorem ri_of_rmEq {x y : N.W} (h : RmEq N x y) : N.Ri x y ∧ N.Ri y x :=
  ⟨N.sub_mi h.1, N.sub_mi h.2⟩

/-- The quotient model. -/
def qModel (N : ConstraintModel) : ConstraintModel :=
  letI : Setoid N.W := rmSetoid N
  { W := Quotient (rmSetoid N)
    Ri := Quotient.lift₂ (fun x y => N.Ri x y) (by
    intro a b c d hac hbd
    exact propext ⟨fun h => N.trans_i (N.trans_i (ri_of_rmEq hac).2 h) (ri_of_rmEq hbd).1,
      fun h => N.trans_i (N.trans_i (ri_of_rmEq hac).1 h) (ri_of_rmEq hbd).2⟩)
    Rm := Quotient.lift₂ (fun x y => N.Rm x y) (by
    intro a b c d hac hbd
    exact propext ⟨fun h => N.trans_m (N.trans_m hac.2 h) hbd.1,
      fun h => N.trans_m (N.trans_m hac.1 h) hbd.2⟩)
    F := {q | Quotient.lift (fun x => x ∈ N.F) (by
    intro a b hab
    exact propext ⟨fun h => N.hered_F (ri_of_rmEq hab).1 h,
      fun h => N.hered_F (ri_of_rmEq hab).2 h⟩) q}
    V a := {q | Quotient.lift (fun x => x ∈ N.V a) (by
    intro c d hcd
    exact propext ⟨fun h => N.hered_V (ri_of_rmEq hcd).1 h,
      fun h => N.hered_V (ri_of_rmEq hcd).2 h⟩) q}
    refl_i := by rintro ⟨x⟩; exact N.refl_i x
    trans_i := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ h1 h2; exact N.trans_i h1 h2
    refl_m := by rintro ⟨x⟩; exact N.refl_m x
    trans_m := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ h1 h2; exact N.trans_m h1 h2
    sub_mi := by rintro ⟨x⟩ ⟨y⟩ h; exact N.sub_mi h
    hered_F := by rintro ⟨x⟩ ⟨y⟩ h hx; exact N.hered_F h hx
    hered_V := by rintro a ⟨x⟩ ⟨y⟩ h hx; exact N.hered_V h hx
    full_F := by rintro a ⟨x⟩ hx; exact N.full_F hx }

/-- **The quotient map is a bisimulation**, so forcing is untouched. -/
def qBisim (N : ConstraintModel) : Bisim N (qModel N) where
  Z x q := Quotient.mk (rmSetoid N) x = q
  atoms := by rintro x q rfl a _; exact Iff.rfl
  fall := by rintro x q rfl; exact Iff.rfl
  iforth := by rintro x q rfl y h; exact ⟨Quotient.mk (rmSetoid N) y, h, rfl⟩
  iback := by
    rintro x q rfl ⟨y⟩ h
    exact ⟨y, h, rfl⟩
  mforth := by rintro x q rfl y h; exact ⟨Quotient.mk (rmSetoid N) y, h, rfl⟩
  mback := by
    rintro x q rfl ⟨y⟩ h
    exact ⟨y, h, rfl⟩

/-- The quotient is `Rₘ`-ANTISYMMETRIC: the cycles are gone. -/
theorem qModel_rm_antisymm {p q : (qModel N).W}
    (h1 : (qModel N).Rm p q) (h2 : (qModel N).Rm q p) : p = q := by
  induction p using Quotient.inductionOn with
  | _ x =>
    induction q using Quotient.inductionOn with
    | _ y => exact Quotient.sound ⟨h1, h2⟩

instance qModel_finite [Finite N.W] : Finite (qModel N).W := by
  show Finite (Quotient (rmSetoid N)); infer_instance

/-! ## The refinement -/

variable [Fintype N.W]

/-- An arbitrary injective key, to break the last ties. -/
noncomputable def wkey (N : ConstraintModel) [Fintype N.W] (x : N.W) : Nat :=
  ((Fintype.equivFin N.W) x).val

theorem wkey_inj {x y : N.W} (h : wkey N x = wkey N y) : x = y := by
  have : (Fintype.equivFin N.W) x = (Fintype.equivFin N.W) y := Fin.ext h
  exact (Fintype.equivFin N.W).injective this

/-- **The refinement order**: `Fm`-inclusion first, then `Rₘ`-rank,
then the key. -/
def rle (N : ConstraintModel) [Fintype N.W] (x y : N.W) : Prop :=
  Fm N x ⊆ Fm N y ∧
    (Fm N y ⊆ Fm N x →
      rrank N x < rrank N y ∨ (rrank N x = rrank N y ∧ wkey N x ≤ wkey N y))

theorem rle_refl (x : N.W) : rle N x x :=
  ⟨subset_rfl, fun _ => .inr ⟨rfl, le_rfl⟩⟩

theorem rle_trans {x y z : N.W} (h1 : rle N x y) (h2 : rle N y z) : rle N x z := by
  refine ⟨h1.1.trans h2.1, fun hzx => ?_⟩
  have hxy : Fm N y ⊆ Fm N x := h2.1.trans hzx
  have hyz : Fm N z ⊆ Fm N y := hzx.trans h1.1
  rcases h1.2 hxy with a | ⟨ae, ak⟩ <;> rcases h2.2 hyz with b | ⟨be, bk⟩
  · exact .inl (a.trans b)
  · exact .inl (be ▸ a)
  · exact .inl (ae ▸ b)
  · exact .inr ⟨ae.trans be, ak.trans bk⟩

theorem rle_antisymm {x y : N.W} (h1 : rle N x y) (h2 : rle N y x) : x = y := by
  rcases h1.2 h2.1 with a | ⟨ae, ak⟩ <;> rcases h2.2 h1.1 with b | ⟨be, bk⟩
  · omega
  · omega
  · omega
  · exact wkey_inj (le_antisymm ak bk)

/-- **The refined model**: same worlds, same `Rₘ`, `Rᵢ` cut down so
that `Rᵢ`-equivalent worlds are separated by their modal data. -/
def refineM (N : ConstraintModel) [Fintype N.W]
    (hanti : ∀ {x y : N.W}, N.Rm x y → N.Rm y x → x = y) : ConstraintModel where
  W := N.W
  Ri x y := N.Ri x y ∧ (N.Ri y x → rle N x y)
  Rm := N.Rm
  F := N.F
  V := N.V
  refl_i x := ⟨N.refl_i x, fun _ => rle_refl x⟩
  trans_i := by
    rintro x y z ⟨h1, h1'⟩ ⟨h2, h2'⟩
    refine ⟨N.trans_i h1 h2, fun hzx => ?_⟩
    exact rle_trans (h1' (N.trans_i h2 hzx)) (h2' (N.trans_i hzx h1))
  refl_m := N.refl_m
  trans_m := N.trans_m
  sub_mi := by
    intro x y h
    refine ⟨N.sub_mi h, fun hyx => ⟨Fm_mono h, fun _ => ?_⟩⟩
    rcases Nat.lt_or_ge (rrank N x) (rrank N y) with hlt | hge
    · exact .inl hlt
    · have : rrank N x = rrank N y := le_antisymm (rrank_le h) hge
      exact .inr ⟨this, le_of_eq (congrArg _ (eq_of_rm_of_rrank_eq hanti h this))⟩
  hered_F := fun h hx => N.hered_F h.1 hx
  hered_V := fun h hx => N.hered_V h.1 hx
  full_F := N.full_F

/-- **The refined model is REDUCED.** -/
theorem refineM_reduced (hanti : ∀ {x y : N.W}, N.Rm x y → N.Rm y x → x = y) :
    Reduced (refineM N hanti) := by
  intro x y h1 h2
  exact rle_antisymm (N := N) (h1.2 h2.1) (h2.2 h1.1)

/-! ## Forcing is untouched by the refinement

The `⊃` case is immediate: a dropped witness is `Rᵢ`-equivalent to the
source, so the source itself replaces it.  The `◯` case is the content,
and `exists_refined_witness` is the argument. -/

/-- **A `◯`-witness can be pushed up into the refinement.**  If `x`'s
own cone realises `A` but some `Rᵢ`-successor `y` refutes `A`
throughout its cone, then some world the refinement KEEPS above `x`
does too.  The witness is a world of maximal `Rₘ`-rank among the
refuters: its only `Rₘ`-successor is itself, so its fingerprint is
exactly what it refutes, and that forces `Fm x ⊊ Fm m`. -/
theorem exists_refined_witness
    (hanti : ∀ {x y : N.W}, N.Rm x y → N.Rm y x → x = y)
    {x : N.W} {A : PLLFormula} (hx : A ∉ Fm N x)
    {y : N.W} (hxy : N.Ri x y) (hy : A ∈ Fm N y) :
    ∃ u, (refineM N hanti).Ri x u ∧ A ∈ Fm N u := by
  classical
  obtain ⟨m, hm, hmax⟩ :=
    Set.exists_max_image {v : N.W | N.Ri x v ∧ A ∈ Fm N v} (rrank N)
      (Set.toFinite _) ⟨y, hxy, hy⟩
  -- `m` is `Rₘ`-maximal: any `Rₘ`-successor is again a refuter, of no
  -- smaller rank, hence equal to `m`.
  have hmM : ∀ u, N.Rm m u → u = m := by
    intro u hu
    have hu' : u ∈ {v : N.W | N.Ri x v ∧ A ∈ Fm N v} :=
      ⟨N.trans_i hm.1 (N.sub_mi hu), Fm_mono hu hm.2⟩
    exact (eq_of_rm_of_rrank_eq hanti hu
      (le_antisymm (rrank_le hu) (hmax u hu'))).symm
  refine ⟨m, ⟨hm.1, fun hmx => ⟨?_, fun hsub => ?_⟩⟩, hm.2⟩
  · -- `Fm x ⊆ Fm m`: `x` refutes everything in `Fm x` (it is its own
    -- `Rₘ`-successor), and `m` is `Rᵢ`-equivalent to `x`.
    intro B hB u hu
    rw [hmM u hu]
    exact fun hf => hB x (N.refl_m x) ((force_iff_of_ri_equiv hmx hm.1 B).mp hf)
  · -- the second clause is vacuous: `A ∈ Fm m \ Fm x`, so the
    -- fingerprints are NOT equal and `Fm m ⊆ Fm x` is impossible
    exact absurd (hsub hm.2) hx

/-- **Forcing is preserved by the refinement**, at every world for
every formula. -/
theorem refineM_force (hanti : ∀ {x y : N.W}, N.Rm x y → N.Rm y x → x = y)
    (φ : PLLFormula) : ∀ x : N.W, (refineM N hanti).force x φ ↔ N.force x φ := by
  classical
  induction φ with
  | prop a => exact fun _ => Iff.rfl
  | falsePLL => exact fun _ => Iff.rfl
  | and φ ψ ihφ ihψ => exact fun x => and_congr (ihφ x) (ihψ x)
  | or φ ψ ihφ ihψ => exact fun x => or_congr (ihφ x) (ihψ x)
  | ifThen φ ψ ihφ ihψ =>
      intro x
      constructor
      · intro h y hxy hφ
        by_cases hyx : N.Ri y x
        · -- the dropped case: `y ≈ᵢ x`, so `x` itself replaces it
          have hφx : N.force x φ := N.force_hered hyx hφ
          have := (ihψ x).mp (h x ((refineM N hanti).refl_i x) ((ihφ x).mpr hφx))
          exact N.force_hered hxy this
        · exact (ihψ y).mp (h y ⟨hxy, fun k => absurd k hyx⟩ ((ihφ y).mpr hφ))
      · intro h y hxy hφ
        exact (ihψ y).mpr (h y hxy.1 ((ihφ y).mp hφ))
  | somehow φ ih =>
      intro x
      constructor
      · intro h y hxy
        by_contra hc
        have hyF : φ ∈ Fm N y := fun u hu hf => hc ⟨u, hu, hf⟩
        obtain ⟨u, hu, hfu⟩ := h x ((refineM N hanti).refl_i x)
        have hxF : φ ∉ Fm N x := fun k => k u hu ((ih u).mp hfu)
        obtain ⟨m, hm, hmF⟩ := exists_refined_witness hanti hxF hxy hyF
        obtain ⟨v, hv, hfv⟩ := h m hm
        exact hmF v hv ((ih v).mp hfv)
      · intro h y hxy
        obtain ⟨u, hu, hf⟩ := h y hxy.1
        exact ⟨u, hu, (ih u).mpr hf⟩

/-! ## (R), assembled -/

/-- **(R) — every underivable sequent has a finite REDUCED
countermodel.**  Quotient by `Rₘ`-equivalence, then refine `Rᵢ`. -/
theorem exists_reduced_countermodel {Γ : List PLLFormula} {ψ : PLLFormula}
    (h : Γ ⊬ ψ) :
    ∃ (K : ConstraintModel) (_ : Fintype K.W), Reduced K ∧
      ∃ w : K.W, (∀ χ ∈ Γ, K.force w χ) ∧ ¬ K.force w ψ := by
  classical
  obtain ⟨M, w, hchk⟩ := PLLND.FinComp.emitter_completeness h
  simp only [FinCM.checkB, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨hwb, hlt⟩, hΓ⟩, hψ⟩ := hchk
  have hwf := FinCM.wellFormed_of_wellB hwb
  set N₀ := M.toModel hwf with hN₀
  have hfin : Fintype N₀.W := inferInstanceAs (Fintype (Fin M.n))
  -- step 1: the Rₘ-quotient
  let N₁ := qModel N₀
  have hfin₁ : Fintype N₁.W := Fintype.ofFinite _
  let B := qBisim N₀
  -- step 2: the refinement
  let N₂ := @refineM N₁ hfin₁ (fun {_ _} => qModel_rm_antisymm)
  refine ⟨N₂, hfin₁, @refineM_reduced N₁ hfin₁ _, Quotient.mk (rmSetoid N₀) ⟨w, hlt⟩,
    fun χ hχ => ?_, fun hf => ?_⟩
  · refine (@refineM_force N₁ hfin₁ _ χ _).mpr ((B.force χ (x := (⟨w, hlt⟩ : N₀.W)) rfl).mp ?_)
    exact (FinCM.force_iff M hwf χ ⟨w, hlt⟩).mpr (hΓ χ hχ)
  · have h1 : M.forceB w ψ = true :=
      (FinCM.force_iff M hwf ψ ⟨w, hlt⟩).mp
        ((B.force ψ (x := (⟨w, hlt⟩ : N₀.W)) rfl).mpr
          ((@refineM_force N₁ hfin₁ _ ψ _).mp hf))
    rw [hψ] at h1
    exact Bool.noConfusion h1

/-- **T2, UNCONDITIONALLY.**  Every underivable sequent has a
countermodel that is a CONSTRUCTION of the calculus.  With
`not_laxND_of_root` (T1) this is an equivalence: on PLL,
underivability and constructibility coincide. -/
theorem built_countermodel {Γ : List PLLFormula} {ψ : PLLFormula}
    (h : Γ ⊬ ψ) :
    ∃ (M : ConstraintModel) (r : M.W),
      Built M ∧ (∀ χ ∈ Γ, M.force r χ) ∧ ¬ M.force r ψ := by
  obtain ⟨K, hfin, hred, w, hΓ, hψ⟩ := exists_reduced_countermodel h
  exact @built_countermodel_of_reduced K (Finite.of_fintype _) hred w Γ ψ hΓ hψ

/-- **The calculus is SOUND AND COMPLETE for PLL underivability.** -/
theorem not_laxND_iff_built {Γ : List PLLFormula} {ψ : PLLFormula} :
    Γ ⊬ ψ ↔
      ∃ (M : ConstraintModel) (r : M.W),
        Built M ∧ (∀ χ ∈ Γ, M.force r χ) ∧ ¬ M.force r ψ := by
  refine ⟨built_countermodel, ?_⟩
  rintro ⟨M, r, -, hΓ, hψ⟩
  exact not_laxND_of_root hΓ hψ

/-! ## Pins -/

/--
info: 'Reject.Fm_mono' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fm_mono

/--
info: 'Reject.force_iff_of_ri_equiv' does not depend on any axioms
-/
#guard_msgs in
#print axioms force_iff_of_ri_equiv

/--
info: 'Reject.eq_of_rm_of_rrank_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eq_of_rm_of_rrank_eq

/--
info: 'Reject.qBisim' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms qBisim

/--
info: 'Reject.qModel_rm_antisymm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms qModel_rm_antisymm

/--
info: 'Reject.refineM_reduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refineM_reduced

/--
info: 'Reject.exists_refined_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_refined_witness

/--
info: 'Reject.refineM_force' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refineM_force

/--
info: 'Reject.exists_reduced_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_reduced_countermodel

/--
info: 'Reject.built_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms built_countermodel

/--
info: 'Reject.not_laxND_iff_built' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_laxND_iff_built

end Reject
