import LaxLogic.ClosedFragmentLattice
import wip.f0MacNeille
import Meta.Audit

/-!
# F0 is a Heyting algebra with a nucleus, and `◯` extends to `DM(F0)`

2026-10-22.  F0, the Lindenbaum algebra of variable-free PLL formulas, is
`PLLND.RNClass = Quotient closedSetoid` (`LaxLogic/ClosedFragmentLattice.lean`),
ordered by the semantic entailment `Le` (equal to single-hypothesis
derivability by `le_iff_nonempty`).  That file gives it `DistribLattice` and
`BoundedOrder` only.  Here, by the semantic route (pointwise facts of the
forcing clauses against `Le`):

1. **the ◯-free part first** (CLAUDE.md rule 8): `HeytingAlgebra RNClass`,
   with `⇨` lifted from `ifThen` (`HeytingAlgebra.ofHImp`);
2. `circNucleus : Nucleus RNClass`, with `◯` lifted from `somehow`;
3. the corollary `circ_extends_to_DM`: `dmNucleus circNucleus` (from
   `wip/f0MacNeille.lean`) is a nucleus on `DedekindCut RNClass` that extends
   `◯` on principal cuts and is the greatest monotone such map.

**Uniqueness at F0 is OPEN.**  The general refutation
`MacNeilleNonUnique.nucleus_extension_not_unique`
(`wip/f0MacNeilleNonUnique.lean`) is a chain with a gap: a down-set with no
greatest element under an up-set with no least element, the gap cut being
where the least and greatest extensions differ.  F0 has gaps of its own
(`gap_no_glb`, `L_no_greatest`, `wip/floor.lean`: a descending family with no
greatest lower bound), so the question at F0 is live.  Not attempted here.
-/

open PLLFormula

namespace F0Nuclear

open PLLND PLLND.LaxInfinite

/-! ## Closed constructors for `⊃` and `◯` -/

/-- `x ⊃ y` on closed formulas. -/
def cImp (x y : Closed) : Closed :=
  Closed.mk (.ifThen x.1 y.1) (by simp [atomFree, x.2, y.2])

/-- `◯x` on closed formulas. -/
def cBox (x : Closed) : Closed :=
  Closed.mk (.somehow x.1) (by simp [atomFree, x.2])

/-! ## §1 The ◯-free part: F0 is a Heyting algebra -/

/-- The lifted implication. -/
def himp : RNClass → RNClass → RNClass :=
  Quotient.map₂ cImp (by
    intro a a' ha b b' hb
    have ha : LaxEquiv a.1 a'.1 := ha
    have hb : LaxEquiv b.1 b'.1 := hb
    show LaxEquiv (PLLFormula.ifThen a.1 b.1) (PLLFormula.ifThen a'.1 b'.1)
    exact ⟨fun M _ h v hv hx => hb.1 M v (h v hv (ha.2 M v hx)),
           fun M _ h v hv hx => hb.2 M v (h v hv (ha.1 M v hx))⟩)

theorem himp_mk (a b : Closed) :
    himp (Quotient.mk closedSetoid a) (Quotient.mk closedSetoid b) =
      Quotient.mk closedSetoid (cImp a b) := rfl

/-- The adjunction `x ≤ y ⇨ z ↔ x ⊓ y ≤ z`: the forcing clause of `⊃` and
heredity. -/
theorem le_himp_iff_rn (x y z : RNClass) : x ≤ himp y z ↔ x ⊓ y ≤ z := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  induction z using Quotient.ind
  exact ⟨fun h M w hw => h M w hw.1 w (M.refl_i w) hw.2,
         fun h M _ hx v hv hy => h M v ⟨M.force_hered hv hx, hy⟩⟩

/-- **F0 is a Heyting algebra.** -/
instance instHeyting : HeytingAlgebra RNClass :=
  HeytingAlgebra.ofHImp himp le_himp_iff_rn

theorem himp_eq (x y : RNClass) : x ⇨ y = himp x y := rfl

/-! ## §2 `◯` is a nucleus on F0 -/

/-- The lifted lax modality. -/
def box : RNClass → RNClass :=
  Quotient.map cBox (by
    intro a a' ha
    have ha : LaxEquiv a.1 a'.1 := ha
    show LaxEquiv (PLLFormula.somehow a.1) (PLLFormula.somehow a'.1)
    exact ⟨fun M _ h v hv => (h v hv).imp fun _ hu => ⟨hu.1, ha.1 M _ hu.2⟩,
           fun M _ h v hv => (h v hv).imp fun _ hu => ⟨hu.1, ha.2 M _ hu.2⟩⟩)

theorem box_mk (a : Closed) :
    box (Quotient.mk closedSetoid a) = Quotient.mk closedSetoid (cBox a) := rfl

/-- `x ≤ ◯x`: `refl_m` and heredity. -/
theorem le_box (x : RNClass) : x ≤ box x := by
  induction x using Quotient.ind
  exact fun M _ h v hv => ⟨v, M.refl_m v, M.force_hered hv h⟩

/-- `◯◯x ≤ ◯x`: `trans_m`. -/
theorem box_box_le (x : RNClass) : box (box x) ≤ box x := by
  induction x using Quotient.ind
  intro M w h v hv
  obtain ⟨u, hvu, hu⟩ := h v hv
  obtain ⟨u', huu', hu'⟩ := hu u (M.refl_i u)
  exact ⟨u', M.trans_m hvu huu', hu'⟩

/-- `◯(x ⊓ y) = ◯x ⊓ ◯y`; the inequality `≥` uses `sub_mi`, `trans_i`,
`trans_m` and heredity. -/
theorem box_inf (x y : RNClass) : box (x ⊓ y) = box x ⊓ box y := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  apply le_antisymm
  · exact fun M _ h => ⟨fun v hv => (h v hv).imp fun _ hu => ⟨hu.1, hu.2.1⟩,
                        fun v hv => (h v hv).imp fun _ hu => ⟨hu.1, hu.2.2⟩⟩
  · intro M w h v hv
    obtain ⟨u, hvu, ha⟩ := h.1 v hv
    obtain ⟨u', huu', hb⟩ := h.2 u (M.trans_i hv (M.sub_mi hvu))
    exact ⟨u', M.trans_m hvu huu', M.force_hered (M.sub_mi huu') ha, hb⟩

/-- **`◯` is a nucleus on F0.** -/
def circNucleus : Nucleus RNClass where
  toFun := box
  map_inf' := box_inf
  idempotent' := box_box_le
  le_apply' := le_box

theorem circNucleus_apply (x : RNClass) : circNucleus x = box x := rfl

/-! ## §3 `◯` extends to `DM(F0)` -/

open DedekindCut in
/-- **`◯` extends to the MacNeille completion of F0 as a nucleus**, and the
extension `dmNucleus circNucleus` is the greatest monotone extension. -/
theorem circ_extends_to_DM :
    (∀ a : RNClass,
        MacNeille.dmNucleus circNucleus (principal a) = principal (circNucleus a)) ∧
    ∀ k' : DedekindCut RNClass → DedekindCut RNClass, Monotone k' →
      (∀ a : RNClass, k' (principal a) = principal (circNucleus a)) →
      ∀ X, k' X ≤ MacNeille.dmNucleus circNucleus X :=
  ⟨MacNeille.dmNucleus_principal circNucleus,
   fun k' hk' hext X => MacNeille.le_dmNucleus circNucleus k' hk' hext X⟩

end F0Nuclear

/-! ## Pins

Measured 2026-10-22, each watched failing at `[]` first.  The packaging is
choice-free (`#choice_path` on `instHeyting` and `circNucleus`: "does not
depend on 'Classical.choice'").  The corollary carries Mathlib's choice
through `wip/f0MacNeille.lean` (the `Nucleus` API and the order on
`DedekindCut`), as recorded there. -/

#axioms_within F0Nuclear.himp [propext, Quot.sound]
#axioms_within F0Nuclear.le_himp_iff_rn [propext, Quot.sound]
#axioms_within F0Nuclear.instHeyting [propext, Quot.sound]
#axioms_within F0Nuclear.box [propext, Quot.sound]
#axioms_within F0Nuclear.box_inf [propext, Quot.sound]
#axioms_within F0Nuclear.circNucleus [propext, Quot.sound]
#axioms_within F0Nuclear.circ_extends_to_DM [propext, Classical.choice, Quot.sound]
