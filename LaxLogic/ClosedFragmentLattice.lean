/-
# RN(◯,{}) is a bounded distributive lattice

The closed-fragment Lindenbaum quotient `Quotient closedSetoid`
(`PLLLaxInfinite.lean`) carries the structure the cube-embedding theorem
(`CubeEmbedding.lean`) needs: `⊓`/`⊔` are the lifted `∧`/`∨`, `⊥` is the
class of `falsePLL`, `⊤` the class of `⊥ ⊃ ⊥` — both ALREADY formulas of
the fragment, nothing is added.  Every lattice law, distributivity
included, is a pointwise fact of the Kripke forcing clauses (`force` on
`∧`/`∨` is the metalanguage `∧`/`∨`), so the proofs are one-liners
against the semantic `Le`.

With this instance, `CubeEmbedding.cube_le_iff` applies verbatim to
RN(◯,{}): any certified finite set of genuine fragment covers of a class
`n` spans a Boolean cube above `n`.
-/
import LaxLogic.PLLLaxInfinite
import LaxLogic.CubeEmbedding

open PLLFormula

namespace PLLND
open LaxInfinite

/-! ## Operations on the closed carrier -/

namespace Closed

/-- Constructor through the `Closed` definition. -/
def mk (φ : PLLFormula) (h : atomFree φ = true) : Closed :=
  show {ψ : PLLFormula // atomFree ψ = true} from ⟨φ, h⟩

def and (x y : Closed) : Closed :=
  mk (.and x.1 y.1) (by simp [atomFree, x.2, y.2])

def or (x y : Closed) : Closed :=
  mk (.or x.1 y.1) (by simp [atomFree, x.2, y.2])

def bot : Closed := mk .falsePLL rfl

def top : Closed := mk (.ifThen .falsePLL .falsePLL) rfl

@[simp] theorem mk_val (φ h) : (mk φ h).1 = φ := rfl
@[simp] theorem and_val (x y : Closed) : (and x y).1 = .and x.1 y.1 := rfl
@[simp] theorem or_val (x y : Closed) : (or x y).1 = .or x.1 y.1 := rfl

end Closed

/-! ## The quotient carrier -/

/-- RN(◯,{}): the closed-fragment Lindenbaum quotient. -/
abbrev RNClass := Quotient closedSetoid

namespace RNClass

/-- The lifted entailment order. -/
def le : RNClass → RNClass → Prop :=
  Quotient.lift₂ (fun a b => Le a.1 b.1) (by
    intro a b a' b' ha hb
    have ⟨haf, hab⟩ : LaxEquiv a.1 a'.1 := ha
    have ⟨hbf, hbb⟩ : LaxEquiv b.1 b'.1 := hb
    exact propext ⟨fun h => Le.trans hab (Le.trans h hbf),
                   fun h => Le.trans haf (Le.trans h hbb)⟩)

/-- The lifted meet. -/
def inf : RNClass → RNClass → RNClass :=
  Quotient.map₂ Closed.and (by
    intro a a' ha b b' hb
    have ha : LaxEquiv a.1 a'.1 := ha
    have hb : LaxEquiv b.1 b'.1 := hb
    show LaxEquiv (PLLFormula.and a.1 b.1) (PLLFormula.and a'.1 b'.1)
    exact ⟨fun M w h => ⟨ha.1 M w h.1, hb.1 M w h.2⟩,
           fun M w h => ⟨ha.2 M w h.1, hb.2 M w h.2⟩⟩)

/-- The lifted join. -/
def sup : RNClass → RNClass → RNClass :=
  Quotient.map₂ Closed.or (by
    intro a a' ha b b' hb
    have ha : LaxEquiv a.1 a'.1 := ha
    have hb : LaxEquiv b.1 b'.1 := hb
    show LaxEquiv (PLLFormula.or a.1 b.1) (PLLFormula.or a'.1 b'.1)
    exact ⟨fun M w h => h.elim (fun x => .inl (ha.1 M w x)) (fun x => .inr (hb.1 M w x)),
           fun M w h => h.elim (fun x => .inl (ha.2 M w x)) (fun x => .inr (hb.2 M w x))⟩)

instance : DistribLattice RNClass where
  le := le
  le_refl x := by induction x using Quotient.ind; exact Le.refl _
  le_trans x y z := by
    induction x using Quotient.ind; induction y using Quotient.ind
    induction z using Quotient.ind
    exact Le.trans
  le_antisymm x y := by
    induction x using Quotient.ind; induction y using Quotient.ind
    exact fun h₁ h₂ => Quotient.sound ⟨h₁, h₂⟩
  inf := inf
  sup := sup
  inf_le_left x y := by
    induction x using Quotient.ind; induction y using Quotient.ind
    exact fun M w h => h.1
  inf_le_right x y := by
    induction x using Quotient.ind; induction y using Quotient.ind
    exact fun M w h => h.2
  le_inf x y z := by
    induction x using Quotient.ind; induction y using Quotient.ind
    induction z using Quotient.ind
    exact fun h₁ h₂ M w h => ⟨h₁ M w h, h₂ M w h⟩
  le_sup_left x y := by
    induction x using Quotient.ind; induction y using Quotient.ind
    exact fun M w h => .inl h
  le_sup_right x y := by
    induction x using Quotient.ind; induction y using Quotient.ind
    exact fun M w h => .inr h
  sup_le x y z := by
    induction x using Quotient.ind; induction y using Quotient.ind
    induction z using Quotient.ind
    exact fun h₁ h₂ M w h => h.elim (h₁ M w) (h₂ M w)
  le_sup_inf x y z := by
    induction x using Quotient.ind; induction y using Quotient.ind
    induction z using Quotient.ind
    exact fun M w h => h.1.elim (fun hx => .inl hx)
      (fun hy => h.2.elim (fun hx => .inl hx) (fun hz => .inr ⟨hy, hz⟩))

instance : OrderBot RNClass where
  bot := Quotient.mk closedSetoid Closed.bot
  bot_le x := by
    induction x using Quotient.ind
    exact fun M w h => M.force_of_fallible h

instance : OrderTop RNClass where
  top := Quotient.mk closedSetoid Closed.top
  le_top x := by
    induction x using Quotient.ind
    exact fun M w _ => fun v _ h => h

instance : BoundedOrder RNClass := ⟨⟩

end RNClass

/-! ## The cube embedding, instantiated at RN(◯,{})

For any class `n` and any certified finite set `U` of genuine fragment
covers of `n` (Mathlib's `⋖` at this instance IS the fragment's own
unscoped cover relation), the map `S ⟼ n ⊔ ⋁S` order-embeds `2^U`.  The
EXISTENCE of such `U` at a given class — and the growth of `|U|` with
◯-depth — is the open premise; this corollary is the theorem "subject to
the existence premise". -/

theorem rn_cube_le_iff {n : RNClass} {U : Finset RNClass}
    (hcov : ∀ y ∈ U, n ⋖ y) {S T : Finset RNClass} (hS : S ⊆ U) (hT : T ⊆ U) :
    CubeEmbedding.cube n S ≤ CubeEmbedding.cube n T ↔ S ⊆ T :=
  CubeEmbedding.cube_le_iff hcov hS hT

theorem rn_cube_inj {n : RNClass} {U : Finset RNClass}
    (hcov : ∀ y ∈ U, n ⋖ y) {S T : Finset RNClass} (hS : S ⊆ U) (hT : T ⊆ U)
    (h : CubeEmbedding.cube n S = CubeEmbedding.cube n T) : S = T :=
  CubeEmbedding.cube_inj hcov hS hT h

end PLLND

/-! ## Pins -/

/-- info: 'PLLND.rn_cube_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.rn_cube_le_iff

/-- info: 'PLLND.rn_cube_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.rn_cube_inj
