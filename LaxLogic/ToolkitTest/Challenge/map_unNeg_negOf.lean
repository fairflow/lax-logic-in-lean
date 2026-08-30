/- Challenge: `map_unNeg_negOf`.  Group: completeness.
   Replace the `sorry`.  Do not look for the original proof.

   Deliberately not stated here: where this comes from, how long the known
   proof is, or how hard it is.  Those were hints. -/
import LaxLogic.LJF
import LaxLogic.PLLSequent
import LaxLogic.PLLSemUIFrag

/-!
# Focalization completeness for `LJF`, and uniform interpolation for IPC

`LaxLogic/LJF.lean` builds a polarised focused calculus from scratch and proves
**uniform interpolation for it**: `eSound`, `aSound`, `eMinF`, `aMinF`.  That
file is deliberately self-contained — it has no bridge to the repository's
natural-deduction system, so on its own the interpolation theorem is a theorem
*about `LJF`*, not about intuitionistic propositional logic.

This file supplies the missing half: the two directions of

    Γ ⊢ φ   (natural deduction, `◯`-free)     ⟺     `LJF` derives its translation

and reads the four interpolation properties back across the bridge, giving
**uniform interpolation for IPC** stated in `Deriv` terms.

## The route

Two routes were available.  The one taken here is the cheap one:

* **soundness** (`LJF` ⟹ ND) is a direct four-judgment erasure — focus phases
  carry no information that natural deduction cannot reconstruct;
* **completeness** (ND ⟹ `LJF`) is obtained by *simulating the repository's
  cut-free sequent calculus* `PLLND.SCh` rule by rule in `LJF`, and composing
  with `PLLND.ND_to_SC` (cut elimination, F&M Theorem 2.6, already machine
  checked in `LaxLogic/PLLSequent.lean`).

The alternative — proving identity expansion and cut admissibility for `LJF`
itself, in the style of Simmons' *Structural focalization* — was rejected as
the more expensive route: **no cut whatsoever is needed on the `LJF` side**
once the simulated calculus is cut-free.  That is the whole point of
simulating a *sequent* calculus rather than natural deduction: a sequent
calculus has left rules where natural deduction has elimination rules, and a
left rule is exactly what a left focus performs.  Concretely, `SCh`'s

    A ⊃ B ∈ Γ    Γ ⇒ A    B, Γ ⇒ C
    ------------------------------  (impL)
                Γ ⇒ C

is simulated by `simHyp`: every left focus on the hypothesis `B` in the right
premise is replaced by `LFoc.impL` applied to the left premise, under the
hypothesis `A ⊃ B` that is already in the context.  Nothing is cut.

The one case that genuinely needs an argument is `orL`, where the disjunctive
hypothesis fires (`upMerge`) and hands back the *branch contexts* of the
inversion of `posOf A`, not the hypothesis `negOf A` that the premise was
proved from.  `branchIn` below closes that gap, again without cut: a branch of
`invertPos (posOf φ)` re-proves `negOf φ` by `extract`, which replays the
already-present branch of the inversion.

## Provenance

* `LJF.*` — the focused calculus and its uniform interpolant, `LaxLogic/LJF.lean`.
* `PLLND.LaxND` / `PLLND.SemUI.Deriv` — the canonical natural-deduction system
  ("PLL proves"), `LaxLogic/PLLNDCore.lean` and `LaxLogic/PLLSemUIFrag.lean`.
* `PLLND.SCh` / `PLLND.ND_to_SC` — the cut-free sequent calculus and cut
  elimination, `LaxLogic/PLLSequent.lean`.

See `docs/calculus-map.md`.
-/

namespace LJFIPC

open PLLND (LaxND SCh SC)

/-! ## Part 1: the polarisation translation

Canonical polarity: atoms, `⊥` and `∨` are positive; `⊃` and `∧` are negative.
A formula therefore has *both* a positive and a negative translation, and the
two differ only by a shift at the head:

    posOf φ = ↓(negOf φ)   when φ is `⊃`- or `∧`-headed,
    negOf φ = ↑(posOf φ)   when φ is atom-, `⊥`- or `∨`-headed.

`◯` is transparent: `posOf (◯φ) = posOf φ`.  The translation is thus total on
`PLLFormula`, and equals the translation of the `◯`-erasure.  Every theorem
below about the *round trip* is stated for `◯`-free formulas, where erasure is
the identity; the bridge theorems themselves need no such restriction. -/

mutual

/-- The positive translation. -/
def posOf : PLLFormula → LJF.Pos
  | .prop a     => .atom a
  | .falsePLL   => .fls
  | .or φ ψ     => .or (posOf φ) (posOf ψ)
  | .and φ ψ    => .down (.and (negOf φ) (negOf ψ))
  | .ifThen φ ψ => .down (.imp (posOf φ) (negOf ψ))
  | .somehow φ  => posOf φ

/-- The negative translation. -/
def negOf : PLLFormula → LJF.Neg
  | .prop a     => .up (.atom a)
  | .falsePLL   => .up .fls
  | .or φ ψ     => .up (.or (posOf φ) (posOf ψ))
  | .and φ ψ    => .and (negOf φ) (negOf ψ)
  | .ifThen φ ψ => .imp (posOf φ) (negOf ψ)
  | .somehow φ  => negOf φ

end

/-! ## The erasure back to `PLLFormula` -/

mutual

/-- Forget the polarity of a positive. -/
def unPos : LJF.Pos → PLLFormula
  | .atom a  => .prop a
  | .fls     => .falsePLL
  | .or P Q  => .or (unPos P) (unPos Q)
  | .down N  => unNeg N

/-- Forget the polarity of a negative. -/
def unNeg : LJF.Neg → PLLFormula
  | .up P    => unPos P
  | .imp Q N => .ifThen (unPos Q) (unNeg N)
  | .and M N => .and (unNeg M) (unNeg N)

end

/-! Nothing in the polarised syntax mentions `◯`, so every erasure is an IPL
formula. -/

mutual

theorem isIPL_unPos : ∀ P : LJF.Pos, PLLND.isIPL (unPos P)
  | .atom _  => trivial
  | .fls     => trivial
  | .or P Q  => ⟨isIPL_unPos P, isIPL_unPos Q⟩
  | .down N  => isIPL_unNeg N

theorem isIPL_unNeg : ∀ N : LJF.Neg, PLLND.isIPL (unNeg N)
  | .up P    => isIPL_unPos P
  | .imp Q N => ⟨isIPL_unPos Q, isIPL_unNeg N⟩
  | .and M N => ⟨isIPL_unNeg M, isIPL_unNeg N⟩

end

/-- **The round trip.**  Translating and erasing is `◯`-erasure. -/
theorem un_round : ∀ φ : PLLFormula,
    unPos (posOf φ) = PLLND.erase φ ∧ unNeg (negOf φ) = PLLND.erase φ := by
  intro φ
  induction φ with
  | prop a => exact ⟨rfl, rfl⟩
  | falsePLL => exact ⟨rfl, rfl⟩
  | and a b iha ihb =>
      refine ⟨?_, ?_⟩
      · show unNeg (LJF.Neg.and (negOf a) (negOf b)) = _
        rw [unNeg, iha.2, ihb.2]; rfl
      · show unNeg (LJF.Neg.and (negOf a) (negOf b)) = _
        rw [unNeg, iha.2, ihb.2]; rfl
  | or a b iha ihb =>
      refine ⟨?_, ?_⟩
      · show unPos (LJF.Pos.or (posOf a) (posOf b)) = _
        rw [unPos, iha.1, ihb.1]; rfl
      · show unNeg (LJF.Neg.up (LJF.Pos.or (posOf a) (posOf b))) = _
        rw [unNeg, unPos, iha.1, ihb.1]; rfl
  | ifThen a b iha ihb =>
      refine ⟨?_, ?_⟩
      · show unNeg (LJF.Neg.imp (posOf a) (negOf b)) = _
        rw [unNeg, iha.1, ihb.2]; rfl
      · show unNeg (LJF.Neg.imp (posOf a) (negOf b)) = _
        rw [unNeg, iha.1, ihb.2]; rfl
  | somehow a iha => exact ⟨iha.1, iha.2⟩

theorem unPos_posOf (φ : PLLFormula) : unPos (posOf φ) = PLLND.erase φ :=
  (un_round φ).1

theorem unNeg_negOf (φ : PLLFormula) : unNeg (negOf φ) = PLLND.erase φ :=
  (un_round φ).2

theorem unNeg_negOf_isIPL {φ : PLLFormula} (h : PLLND.isIPL φ) :
    unNeg (negOf φ) = φ := by
  rw [unNeg_negOf, PLLND.erase_eq_self_of_isIPL φ h]

theorem map_unNeg_negOf {Γ : List PLLFormula} (h : ∀ ψ ∈ Γ, PLLND.isIPL ψ) :
    (Γ.map negOf).map unNeg = Γ := by
  sorry
