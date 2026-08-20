import LaxLogic.PLLNDCore
import LaxLogic.PLLConsequence

/-!
# `Deriv` — derivability as a `Prop`, with the rules lifted to it

`Γ ⊢- φ` (`LaxND Γ φ`) is the *type* of natural-deduction derivations;
`Deriv Γ φ` is its inhabitedness, i.e. the proposition "PLL proves
`Γ ⊢ φ`".  It is the positive counterpart of `Γ ⊬ φ` (`Underivable`,
`PLLNDCore.lean`), which is literally its negation, and it is the form
in which derivability is stated wherever a `Prop` is wanted rather than
a term.

The rest of the file lifts each `LaxND` constructor to `Deriv`, plus
`toHead` (weaken a one-hypothesis derivation) and `cutHead` (cut against
a single hypothesis).

Namespace note: these live in `PLLND.SemUI` for historical reasons —
they were first written inside the semantic uniform-interpolation
campaign (`PLLSemUIFrag.lean`, 2026-07-20) and are referenced under that
name by roughly eighty files.  Nothing about `Deriv` is specific to that
campaign, and moving the declarations here is what lets results built on
them stand independently of it.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-! ## Derivability, `Prop`-level -/

/-- `Deriv Γ φ`: the natural-deduction sequent `Γ ⊢ φ` is derivable. -/
def Deriv (Γ : List PLLFormula) (φ : PLLFormula) : Prop := Nonempty (LaxND Γ φ)

namespace Deriv

theorem iden {Γ : List PLLFormula} {φ : PLLFormula} (h : φ ∈ Γ) : Deriv Γ φ :=
  ⟨.iden h⟩

theorem rename {Γ Γ' : List PLLFormula} {φ : PLLFormula}
    (H : ∀ χ ∈ Γ, χ ∈ Γ') : Deriv Γ φ → Deriv Γ' φ
  | ⟨p⟩ => ⟨p.rename H⟩

theorem falsoElim {Γ : List PLLFormula} (φ : PLLFormula) :
    Deriv Γ .falsePLL → Deriv Γ φ
  | ⟨p⟩ => ⟨.falsoElim φ p⟩

theorem impIntro {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv (φ :: Γ) ψ → Deriv Γ (φ.ifThen ψ)
  | ⟨p⟩ => ⟨.impIntro p⟩

theorem impElim {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ (φ.ifThen ψ) → Deriv Γ φ → Deriv Γ ψ
  | ⟨p⟩, ⟨q⟩ => ⟨.impElim p q⟩

theorem andIntro {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ φ → Deriv Γ ψ → Deriv Γ (φ.and ψ)
  | ⟨p⟩, ⟨q⟩ => ⟨.andIntro p q⟩

theorem andElim1 {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ (φ.and ψ) → Deriv Γ φ
  | ⟨p⟩ => ⟨.andElim1 p⟩

theorem andElim2 {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ (φ.and ψ) → Deriv Γ ψ
  | ⟨p⟩ => ⟨.andElim2 p⟩

theorem orIntro1 {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ φ → Deriv Γ (φ.or ψ)
  | ⟨p⟩ => ⟨.orIntro1 p⟩

theorem orIntro2 {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ ψ → Deriv Γ (φ.or ψ)
  | ⟨p⟩ => ⟨.orIntro2 p⟩

theorem orElim {Γ : List PLLFormula} {φ ψ χ : PLLFormula} :
    Deriv Γ (φ.or ψ) → Deriv (φ :: Γ) χ → Deriv (ψ :: Γ) χ → Deriv Γ χ
  | ⟨p⟩, ⟨q₁⟩, ⟨q₂⟩ => ⟨.orElim p q₁ q₂⟩

theorem somehowMono {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv (φ :: Γ) ψ → Deriv (.somehow φ :: Γ) (.somehow ψ)
  | ⟨p⟩ => ⟨LaxND.somehowMono p⟩

/-- Weaken a one-hypothesis derivation to any context carrying that
hypothesis at the head. -/
theorem toHead {φ ψ : PLLFormula} {Γ : List PLLFormula} (h : Deriv [φ] ψ) :
    Deriv (φ :: Γ) ψ :=
  h.rename fun χ hχ => by
    simp only [List.mem_singleton] at hχ; subst hχ; exact List.mem_cons_self ..

/-- Cut against a single hypothesis. -/
theorem cutHead {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (p : Deriv Γ φ) (q : Deriv [φ] ψ) : Deriv Γ ψ :=
  impElim (impIntro q.toHead) p

end Deriv

end SemUI
end PLLND
