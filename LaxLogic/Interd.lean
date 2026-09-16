/-
# `Interd` — interderivability, hoisted out of the semantic-UI campaign

The second stranded shared definition of the W1 pattern, alongside
`Deriv` (`LaxLogic/Deriv.lean`): `Interd φ ψ` is `Deriv [φ] ψ ∧
Deriv [ψ] φ`, depends on nothing but `LaxND`, and is what every
dictionary cell is stated in — yet it lived only inside
`PLLSemUIFrag.lean`, whose import chain carries the parked semantic-UI
campaign and (through `PLLSemUILayered`) a `sorry`.  Hoisted 2026-08-24
so that results stated in `Interd` stand independently of the campaign.

Namespace `PLLND.SemUI` preserved, as for `Deriv`: roughly eighty files
name it that way.
-/
import LaxLogic.Deriv

open PLLFormula

namespace PLLND
namespace SemUI


/-! ## Interderivability -/

/-- Interderivability: each formula proves the other from a single
hypothesis. -/
def Interd (φ ψ : PLLFormula) : Prop :=
  Nonempty (LaxND [φ] ψ) ∧ Nonempty (LaxND [ψ] φ)

namespace Interd

theorem refl (φ : PLLFormula) : Interd φ φ :=
  ⟨⟨.iden (.head _)⟩, ⟨.iden (.head _)⟩⟩

theorem symm {φ ψ : PLLFormula} (h : Interd φ ψ) : Interd ψ φ := ⟨h.2, h.1⟩

theorem trans {φ ψ χ : PLLFormula} (h₁ : Interd φ ψ) (h₂ : Interd ψ χ) :
    Interd φ χ :=
  ⟨Deriv.cutHead h₁.1 h₂.1, Deriv.cutHead h₂.2 h₁.2⟩

/-- **Interderivable formulas are derivable together from the empty
context.**  This is what lets a decision procedure work on a NORMALISED
formula and report the verdict about the ORIGINAL: with
`Rewrite.simplifyWith_interd` it gives
`Nonempty (LaxND [] φ) ↔ Nonempty (LaxND [] (simplifyWith rs n φ))`.

Note it transfers PROVABILITY, not proof TERMS: `Interd` is `Prop`-valued
(a pair of `Nonempty`s), so a `Tm` for the normal form does not yield a
`Tm` for the original.  A tool may print the term it actually has — the
one for the normal form — and prove the original by this lemma. -/
theorem closed_iff {φ ψ : PLLFormula} (h : Interd φ ψ) :
    Nonempty (LaxND [] φ) ↔ Nonempty (LaxND [] ψ) :=
  ⟨fun ⟨d⟩ => h.1.elim fun e => ⟨.impElim (.impIntro e) d⟩,
   fun ⟨d⟩ => h.2.elim fun e => ⟨.impElim (.impIntro e) d⟩⟩

theorem and_congr {φ φ' ψ ψ' : PLLFormula} (h₁ : Interd φ φ') (h₂ : Interd ψ ψ') :
    Interd (φ.and ψ) (φ'.and ψ') :=
  ⟨Deriv.andIntro (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) h₁.1)
      (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) h₂.1),
   Deriv.andIntro (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) h₁.2)
      (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) h₂.2)⟩

theorem or_congr {φ φ' ψ ψ' : PLLFormula} (h₁ : Interd φ φ') (h₂ : Interd ψ ψ') :
    Interd (φ.or ψ) (φ'.or ψ') :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
      (Deriv.orIntro1 (Deriv.toHead h₁.1)) (Deriv.orIntro2 (Deriv.toHead h₂.1)),
   Deriv.orElim (Deriv.iden (.head _))
      (Deriv.orIntro1 (Deriv.toHead h₁.2)) (Deriv.orIntro2 (Deriv.toHead h₂.2))⟩

theorem imp_congr {φ φ' ψ ψ' : PLLFormula} (h₁ : Interd φ φ') (h₂ : Interd ψ ψ') :
    Interd (φ.ifThen ψ) (φ'.ifThen ψ') := by
  refine ⟨?_, ?_⟩
  · refine Deriv.impIntro (Deriv.cutHead
      (Deriv.impElim (Deriv.iden (.tail _ (.head _))) ?_) h₂.1)
    exact Deriv.cutHead (Deriv.iden (.head _)) h₁.2
  · refine Deriv.impIntro (Deriv.cutHead
      (Deriv.impElim (Deriv.iden (.tail _ (.head _))) ?_) h₂.2)
    exact Deriv.cutHead (Deriv.iden (.head _)) h₁.1

theorem box_congr {φ φ' : PLLFormula} (h : Interd φ φ') :
    Interd (PLLFormula.somehow φ) (PLLFormula.somehow φ') :=
  ⟨Deriv.somehowMono h.1, Deriv.somehowMono h.2⟩

end Interd

end SemUI
end PLLND
