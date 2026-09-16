/-
# The two hand cells: ρ20∧ρ21 ≡ ρ20 and ρ20∨ρ21 ≡ ρ21

The R-increment generator's two skips (`rcellsgen`, 2026-08-26): the
forward directions defeated the G4 searcher not on content but on
compound-identity expansion (G4's `init` is atomic; the closed fragment
has no atoms).  ND has `iden` at every formula, so the cells are hand
terms.  Both absorptions reduce to the single fact

    ρ20 ⊢ ρ21,  i.e.  [(b ⊃ ρ4) ⊃ ρ6] ⊢ (ρ9 ⊃ ρ4) ⊃ b

(a = ◯⊥, b = ◯¬a, ρ4 = a∨¬a, ρ6 = ¬a∨¬¬a, ρ9 = b∨¬¬a), proved
constructively: from K : ρ9⊃ρ4, `fun hb => K (inl hb)` inhabits b⊃ρ4,
so the hypothesis yields ρ6; case ¬a gives b by the unit; case ¬¬a
feeds K again for ρ4, where case a = ◯⊥ gives b by bind-over-falsum
and case ¬a is absurd against ¬¬a.
-/
import LaxLogic.Interd
import LaxLogic.RN.Rho
import Rewrite.Core

open PLLFormula PLLND RhoOrder

namespace PLLND
namespace SemUI
namespace RCH

/-! ## The formulas, spelled out -/

private abbrev aF   : PLLFormula := .somehow .falsePLL          -- a  = ◯⊥
private abbrev naF  : PLLFormula := .ifThen aF .falsePLL        -- ¬a
private abbrev bF   : PLLFormula := .somehow naF                -- b  = ◯¬a
private abbrev nnaF : PLLFormula := .ifThen naF .falsePLL       -- ¬¬a
private abbrev r4   : PLLFormula := .or aF naF                  -- ρ4
private abbrev r6   : PLLFormula := .or naF nnaF                -- ρ6
private abbrev r9   : PLLFormula := .or bF nnaF                 -- ρ9
private abbrev r20  : PLLFormula := .ifThen (.ifThen bF r4) r6  -- ρ20
private abbrev r21  : PLLFormula := .ifThen (.ifThen r9 r4) bF  -- ρ21

-- statement-alignment guards: the spelled-out formulas ARE ρ20/ρ21
example : rhoF 20 = r20 := by decide
example : rhoF 21 = r21 := by decide

/-! ## The content lemma, over any context containing ρ20 -/

/-- `ρ20 ⊢ ρ21`, context-polymorphic (weakening for free). -/
private def nd2021 : ∀ {Γ : List PLLFormula}, r20 ∈ Γ → LaxND Γ r21 :=
  fun {_} h =>
  -- goal (ρ9 ⊃ ρ4) ⊃ b: assume K
  .impIntro (
    -- context K :: Γ, K = ρ9 ⊃ ρ4
    -- b ⊃ ρ4 from K:  fun hb => K (inl hb)
    -- feed it to ρ20 and case on ρ6
    .orElim (φ := naF) (ψ := nnaF)
      (.impElim (.iden (List.mem_cons_of_mem _ h))
        (.impIntro
          (.impElim (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.orIntro1 (.iden (List.mem_cons_self ..))))))
      -- case ¬a  (context ¬a :: K :: Γ): the unit
      (.laxIntro (.iden (List.mem_cons_self ..)))
      -- case ¬¬a (context ¬¬a :: K :: Γ): K at (inr ¬¬a) gives ρ4
      (.orElim (φ := aF) (ψ := naF)
        (.impElim (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          (.orIntro2 (.iden (List.mem_cons_self ..))))
        -- case a = ◯⊥ (context a :: ¬¬a :: K :: Γ): bind over falsum
        (.laxElim (.iden (List.mem_cons_self ..))
          (.falsoElim _ (.iden (List.mem_cons_self ..))))
        -- case ¬a (context ¬a :: ¬¬a :: K :: Γ): absurd against ¬¬a
        (.falsoElim _
          (.impElim (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.iden (List.mem_cons_self ..))))))

/-! ## The two cells -/

theorem rc_and_20_21 : Interd ((rhoF 20).and (rhoF 21)) (rhoF 20) :=
  ⟨⟨.andElim1 (.iden (List.mem_cons_self ..))⟩,
   ⟨.andIntro (.iden (List.mem_cons_self ..))
              (nd2021 (List.mem_cons_self ..))⟩⟩

theorem rc_or_20_21 : Interd ((rhoF 20).or (rhoF 21)) (rhoF 21) :=
  ⟨⟨.orElim (.iden (List.mem_cons_self ..))
            (nd2021 (List.mem_cons_self ..))
            (.iden (List.mem_cons_self ..))⟩,
   ⟨.orIntro2 (.iden (List.mem_cons_self ..))⟩⟩

/-- The two hand rules, same orientation as the generated set. -/
def rcHandSet : List Rewrite.RwRule :=
  [ ⟨_, _, rc_and_20_21⟩, ⟨_, _, rc_or_20_21⟩ ]

end RCH
end SemUI
end PLLND

/-! ## Pins -/

/-- info: 'PLLND.SemUI.RCH.rc_and_20_21' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.SemUI.RCH.rc_and_20_21

/-- info: 'PLLND.SemUI.RCH.rc_or_20_21' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.SemUI.RCH.rc_or_20_21
