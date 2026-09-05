/-
The instance bound — the certified form of the screening principle of
`docs/ui-ljfo-clause-table.md` §4.10 (2026-09-05).

For a cell `Γ ⇒ G`, an eliminated atom `p`, and a `p`-free `χ`, every
`p`-free `Δ` sufficient for the cell (`Δ, Γ ⊢ G`) satisfies

    Δ ⊢ Γ[χ/p] ⊃ G[χ/p],

by substituting `χ` for `p` in the derivation (`substND`), under which the
`p`-free `Δ` is unchanged.  So the χ-instance bound `Γ[χ] ⊃ G[χ]` is a
`p`-free upper bound of every sufficient formula; when it is itself
sufficient it is the weakest sufficient `p`-free formula — the cell's
`∀p`.  The record called this "instance closure" and asked for it as a
certificate; the two cells it settled by oracle on 2026-09-04 are
certified below in the kernel.
-/
import LaxLogic.PLLSemUICtx
import Meta.Audit

namespace PLLND.SemUI

open PLLFormula

/-! ## The bound -/

/-- **The instance bound.**  `Δ` `p`-free, `Δ, Γ ⊢ G`  ⟹  `Δ ⊢ Γ[χ] ⊃ G[χ]`. -/
def instanceBound (p : String) (χ : PLLFormula) {Δ Γ G : PLLFormula}
    (hΔ : p ∉ Δ.atoms) (d : LaxND [Δ, Γ] G) :
    LaxND [Δ] (.ifThen (substP p χ Γ) (substP p χ G)) := by
  have d' : LaxND [substP p χ Δ, substP p χ Γ] (substP p χ G) := substND p χ d
  rw [substP_of_not_mem hΔ] at d'
  exact .impIntro (d'.rename (by
    intro ψ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp))

/-- The bound is `p`-free when `χ` is. -/
theorem instanceBound_pfree (p : String) {χ : PLLFormula} (hχ : p ∉ χ.atoms)
    (Γ G : PLLFormula) :
    p ∉ (PLLFormula.ifThen (substP p χ Γ) (substP p χ G)).atoms := by
  intro h
  rcases mem_atoms_ifThen.mp h with h | h
  · exact substP_pfree hχ Γ h
  · exact substP_pfree hχ G h

/-! ## Weakest sufficient formulas and instance closure -/

/-- `ψ` is the weakest `p`-free formula sufficient for the cell `Γ ⇒ G`:
`p`-free, sufficient, and implied by every `p`-free sufficient formula.
This is the cell's `∀p` in Pitts's sense, unrelativised (the goal `G` is
a single formula and `Γ` a single hypothesis). -/
structure IsWeakestSufficient (p : String) (Γ G ψ : PLLFormula) : Prop where
  pfree : p ∉ ψ.atoms
  suff : Nonempty (LaxND [ψ, Γ] G)
  weakest : ∀ Δ : PLLFormula, p ∉ Δ.atoms → Nonempty (LaxND [Δ, Γ] G) →
    Nonempty (LaxND [Δ] ψ)

/-- **Instance closure.**  If the χ-instance bound is itself sufficient, it
is the weakest sufficient `p`-free formula. -/
theorem instanceClosed (p : String) {χ Γ G : PLLFormula} (hχ : p ∉ χ.atoms)
    (suff : Nonempty (LaxND [.ifThen (substP p χ Γ) (substP p χ G), Γ] G)) :
    IsWeakestSufficient p Γ G (.ifThen (substP p χ Γ) (substP p χ G)) where
  pfree := instanceBound_pfree p hχ Γ G
  suff := suff
  weakest := fun _ hΔ ⟨d⟩ => ⟨instanceBound p χ hΔ d⟩

/-! ## The two cells of §4.10, certified

Atoms are named by their letters; `p` is the eliminated atom. -/

def pA : PLLFormula := .prop "p"
def qA : PLLFormula := .prop "q"
def rA : PLLFormula := .prop "r"
def sA : PLLFormula := .prop "s"

/-! ### Cell 1: `{◯p ⊃ r, ◯q} ⇒ ◯p`, closed by `χ = ⊥`

`∀p = ((◯⊥ ⊃ r) ∧ ◯q) ⊃ ◯⊥`, the record's `θmax`. -/

def Γ₁ : PLLFormula := .and (.ifThen (.somehow pA) rA) (.somehow qA)
def G₁ : PLLFormula := .somehow pA
/-- `θmax`, literally the `⊥`-instance bound. -/
def θmax : PLLFormula := .ifThen (substP "p" .falsePLL Γ₁) (substP "p" .falsePLL G₁)

theorem θmax_eq :
    θmax = .ifThen (.and (.ifThen (.somehow .falsePLL) rA) (.somehow qA))
                   (.somehow .falsePLL) := by
  decide

/-- `θmax, Γ₁ ⊢ ◯p`: `◯⊥ ⊃ r` from `◯p ⊃ r` (a box of `⊥` yields a box of
anything), `◯q` from `Γ₁`, so `θmax` yields `◯⊥`, hence `◯p`. -/
def θmax_suff : LaxND [θmax, Γ₁] G₁ := by
  rw [θmax_eq]
  exact
    let boxq : LaxND [.ifThen (.and (.ifThen (.somehow .falsePLL) rA) (.somehow qA)) (.somehow .falsePLL), Γ₁]
        (.somehow qA) := .andElim2 (.iden (.tail _ (.head _)))
    let botr : LaxND [.ifThen (.and (.ifThen (.somehow .falsePLL) rA) (.somehow qA)) (.somehow .falsePLL), Γ₁]
        (.ifThen (.somehow .falsePLL) rA) :=
      .impIntro (.impElim (.andElim1 (.iden (.tail _ (.tail _ (.head _)))))
        (.laxElim (.iden (.head _)) (.falsoElim _ (.iden (.head _)))))
    let boxbot := LaxND.impElim (.iden (.head _)) (.andIntro botr boxq)
    .laxElim boxbot (.falsoElim _ (.iden (.head _)))

theorem cell1_forall_p : IsWeakestSufficient "p" Γ₁ G₁ θmax :=
  instanceClosed "p" (by decide) ⟨θmax_suff⟩

/-! ### Cell 2: `{◯p ⊃ r, s ⊃ ◯p} ⇒ r`, closed by `χ = s`

`∀p = ((◯s ⊃ r) ∧ (s ⊃ ◯s)) ⊃ r`, which is the record's `T = (◯s ⊃ r) ⊃ r`
up to the provable conjunct `s ⊃ ◯s`. -/

def Γ₂ : PLLFormula := .and (.ifThen (.somehow pA) rA) (.ifThen sA (.somehow pA))
def G₂ : PLLFormula := rA
def Ts : PLLFormula := .ifThen (substP "p" sA Γ₂) (substP "p" sA G₂)

theorem Ts_eq :
    Ts = .ifThen (.and (.ifThen (.somehow sA) rA) (.ifThen sA (.somehow sA))) rA := by
  decide

/-- `Ts, Γ₂ ⊢ r`: `◯s ⊃ r` (open `◯s` under the lax goal `◯p`, use
`s ⊃ ◯p`, then `◯p ⊃ r`), `s ⊃ ◯s` outright, so `Ts` yields `r`. -/
def Ts_suff : LaxND [Ts, Γ₂] G₂ := by
  rw [Ts_eq]
  exact
    let boxs_r : LaxND [.ifThen (.and (.ifThen (.somehow sA) rA) (.ifThen sA (.somehow sA))) rA, Γ₂]
        (.ifThen (.somehow sA) rA) :=
      .impIntro (.impElim (.andElim1 (.iden (.tail _ (.tail _ (.head _)))))
        (.laxElim (.iden (.head _))
          (.impElim (.andElim2 (.iden (.tail _ (.tail _ (.tail _ (.head _))))))
            (.iden (.head _)))))
    let s_boxs : LaxND [.ifThen (.and (.ifThen (.somehow sA) rA) (.ifThen sA (.somehow sA))) rA, Γ₂]
        (.ifThen sA (.somehow sA)) :=
      .impIntro (.laxIntro (.iden (.head _)))
    LaxND.impElim (.iden (.head _)) (.andIntro boxs_r s_boxs)

theorem cell2_forall_p : IsWeakestSufficient "p" Γ₂ G₂ Ts :=
  instanceClosed "p" (by decide) ⟨Ts_suff⟩

end PLLND.SemUI

/-! ### Axiom audit — the measured sets (`#axioms_within_pin`, 2026-09-05).
The two sufficiency derivations are closed terms with no axioms at all. -/

#axioms_within PLLND.SemUI.instanceBound [propext, Quot.sound]
#axioms_within PLLND.SemUI.instanceClosed [propext, Quot.sound]
#axioms_within PLLND.SemUI.θmax_suff []
#axioms_within PLLND.SemUI.Ts_suff []
#axioms_within PLLND.SemUI.cell1_forall_p [propext, Quot.sound]
#axioms_within PLLND.SemUI.cell2_forall_p [propext, Quot.sound]
