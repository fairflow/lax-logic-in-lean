/-
STAGE 2, part (e): the LEVELLED agreement Wit-family over p-pure
confluent models — the dictionary-free constant link.

`wip/stabilise.lean`'s constant family needed `D : RNDict` to make one
rank serve all; the levelled family `Z α := rank-2α closed-formula
agreement` finances itself and its clauses are exactly today's proved
lemmas: i-clauses by the character argument (`agree_iforth`/`iback` at
`V := ∅`), the witness m-clauses by the σ-ping-pong
(`agree_mwit`/`agree_mwitN`), atoms by p-purity, fall by the `⊥`
instance.  This family feeds `amalgamation_assembledW`
(`wip/witOut.lean`) modulo `MwitResidue` — the (f) item.
-/
import wip.pcll1pv_stage2
import wip.stabilise

namespace PLLND
namespace SemUI

open Classical

variable {p : String} {K M : ConstraintModel}

/-- The levelled variable-free agreement: rank-2α agreement on closed
formulas. -/
def lvlZ (K M : ConstraintModel) (α : Nat) (k : K.W) (m : M.W) : Prop :=
  ∀ χ : PLLFormula, crank χ ≤ 2 * α →
    (∀ a ∈ χ.atoms, a ∈ (∅ : Finset String)) →
    (K.force k χ ↔ M.force m χ)

/-- **The levelled agreement Wit-family** over p-pure mutually
confluent models. -/
def lvlB (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M) :
    LayeredBisimWit (fun a => a ≠ p) K M where
  Z := lvlZ K M
  mono := fun hZ χ hc ha => hZ χ (by omega) ha
  atoms := by
    intro n k m _ a ha
    exact iff_of_false (hPK a ha k) (hPM a ha m)
  fall := by
    intro n k m hZ
    have := hZ .falsePLL (by simp [crank])
      (by intro b hb; simp [PLLFormula.atoms] at hb)
    simpa [ConstraintModel.force] using this
  iforth := by
    intro n k m hZ v hv
    by_cases hvF : v ∈ K.F
    · exact .inr hvF
    · exact .inl (agree_iforth (V := (∅ : Finset String)) (α := n)
        (fun χ hc ha => hZ χ (by omega) ha) hv hvF)
  iback := by
    intro n k m hZ v' hv'
    by_cases hv'F : v' ∈ M.F
    · exact .inr hv'F
    · exact .inl (agree_iback (V := (∅ : Finset String)) (α := n)
        (fun χ hc ha => hZ χ (by omega) ha) hv' hv'F)
  mwit := by
    intro n k m hZ ψ hex
    exact agree_mwit hK hM (fun χ hc ha => hZ χ (by omega) ha) hex

/-- The M-side witness clause holds for the levelled family. -/
theorem lvlB_mwitM (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M) :
    (lvlB (p := p) hK hM hPK hPM).MWitM := by
  intro n k m hZ ψ hex
  exact agree_mwitN hK hM (fun χ hc ha => hZ χ (by omega) ha) hex

/-! ## Pins -/

/--
info: 'PLLND.SemUI.lvlB' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms lvlB

/--
info: 'PLLND.SemUI.lvlB_mwitM' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms lvlB_mwitM

end SemUI
end PLLND
