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

/-- **Weak p-purity**: atoms other than `p` are decorated only at
fallible worlds.  (STRICT purity `PPure` is inconsistent with
fallibility: `full_F` puts every fallible world in every `V a`, so a
strictly pure `ConstraintModel` has `F = ∅` — the infallible class,
PICLL not PCLL.  Weak purity is what the fallible battery models
actually satisfy, and the atoms clause below recovers the transfer
through the fall-tie and `full_F`.) -/
def PPureF (p : String) (C : ConstraintModel) : Prop :=
  ∀ a, a ≠ p → ∀ w : C.W, w ∈ C.V a → w ∈ C.F

/-- **The levelled agreement Wit-family** over weakly p-pure mutually
confluent models. -/
def lvlB (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPureF p K) (hPM : PPureF p M) :
    LayeredBisimWit (fun a => a ≠ p) K M where
  Z := lvlZ K M
  mono := fun hZ χ hc ha => hZ χ (by omega) ha
  atoms := by
    intro n k m hZ a ha
    have hfall : k ∈ K.F ↔ m ∈ M.F := by
      have := hZ .falsePLL (by simp [crank])
        (by intro b hb; simp [PLLFormula.atoms] at hb)
      simpa [ConstraintModel.force] using this
    constructor
    · intro hk
      exact M.full_F (hfall.mp (hPK a ha k hk))
    · intro hm
      exact K.full_F (hfall.mpr (hPM a ha m hm))
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
    (hPK : PPureF p K) (hPM : PPureF p M) :
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
