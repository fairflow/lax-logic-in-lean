/-
# Consequences of the repaired calculus, end to end

The RefAt campaign's closing theorems: the hand-built repaired-calculus
witnesses (`wip/frjv_witness.lean`) composed with the PROVED soundness
(`FRJ/SoundV.lean`) and the bridge (`FRJ/BridgeV.lean`) re-derive the
kernel refutations of the two incompleteness cells — a THIRD independent
route (after the sepM `decide` and the banked battery certificates),
this time THROUGH the repaired calculus:

    derivation in FRJV  +  soundnessV  ⟹  ¬ Deriv [ρᵢ] ρⱼ

So the repair is validated end to end inside the kernel: the calculus
derives the cells the paper calculus provably cannot, and its
derivations mean what they must.
-/
import FRJ.BridgeV
import wip.frjv_witness
import LaxLogic.RN.Rho
import LaxLogic.Deriv

open PLLND PLLND.SemUI RhoOrder

namespace FRJVConsequences

/-- The witness formulas of `wip/frjv_witness.lean` are the images of the
ρ-cells. -/
theorem ofPLL_g80 : FRJ.ofPLL (PLLFormula.ifThen (rhoF 12) (rhoF 9)) = G80 := by
  decide

theorem ofPLL_g81 : FRJ.ofPLL (PLLFormula.ifThen (rhoF 13) (rhoF 6)) = G81 := by
  decide

/-- `[ρ12] ⊬ ρ9`, through the repaired calculus. -/
theorem rho12_nle_rho9_viaV : ¬ Deriv [rhoF 12] (rhoF 9) :=
  FRJ.not_entails_of_provableV (ofPLL_g80 ▸ provableV_G80)

/-- `[ρ13] ⊬ ρ6`, through the repaired calculus. -/
theorem rho13_nle_rho6_viaV : ¬ Deriv [rhoF 13] (rhoF 6) :=
  FRJ.not_entails_of_provableV (ofPLL_g81 ▸ provableV_G81)

/-! ## Pins -/

/-- info: 'FRJVConsequences.rho12_nle_rho9_viaV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho12_nle_rho9_viaV

/-- info: 'FRJVConsequences.rho13_nle_rho6_viaV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho13_nle_rho6_viaV

end FRJVConsequences
