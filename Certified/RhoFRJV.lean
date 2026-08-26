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
import FRJ.WitnessV
import FRJ.WitnessV1215
import FRJ.WitnessV1918
import FRJ.WitnessV2018
import FRJ.WitnessV2013
import FRJ.WitnessV2012
import LaxLogic.RN.Rho
import LaxLogic.Deriv

open PLLND PLLND.SemUI RhoOrder

-- The namespace is kept as `FRJVConsequences` (not `Certified.…`) because the
-- redevelopment branch already cites these names; hoisted from
-- `wip/frjv_consequences.lean`, which remains as a forwarding stub.
namespace FRJVConsequences

/-- The witness formulas of `wip/frjv_witness.lean` are the images of the
ρ-cells. -/
theorem ofPLL_g80 : FRJ.ofPLL (PLLFormula.ifThen (rhoF 12) (rhoF 9)) = FRJ.WitnessV.G80 := by
  decide

theorem ofPLL_g81 : FRJ.ofPLL (PLLFormula.ifThen (rhoF 13) (rhoF 6)) = FRJ.WitnessV.G81 := by
  decide

/-- `[ρ12] ⊬ ρ9`, through the repaired calculus. -/
theorem rho12_nle_rho9_viaV : [rhoF 12] ⊬ rhoF 9 :=
  FRJ.not_entails_of_provableV (ofPLL_g80 ▸ FRJ.WitnessV.provableV_G80)

/-- `[ρ13] ⊬ ρ6`, through the repaired calculus. -/
theorem rho13_nle_rho6_viaV : [rhoF 13] ⊬ rhoF 6 :=
  FRJ.not_entails_of_provableV (ofPLL_g81 ▸ FRJ.WitnessV.provableV_G81)

/-! ## THE FRONTIER CELL: `ρ12 ⊢? ρ15` SETTLED NEGATIVE

The single remaining open claim of the 462-cell ρ-order matrix
(`RNDB.frontierOrder`).  The repaired calculus derives the refutation
sequent (`wip/frjv_witness_1215.lean`, hand-built, kernel-checked), and
`soundnessV` turns it into the underivability of the cell.  With its
converse already battery-settled (`ρ15 ⊬ ρ12`), the pair {ρ12, ρ15} is
INCOMPARABLE and no Hasse edge moves.  Banking this as an `RNDB` entry
and retiring `frontierOrder` is a DATA-layer decision — Matthew's. -/

theorem ofPLL_g1215 :
    FRJ.ofPLL (PLLFormula.ifThen (rhoF 12) (rhoF 15)) = FRJ.WitnessV1215.G1215 := by
  decide

/-- `[ρ12] ⊬ ρ15` — the last open cell of the matrix, settled through
the repaired calculus. -/
theorem rho12_nle_rho15 : [rhoF 12] ⊬ rhoF 15 :=
  FRJ.not_entails_of_provableV (ofPLL_g1215 ▸ FRJ.WitnessV1215.provableV_1215)

/-! ## Pins -/

/-- info: 'FRJVConsequences.rho12_nle_rho9_viaV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho12_nle_rho9_viaV

/-- info: 'FRJVConsequences.rho13_nle_rho6_viaV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho13_nle_rho6_viaV

/-- info: 'FRJVConsequences.rho12_nle_rho15' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho12_nle_rho15


/-! ## The four hand witnesses (2026-08-26): the FRJX sweep's remaining
misses, settled THROUGH the repaired calculus by hand-built derivations
(`FRJ/WitnessV1918.lean`, `V2018`, `V2013`, `V2012`) — with the two
engine hits at raised join arity (ρ12⊬ρ18, ρ13⊬ρ18), every ⊬ cell of
the 462-cell matrix the sweep could not re-derive is now known INSIDE
FRJV: no incompleteness witness survives the corpus. -/

theorem ofPLL_g1918 :
    FRJ.ofPLL (PLLFormula.ifThen (rhoF 19) (rhoF 18)) = FRJ.WitnessV1918.G1918 := by
  decide

theorem ofPLL_g2018 :
    FRJ.ofPLL (PLLFormula.ifThen (rhoF 20) (rhoF 18)) = FRJ.WitnessV2018.G2018 := by
  decide

theorem ofPLL_g2013 :
    FRJ.ofPLL (PLLFormula.ifThen (rhoF 20) (rhoF 13)) = FRJ.WitnessV2013.G2013 := by
  decide

theorem ofPLL_g2012 :
    FRJ.ofPLL (PLLFormula.ifThen (rhoF 20) (rhoF 12)) = FRJ.WitnessV2012.G2012 := by
  decide

/-- `[ρ19] ⊬ ρ18`, through the repaired calculus (hand witness). -/
theorem rho19_nle_rho18_viaV : [rhoF 19] ⊬ rhoF 18 :=
  FRJ.not_entails_of_provableV (ofPLL_g1918 ▸ FRJ.WitnessV1918.provableV_1918)

/-- `[ρ20] ⊬ ρ18`, through the repaired calculus (hand witness). -/
theorem rho20_nle_rho18_viaV : [rhoF 20] ⊬ rhoF 18 :=
  FRJ.not_entails_of_provableV (ofPLL_g2018 ▸ FRJ.WitnessV2018.provableV_2018)

/-- `[ρ20] ⊬ ρ13`, through the repaired calculus (hand witness). -/
theorem rho20_nle_rho13_viaV : [rhoF 20] ⊬ rhoF 13 :=
  FRJ.not_entails_of_provableV (ofPLL_g2013 ▸ FRJ.WitnessV2013.provableV_2013)

/-- `[ρ20] ⊬ ρ12`, through the repaired calculus (hand witness). -/
theorem rho20_nle_rho12_viaV : [rhoF 20] ⊬ rhoF 12 :=
  FRJ.not_entails_of_provableV (ofPLL_g2012 ▸ FRJ.WitnessV2012.provableV_2012)

/-- info: 'FRJVConsequences.rho19_nle_rho18_viaV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho19_nle_rho18_viaV

/-- info: 'FRJVConsequences.rho20_nle_rho18_viaV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho20_nle_rho18_viaV

/-- info: 'FRJVConsequences.rho20_nle_rho13_viaV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho20_nle_rho13_viaV

/-- info: 'FRJVConsequences.rho20_nle_rho12_viaV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho20_nle_rho12_viaV

end FRJVConsequences
