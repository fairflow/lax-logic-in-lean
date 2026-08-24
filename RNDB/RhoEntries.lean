/-
# The ρ-order refutations as DATABASE ENTRIES — the first bulk migration

Layer 3 begins here: each of the 185 kernel-checked refutation
certificates of `Certified/RhoRefutations.lean` becomes one `RNDB.Entry`.
The `ok` field consumes the certificate theorem DIRECTLY — `[ρi] ⊬ ρj`
is `¬ Nonempty (LaxND [ρi] ρj)` by the reducible abbrev `Underivable`,
and `Deriv Γ φ := Nonempty (LaxND Γ φ)` (LaxLogic/PLLSemUIFrag.lean:30),
so `Claim.Holds` for `Rel.nle` unifies with it with no glue.

GENERATED 2026-08-24 from the banked certificates; regenerate rather
than hand-edit.  Scope on every entry: the 22 ρ-order representatives —
the set these verdicts were asked against.  Provenance: 137 of the 185
confirm cells the two-sided ground truth already held refutable; **48
settle cells it left UNKNOWN**.  Zero conflicts with any proved cell.
-/
import RNDB.Types
import Certified.RhoRefutations
import wip.rho_order

open PLLND PLLND.SemUI

namespace RNDB

/-- The scope every ρ-entry is relative to: the 22 ρ-order classes. -/
def rhoScope : List PLLFormula := (List.range RhoOrder.n).map RhoOrder.rhoF

/-- Smart constructor for a ρ-cell refutation entry: the claim is
`ρi ⊬ ρj` (one-directional, scoped to the ρ catalogue), the evidence a
`w`-world countermodel found by the FRJ(◯) engine, and the obligation is
discharged by the kernel-checked certificate theorem itself. -/
def nleEntry (id : EntryId) (i j w : Nat) (hw : 0 < w)
    (h : ¬ Deriv [RhoOrder.rhoF i] (RhoOrder.rhoF j)) : Entry where
  id := id
  claim := ⟨RhoOrder.rhoF i, RhoOrder.rhoF j, Rel.nle, some rhoScope⟩
  ev := Evidence.countermodel Engine.frj w
  ok := ⟨Claim.wellScoped_some, rfl, hw, h⟩

def nle_1_0 : Entry := nleEntry "rho-0000" 1 0 1 (by decide) RhoCerts.rho_1_nle_0
def nle_1_2 : Entry := nleEntry "rho-0001" 1 2 1 (by decide) RhoCerts.rho_1_nle_2
def nle_1_3 : Entry := nleEntry "rho-0002" 1 3 2 (by decide) RhoCerts.rho_1_nle_3
def nle_1_4 : Entry := nleEntry "rho-0003" 1 4 3 (by decide) RhoCerts.rho_1_nle_4
def nle_1_5 : Entry := nleEntry "rho-0004" 1 5 1 (by decide) RhoCerts.rho_1_nle_5
def nle_1_6 : Entry := nleEntry "rho-0005" 1 6 4 (by decide) RhoCerts.rho_1_nle_6
def nle_1_7 : Entry := nleEntry "rho-0006" 1 7 3 (by decide) RhoCerts.rho_1_nle_7
def nle_1_8 : Entry := nleEntry "rho-0007" 1 8 3 (by decide) RhoCerts.rho_1_nle_8
def nle_1_10 : Entry := nleEntry "rho-0008" 1 10 5 (by decide) RhoCerts.rho_1_nle_10
def nle_1_11 : Entry := nleEntry "rho-0009" 1 11 4 (by decide) RhoCerts.rho_1_nle_11
def nle_1_12 : Entry := nleEntry "rho-0010" 1 12 4 (by decide) RhoCerts.rho_1_nle_12
def nle_1_13 : Entry := nleEntry "rho-0011" 1 13 4 (by decide) RhoCerts.rho_1_nle_13
def nle_1_14 : Entry := nleEntry "rho-0012" 1 14 3 (by decide) RhoCerts.rho_1_nle_14
def nle_1_17 : Entry := nleEntry "rho-0013" 1 17 5 (by decide) RhoCerts.rho_1_nle_17
def nle_2_0 : Entry := nleEntry "rho-0014" 2 0 2 (by decide) RhoCerts.rho_2_nle_0
def nle_2_3 : Entry := nleEntry "rho-0015" 2 3 2 (by decide) RhoCerts.rho_2_nle_3
def nle_3_0 : Entry := nleEntry "rho-0016" 3 0 1 (by decide) RhoCerts.rho_3_nle_0
def nle_3_2 : Entry := nleEntry "rho-0017" 3 2 1 (by decide) RhoCerts.rho_3_nle_2
def nle_3_5 : Entry := nleEntry "rho-0018" 3 5 1 (by decide) RhoCerts.rho_3_nle_5
def nle_4_0 : Entry := nleEntry "rho-0019" 4 0 1 (by decide) RhoCerts.rho_4_nle_0
def nle_4_2 : Entry := nleEntry "rho-0020" 4 2 1 (by decide) RhoCerts.rho_4_nle_2
def nle_4_3 : Entry := nleEntry "rho-0021" 4 3 2 (by decide) RhoCerts.rho_4_nle_3
def nle_4_5 : Entry := nleEntry "rho-0022" 4 5 1 (by decide) RhoCerts.rho_4_nle_5
def nle_5_0 : Entry := nleEntry "rho-0023" 5 0 3 (by decide) RhoCerts.rho_5_nle_0
def nle_5_2 : Entry := nleEntry "rho-0024" 5 2 3 (by decide) RhoCerts.rho_5_nle_2
def nle_5_3 : Entry := nleEntry "rho-0025" 5 3 2 (by decide) RhoCerts.rho_5_nle_3
def nle_5_4 : Entry := nleEntry "rho-0026" 5 4 3 (by decide) RhoCerts.rho_5_nle_4
def nle_5_7 : Entry := nleEntry "rho-0027" 5 7 3 (by decide) RhoCerts.rho_5_nle_7
def nle_5_8 : Entry := nleEntry "rho-0028" 5 8 3 (by decide) RhoCerts.rho_5_nle_8
def nle_5_14 : Entry := nleEntry "rho-0029" 5 14 3 (by decide) RhoCerts.rho_5_nle_14
def nle_6_0 : Entry := nleEntry "rho-0030" 6 0 1 (by decide) RhoCerts.rho_6_nle_0
def nle_6_2 : Entry := nleEntry "rho-0031" 6 2 1 (by decide) RhoCerts.rho_6_nle_2
def nle_6_3 : Entry := nleEntry "rho-0032" 6 3 2 (by decide) RhoCerts.rho_6_nle_3
def nle_6_4 : Entry := nleEntry "rho-0033" 6 4 3 (by decide) RhoCerts.rho_6_nle_4
def nle_6_5 : Entry := nleEntry "rho-0034" 6 5 1 (by decide) RhoCerts.rho_6_nle_5
def nle_6_7 : Entry := nleEntry "rho-0035" 6 7 3 (by decide) RhoCerts.rho_6_nle_7
def nle_6_8 : Entry := nleEntry "rho-0036" 6 8 3 (by decide) RhoCerts.rho_6_nle_8
def nle_6_14 : Entry := nleEntry "rho-0037" 6 14 3 (by decide) RhoCerts.rho_6_nle_14
def nle_7_0 : Entry := nleEntry "rho-0038" 7 0 1 (by decide) RhoCerts.rho_7_nle_0
def nle_7_2 : Entry := nleEntry "rho-0039" 7 2 1 (by decide) RhoCerts.rho_7_nle_2
def nle_7_3 : Entry := nleEntry "rho-0040" 7 3 2 (by decide) RhoCerts.rho_7_nle_3
def nle_7_4 : Entry := nleEntry "rho-0041" 7 4 4 (by decide) RhoCerts.rho_7_nle_4
def nle_7_5 : Entry := nleEntry "rho-0042" 7 5 1 (by decide) RhoCerts.rho_7_nle_5
def nle_7_6 : Entry := nleEntry "rho-0043" 7 6 4 (by decide) RhoCerts.rho_7_nle_6
def nle_7_11 : Entry := nleEntry "rho-0044" 7 11 4 (by decide) RhoCerts.rho_7_nle_11
def nle_7_13 : Entry := nleEntry "rho-0045" 7 13 4 (by decide) RhoCerts.rho_7_nle_13
def nle_7_14 : Entry := nleEntry "rho-0046" 7 14 4 (by decide) RhoCerts.rho_7_nle_14
def nle_7_17 : Entry := nleEntry "rho-0047" 7 17 4 (by decide) RhoCerts.rho_7_nle_17
def nle_8_0 : Entry := nleEntry "rho-0048" 8 0 1 (by decide) RhoCerts.rho_8_nle_0
def nle_8_2 : Entry := nleEntry "rho-0049" 8 2 1 (by decide) RhoCerts.rho_8_nle_2
def nle_8_3 : Entry := nleEntry "rho-0050" 8 3 2 (by decide) RhoCerts.rho_8_nle_3
def nle_8_4 : Entry := nleEntry "rho-0051" 8 4 4 (by decide) RhoCerts.rho_8_nle_4
def nle_8_5 : Entry := nleEntry "rho-0052" 8 5 1 (by decide) RhoCerts.rho_8_nle_5
def nle_8_6 : Entry := nleEntry "rho-0053" 8 6 4 (by decide) RhoCerts.rho_8_nle_6
def nle_8_7 : Entry := nleEntry "rho-0054" 8 7 4 (by decide) RhoCerts.rho_8_nle_7
def nle_8_11 : Entry := nleEntry "rho-0055" 8 11 4 (by decide) RhoCerts.rho_8_nle_11
def nle_8_12 : Entry := nleEntry "rho-0056" 8 12 4 (by decide) RhoCerts.rho_8_nle_12
def nle_8_13 : Entry := nleEntry "rho-0057" 8 13 4 (by decide) RhoCerts.rho_8_nle_13
def nle_8_14 : Entry := nleEntry "rho-0058" 8 14 4 (by decide) RhoCerts.rho_8_nle_14
def nle_8_17 : Entry := nleEntry "rho-0059" 8 17 5 (by decide) RhoCerts.rho_8_nle_17
def nle_9_0 : Entry := nleEntry "rho-0060" 9 0 1 (by decide) RhoCerts.rho_9_nle_0
def nle_9_2 : Entry := nleEntry "rho-0061" 9 2 1 (by decide) RhoCerts.rho_9_nle_2
def nle_9_3 : Entry := nleEntry "rho-0062" 9 3 2 (by decide) RhoCerts.rho_9_nle_3
def nle_9_4 : Entry := nleEntry "rho-0063" 9 4 3 (by decide) RhoCerts.rho_9_nle_4
def nle_9_5 : Entry := nleEntry "rho-0064" 9 5 1 (by decide) RhoCerts.rho_9_nle_5
def nle_9_6 : Entry := nleEntry "rho-0065" 9 6 4 (by decide) RhoCerts.rho_9_nle_6
def nle_9_7 : Entry := nleEntry "rho-0066" 9 7 3 (by decide) RhoCerts.rho_9_nle_7
def nle_9_8 : Entry := nleEntry "rho-0067" 9 8 3 (by decide) RhoCerts.rho_9_nle_8
def nle_9_11 : Entry := nleEntry "rho-0068" 9 11 4 (by decide) RhoCerts.rho_9_nle_11
def nle_9_13 : Entry := nleEntry "rho-0069" 9 13 4 (by decide) RhoCerts.rho_9_nle_13
def nle_9_14 : Entry := nleEntry "rho-0070" 9 14 3 (by decide) RhoCerts.rho_9_nle_14
def nle_9_17 : Entry := nleEntry "rho-0071" 9 17 4 (by decide) RhoCerts.rho_9_nle_17
def nle_10_0 : Entry := nleEntry "rho-0072" 10 0 1 (by decide) RhoCerts.rho_10_nle_0
def nle_10_2 : Entry := nleEntry "rho-0073" 10 2 1 (by decide) RhoCerts.rho_10_nle_2
def nle_10_3 : Entry := nleEntry "rho-0074" 10 3 2 (by decide) RhoCerts.rho_10_nle_3
def nle_10_4 : Entry := nleEntry "rho-0075" 10 4 3 (by decide) RhoCerts.rho_10_nle_4
def nle_10_5 : Entry := nleEntry "rho-0076" 10 5 1 (by decide) RhoCerts.rho_10_nle_5
def nle_10_6 : Entry := nleEntry "rho-0077" 10 6 4 (by decide) RhoCerts.rho_10_nle_6
def nle_10_7 : Entry := nleEntry "rho-0078" 10 7 3 (by decide) RhoCerts.rho_10_nle_7
def nle_10_8 : Entry := nleEntry "rho-0079" 10 8 3 (by decide) RhoCerts.rho_10_nle_8
def nle_10_11 : Entry := nleEntry "rho-0080" 10 11 4 (by decide) RhoCerts.rho_10_nle_11
def nle_10_12 : Entry := nleEntry "rho-0081" 10 12 4 (by decide) RhoCerts.rho_10_nle_12
def nle_10_13 : Entry := nleEntry "rho-0082" 10 13 4 (by decide) RhoCerts.rho_10_nle_13
def nle_10_14 : Entry := nleEntry "rho-0083" 10 14 3 (by decide) RhoCerts.rho_10_nle_14
def nle_10_17 : Entry := nleEntry "rho-0084" 10 17 5 (by decide) RhoCerts.rho_10_nle_17
def nle_11_0 : Entry := nleEntry "rho-0085" 11 0 1 (by decide) RhoCerts.rho_11_nle_0
def nle_11_2 : Entry := nleEntry "rho-0086" 11 2 1 (by decide) RhoCerts.rho_11_nle_2
def nle_11_3 : Entry := nleEntry "rho-0087" 11 3 2 (by decide) RhoCerts.rho_11_nle_3
def nle_11_5 : Entry := nleEntry "rho-0088" 11 5 1 (by decide) RhoCerts.rho_11_nle_5
def nle_12_0 : Entry := nleEntry "rho-0089" 12 0 1 (by decide) RhoCerts.rho_12_nle_0
def nle_12_2 : Entry := nleEntry "rho-0090" 12 2 1 (by decide) RhoCerts.rho_12_nle_2
def nle_12_3 : Entry := nleEntry "rho-0091" 12 3 2 (by decide) RhoCerts.rho_12_nle_3
def nle_12_4 : Entry := nleEntry "rho-0092" 12 4 3 (by decide) RhoCerts.rho_12_nle_4
def nle_12_5 : Entry := nleEntry "rho-0093" 12 5 1 (by decide) RhoCerts.rho_12_nle_5
def nle_12_6 : Entry := nleEntry "rho-0094" 12 6 4 (by decide) RhoCerts.rho_12_nle_6
def nle_12_11 : Entry := nleEntry "rho-0095" 12 11 4 (by decide) RhoCerts.rho_12_nle_11
def nle_12_13 : Entry := nleEntry "rho-0096" 12 13 4 (by decide) RhoCerts.rho_12_nle_13
def nle_12_14 : Entry := nleEntry "rho-0097" 12 14 3 (by decide) RhoCerts.rho_12_nle_14
def nle_12_17 : Entry := nleEntry "rho-0098" 12 17 4 (by decide) RhoCerts.rho_12_nle_17
def nle_13_0 : Entry := nleEntry "rho-0099" 13 0 1 (by decide) RhoCerts.rho_13_nle_0
def nle_13_2 : Entry := nleEntry "rho-0100" 13 2 1 (by decide) RhoCerts.rho_13_nle_2
def nle_13_3 : Entry := nleEntry "rho-0101" 13 3 2 (by decide) RhoCerts.rho_13_nle_3
def nle_13_5 : Entry := nleEntry "rho-0102" 13 5 1 (by decide) RhoCerts.rho_13_nle_5
def nle_14_0 : Entry := nleEntry "rho-0103" 14 0 1 (by decide) RhoCerts.rho_14_nle_0
def nle_14_2 : Entry := nleEntry "rho-0104" 14 2 1 (by decide) RhoCerts.rho_14_nle_2
def nle_14_3 : Entry := nleEntry "rho-0105" 14 3 2 (by decide) RhoCerts.rho_14_nle_3
def nle_14_5 : Entry := nleEntry "rho-0106" 14 5 1 (by decide) RhoCerts.rho_14_nle_5
def nle_15_0 : Entry := nleEntry "rho-0107" 15 0 1 (by decide) RhoCerts.rho_15_nle_0
def nle_15_2 : Entry := nleEntry "rho-0108" 15 2 1 (by decide) RhoCerts.rho_15_nle_2
def nle_15_3 : Entry := nleEntry "rho-0109" 15 3 2 (by decide) RhoCerts.rho_15_nle_3
def nle_15_4 : Entry := nleEntry "rho-0110" 15 4 3 (by decide) RhoCerts.rho_15_nle_4
def nle_15_5 : Entry := nleEntry "rho-0111" 15 5 1 (by decide) RhoCerts.rho_15_nle_5
def nle_15_6 : Entry := nleEntry "rho-0112" 15 6 4 (by decide) RhoCerts.rho_15_nle_6
def nle_15_11 : Entry := nleEntry "rho-0113" 15 11 4 (by decide) RhoCerts.rho_15_nle_11
def nle_15_13 : Entry := nleEntry "rho-0114" 15 13 4 (by decide) RhoCerts.rho_15_nle_13
def nle_15_14 : Entry := nleEntry "rho-0115" 15 14 3 (by decide) RhoCerts.rho_15_nle_14
def nle_15_17 : Entry := nleEntry "rho-0116" 15 17 4 (by decide) RhoCerts.rho_15_nle_17
def nle_16_0 : Entry := nleEntry "rho-0117" 16 0 1 (by decide) RhoCerts.rho_16_nle_0
def nle_16_2 : Entry := nleEntry "rho-0118" 16 2 1 (by decide) RhoCerts.rho_16_nle_2
def nle_16_3 : Entry := nleEntry "rho-0119" 16 3 2 (by decide) RhoCerts.rho_16_nle_3
def nle_16_4 : Entry := nleEntry "rho-0120" 16 4 4 (by decide) RhoCerts.rho_16_nle_4
def nle_16_5 : Entry := nleEntry "rho-0121" 16 5 1 (by decide) RhoCerts.rho_16_nle_5
def nle_16_6 : Entry := nleEntry "rho-0122" 16 6 4 (by decide) RhoCerts.rho_16_nle_6
def nle_16_11 : Entry := nleEntry "rho-0123" 16 11 4 (by decide) RhoCerts.rho_16_nle_11
def nle_16_13 : Entry := nleEntry "rho-0124" 16 13 4 (by decide) RhoCerts.rho_16_nle_13
def nle_16_14 : Entry := nleEntry "rho-0125" 16 14 4 (by decide) RhoCerts.rho_16_nle_14
def nle_16_17 : Entry := nleEntry "rho-0126" 16 17 4 (by decide) RhoCerts.rho_16_nle_17
def nle_17_0 : Entry := nleEntry "rho-0127" 17 0 1 (by decide) RhoCerts.rho_17_nle_0
def nle_17_2 : Entry := nleEntry "rho-0128" 17 2 1 (by decide) RhoCerts.rho_17_nle_2
def nle_17_3 : Entry := nleEntry "rho-0129" 17 3 2 (by decide) RhoCerts.rho_17_nle_3
def nle_17_4 : Entry := nleEntry "rho-0130" 17 4 3 (by decide) RhoCerts.rho_17_nle_4
def nle_17_5 : Entry := nleEntry "rho-0131" 17 5 1 (by decide) RhoCerts.rho_17_nle_5
def nle_17_7 : Entry := nleEntry "rho-0132" 17 7 3 (by decide) RhoCerts.rho_17_nle_7
def nle_17_8 : Entry := nleEntry "rho-0133" 17 8 3 (by decide) RhoCerts.rho_17_nle_8
def nle_17_14 : Entry := nleEntry "rho-0134" 17 14 3 (by decide) RhoCerts.rho_17_nle_14
def nle_18_0 : Entry := nleEntry "rho-0135" 18 0 1 (by decide) RhoCerts.rho_18_nle_0
def nle_18_2 : Entry := nleEntry "rho-0136" 18 2 1 (by decide) RhoCerts.rho_18_nle_2
def nle_18_3 : Entry := nleEntry "rho-0137" 18 3 2 (by decide) RhoCerts.rho_18_nle_3
def nle_18_4 : Entry := nleEntry "rho-0138" 18 4 3 (by decide) RhoCerts.rho_18_nle_4
def nle_18_5 : Entry := nleEntry "rho-0139" 18 5 1 (by decide) RhoCerts.rho_18_nle_5
def nle_18_6 : Entry := nleEntry "rho-0140" 18 6 4 (by decide) RhoCerts.rho_18_nle_6
def nle_18_7 : Entry := nleEntry "rho-0141" 18 7 3 (by decide) RhoCerts.rho_18_nle_7
def nle_18_8 : Entry := nleEntry "rho-0142" 18 8 3 (by decide) RhoCerts.rho_18_nle_8
def nle_18_11 : Entry := nleEntry "rho-0143" 18 11 4 (by decide) RhoCerts.rho_18_nle_11
def nle_18_13 : Entry := nleEntry "rho-0144" 18 13 4 (by decide) RhoCerts.rho_18_nle_13
def nle_18_14 : Entry := nleEntry "rho-0145" 18 14 3 (by decide) RhoCerts.rho_18_nle_14
def nle_18_17 : Entry := nleEntry "rho-0146" 18 17 4 (by decide) RhoCerts.rho_18_nle_17
def nle_19_0 : Entry := nleEntry "rho-0147" 19 0 1 (by decide) RhoCerts.rho_19_nle_0
def nle_19_2 : Entry := nleEntry "rho-0148" 19 2 1 (by decide) RhoCerts.rho_19_nle_2
def nle_19_3 : Entry := nleEntry "rho-0149" 19 3 2 (by decide) RhoCerts.rho_19_nle_3
def nle_19_4 : Entry := nleEntry "rho-0150" 19 4 5 (by decide) RhoCerts.rho_19_nle_4
def nle_19_5 : Entry := nleEntry "rho-0151" 19 5 1 (by decide) RhoCerts.rho_19_nle_5
def nle_19_6 : Entry := nleEntry "rho-0152" 19 6 5 (by decide) RhoCerts.rho_19_nle_6
def nle_19_7 : Entry := nleEntry "rho-0153" 19 7 5 (by decide) RhoCerts.rho_19_nle_7
def nle_19_11 : Entry := nleEntry "rho-0154" 19 11 4 (by decide) RhoCerts.rho_19_nle_11
def nle_19_12 : Entry := nleEntry "rho-0155" 19 12 5 (by decide) RhoCerts.rho_19_nle_12
def nle_19_13 : Entry := nleEntry "rho-0156" 19 13 5 (by decide) RhoCerts.rho_19_nle_13
def nle_19_14 : Entry := nleEntry "rho-0157" 19 14 4 (by decide) RhoCerts.rho_19_nle_14
def nle_19_17 : Entry := nleEntry "rho-0158" 19 17 5 (by decide) RhoCerts.rho_19_nle_17
def nle_20_0 : Entry := nleEntry "rho-0159" 20 0 1 (by decide) RhoCerts.rho_20_nle_0
def nle_20_2 : Entry := nleEntry "rho-0160" 20 2 1 (by decide) RhoCerts.rho_20_nle_2
def nle_20_3 : Entry := nleEntry "rho-0161" 20 3 2 (by decide) RhoCerts.rho_20_nle_3
def nle_20_4 : Entry := nleEntry "rho-0162" 20 4 3 (by decide) RhoCerts.rho_20_nle_4
def nle_20_5 : Entry := nleEntry "rho-0163" 20 5 1 (by decide) RhoCerts.rho_20_nle_5
def nle_20_6 : Entry := nleEntry "rho-0164" 20 6 5 (by decide) RhoCerts.rho_20_nle_6
def nle_20_7 : Entry := nleEntry "rho-0165" 20 7 3 (by decide) RhoCerts.rho_20_nle_7
def nle_20_8 : Entry := nleEntry "rho-0166" 20 8 3 (by decide) RhoCerts.rho_20_nle_8
def nle_20_10 : Entry := nleEntry "rho-0167" 20 10 8 (by decide) RhoCerts.rho_20_nle_10
def nle_20_11 : Entry := nleEntry "rho-0168" 20 11 4 (by decide) RhoCerts.rho_20_nle_11
def nle_20_12 : Entry := nleEntry "rho-0169" 20 12 5 (by decide) RhoCerts.rho_20_nle_12
def nle_20_13 : Entry := nleEntry "rho-0170" 20 13 5 (by decide) RhoCerts.rho_20_nle_13
def nle_20_14 : Entry := nleEntry "rho-0171" 20 14 3 (by decide) RhoCerts.rho_20_nle_14
def nle_20_17 : Entry := nleEntry "rho-0172" 20 17 5 (by decide) RhoCerts.rho_20_nle_17
def nle_21_0 : Entry := nleEntry "rho-0173" 21 0 1 (by decide) RhoCerts.rho_21_nle_0
def nle_21_2 : Entry := nleEntry "rho-0174" 21 2 1 (by decide) RhoCerts.rho_21_nle_2
def nle_21_3 : Entry := nleEntry "rho-0175" 21 3 2 (by decide) RhoCerts.rho_21_nle_3
def nle_21_4 : Entry := nleEntry "rho-0176" 21 4 3 (by decide) RhoCerts.rho_21_nle_4
def nle_21_5 : Entry := nleEntry "rho-0177" 21 5 1 (by decide) RhoCerts.rho_21_nle_5
def nle_21_6 : Entry := nleEntry "rho-0178" 21 6 5 (by decide) RhoCerts.rho_21_nle_6
def nle_21_7 : Entry := nleEntry "rho-0179" 21 7 3 (by decide) RhoCerts.rho_21_nle_7
def nle_21_11 : Entry := nleEntry "rho-0180" 21 11 4 (by decide) RhoCerts.rho_21_nle_11
def nle_21_12 : Entry := nleEntry "rho-0181" 21 12 5 (by decide) RhoCerts.rho_21_nle_12
def nle_21_13 : Entry := nleEntry "rho-0182" 21 13 5 (by decide) RhoCerts.rho_21_nle_13
def nle_21_14 : Entry := nleEntry "rho-0183" 21 14 3 (by decide) RhoCerts.rho_21_nle_14
def nle_21_17 : Entry := nleEntry "rho-0184" 21 17 5 (by decide) RhoCerts.rho_21_nle_17

/-- All 185, as data.  `Entry.holds` makes every claim in this list a
theorem; `entries_hold` (RNDB/Types.lean) says so for any list, so no
per-entry pin is needed beyond the axiom audit at the foot. -/
def rhoEntries : List Entry :=
  [ nle_1_0,
    nle_1_2,
    nle_1_3,
    nle_1_4,
    nle_1_5,
    nle_1_6,
    nle_1_7,
    nle_1_8,
    nle_1_10,
    nle_1_11,
    nle_1_12,
    nle_1_13,
    nle_1_14,
    nle_1_17,
    nle_2_0,
    nle_2_3,
    nle_3_0,
    nle_3_2,
    nle_3_5,
    nle_4_0,
    nle_4_2,
    nle_4_3,
    nle_4_5,
    nle_5_0,
    nle_5_2,
    nle_5_3,
    nle_5_4,
    nle_5_7,
    nle_5_8,
    nle_5_14,
    nle_6_0,
    nle_6_2,
    nle_6_3,
    nle_6_4,
    nle_6_5,
    nle_6_7,
    nle_6_8,
    nle_6_14,
    nle_7_0,
    nle_7_2,
    nle_7_3,
    nle_7_4,
    nle_7_5,
    nle_7_6,
    nle_7_11,
    nle_7_13,
    nle_7_14,
    nle_7_17,
    nle_8_0,
    nle_8_2,
    nle_8_3,
    nle_8_4,
    nle_8_5,
    nle_8_6,
    nle_8_7,
    nle_8_11,
    nle_8_12,
    nle_8_13,
    nle_8_14,
    nle_8_17,
    nle_9_0,
    nle_9_2,
    nle_9_3,
    nle_9_4,
    nle_9_5,
    nle_9_6,
    nle_9_7,
    nle_9_8,
    nle_9_11,
    nle_9_13,
    nle_9_14,
    nle_9_17,
    nle_10_0,
    nle_10_2,
    nle_10_3,
    nle_10_4,
    nle_10_5,
    nle_10_6,
    nle_10_7,
    nle_10_8,
    nle_10_11,
    nle_10_12,
    nle_10_13,
    nle_10_14,
    nle_10_17,
    nle_11_0,
    nle_11_2,
    nle_11_3,
    nle_11_5,
    nle_12_0,
    nle_12_2,
    nle_12_3,
    nle_12_4,
    nle_12_5,
    nle_12_6,
    nle_12_11,
    nle_12_13,
    nle_12_14,
    nle_12_17,
    nle_13_0,
    nle_13_2,
    nle_13_3,
    nle_13_5,
    nle_14_0,
    nle_14_2,
    nle_14_3,
    nle_14_5,
    nle_15_0,
    nle_15_2,
    nle_15_3,
    nle_15_4,
    nle_15_5,
    nle_15_6,
    nle_15_11,
    nle_15_13,
    nle_15_14,
    nle_15_17,
    nle_16_0,
    nle_16_2,
    nle_16_3,
    nle_16_4,
    nle_16_5,
    nle_16_6,
    nle_16_11,
    nle_16_13,
    nle_16_14,
    nle_16_17,
    nle_17_0,
    nle_17_2,
    nle_17_3,
    nle_17_4,
    nle_17_5,
    nle_17_7,
    nle_17_8,
    nle_17_14,
    nle_18_0,
    nle_18_2,
    nle_18_3,
    nle_18_4,
    nle_18_5,
    nle_18_6,
    nle_18_7,
    nle_18_8,
    nle_18_11,
    nle_18_13,
    nle_18_14,
    nle_18_17,
    nle_19_0,
    nle_19_2,
    nle_19_3,
    nle_19_4,
    nle_19_5,
    nle_19_6,
    nle_19_7,
    nle_19_11,
    nle_19_12,
    nle_19_13,
    nle_19_14,
    nle_19_17,
    nle_20_0,
    nle_20_2,
    nle_20_3,
    nle_20_4,
    nle_20_5,
    nle_20_6,
    nle_20_7,
    nle_20_8,
    nle_20_10,
    nle_20_11,
    nle_20_12,
    nle_20_13,
    nle_20_14,
    nle_20_17,
    nle_21_0,
    nle_21_2,
    nle_21_3,
    nle_21_4,
    nle_21_5,
    nle_21_6,
    nle_21_7,
    nle_21_11,
    nle_21_12,
    nle_21_13,
    nle_21_14,
    nle_21_17 ]

set_option maxRecDepth 4096 in
theorem rhoEntries_length : rhoEntries.length = 185 := rfl

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.rhoEntries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rhoEntries
/-- info: 'RNDB.rhoEntries_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rhoEntries_length

end RNDB