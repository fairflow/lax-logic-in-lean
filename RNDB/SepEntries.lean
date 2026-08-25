/-
# The 95 battery-separation entries (GENERATED with Certified/RhoSeparations.lean)

Engine is `finCM` — the confluent battery found these countermodels;
provenance only, never a truth condition.  `worlds` = separating frame size.
-/
import RNDB.RhoEntries
import Certified.RhoSeparations

open PLLND PLLND.SemUI PLLFormula

namespace RNDB

/-- Like `nleEntry` but for battery-found countermodels. -/
def sepEntry (id : EntryId) (i j w : Nat) (hw : 0 < w)
    (h : ¬ Deriv [RhoOrder.rhoF i] (RhoOrder.rhoF j)) : Entry where
  id := id
  claim := ⟨RhoOrder.rhoF i, RhoOrder.rhoF j, Rel.nle, some rhoScope⟩
  ev := Evidence.countermodel Engine.finCM w
  ok := ⟨Claim.wellScoped_some, rfl, hw, h⟩

def nle_1_9 : Entry := sepEntry "sep-1" 1 9 4 (by decide) RhoSeps.rho_1_nle_9
def nle_1_15 : Entry := sepEntry "sep-2" 1 15 5 (by decide) RhoSeps.rho_1_nle_15
def nle_1_16 : Entry := sepEntry "sep-3" 1 16 3 (by decide) RhoSeps.rho_1_nle_16
def nle_1_18 : Entry := sepEntry "sep-4" 1 18 5 (by decide) RhoSeps.rho_1_nle_18
def nle_5_16 : Entry := sepEntry "sep-5" 5 16 3 (by decide) RhoSeps.rho_5_nle_16
def nle_5_19 : Entry := sepEntry "sep-6" 5 19 3 (by decide) RhoSeps.rho_5_nle_19
def nle_6_16 : Entry := sepEntry "sep-7" 6 16 3 (by decide) RhoSeps.rho_6_nle_16
def nle_6_19 : Entry := sepEntry "sep-8" 6 19 3 (by decide) RhoSeps.rho_6_nle_19
def nle_8_9 : Entry := sepEntry "sep-9" 8 9 4 (by decide) RhoSeps.rho_8_nle_9
def nle_8_15 : Entry := sepEntry "sep-10" 8 15 5 (by decide) RhoSeps.rho_8_nle_15
def nle_8_16 : Entry := sepEntry "sep-11" 8 16 5 (by decide) RhoSeps.rho_8_nle_16
def nle_8_18 : Entry := sepEntry "sep-12" 8 18 5 (by decide) RhoSeps.rho_8_nle_18
def nle_8_20 : Entry := sepEntry "sep-13" 8 20 4 (by decide) RhoSeps.rho_8_nle_20
def nle_8_21 : Entry := sepEntry "sep-14" 8 21 4 (by decide) RhoSeps.rho_8_nle_21
def nle_9_16 : Entry := sepEntry "sep-15" 9 16 3 (by decide) RhoSeps.rho_9_nle_16
def nle_9_19 : Entry := sepEntry "sep-16" 9 19 3 (by decide) RhoSeps.rho_9_nle_19
def nle_10_9 : Entry := sepEntry "sep-17" 10 9 4 (by decide) RhoSeps.rho_10_nle_9
def nle_10_15 : Entry := sepEntry "sep-18" 10 15 5 (by decide) RhoSeps.rho_10_nle_15
def nle_10_16 : Entry := sepEntry "sep-19" 10 16 3 (by decide) RhoSeps.rho_10_nle_16
def nle_10_18 : Entry := sepEntry "sep-20" 10 18 5 (by decide) RhoSeps.rho_10_nle_18
def nle_10_20 : Entry := sepEntry "sep-21" 10 20 4 (by decide) RhoSeps.rho_10_nle_20
def nle_10_21 : Entry := sepEntry "sep-22" 10 21 4 (by decide) RhoSeps.rho_10_nle_21
def nle_11_4 : Entry := sepEntry "sep-23" 11 4 3 (by decide) RhoSeps.rho_11_nle_4
def nle_11_6 : Entry := sepEntry "sep-24" 11 6 4 (by decide) RhoSeps.rho_11_nle_6
def nle_11_7 : Entry := sepEntry "sep-25" 11 7 3 (by decide) RhoSeps.rho_11_nle_7
def nle_11_8 : Entry := sepEntry "sep-26" 11 8 3 (by decide) RhoSeps.rho_11_nle_8
def nle_11_9 : Entry := sepEntry "sep-27" 11 9 4 (by decide) RhoSeps.rho_11_nle_9
def nle_11_10 : Entry := sepEntry "sep-28" 11 10 5 (by decide) RhoSeps.rho_11_nle_10
def nle_11_12 : Entry := sepEntry "sep-29" 11 12 4 (by decide) RhoSeps.rho_11_nle_12
def nle_11_14 : Entry := sepEntry "sep-30" 11 14 3 (by decide) RhoSeps.rho_11_nle_14
def nle_11_16 : Entry := sepEntry "sep-31" 11 16 3 (by decide) RhoSeps.rho_11_nle_16
def nle_11_18 : Entry := sepEntry "sep-32" 11 18 5 (by decide) RhoSeps.rho_11_nle_18
def nle_11_19 : Entry := sepEntry "sep-33" 11 19 3 (by decide) RhoSeps.rho_11_nle_19
def nle_11_20 : Entry := sepEntry "sep-34" 11 20 4 (by decide) RhoSeps.rho_11_nle_20
def nle_11_21 : Entry := sepEntry "sep-35" 11 21 4 (by decide) RhoSeps.rho_11_nle_21
def nle_12_7 : Entry := sepEntry "sep-36" 12 7 3 (by decide) RhoSeps.rho_12_nle_7
def nle_12_8 : Entry := sepEntry "sep-37" 12 8 3 (by decide) RhoSeps.rho_12_nle_8
def nle_12_10 : Entry := sepEntry "sep-38" 12 10 5 (by decide) RhoSeps.rho_12_nle_10
def nle_12_16 : Entry := sepEntry "sep-39" 12 16 3 (by decide) RhoSeps.rho_12_nle_16
def nle_12_18 : Entry := sepEntry "sep-40" 12 18 5 (by decide) RhoSeps.rho_12_nle_18
def nle_12_19 : Entry := sepEntry "sep-41" 12 19 3 (by decide) RhoSeps.rho_12_nle_19
def nle_12_20 : Entry := sepEntry "sep-42" 12 20 5 (by decide) RhoSeps.rho_12_nle_20
def nle_13_16 : Entry := sepEntry "sep-43" 13 16 3 (by decide) RhoSeps.rho_13_nle_16
def nle_13_17 : Entry := sepEntry "sep-44" 13 17 5 (by decide) RhoSeps.rho_13_nle_17
def nle_13_18 : Entry := sepEntry "sep-45" 13 18 5 (by decide) RhoSeps.rho_13_nle_18
def nle_13_19 : Entry := sepEntry "sep-46" 13 19 3 (by decide) RhoSeps.rho_13_nle_19
def nle_13_20 : Entry := sepEntry "sep-47" 13 20 5 (by decide) RhoSeps.rho_13_nle_20
def nle_14_4 : Entry := sepEntry "sep-48" 14 4 4 (by decide) RhoSeps.rho_14_nle_4
def nle_14_6 : Entry := sepEntry "sep-49" 14 6 4 (by decide) RhoSeps.rho_14_nle_6
def nle_14_7 : Entry := sepEntry "sep-50" 14 7 4 (by decide) RhoSeps.rho_14_nle_7
def nle_14_9 : Entry := sepEntry "sep-51" 14 9 4 (by decide) RhoSeps.rho_14_nle_9
def nle_14_12 : Entry := sepEntry "sep-52" 14 12 4 (by decide) RhoSeps.rho_14_nle_12
def nle_14_13 : Entry := sepEntry "sep-53" 14 13 4 (by decide) RhoSeps.rho_14_nle_13
def nle_14_19 : Entry := sepEntry "sep-54" 14 19 4 (by decide) RhoSeps.rho_14_nle_19
def nle_14_20 : Entry := sepEntry "sep-55" 14 20 4 (by decide) RhoSeps.rho_14_nle_20
def nle_14_21 : Entry := sepEntry "sep-56" 14 21 4 (by decide) RhoSeps.rho_14_nle_21
def nle_15_7 : Entry := sepEntry "sep-57" 15 7 3 (by decide) RhoSeps.rho_15_nle_7
def nle_15_8 : Entry := sepEntry "sep-58" 15 8 3 (by decide) RhoSeps.rho_15_nle_8
def nle_15_9 : Entry := sepEntry "sep-59" 15 9 4 (by decide) RhoSeps.rho_15_nle_9
def nle_15_10 : Entry := sepEntry "sep-60" 15 10 5 (by decide) RhoSeps.rho_15_nle_10
def nle_15_12 : Entry := sepEntry "sep-61" 15 12 4 (by decide) RhoSeps.rho_15_nle_12
def nle_15_16 : Entry := sepEntry "sep-62" 15 16 3 (by decide) RhoSeps.rho_15_nle_16
def nle_15_18 : Entry := sepEntry "sep-63" 15 18 5 (by decide) RhoSeps.rho_15_nle_18
def nle_15_19 : Entry := sepEntry "sep-64" 15 19 3 (by decide) RhoSeps.rho_15_nle_19
def nle_15_20 : Entry := sepEntry "sep-65" 15 20 4 (by decide) RhoSeps.rho_15_nle_20
def nle_15_21 : Entry := sepEntry "sep-66" 15 21 4 (by decide) RhoSeps.rho_15_nle_21
def nle_16_7 : Entry := sepEntry "sep-67" 16 7 4 (by decide) RhoSeps.rho_16_nle_7
def nle_16_9 : Entry := sepEntry "sep-68" 16 9 4 (by decide) RhoSeps.rho_16_nle_9
def nle_16_12 : Entry := sepEntry "sep-69" 16 12 4 (by decide) RhoSeps.rho_16_nle_12
def nle_16_19 : Entry := sepEntry "sep-70" 16 19 4 (by decide) RhoSeps.rho_16_nle_19
def nle_16_20 : Entry := sepEntry "sep-71" 16 20 4 (by decide) RhoSeps.rho_16_nle_20
def nle_16_21 : Entry := sepEntry "sep-72" 16 21 4 (by decide) RhoSeps.rho_16_nle_21
def nle_17_13 : Entry := sepEntry "sep-73" 17 13 4 (by decide) RhoSeps.rho_17_nle_13
def nle_17_16 : Entry := sepEntry "sep-74" 17 16 3 (by decide) RhoSeps.rho_17_nle_16
def nle_17_19 : Entry := sepEntry "sep-75" 17 19 3 (by decide) RhoSeps.rho_17_nle_19
def nle_17_20 : Entry := sepEntry "sep-76" 17 20 4 (by decide) RhoSeps.rho_17_nle_20
def nle_17_21 : Entry := sepEntry "sep-77" 17 21 4 (by decide) RhoSeps.rho_17_nle_21
def nle_18_9 : Entry := sepEntry "sep-78" 18 9 4 (by decide) RhoSeps.rho_18_nle_9
def nle_18_12 : Entry := sepEntry "sep-79" 18 12 4 (by decide) RhoSeps.rho_18_nle_12
def nle_18_16 : Entry := sepEntry "sep-80" 18 16 3 (by decide) RhoSeps.rho_18_nle_16
def nle_18_19 : Entry := sepEntry "sep-81" 18 19 3 (by decide) RhoSeps.rho_18_nle_19
def nle_18_20 : Entry := sepEntry "sep-82" 18 20 4 (by decide) RhoSeps.rho_18_nle_20
def nle_18_21 : Entry := sepEntry "sep-83" 18 21 4 (by decide) RhoSeps.rho_18_nle_21
def nle_19_15 : Entry := sepEntry "sep-84" 19 15 5 (by decide) RhoSeps.rho_19_nle_15
def nle_19_16 : Entry := sepEntry "sep-85" 19 16 5 (by decide) RhoSeps.rho_19_nle_16
def nle_19_18 : Entry := sepEntry "sep-86" 19 18 5 (by decide) RhoSeps.rho_19_nle_18
def nle_20_15 : Entry := sepEntry "sep-87" 20 15 5 (by decide) RhoSeps.rho_20_nle_15
def nle_20_16 : Entry := sepEntry "sep-88" 20 16 3 (by decide) RhoSeps.rho_20_nle_16
def nle_20_18 : Entry := sepEntry "sep-89" 20 18 5 (by decide) RhoSeps.rho_20_nle_18
def nle_20_19 : Entry := sepEntry "sep-90" 20 19 3 (by decide) RhoSeps.rho_20_nle_19
def nle_21_15 : Entry := sepEntry "sep-91" 21 15 5 (by decide) RhoSeps.rho_21_nle_15
def nle_21_16 : Entry := sepEntry "sep-92" 21 16 3 (by decide) RhoSeps.rho_21_nle_16
def nle_21_18 : Entry := sepEntry "sep-93" 21 18 5 (by decide) RhoSeps.rho_21_nle_18
def nle_21_19 : Entry := sepEntry "sep-94" 21 19 3 (by decide) RhoSeps.rho_21_nle_19
def nle_21_20 : Entry := sepEntry "sep-95" 21 20 5 (by decide) RhoSeps.rho_21_nle_20

/-- All 95 separation entries. -/
def sepEntries : List Entry :=
  [ nle_1_9, nle_1_15, nle_1_16, nle_1_18, nle_5_16, nle_5_19, nle_6_16, nle_6_19, nle_8_9, nle_8_15, nle_8_16, nle_8_18, nle_8_20, nle_8_21, nle_9_16, nle_9_19, nle_10_9, nle_10_15, nle_10_16, nle_10_18, nle_10_20, nle_10_21, nle_11_4, nle_11_6, nle_11_7, nle_11_8, nle_11_9, nle_11_10, nle_11_12, nle_11_14, nle_11_16, nle_11_18, nle_11_19, nle_11_20, nle_11_21, nle_12_7, nle_12_8, nle_12_10, nle_12_16, nle_12_18, nle_12_19, nle_12_20, nle_13_16, nle_13_17, nle_13_18, nle_13_19, nle_13_20, nle_14_4, nle_14_6, nle_14_7, nle_14_9, nle_14_12, nle_14_13, nle_14_19, nle_14_20, nle_14_21, nle_15_7, nle_15_8, nle_15_9, nle_15_10, nle_15_12, nle_15_16, nle_15_18, nle_15_19, nle_15_20, nle_15_21, nle_16_7, nle_16_9, nle_16_12, nle_16_19, nle_16_20, nle_16_21, nle_17_13, nle_17_16, nle_17_19, nle_17_20, nle_17_21, nle_18_9, nle_18_12, nle_18_16, nle_18_19, nle_18_20, nle_18_21, nle_19_15, nle_19_16, nle_19_18, nle_20_15, nle_20_16, nle_20_18, nle_20_19, nle_21_15, nle_21_16, nle_21_18, nle_21_19, nle_21_20 ]

set_option maxRecDepth 4096 in
theorem sepEntries_length : sepEntries.length = 95 := rfl

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.sepEntries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sepEntries

end RNDB
