/-
# The FRJ(◯) incompleteness candidates, as FRONTIER members

GENERATED 2026-08-24 from the 185-cell cap-free sweep of 2026-08-24
(scratch log `rho185.txt`; harness `lake exe frjdiff --rho`, engine
`FRJ/Search/Profile.lean`, no arity caps, `lamCap` off).

## What each member is

A `Claim` — `⟨ρᵢ, ρⱼ, Rel.nle, some rhoScope⟩` — that is UNSETTLED
RELATIVE TO THIS DATABASE: no entry in `allEntries` backs it.  Verified
at generation time (Python, exact match on the banked index pairs): none
of the 79 appears among the 185 banked ρ-refutations.  A `Frontier`
asserts nothing; these are questions, recorded as data.

## Why these 79 are not ordinary open questions

Each carries a THREE-PART evidence situation, recorded per-member in the
end-of-line comments (rounds, database size, profile count, time):

1. the two-sided ground truth of 2026-08-22 certifies the cell
   REFUTABLE — a kernel-checkable countermodel exists (found by the G4c
   battery; never banked, which is WHY the claim is frontier);
2. FRJ(◯)'s saturation CLOSED on the cell with EVERY cap observed slack
   (`caps=NONE`: rounds unexhausted, RS/IS far under bound, `lamCap`
   off, no arity caps exist in this engine) and constructed nothing;
3. the misses are consequent-shaped — five ∨/⊃-over-modal-compound
   target shapes account for all of them, 0/56 refuted across every
   antecedent tried.

So each member is simultaneously (a) a routine banking task — emit the
G4c countermodel and the claim leaves the frontier as a settled entry —
and (b) an INCOMPLETENESS CANDIDATE for the FRJ(◯) search: settled
cell, cap-free closure, nothing found.  The candidate becomes a WITNESS
against `Certified.CompletenessFRJ` only through the FinCM → FRJ.Kripke
unification (Matthew's instruction: unify, do not bridge — see
`docs/frj-profile-search.md`), and modulo the unproved subsumption in
`insertAllR`/`insertAllI`.  Until then: candidates, not witnesses, and
this list IS the incompleteness miner's output.

## What is deliberately NOT here

No in-Lean freshness theorem.  `frontier79.all (fun c => rhoEntries.all
(e.claim ≠ c))` is ~15k kernel comparisons of catalogue-sized formulas
through `rhoF`'s list lookups — a build liability out of proportion to
what it checks.  Freshness is verified by the generator (exact index
pairs) and recorded here; re-run the generator to re-verify.
-/
import RNDB.RhoEntries

open PLLND PLLND.SemUI

namespace RNDB

def frontier79 : Frontier :=

  [
    ⟨RhoOrder.rhoF 5, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ5⊬ρ16?  closed cap-free  [r=8 RS=16 IS=23 fams=109 caps=NONE 46ms]
    ⟨RhoOrder.rhoF 5, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ5⊬ρ19?  closed cap-free  [r=6 RS=7 IS=15 fams=34 caps=NONE 6ms]
    ⟨RhoOrder.rhoF 6, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ6⊬ρ16?  closed cap-free  [r=8 RS=16 IS=25 fams=111 caps=NONE 70ms]
    ⟨RhoOrder.rhoF 6, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ6⊬ρ19?  closed cap-free  [r=6 RS=7 IS=17 fams=36 caps=NONE 12ms]
    ⟨RhoOrder.rhoF 8, RhoOrder.rhoF 9, Rel.nle, some rhoScope⟩,  -- ρ8⊬ρ9?  closed cap-free  [r=5 RS=6 IS=17 fams=44 caps=NONE 6ms]
    ⟨RhoOrder.rhoF 8, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ8⊬ρ19?  closed cap-free  [r=5 RS=6 IS=25 fams=68 caps=NONE 20ms]
    ⟨RhoOrder.rhoF 8, RhoOrder.rhoF 20, Rel.nle, some rhoScope⟩,  -- ρ8⊬ρ20?  closed cap-free  [r=7 RS=7 IS=44 fams=439 caps=NONE 339ms]
    ⟨RhoOrder.rhoF 8, RhoOrder.rhoF 21, Rel.nle, some rhoScope⟩,  -- ρ8⊬ρ21?  closed cap-free  [r=5 RS=6 IS=28 fams=71 caps=NONE 47ms]
    ⟨RhoOrder.rhoF 9, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ9⊬ρ16?  closed cap-free  [r=8 RS=16 IS=25 fams=111 caps=NONE 101ms]
    ⟨RhoOrder.rhoF 9, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ9⊬ρ19?  closed cap-free  [r=6 RS=10 IS=25 fams=52 caps=NONE 37ms]
    ⟨RhoOrder.rhoF 10, RhoOrder.rhoF 9, Rel.nle, some rhoScope⟩,  -- ρ10⊬ρ9?  closed cap-free  [r=6 RS=9 IS=27 fams=77 caps=NONE 24ms]
    ⟨RhoOrder.rhoF 10, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ10⊬ρ16?  closed cap-free  [r=8 RS=25 IS=52 fams=300 caps=NONE 517ms]
    ⟨RhoOrder.rhoF 10, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ10⊬ρ19?  closed cap-free  [r=6 RS=9 IS=43 fams=121 caps=NONE 127ms]
    ⟨RhoOrder.rhoF 10, RhoOrder.rhoF 20, Rel.nle, some rhoScope⟩,  -- ρ10⊬ρ20?  closed cap-free  [r=7 RS=10 IS=74 fams=724 caps=NONE 1742ms]
    ⟨RhoOrder.rhoF 10, RhoOrder.rhoF 21, Rel.nle, some rhoScope⟩,  -- ρ10⊬ρ21?  closed cap-free  [r=6 RS=9 IS=46 fams=124 caps=NONE 293ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 4, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ4?  closed cap-free  [r=5 RS=6 IS=13 fams=43 caps=NONE 2ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 6, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ6?  closed cap-free  [r=5 RS=7 IS=23 fams=140 caps=NONE 16ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 7, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ7?  closed cap-free  [r=4 RS=5 IS=9 fams=17 caps=NONE 1ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 8, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ8?  closed cap-free  [r=7 RS=8 IS=18 fams=51 caps=NONE 6ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 9, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ9?  closed cap-free  [r=4 RS=6 IS=17 fams=44 caps=NONE 6ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 12, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ12?  closed cap-free  [r=6 RS=7 IS=26 fams=84 caps=NONE 23ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 13, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ13?  closed cap-free  [r=6 RS=8 IS=32 fams=246 caps=NONE 40ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 14, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ14?  closed cap-free  [r=8 RS=16 IS=34 fams=174 caps=NONE 87ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ16?  closed cap-free  [r=8 RS=16 IS=34 fams=143 caps=NONE 143ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ19?  closed cap-free  [r=4 RS=5 IS=12 fams=20 caps=NONE 12ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 20, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ20?  closed cap-free  [r=6 RS=7 IS=29 fams=271 caps=NONE 104ms]
    ⟨RhoOrder.rhoF 11, RhoOrder.rhoF 21, Rel.nle, some rhoScope⟩,  -- ρ11⊬ρ21?  closed cap-free  [r=4 RS=6 IS=28 fams=71 caps=NONE 71ms]
    ⟨RhoOrder.rhoF 12, RhoOrder.rhoF 7, Rel.nle, some rhoScope⟩,  -- ρ12⊬ρ7?  closed cap-free  [r=7 RS=11 IS=26 fams=67 caps=NONE 17ms]
    ⟨RhoOrder.rhoF 12, RhoOrder.rhoF 8, Rel.nle, some rhoScope⟩,  -- ρ12⊬ρ8?  closed cap-free  [r=7 RS=10 IS=28 fams=69 caps=NONE 23ms]
    ⟨RhoOrder.rhoF 12, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ12⊬ρ16?  closed cap-free  [r=8 RS=17 IS=38 fams=221 caps=NONE 260ms]
    ⟨RhoOrder.rhoF 12, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ12⊬ρ19?  closed cap-free  [r=7 RS=11 IS=45 fams=102 caps=NONE 139ms]
    ⟨RhoOrder.rhoF 13, RhoOrder.rhoF 4, Rel.nle, some rhoScope⟩,  -- ρ13⊬ρ4?  closed cap-free  [r=7 RS=8 IS=23 fams=109 caps=NONE 11ms]
    ⟨RhoOrder.rhoF 13, RhoOrder.rhoF 7, Rel.nle, some rhoScope⟩,  -- ρ13⊬ρ7?  closed cap-free  [r=7 RS=8 IS=18 fams=51 caps=NONE 6ms]
    ⟨RhoOrder.rhoF 13, RhoOrder.rhoF 8, Rel.nle, some rhoScope⟩,  -- ρ13⊬ρ8?  closed cap-free  [r=7 RS=7 IS=20 fams=53 caps=NONE 10ms]
    ⟨RhoOrder.rhoF 13, RhoOrder.rhoF 14, Rel.nle, some rhoScope⟩,  -- ρ13⊬ρ14?  closed cap-free  [r=8 RS=16 IS=38 fams=240 caps=NONE 136ms]
    ⟨RhoOrder.rhoF 13, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ13⊬ρ16?  closed cap-free  [r=8 RS=17 IS=38 fams=209 caps=NONE 268ms]
    ⟨RhoOrder.rhoF 13, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ13⊬ρ19?  closed cap-free  [r=7 RS=8 IS=29 fams=70 caps=NONE 71ms]
    ⟨RhoOrder.rhoF 14, RhoOrder.rhoF 4, Rel.nle, some rhoScope⟩,  -- ρ14⊬ρ4?  closed cap-free  [r=5 RS=7 IS=21 fams=94 caps=NONE 12ms]
    ⟨RhoOrder.rhoF 14, RhoOrder.rhoF 6, Rel.nle, some rhoScope⟩,  -- ρ14⊬ρ6?  closed cap-free  [r=5 RS=7 IS=26 fams=143 caps=NONE 27ms]
    ⟨RhoOrder.rhoF 14, RhoOrder.rhoF 7, Rel.nle, some rhoScope⟩,  -- ρ14⊬ρ7?  closed cap-free  [r=4 RS=6 IS=17 fams=44 caps=NONE 7ms]
    ⟨RhoOrder.rhoF 14, RhoOrder.rhoF 9, Rel.nle, some rhoScope⟩,  -- ρ14⊬ρ9?  closed cap-free  [r=4 RS=6 IS=20 fams=47 caps=NONE 14ms]
    ⟨RhoOrder.rhoF 14, RhoOrder.rhoF 12, Rel.nle, some rhoScope⟩,  -- ρ14⊬ρ12?  closed cap-free  [r=6 RS=7 IS=29 fams=87 caps=NONE 50ms]
    ⟨RhoOrder.rhoF 14, RhoOrder.rhoF 13, Rel.nle, some rhoScope⟩,  -- ρ14⊬ρ13?  closed cap-free  [r=6 RS=8 IS=35 fams=249 caps=NONE 79ms]
    ⟨RhoOrder.rhoF 14, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ14⊬ρ19?  closed cap-free  [r=4 RS=6 IS=28 fams=71 caps=NONE 72ms]
    ⟨RhoOrder.rhoF 14, RhoOrder.rhoF 20, Rel.nle, some rhoScope⟩,  -- ρ14⊬ρ20?  closed cap-free  [r=6 RS=7 IS=47 fams=442 caps=NONE 457ms]
    ⟨RhoOrder.rhoF 14, RhoOrder.rhoF 21, Rel.nle, some rhoScope⟩,  -- ρ14⊬ρ21?  closed cap-free  [r=4 RS=6 IS=23 fams=50 caps=NONE 146ms]
    ⟨RhoOrder.rhoF 15, RhoOrder.rhoF 7, Rel.nle, some rhoScope⟩,  -- ρ15⊬ρ7?  closed cap-free  [r=4 RS=8 IS=15 fams=27 caps=NONE 7ms]
    ⟨RhoOrder.rhoF 15, RhoOrder.rhoF 8, Rel.nle, some rhoScope⟩,  -- ρ15⊬ρ8?  closed cap-free  [r=7 RS=11 IS=28 fams=69 caps=NONE 30ms]
    ⟨RhoOrder.rhoF 15, RhoOrder.rhoF 9, Rel.nle, some rhoScope⟩,  -- ρ15⊬ρ9?  closed cap-free  [r=5 RS=13 IS=27 fams=70 caps=NONE 40ms]
    ⟨RhoOrder.rhoF 15, RhoOrder.rhoF 12, Rel.nle, some rhoScope⟩,  -- ρ15⊬ρ12?  closed cap-free  [r=6 RS=14 IS=44 fams=134 caps=NONE 149ms]
    ⟨RhoOrder.rhoF 15, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ15⊬ρ16?  closed cap-free  [r=8 RS=16 IS=36 fams=145 caps=NONE 426ms]
    ⟨RhoOrder.rhoF 15, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ15⊬ρ19?  closed cap-free  [r=4 RS=8 IS=18 fams=30 caps=NONE 78ms]
    ⟨RhoOrder.rhoF 15, RhoOrder.rhoF 20, Rel.nle, some rhoScope⟩,  -- ρ15⊬ρ20?  closed cap-free  [r=6 RS=17 IS=47 fams=505 caps=NONE 608ms]
    ⟨RhoOrder.rhoF 15, RhoOrder.rhoF 21, Rel.nle, some rhoScope⟩,  -- ρ15⊬ρ21?  closed cap-free  [r=5 RS=13 IS=46 fams=121 caps=NONE 477ms]
    ⟨RhoOrder.rhoF 16, RhoOrder.rhoF 7, Rel.nle, some rhoScope⟩,  -- ρ16⊬ρ7?  closed cap-free  [r=5 RS=13 IS=27 fams=70 caps=NONE 39ms]
    ⟨RhoOrder.rhoF 16, RhoOrder.rhoF 9, Rel.nle, some rhoScope⟩,  -- ρ16⊬ρ9?  closed cap-free  [r=5 RS=13 IS=30 fams=73 caps=NONE 78ms]
    ⟨RhoOrder.rhoF 16, RhoOrder.rhoF 12, Rel.nle, some rhoScope⟩,  -- ρ16⊬ρ12?  closed cap-free  [r=6 RS=14 IS=47 fams=137 caps=NONE 317ms]
    ⟨RhoOrder.rhoF 16, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ16⊬ρ19?  closed cap-free  [r=5 RS=13 IS=46 fams=121 caps=NONE 480ms]
    ⟨RhoOrder.rhoF 16, RhoOrder.rhoF 20, Rel.nle, some rhoScope⟩,  -- ρ16⊬ρ20?  closed cap-free  [r=6 RS=17 IS=81 fams=908 caps=NONE 2749ms]
    ⟨RhoOrder.rhoF 16, RhoOrder.rhoF 21, Rel.nle, some rhoScope⟩,  -- ρ16⊬ρ21?  closed cap-free  [r=5 RS=13 IS=33 fams=76 caps=NONE 913ms]
    ⟨RhoOrder.rhoF 17, RhoOrder.rhoF 6, Rel.nle, some rhoScope⟩,  -- ρ17⊬ρ6?  closed cap-free  [r=6 RS=9 IS=40 fams=232 caps=NONE 141ms]
    ⟨RhoOrder.rhoF 17, RhoOrder.rhoF 9, Rel.nle, some rhoScope⟩,  -- ρ17⊬ρ9?  closed cap-free  [r=6 RS=8 IS=30 fams=80 caps=NONE 67ms]
    ⟨RhoOrder.rhoF 17, RhoOrder.rhoF 12, Rel.nle, some rhoScope⟩,  -- ρ17⊬ρ12?  closed cap-free  [r=6 RS=10 IS=47 fams=140 caps=NONE 305ms]
    ⟨RhoOrder.rhoF 17, RhoOrder.rhoF 13, Rel.nle, some rhoScope⟩,  -- ρ17⊬ρ13?  closed cap-free  [r=7 RS=12 IS=54 fams=326 caps=NONE 398ms]
    ⟨RhoOrder.rhoF 17, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ17⊬ρ16?  closed cap-free  [r=8 RS=23 IS=55 fams=279 caps=NONE 1727ms]
    ⟨RhoOrder.rhoF 17, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ17⊬ρ19?  closed cap-free  [r=6 RS=8 IS=46 fams=124 caps=NONE 561ms]
    ⟨RhoOrder.rhoF 17, RhoOrder.rhoF 20, Rel.nle, some rhoScope⟩,  -- ρ17⊬ρ20?  closed cap-free  [r=6 RS=9 IS=77 fams=727 caps=NONE 2738ms]
    ⟨RhoOrder.rhoF 17, RhoOrder.rhoF 21, Rel.nle, some rhoScope⟩,  -- ρ17⊬ρ21?  closed cap-free  [r=6 RS=8 IS=33 fams=83 caps=NONE 1044ms]
    ⟨RhoOrder.rhoF 18, RhoOrder.rhoF 9, Rel.nle, some rhoScope⟩,  -- ρ18⊬ρ9?  closed cap-free  [r=6 RS=15 IS=48 fams=126 caps=NONE 386ms]
    ⟨RhoOrder.rhoF 18, RhoOrder.rhoF 12, Rel.nle, some rhoScope⟩,  -- ρ18⊬ρ12?  closed cap-free  [r=6 RS=17 IS=81 fams=230 caps=NONE 2115ms]
    ⟨RhoOrder.rhoF 18, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ18⊬ρ16?  closed cap-free  [r=8 RS=23 IS=57 fams=281 caps=NONE 6688ms]
    ⟨RhoOrder.rhoF 18, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ18⊬ρ19?  closed cap-free  [r=6 RS=15 IS=80 fams=214 caps=NONE 4009ms]
    ⟨RhoOrder.rhoF 18, RhoOrder.rhoF 20, Rel.nle, some rhoScope⟩,  -- ρ18⊬ρ20?  closed cap-free  [r=6 RS=19 IS=139 fams=1457 caps=NONE 18490ms]
    ⟨RhoOrder.rhoF 18, RhoOrder.rhoF 21, Rel.nle, some rhoScope⟩,  -- ρ18⊬ρ21?  closed cap-free  [r=6 RS=15 IS=51 fams=129 caps=NONE 7227ms]
    ⟨RhoOrder.rhoF 20, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ20⊬ρ16?  closed cap-free  [r=9 RS=25 IS=43 fams=260 caps=NONE 1474ms]
    ⟨RhoOrder.rhoF 20, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩,  -- ρ20⊬ρ19?  closed cap-free  [r=9 RS=22 IS=53 fams=193 caps=NONE 854ms]
    ⟨RhoOrder.rhoF 21, RhoOrder.rhoF 8, Rel.nle, some rhoScope⟩,  -- ρ21⊬ρ8?  closed cap-free  [r=8 RS=22 IS=37 fams=220 caps=NONE 185ms]
    ⟨RhoOrder.rhoF 21, RhoOrder.rhoF 16, Rel.nle, some rhoScope⟩,  -- ρ21⊬ρ16?  closed cap-free  [r=8 RS=23 IS=39 fams=160 caps=NONE 2432ms]
    ⟨RhoOrder.rhoF 21, RhoOrder.rhoF 19, Rel.nle, some rhoScope⟩  -- ρ21⊬ρ19?  closed cap-free  [r=8 RS=23 IS=54 fams=221 caps=NONE 1321ms]
  ]

set_option maxRecDepth 8192 in
theorem frontier79_length : frontier79.length = 79 := rfl

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.frontier79' depends on axioms: [propext] -/
#guard_msgs in
#print axioms frontier79

end RNDB