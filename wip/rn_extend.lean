/-
**Can the certified simpset extend the RN(◯,{}) dictionary?**

`wip/rnDict.lean` is a PARTIAL record: of its 690 closure cells, 603
are certified, and of the 323 stated cell theorems 87 are `sorry` —
4 REFUTED (the closure genuinely fails: the combination is a new
class) and 83 OPEN (neither proved by either searcher nor refuted by
the exhaustive ≤4-world battery).

This probe asks whether `Rewrite.simplify` — canonicalise, then
rewrite by the 236 kernel-checked cells — closes any of the 87 for
free.  The test is SYNTACTIC and therefore certifying: if

    simplify fullSet n (qi ⊙ qj)  =  simplify fullSet n qk

as formulas, then `Interd (qi ⊙ qj) qk` follows from
`simplify_interd` (both sides), `Interd.symm` and `Interd.trans` —
no search, no new axiom.  A match is a SETTLED cell; a match against
a rep OTHER than the one the table claims is a settled cell with a
CORRECTED target.

The 4 refuted cells are the built-in adversarial check: the simpset
must NOT match them to `q0`.  If it does, the simpset is unsound and
the run is a defect report, not a result.
-/
import Rewrite

open PLLND PLLND.SemUI Rewrite

namespace RnExtend

abbrev F := PLLFormula

/-- The 87 unproved cells of `rnDict15`: name, the combination, and
the target index the table claims. -/
def openCells : List (String × F × Nat) :=
  [ ("cAnd_4_14", .and RND.q4 RND.q14, 4),
   ("cAnd_8_10", .and RND.q8 RND.q10, 0),
   ("cAnd_8_11", .and RND.q8 RND.q11, 8),
   ("cAnd_8_12", .and RND.q8 RND.q12, 7),
   ("cAnd_8_14", .and RND.q8 RND.q14, 7),
   ("cAnd_9_13", .and RND.q9 RND.q13, 9),
   ("cAnd_9_14", .and RND.q9 RND.q14, 9),
   ("cAnd_10_13", .and RND.q10 RND.q13, 10),
   ("cAnd_10_14", .and RND.q10 RND.q14, 5),
   ("cAnd_11_13", .and RND.q11 RND.q13, 1),
   ("cAnd_11_14", .and RND.q11 RND.q14, 9),
   ("cAnd_12_13", .and RND.q12 RND.q13, 9),
   ("cAnd_12_14", .and RND.q12 RND.q14, 9),
   ("cAnd_13_14", .and RND.q13 RND.q14, 9),
   ("cOr_2_13", .or RND.q2 RND.q13, 1),
   ("cOr_2_14", .or RND.q2 RND.q14, 9),
   ("cOr_3_13", .or RND.q3 RND.q13, 1),
   ("cOr_3_14", .or RND.q3 RND.q14, 9),
   ("cOr_4_14", .or RND.q4 RND.q14, 9),
   ("cOr_5_8", .or RND.q5 RND.q8, 1),
   ("cOr_5_14", .or RND.q5 RND.q14, 9),
   ("cOr_6_13", .or RND.q6 RND.q13, 1),
   ("cOr_6_14", .or RND.q6 RND.q14, 9),
   ("cOr_7_13", .or RND.q7 RND.q13, 1),
   ("cOr_7_14", .or RND.q7 RND.q14, 9),
   ("cOr_8_9", .or RND.q8 RND.q9, 1),
   ("cOr_8_10", .or RND.q8 RND.q10, 1),
   ("cOr_8_11", .or RND.q8 RND.q11, 1),
   ("cOr_8_12", .or RND.q8 RND.q12, 1),
   ("cOr_8_13", .or RND.q8 RND.q13, 1),
   ("cOr_8_14", .or RND.q8 RND.q14, 1),
   ("cOr_9_13", .or RND.q9 RND.q13, 1),
   ("cOr_9_14", .or RND.q9 RND.q14, 9),
   ("cOr_10_12", .or RND.q10 RND.q12, 1),
   ("cOr_10_13", .or RND.q10 RND.q13, 1),
   ("cOr_10_14", .or RND.q10 RND.q14, 1),
   ("cOr_11_12", .or RND.q11 RND.q12, 1),
   ("cOr_11_13", .or RND.q11 RND.q13, 1),
   ("cOr_11_14", .or RND.q11 RND.q14, 1),
   ("cOr_12_13", .or RND.q12 RND.q13, 1),
   ("cOr_12_14", .or RND.q12 RND.q14, 9),
   ("cOr_13_14", .or RND.q13 RND.q14, 1),
   ("cImp_8_4", .ifThen RND.q8 RND.q4, 5),
   ("cImp_8_5", .ifThen RND.q8 RND.q5, 5),
   ("cImp_8_7", .ifThen RND.q8 RND.q7, 9),
   ("cImp_8_9", .ifThen RND.q8 RND.q9, 9),
   ("cImp_8_10", .ifThen RND.q8 RND.q10, 10),
   ("cImp_8_11", .ifThen RND.q8 RND.q11, 1),
   ("cImp_8_12", .ifThen RND.q8 RND.q12, 9),
   ("cImp_8_14", .ifThen RND.q8 RND.q14, 9),
   ("cImp_9_4", .ifThen RND.q9 RND.q4, 0),
   ("cImp_9_8", .ifThen RND.q9 RND.q8, 8),
   ("cImp_10_4", .ifThen RND.q10 RND.q4, 7),
   ("cImp_10_7", .ifThen RND.q10 RND.q7, 7),
   ("cImp_10_8", .ifThen RND.q10 RND.q8, 8),
   ("cImp_10_9", .ifThen RND.q10 RND.q9, 9),
   ("cImp_10_12", .ifThen RND.q10 RND.q12, 9),
   ("cImp_10_13", .ifThen RND.q10 RND.q13, 1),
   ("cImp_10_14", .ifThen RND.q10 RND.q14, 9),
   ("cImp_11_4", .ifThen RND.q11 RND.q4, 4),
   ("cImp_11_7", .ifThen RND.q11 RND.q7, 7),
   ("cImp_11_8", .ifThen RND.q11 RND.q8, 8),
   ("cImp_11_9", .ifThen RND.q11 RND.q9, 9),
   ("cImp_11_12", .ifThen RND.q11 RND.q12, 9),
   ("cImp_11_13", .ifThen RND.q11 RND.q13, 1),
   ("cImp_11_14", .ifThen RND.q11 RND.q14, 9),
   ("cImp_12_4", .ifThen RND.q12 RND.q4, 0),
   ("cImp_12_7", .ifThen RND.q12 RND.q7, 8),
   ("cImp_12_8", .ifThen RND.q12 RND.q8, 8),
   ("cImp_12_9", .ifThen RND.q12 RND.q9, 1),
   ("cImp_12_11", .ifThen RND.q12 RND.q11, 1),
   ("cImp_13_5", .ifThen RND.q13 RND.q5, 5),
   ("cImp_13_8", .ifThen RND.q13 RND.q8, 8),
   ("cImp_13_9", .ifThen RND.q13 RND.q9, 9),
   ("cImp_13_11", .ifThen RND.q13 RND.q11, 1),
   ("cImp_13_12", .ifThen RND.q13 RND.q12, 9),
   ("cImp_13_14", .ifThen RND.q13 RND.q14, 9),
   ("cImp_14_4", .ifThen RND.q14 RND.q4, 0),
   ("cImp_14_5", .ifThen RND.q14 RND.q5, 10),
   ("cImp_14_7", .ifThen RND.q14 RND.q7, 8),
   ("cImp_14_8", .ifThen RND.q14 RND.q8, 8),
   ("cImp_14_9", .ifThen RND.q14 RND.q9, 1),
   ("cImp_14_11", .ifThen RND.q14 RND.q11, 1),
   ("cImp_14_12", .ifThen RND.q14 RND.q12, 1),
   ("cImp_14_13", .ifThen RND.q14 RND.q13, 1),
   ("cBox_11", .somehow RND.q11, 1),
   ("cBox_14", .somehow RND.q14, 9) ]

def refuted : List String := ["cAnd_8_10", "cImp_9_4", "cImp_12_4", "cImp_14_4"]

def fuel : Nat := 60

/-- Normal forms of the fifteen representatives. -/
def repNF : List F := RND.repsL.map (simplifyWith fullSetC fuel)

/-- Which representatives share a normal form with `φ`? -/
def matchReps (φ : F) : List Nat :=
  let n := simplifyWith fullSetC fuel φ
  (repNF.zipIdx.filter fun p => p.1 = n).map (·.2)

/-- CONTROL: the 236 cells the table DOES prove.  `simplify` must
close these, or the pipeline is not firing at all and the negative
result on the open cells says nothing. -/
def control : List (F × F) := fullSet.map (fun r => (r.lhs, r.rhs))

def main : IO Unit := do
  IO.println "RN dictionary extension by the certified simpset"
  IO.println s!"simpset: {fullSet.length} rules (236 dictionary cells + {pllSet.length} modal laws)"
  IO.println s!"open cells: {openCells.length} (83 OPEN + 4 REFUTED)"
  -- sanity: the fifteen representatives must stay pairwise distinct
  -- under the normaliser, or the simpset has collapsed the dictionary.
  let distinct := repNF.eraseDups.length
  IO.println s!"representatives distinct after simplify: {distinct}/15"
  if distinct != 15 then
    IO.println "  *** SIMPSET COLLAPSES DISTINCT CLASSES — DEFECT, not a result ***"
    for (a, i) in repNF.zipIdx do
      for (b, j) in repNF.zipIdx do
        if i < j && a == b then IO.println s!"    q{i} and q{j} share a normal form"
  -- CONTROL
  let mut ctlOk := 0
  for (l, r) in control do
    if simplifyWith fullSetC fuel l == simplifyWith fullSetC fuel r then ctlOk := ctlOk + 1
  IO.println s!"CONTROL: certified cells closed by simplify: {ctlOk}/{control.length}"
  if ctlOk * 4 < control.length * 3 then
    IO.println "  *** the pipeline is NOT firing on cells it provably should — canon may be breaking the syntactic match ***"
  IO.println ""
  let mut settled := 0
  let mut corrected := 0
  let mut unsettled : List String := []
  let mut unsound : List String := []
  for (nm, φ, tgt) in openCells do
    let ms := matchReps φ
    if ms.isEmpty then
      unsettled := nm :: unsettled
    else if refuted.contains nm then
      unsound := s!"{nm}: matched {ms} but the cell is REFUTED" :: unsound
    else if ms.contains tgt then
      settled := settled + 1
      IO.println s!"  SETTLED {nm} ≡ q{tgt}  (normal forms coincide)"
    else
      corrected := corrected + 1
      IO.println s!"  SETTLED-CORRECTED {nm}: table claims q{tgt}, normal form matches {ms}"
  IO.println ""
  IO.println s!"settled at claimed target : {settled}"
  IO.println s!"settled at a NEW target   : {corrected}"
  IO.println s!"still open                : {unsettled.length}"
  if unsound.isEmpty then
    IO.println "adversarial check: the 4 REFUTED cells were NOT matched — simpset consistent with them"
  else
    IO.println "*** ADVERSARIAL CHECK FAILED — SIMPSET UNSOUND ***"
    for u in unsound do IO.println s!"  {u}"
  IO.println "RN-EXTEND-DONE"

end RnExtend

def main : IO Unit := RnExtend.main
