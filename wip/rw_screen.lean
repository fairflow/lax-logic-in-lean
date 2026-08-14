/-
Screen for the certified simpset (`Rewrite/`): orientation and, more
to the point, EFFECTIVENESS — does normalising actually shrink the
cells a probe would otherwise attack cold?

Per the design, orientation is NOT a soundness condition
(`norm_interd` is unconditional), so a mis-oriented rule is a warning,
not a defect.  What matters is the shrink rate on real corpora.
-/
import Rewrite

open PLLND PLLND.SemUI Rewrite

namespace RwScreen

abbrev F := PLLFormula

/-- The catalogue's crank-≤6 representatives plus compound cells a
probe would meet. -/
def bot : F := .falsePLL
def top : F := .ifThen bot bot
def oBot : F := .somehow bot
def nOBot : F := .ifThen oBot bot
def q4 : F := .or nOBot oBot
def nnOBot : F := .ifThen nOBot bot
def q5 : F := .somehow nOBot
def q10 : F := .ifThen nnOBot oBot
def q8 : F := .ifThen q5 q4
def q9 : F := .or nnOBot q5

/-- Cells: the representatives, their pairwise ∧/∨/⊃ combinations, and
their boxes — i.e. what a closure sweep generates. -/
def reps : List F := [bot, top, oBot, nOBot, q4, nnOBot, q5, q10, q8, q9]

/-- The SAME classes, but in the dictionary's own definitional form.
Rules match syntactically, so this distinguishes "the rules are weak"
from "the cells are written differently". -/
def repsRND : List F :=
  [RND.q0, RND.q1, RND.q2, RND.q3, RND.q4, RND.q5, RND.q6,
   RND.q7, RND.q8, RND.q9, RND.q10, RND.q11]

def cellsRND : List F :=
  repsRND ++
  (repsRND.flatMap fun a => repsRND.flatMap fun b =>
    [.and a b, .or a b, .ifThen a b]) ++
  (repsRND.map fun a => .somehow a)

def cells : List F :=
  reps ++
  (reps.flatMap fun a => reps.flatMap fun b => [.and a b, .or a b, .ifThen a b]) ++
  (reps.map fun a => .somehow a) ++
  (reps.map fun a => .somehow (.somehow a))

def main : IO Unit := do
  IO.println s!"certified simpset: {fullSet.length} rules ({rndSet.length} from the dictionary table)"
  -- orientation
  let bad := fullSet.filter (fun r => !(crankOriented r))
  IO.println s!"orientation: {fullSet.length - bad.length}/{fullSet.length} crank-oriented, {bad.length} not"
  IO.println "  (not a soundness condition — norm_interd is unconditional)"
  -- effectiveness
  let mut shrunk := 0
  let mut same := 0
  let mut totalBefore := 0
  let mut totalAfter := 0
  for c in cells do
    let n := norm fullSet 6 c
    totalBefore := totalBefore + crank c
    totalAfter := totalAfter + crank n
    if n == c then same := same + 1 else shrunk := shrunk + 1
  IO.println s!"cells: {cells.length}"
  IO.println s!"  rewritten: {shrunk} ({shrunk * 100 / cells.length}%)   unchanged: {same}"
  IO.println s!"  total crank {totalBefore} → {totalAfter} ({(totalBefore - totalAfter) * 100 / (max totalBefore 1)}% reduction)"
  -- the same measurement on the dictionary's OWN forms
  let mut s2 := 0
  let mut tb2 := 0
  let mut ta2 := 0
  for c in cellsRND do
    let n := norm fullSet 6 c
    tb2 := tb2 + crank c
    ta2 := ta2 + crank n
    if n != c then s2 := s2 + 1
  IO.println s!"cells in the dictionary's OWN form: {cellsRND.length}"
  IO.println s!"  rewritten: {s2} ({s2 * 100 / cellsRND.length}%)"
  IO.println s!"  total crank {tb2} → {ta2} ({(tb2 - ta2) * 100 / (max tb2 1)}% reduction)"
  IO.println "RW-SCREEN-DONE"

end RwScreen

def main : IO Unit := RwScreen.main
