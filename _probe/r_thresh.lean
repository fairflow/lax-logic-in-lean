/-
WP12 Stage 0, R1: measure the literal-stabilisation threshold of `interpR`
(the pair-recording loop check) at the designed cells.

For each cell we print the first fuel `f ≤ FMAX` at which the four levels
`f, f+1, f+2, f+3` are literally equal — three fuels above the threshold,
never one (`docs/ui-ljfo-clause-table.md` §4.25: false fixpoints).
A cell that does not bottom out by `FMAX` is a refutation candidate for R1.
-/
import wip.ui_routeB_r_def
import wip.ui_routeB_n4q_cells

set_option autoImplicit false
open LJFO

/-- cell (vii): `[↓((a∨b) ⊃ ↑c) ⊃ ↑g]`, goal `↑↓((a∨b) ⊃ ↑c)`. -/
def q7 : Pos := .down (.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c")))
def cell7 : List Neg := [.imp q7 (.up (.atom "g"))]
def goal7 : Neg := .up q7

/-- cell (ix): `[(a∨b) ⊃ ↑c, c ⊃ ↑a]`, goal `↑a`. -/
def qa9 : Pos := .or (.atom "a") (.atom "b")
def cell9 : List Neg := [.imp qa9 (.up (.atom "c")), .imp (.atom "c") (.up (.atom "a"))]
def goal9 : Neg := .up (.atom "a")

def dflt : Neg := .up .fls

def thresh (nm : String) (done : List Neg) (g : Option Neg) (fmax : Nat) : IO Unit := do
  let mut lvls : Array Neg := #[]
  let t0 ← IO.monoMsNow
  for f in [0:fmax+4] do
    lvls := lvls.push (interpR "p" f [] done g [])
  let t1 ← IO.monoMsNow
  let mut found : Option Nat := none
  for f in [0:fmax+1] do
    if found.isNone then
      if lvls.getD f dflt = lvls.getD (f+1) dflt && lvls.getD (f+1) dflt = lvls.getD (f+2) dflt && lvls.getD (f+2) dflt = lvls.getD (f+3) dflt then
        found := some f
  let mut rep : Option Nat := none
  for f in [0:fmax+1] do
    if rep.isNone then
      if lvls.getD f dflt = lvls.getD (f+1) dflt then rep := some f
  let repS := match rep with | none => "-" | some r => toString r
  match found with
  | some f => IO.println s!"{nm}: threshold {f}  |I| = {LJFO.sizeNeg (lvls.getD f dflt)}  first-repeat {repS}  ({t1-t0} ms)"
  | none =>
      IO.println s!"{nm}: NO fixpoint through {fmax}  |I_{fmax}| = {LJFO.sizeNeg (lvls.getD fmax dflt)}  first-repeat {repS}  ({t1-t0} ms)"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let fmax := match args with | [s] => s.toNat! | _ => 20
  -- ◯-free first (rule 8)
  thresh "(i)   A  cell1 ⇒ ↑(a∨b)      " cell1 (some goal1) fmax
  thresh "(i)   E  cell1               " cell1 none fmax
  thresh "(ii)  A  cell2 ⇒ ↑(a∨b)      " cell2 (some goal2ab) fmax
  thresh "(ii)  A  cell2 ⇒ ↑(c∨d)      " cell2 (some goal2cd) fmax
  thresh "(iii) A  cell3 ⇒ ↑↓(a⊃↑b)    " cell3 (some goal3) fmax
  thresh "(iii) E  cell3               " cell3 none fmax
  thresh "(iv)  A  cell4 ⇒ ↑↓↑a        " cell4 (some goal4) fmax
  thresh "(v)   A  cell5 ⇒ ↑c          " cell5 (some goal5) fmax
  thresh "(vi)  A  cell6 ⇒ ↑d          " cell6 (some goal6d) fmax
  thresh "(vi)  A  cell6 ⇒ ↑(a∨b)      " cell6 (some goal6ab) fmax
  thresh "(vii) A  cell7 ⇒ ↑q7         " cell7 (some goal7) fmax
  thresh "(vii) E  cell7               " cell7 none fmax
  thresh "(ix)  A  cell9 ⇒ ↑a          " cell9 (some goal9) fmax
  thresh "(ix)  E  cell9               " cell9 none fmax
  -- modal
  thresh "(m1)  A  [◯a] ⇒ ◯b            " m1 (some (.circ (.atom "b"))) fmax
  thresh "(m2)  A  m2 ⇒ ↑↓◯a            " m2 (some (.up (.down (.circ (.atom "a"))))) fmax
  thresh "(m2)  A  m2 ⇒ ◯a              " m2 (some (.circ (.atom "a"))) fmax
  thresh "(m3)  A  m3 ⇒ ◯c              " m3 (some (.circ (.atom "c"))) fmax
  thresh "(m4)  A  m4 ⇒ ◯b              " m4 (some (.circ (.atom "b"))) fmax
  thresh "(m5)  A  m5 ⇒ ◯b              " m5 (some (.circ (.atom "b"))) fmax
  thresh "(m6)  A  m6 ⇒ ↑c              " m6 (some (.up (.atom "c"))) fmax
  thresh "(m6)  E  m6                   " m6 none fmax
  thresh "(m7)  A  m7 ⇒ ◯b              " m7 (some (.circ (.atom "b"))) fmax
  thresh "(m8)  A  m8 ⇒ ◯b              " m8 (some (.circ (.atom "b"))) fmax
  thresh "(m9)  A  m9 ⇒ ◯d              " m9 (some (.circ (.atom "d"))) fmax
  thresh "(m10) A  m10 ⇒ ◯g             " m10 (some (.circ (.atom "g"))) fmax
  thresh "(m10) E  m10                  " m10 none fmax
  thresh "(m11) A  m11 ⇒ ◯d             " m11 (some (.circ (.atom "d"))) fmax
  thresh "(S1)  A  s1Station ⇒ ↑e       " s1Station (some (.up (.atom "e"))) fmax
  thresh "(S1)  A  s1Station ⇒ ◯g       " s1Station (some (.circ (.atom "g"))) fmax
  thresh "(S1)  E  s1Station            " s1Station none fmax
