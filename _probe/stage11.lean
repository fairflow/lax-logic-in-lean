/-
WP11 Stage 0c: test the INDUCTION HYPOTHESIS for the hard halves before
proving it.

`docs/pqequiv-cases.md` §3 refutes the naive per-state `∃p` hypothesis
`E^Q(s | seen) ⊢ E^P(s)` at states whose `seen` records a compound antecedent
of the station.  The `∀p` hard half needs exactly that in the NEGATIVE
position of the two rows that carry an `∃p` guard:

    aggQ  (goal `Q ⊃ N`)          ↓E(b, done | seen) ⊃ A(b, done ⇒ N | seen)
    stepQ (`↑(P₁∨P₂) :: todo`)    ↓E(b++todo | seen) ⊃ A(b++todo ⇒ G | seen)

so a row-wise `impMono` step is not available.  This harness measures, at the
states those rows actually occur at inside a guard task:

  Q1  `E^Q(s | seen) ⊢ E^P(s)`                              (row-wise ∃p; expect REFUTED)
  Q2  `E^Q(s | seen) ∧ C ⊢ E^P(s)`                          (relativised ∃p)
        C = ↓A^P_{f-2}([], D, ↑Q′) ⊃ E^P_{f-2}([N], rest)   — the dropped conjunct
  Q3  `A^P(s′) ⊢ A^Q(s′ | seen)`                            (∀p at the row's consequent)
  Q4  `(↓E^P(s) ⊃ A^P(s′)) ⊢ (↓E^Q(s|seen) ⊃ A^Q(s′|seen))` (the ROW, transferred)
  Q5  `E^Q(s | seen) ⊢ A^Q(s′ | seen)`                      (is the Q-row trivial?)
  Q6  `A^P([], done, ↑Q′) ⊢ A^Q([], done, ↑Q′ | [Q′])`      (the guard state, ∀p)

Cells: (iii) `[↓(a ⊃ ↑b) ⊃ ↑c]` and (vii) `[↓((a∨b) ⊃ ↑c) ⊃ ↑g]` — the two
◯-free shapes whose guard task contains an implication goal, hence an `↓E ⊃ A`
row; plus (m6) for the modal case.  Same transfer and decider as
`_probe/stage0.lean`.
-/
import wip.ui_routeB_n4q_cells
import wip.check_closed
import Rewrite
import FRJ.Bridge

set_option autoImplicit false
open LJFO FRJ FRJ.Arity FRJ.Search

def sizeF : PLLFormula → Nat
  | .prop _ => 1 | .falsePLL => 1
  | .and a b => sizeF a + sizeF b + 1 | .or a b => sizeF a + sizeF b + 1
  | .ifThen a b => sizeF a + sizeF b + 1 | .somehow a => sizeF a + 1

def cfgD : Config :=
  { rounds := 16, jmax := 3, pmax := 2, lamCap := 24, maxRS := 3000, maxIS := 3000 }

def nrm (φ : PLLFormula) : PLLFormula := Rewrite.simplifyWith Rewrite.fullSetC 200 φ

def verdict (φ : PLLFormula) (cfg : Config) : String :=
  match decideByEngine (FRJ.ofPLL φ) cfg with
  | some (.inl _) => "PROVED " | some (.inr _) => "REFUTED" | none => "FLAG(not-closed)"

def one (tag : String) (φ : PLLFormula) (cfg : Config) : IO Unit := do
  let n := nrm φ
  let t0 ← IO.monoMsNow
  let v := verdict n cfg
  let t1 ← IO.monoMsNow
  IO.println s!"    {tag}: nrm size {sizeF n}  {v}  ({t1-t0} ms)"
  (← IO.getStdout).flush

/-! ## The control gate (watched: the second must be REFUTED) -/

def gate (cfg : Config) : IO Unit := do
  one "GATE  p |- ◯p (must be PROVED) " (.ifThen (.prop "p") (.somehow (.prop "p"))) cfg
  one "GATE  ◯p |- p (must be REFUTED)" (.ifThen (.somehow (.prop "p")) (.prop "p")) cfg

/-! ## The cells -/

/-- cell (iii): `[↓(a ⊃ ↑b) ⊃ ↑c]`, compound antecedent `qd = ↓(a ⊃ ↑b)`. -/
def qd : Pos := .down (.imp (.atom "a") (.up (.atom "b")))
def d3 : List Neg := [.imp qd (.up (.atom "c"))]

/-- cell (vii): `[↓((a∨b) ⊃ ↑c) ⊃ ↑g]`, compound antecedent
`q7 = ↓((a∨b) ⊃ ↑c)`. -/
def q7 : Pos := .down (.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c")))
def d7 : List Neg := [.imp q7 (.up (.atom "g"))]

/-- cell (m6): the modal Dyckhoff shape of `docs/pqequiv-cases.md` §3. -/
def qm : Pos := .down (.circ (.down (.imp (.atom "a") (.up (.atom "b")))))
def dm : List Neg := [.imp qm (.up (.atom "c"))]

/-- The state the `↓E ⊃ A` row of the guard task sits at, per cell: the branch
`b = [↑a]` of the goal inversion, at the cell's station, with the cell's own
antecedent recorded. -/
structure Site where
  nm    : String
  done  : List Neg     -- the station
  br    : List Neg     -- the branch `b` (the row's `todo`)
  goal  : Neg          -- the row's consequent goal
  qp    : Pos          -- the recorded antecedent `Q′`
  body  : Neg          -- `N` of the parked `Q′ ⊃ N`

def site3 : Site :=
  { nm := "iii", done := d3, br := [.up (.atom "a")], goal := .up (.atom "b")
    qp := qd, body := .up (.atom "c") }
def site7 : Site :=
  { nm := "vii", done := d7, br := [.up (.atom "a")], goal := .up (.atom "c")
    qp := q7, body := .up (.atom "g") }
def sitem : Site :=
  { nm := "m6 ", done := dm, br := [.up (.atom "a")], goal := .up (.atom "b")
    qp := qm, body := .up (.atom "c") }

/-- The dropped conjunct `C`, at the fuel it occurs at inside
`E^P_f(b, done)`: the branch `[↑a]` is processed (one fuel), the station
aggregate is entered (one fuel), so its rows sit at fuel `f-2`. -/
def missingC (s : Site) (f : Nat) : Neg :=
  let D := s.br ++ s.done                     -- the station after processing `b`
  .imp (.down (interpP "p" f [] D (some (.up s.qp))))
       (interpP "p" f [s.body] s.br none)

def runSite (s : Site) (f : Nat) (q : String) (cfg : Config) : IO Unit := do
  let seen := [s.qp]
  let f2 := f - 2
  let eP := nrm (eraseNeg (interpP "p" f s.br s.done none))
  let eQ := nrm (eraseNeg (interpQ "p" f s.br s.done none seen))
  let aP := nrm (eraseNeg (interpP "p" f s.br s.done (some s.goal)))
  let aQ := nrm (eraseNeg (interpQ "p" f s.br s.done (some s.goal) seen))
  let cC := nrm (eraseNeg (missingC s f2))
  IO.println s!"cell({s.nm}) f={f}  |E^P|={sizeF eP} |E^Q|={sizeF eQ} |A^P|={sizeF aP} |A^Q|={sizeF aQ} |C|={sizeF cC} NFEQ_E={decide (eP = eQ)} NFEQ_A={decide (aP = aQ)}"
  (← IO.getStdout).flush
  if q = "Q1" || q = "all" then
    one "Q1 E^Q |- E^P            (naive ∃p, row-wise)" (.ifThen eQ eP) cfg
  if q = "Q2" || q = "all" then
    one "Q2 E^Q ∧ C |- E^P        (relativised ∃p)    " (.ifThen (.and eQ cC) eP) cfg
  if q = "Q3" || q = "all" then
    one "Q3 A^P |- A^Q            (naive ∀p at conseq)" (.ifThen aP aQ) cfg
  if q = "Q4" || q = "all" then
    one "Q4 (E^P→A^P) |- (E^Q→A^Q) (the ROW)          " (.ifThen (.ifThen eP aP) (.ifThen eQ aQ)) cfg
  if q = "Q5" || q = "all" then
    one "Q5 E^Q |- A^Q            (is the Q-row trivial?)" (.ifThen eQ aQ) cfg
  if q = "Q0" || q = "all" then
    one "Q0 E^P |- E^Q            (easy ∃p, control)  " (.ifThen eP eQ) cfg

/-- Q6: the guard state itself, `∀p`. -/
def runGuard (s : Site) (f : Nat) (cfg : Config) : IO Unit := do
  let seen := [s.qp]
  let aP := nrm (eraseNeg (interpP "p" f [] s.done (some (.up s.qp))))
  let aQ := nrm (eraseNeg (interpQ "p" f [] s.done (some (.up s.qp)) seen))
  IO.println s!"cell({s.nm}) f={f} GUARD |A^P|={sizeF aP} |A^Q|={sizeF aQ} NFEQ={decide (aP = aQ)}"
  (← IO.getStdout).flush
  one "Q6 A^P |- A^Q            (guard state, ∀p)   " (.ifThen aP aQ) cfg

def runCell (which : String) (f : Nat) (q : String) (cfg : Config) : IO Unit :=
  match which with
  | "gate"  => gate cfg
  | "iii"   => runSite site3 f q cfg
  | "vii"   => runSite site7 f q cfg
  | "m6"    => runSite sitem f q cfg
  | "iii-g" => runGuard site3 f cfg
  | "vii-g" => runGuard site7 f cfg
  | "m6-g"  => runGuard sitem f cfg
  | _       => IO.println s!"unknown cell {which}"

def main (args : List String) : IO Unit := do
  match args with
  | [w, fs, q] => runCell w fs.toNat! q cfgD
  | [w, fs] => runCell w fs.toNat! "all" cfgD
  | [w]     => runCell w 0 "all" cfgD
  | _ => IO.println "usage: stage11 <cellkey> <fuel> [Q0|Q1|Q2|Q3|Q4|Q5|all]"
