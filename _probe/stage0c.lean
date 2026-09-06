/-
WP10 Stage 0c (refute-first, the DESIGNED refutation candidate for the per-fuel
form of the hard halves at the TOP level, seen = []).

Shape: a Dyckhoff-parked implication whose antecedent is an implication with a
DISJUNCTIVE antecedent.  Inside the guard task for `Q′ = ↓((a∨b) ⊃ ↑c)` the
∀p goal inversion at `(a∨b) ⊃ ↑c` produces the branching rows
`↓E([↑a] ++ done | [Q′]) ⊃ A([↑a] ++ done ⇒ ↑c | [Q′])`, and there the ∃p
interpolant with `Q′ ∈ seen` has dropped the conjunct
`↓A(↑a :: done ⇒ ↑Q′) ⊃ E(↑g :: rest)` (Stage 0b showed E^Q ⊬ E^P at such
states).  A weaker `E` in the negative position of a ∀p row makes that row a
WEAKER disjunct of A^P than of A^Q, so `A^P ⊢ A^Q` may fail per fuel at the
top level here.  If REFUTED, the per-fuel `PQHard` is false as stated and
the cofinal form is the honest statement.

Also: the residue inner states of Stage 0b (goal a residue of Q′, not ↑Q′).
Same transfer and decider as stage0.lean.
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

/-- cell (vii): `[↓((a∨b) ⊃ ↑c) ⊃ ↑g]`, goal `↑↓((a∨b) ⊃ ↑c)` (Dyckhoff shape, disjunctive inner antecedent). -/
def q7 : Pos := .down (.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c")))
def cell7 : List Neg := [.imp q7 (.up (.atom "g"))]
def goal7 : Neg := .up q7
/-- cell (viii): the same under a box goal `◯g`-style: `[↓((a∨b) ⊃ ↑c) ⊃ ↑g, ↑↓◯(d)]`? keep the shape, add a box hypothesis. -/
def cell8 : List Neg := [.imp q7 (.up (.atom "g")), .circ (.atom "d")]
def goal8 : Neg := .circ (.atom "c")

def top (nm : String) (done : List Neg) (g : Option Neg) (f : Nat) (cfg : Config) : IO Unit := do
  let mp := nrm (eraseNeg (interpP "p" f [] done g))
  let mq := nrm (eraseNeg (interpQ "p" f [] done g []))
  IO.println s!"{nm} f={f} top  |P|={sizeF mp} |Q|={sizeF mq} NFEQ={decide (mp = mq)}"
  match g with
  | none => do one "E^Q |- E^P (HARD ∃p)" (.ifThen mq mp) cfg; one "E^P |- E^Q (easy)   " (.ifThen mp mq) cfg
  | some _ => do one "A^P |- A^Q (HARD ∀p)" (.ifThen mp mq) cfg; one "A^Q |- A^P (easy)   " (.ifThen mq mp) cfg

/-- residue inner states: goal a residue of Q′ (not ↑Q′), Q′ ∈ seen. -/
def inner2 (nm : String) (done : List Neg) (g : Neg) (seen : List Pos) (f : Nat) (cfg : Config) : IO Unit := do
  let ap := nrm (eraseNeg (interpP "p" f [] done (some g)))
  let aq := nrm (eraseNeg (interpQ "p" f [] done (some g) seen))
  IO.println s!"{nm} f={f} inner2 ∀p  |A^P|={sizeF ap} |A^Q|={sizeF aq} NFEQ={decide (ap = aq)}"
  one "A^P |- A^Q (naive inner2 ∀p hard)" (.ifThen ap aq) cfg
  one "A^Q |- A^P (easy)               " (.ifThen aq ap) cfg

def runCell (which : String) (f : Nat) (cfg : Config) : IO Unit :=
  match which with
  | "vii-A"  => top "cell(vii) A" cell7 (some goal7) f cfg
  | "vii-E"  => top "cell(vii) E" cell7 none f cfg
  | "viii-A" => top "cell(viii)A" cell8 (some goal8) f cfg
  | "viii-E" => top "cell(viii)E" cell8 none f cfg
  | "i-res"  => inner2 "cell(i) goal ↑a, seen [a∨b]" cell1 (.up (.atom "a")) [.or (.atom "a") (.atom "b")] f cfg
  | "iii-res" => inner2 "cell(iii) ↑a::done goal ↑b, seen [Q′]" (.up (.atom "a") :: cell3) (.up (.atom "b")) [.down dykBody] f cfg
  | "vii-res" => inner2 "cell(vii) ↑a::done goal ↑c, seen [q7]" (.up (.atom "a") :: cell7) (.up (.atom "c")) [q7] f cfg
  | _        => IO.println s!"unknown cell {which}"

def main (args : List String) : IO Unit := do
  match args with
  | [w, fs] => runCell w fs.toNat! cfgD
  | _ => IO.println "usage: stage0c <cellkey> <fuel>"
