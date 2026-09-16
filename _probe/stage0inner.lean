/-
WP10 Stage 0b (refute-first, INNER states): the naive per-state generalisation
of the hard halves — `A^P(s) ⊢ A^Q(s | seen)` and `E^Q(s | seen) ⊢ E^P(s)` at a
state whose `seen` already records the cell's own compound antecedent `Q′` —
is what an induction would need as its hypothesis.  It is expected to FAIL:
inside the guard task for `Q′`, the self-attack row of `interpP` carries a
consequence that `interpQ` has dropped there and recovers only one level UP.
A kernel-certified REFUTED at such a state forces the escape-disjunct form of
the induction hypothesis (see docs/pqequiv-cases.md).
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

/-- The compound antecedents of the parked implications of a station. -/
def ants : List Neg → List Pos
  | [] => []
  | .imp (.atom _) _ :: r => ants r
  | .imp .fls _ :: r => ants r
  | .imp Q _ :: r => Q :: ants r
  | _ :: r => ants r

/-- The inner states: the guard task for `Q′` with `Q′` already recorded. -/
def innerCell (nm : String) (done : List Neg) (f : Nat) (cfg : Config) : IO Unit := do
  for Q' in ants done do
    let seen := [Q']
    -- ∀p at the guard goal ↑Q′, Q′ ∈ seen: naive claim  A^P ⊢ A^Q
    let ap := nrm (eraseNeg (interpP "p" f [] done (some (.up Q'))))
    let aq := nrm (eraseNeg (interpQ "p" f [] done (some (.up Q')) seen))
    IO.println s!"{nm} f={f} inner ∀p at ↑Q′, seen=[Q′]  |A^P|={sizeF ap} |A^Q|={sizeF aq} NFEQ={decide (ap = aq)}"
    one "A^P |- A^Q (naive inner ∀p hard)" (.ifThen ap aq) cfg
    one "A^Q |- A^P (inner ∀p easy)     " (.ifThen aq ap) cfg
    -- ∃p at the station, Q′ ∈ seen: naive claim  E^Q ⊢ E^P
    let ep := nrm (eraseNeg (interpP "p" f [] done none))
    let eq := nrm (eraseNeg (interpQ "p" f [] done none seen))
    IO.println s!"{nm} f={f} inner ∃p, seen=[Q′]  |E^P|={sizeF ep} |E^Q|={sizeF eq} NFEQ={decide (ep = eq)}"
    one "E^Q |- E^P (naive inner ∃p hard)" (.ifThen eq ep) cfg
    one "E^P |- E^Q (inner ∃p easy)     " (.ifThen ep eq) cfg
    (← IO.getStdout).flush

def runCell (which : String) (f : Nat) (cfg : Config) : IO Unit :=
  match which with
  | "i"   => innerCell "cell(i)  " cell1 f cfg
  | "iii" => innerCell "cell(iii)" cell3 f cfg
  | "vi"  => innerCell "cell(vi) " cell6 f cfg
  | "m6"  => innerCell "cell(m6) " m6 f cfg
  | "m10" => innerCell "cell(m10)" m10 f cfg
  | _     => IO.println s!"unknown cell {which}"

def main (args : List String) : IO Unit := do
  match args with
  | [w, fs] => runCell w fs.toNat! cfgD
  | _ => IO.println "usage: stage0inner <cellkey> <fuel>"
