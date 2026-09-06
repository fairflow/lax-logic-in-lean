/-
Designed cell (ix): the naive ∀p inner hypothesis at a RESIDUE state, with a
second hypothesis that makes the self-attack content non-trivial.
  done = [(a∨b) ⊃ ↑c, c ⊃ ↑a],  top goal ↑a.
Inside the guard task for Qa = a∨b (seen = [a∨b]) the residue state
(done ⇒ ↑a | [a∨b]) has, in interpP, the self-attack row
  A(done ⇒ ↑(a∨b)) ∧ A([↑c, c ⊃ ↑a] ⇒ ↑a)  ∋  b ∧ ⊤,
so A^P(r) ∋ b, while A^Q(r | [a∨b]) = a ∨ c.  Prediction: naive ∀p REFUTED at r;
the escape form  A^P(r) ⊢ A^Q(r|seen) ∨ A^Q(done ⇒ ↑Qa | seen)  PROVED;
the top-level PQHard PROVED (b is recovered through the guard's ↑b branch).
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

def qa : Pos := .or (.atom "a") (.atom "b")
def cell9 : List Neg := [.imp qa (.up (.atom "c")), .imp (.atom "c") (.up (.atom "a"))]
def ga : Neg := .up (.atom "a")

def runF (f : Nat) (cfg : Config) : IO Unit := do
  let seen : List Pos := [qa]
  -- residue state r = (cell9 ⇒ ↑a | [a∨b])
  let apR := nrm (eraseNeg (interpP "p" f [] cell9 (some ga)))
  let aqR := nrm (eraseNeg (interpQ "p" f [] cell9 (some ga) seen))
  -- guard state g = (cell9 ⇒ ↑(a∨b) | [a∨b])
  let aqG := nrm (eraseNeg (interpQ "p" f [] cell9 (some (.up qa)) seen))
  let apG := nrm (eraseNeg (interpP "p" f [] cell9 (some (.up qa))))
  -- top t = (cell9 ⇒ ↑a | [])
  let apT := apR
  let aqT := nrm (eraseNeg (interpQ "p" f [] cell9 (some ga) []))
  IO.println s!"cell(ix) f={f}  |A^P(r)|={sizeF apR} |A^Q(r|seen)|={sizeF aqR} |A^Q(g|seen)|={sizeF aqG} |A^P(g)|={sizeF apG} |A^Q(top)|={sizeF aqT}"
  one "residue naive ∀p  A^P(r) |- A^Q(r|seen)              " (.ifThen apR aqR) cfg
  one "residue escape    A^P(r) |- A^Q(r|seen) ∨ A^Q(g|seen)" (.ifThen apR (.or aqR aqG)) cfg
  one "guard naive ∀p    A^P(g) |- A^Q(g|seen)              " (.ifThen apG aqG) cfg
  one "TOP PQHard ∀p     A^P(t) |- A^Q(t|[])                " (.ifThen apT aqT) cfg
  one "TOP easy          A^Q(t|[]) |- A^P(t)                " (.ifThen aqT apT) cfg
  one "witness  b |- A^P(r)  (the self-attack content)      " (.ifThen (.prop "b") apR) cfg
  one "witness  b |- A^Q(r|seen)  (must REFUTE if analysis right)" (.ifThen (.prop "b") aqR) cfg

def main (args : List String) : IO Unit := do
  match args with
  | [fs] => runF fs.toNat! cfgD
  | _ => IO.println "usage: stage0d <fuel>"
