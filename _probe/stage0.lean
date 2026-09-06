/-
WP10 Stage 0 harness (refute-first): decide BOTH directions of
`IDeriv (interpP p f [] done g) (interpQ p f [] done g [])` on designed
cells, by erasure + the certified decider.

Transfer used: `Inv.sound` (LJF/OBridge.lean) and `polInvT`
(LJF/OPolInv.lean) give
    Nonempty (Inv [M] [] .tru N)  ↔  Nonempty (LaxND [eraseNeg M] (eraseNeg N))
and `LaxND [φ] ψ ↔ LaxND [] (φ ⊃ ψ)` by `impIntro` / `subst1`.
The decider is `FRJ.Arity.decideByEngine` on `ofPLL`, certified in-process
(`checkClosed_sound`, `decideGbuW_of_check`).

Labels: at `g = none` the direction `P|-Q` is the EASY half (calibration:
must come back PROVED) and `Q|-P` is the HARD half; at `g = some G` it is
the other way round.
-/
import wip.ui_routeB_n4q_cells
import wip.check_closed
import Rewrite
import FRJ.Bridge

set_option autoImplicit false
open LJFO FRJ FRJ.Arity FRJ.Search

def sizeF : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and a b => sizeF a + sizeF b + 1
  | .or a b => sizeF a + sizeF b + 1
  | .ifThen a b => sizeF a + sizeF b + 1
  | .somehow a => sizeF a + 1

def impsF : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and a b => impsF a + impsF b
  | .or a b => impsF a + impsF b
  | .ifThen a b => impsF a + impsF b + 1
  | .somehow a => impsF a

def cfgD : Config :=
  { rounds := 16, jmax := 3, pmax := 2, lamCap := 24, maxRS := 3000, maxIS := 3000 }

def nrm (φ : PLLFormula) : PLLFormula := Rewrite.simplifyWith Rewrite.fullSetC 200 φ

def verdict (φ : PLLFormula) (cfg : Config) : String :=
  match decideByEngine (FRJ.ofPLL φ) cfg with
  | some (.inl _) => "PROVED "
  | some (.inr _) => "REFUTED"
  | none => "FLAG(not-closed)"

def one (tag : String) (φ : PLLFormula) (cfg : Config) : IO Unit := do
  let n := nrm φ
  let t0 ← IO.monoMsNow
  let v := verdict n cfg
  let t1 ← IO.monoMsNow
  IO.println s!"    {tag}: nrm size {sizeF n} imps {impsF n}  {v}  ({t1-t0} ms)"
  (← IO.getStdout).flush

def cell (nm : String) (done : List Neg) (g : Option Neg) (f : Nat) (cfg : Config) :
    IO Unit := do
  let mp := nrm (eraseNeg (interpP "p" f [] done g))
  let mq := nrm (eraseNeg (interpQ "p" f [] done g []))
  let easyPQ := g.isNone
  IO.println s!"{nm} f={f}  |P|={sizeF mp}/{impsF mp}  |Q|={sizeF mq}/{impsF mq}  NFEQ={decide (mp = mq)}"
  (← IO.getStdout).flush
  one (if easyPQ then "P|-Q EASY" else "P|-Q HARD") (.ifThen mp mq) cfg
  one (if easyPQ then "Q|-P HARD" else "Q|-P EASY") (.ifThen mq mp) cfg

def gm1 : Neg := .circ (.atom "b")
def gm6 : Neg := .up (.atom "c")
def gm10 : Neg := .circ (.atom "g")

def runCell (which : String) (f : Nat) (cfg : Config) : IO Unit :=
  match which with
  | "i-A"    => cell "cell(i)  A" cell1 (some goal1) f cfg
  | "i-E"    => cell "cell(i)  E" cell1 none f cfg
  | "iii-A"  => cell "cell(iii)A" cell3 (some goal3) f cfg
  | "iii-E"  => cell "cell(iii)E" cell3 none f cfg
  | "vi-A"   => cell "cell(vi) A" cell6 (some goal6d) f cfg
  | "vi-E"   => cell "cell(vi) E" cell6 none f cfg
  | "m1-A"   => cell "cell(m1) A" m1 (some gm1) f cfg
  | "m1-E"   => cell "cell(m1) E" m1 none f cfg
  | "m6-A"   => cell "cell(m6) A" m6 (some gm6) f cfg
  | "m6-E"   => cell "cell(m6) E" m6 none f cfg
  | "m10-A"  => cell "cell(m10)A" m10 (some gm10) f cfg
  | "m10-E"  => cell "cell(m10)E" m10 none f cfg
  | "control" => do
      -- The gate watched failing.  Two textbook cells, then a CROSS cell:
      -- `interpP` at cell (i) against `interpQ` at cell (vi), which are not
      -- interderivable and must come back REFUTED in at least one direction.
      one "ctl p |- box p (must be PROVED) " (.ifThen (.prop "p") (.somehow (.prop "p"))) cfg
      one "ctl box p |- p (must be REFUTED)" (.ifThen (.somehow (.prop "p")) (.prop "p")) cfg
      let a := nrm (eraseNeg (interpP "p" f [] cell1 (some goal1)))
      let b := nrm (eraseNeg (interpQ "p" f [] cell6 (some goal6d) []))
      one "ctl cross i-A |- vi-A (must REFUTE)" (.ifThen a b) cfg
      one "ctl cross vi-A |- i-A (must REFUTE)" (.ifThen b a) cfg
  | _        => IO.println s!"unknown cell {which}"

def main (args : List String) : IO Unit := do
  match args with
  | [w, fs] => runCell w fs.toNat! cfgD
  | [w, lo, hi] =>
      for f in List.range (hi.toNat! + 1) do
        if f ≥ lo.toNat! then runCell w f cfgD
  | _ => IO.println "usage: stage0 <cellkey> <fuel> | <cellkey> <lo> <hi>"
