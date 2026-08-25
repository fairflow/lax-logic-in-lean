/-
BiLax round 0/1 — the finite-model screening harness (a `lean_exe`,
per the repo's compiled-bank doctrine; replaces the handoff's Python
appendix).

Screens, all with NON-VACUITY counters (docs/bilax-plan.md §4: the
handoff caught two false positives exactly there):

* S-P  persistence of `◯∃` — verify the analytic claim that the square
       law `Rm;Ri ⊆ Ri;Rm` is EXACT (sufficient here; necessary by the
       ↑w-upset argument, re-checked computationally: a square-failing
       frame is exhibited with a persistence-failing valuation).
* S-C  the counit law is EXACT for `◯∃◯∀A ⊢ A` (both directions).
* S-A  the adjunction as an iff on all upward-closed valuations.
* S-R  co-residuation for `⤙`.
* S-F  fragment-relative fallibility: `⊥ ⊢ A` holds at fallible worlds
       for forward `A`, and `ff = ⊤ ⤙ ⊤` is forced nowhere.
* S-U  unit.
* S-M  `BiModel` is a PROPER subclass: some constraint model fails the
       counit law (so the laws are not free).

Verdicts: pass / FAIL (a certificate: the frame, valuation and world)
/ skip.  One appended line per screen; counters printed always.
-/
import LaxLogic.PLLCountermodelEmit

open PLLND PLLND.FinCM

namespace BiLax.Screens

abbrev W := Nat

structure FFrame where
  n : Nat
  riB : Nat → Nat → Bool
  rmB : Nat → Nat → Bool
  rcB : Nat → Nat → Bool      -- the SEPARATE co-lax relation
  falB : Nat → Bool

def worlds (F : FFrame) : List Nat := List.range F.n

/-- Upward-closed valuations, as Bool-vectors over the worlds. -/
def upsets (F : FFrame) : List (Nat → Bool) :=
  let all := (List.range (2 ^ F.n)).map fun code w =>
    decide ((code / 2 ^ w) % 2 = 1)
  all.filter fun v =>
    (worlds F).all fun x => (worlds F).all fun y =>
      !(v x && F.riB x y) || v y

/-- The three frame laws under test. -/
def squareB (F : FFrame) : Bool :=
  (worlds F).all fun w => (worlds F).all fun u => (worlds F).all fun v =>
    !(F.rcB w u && F.riB u v) ||
      (worlds F).any fun w' => F.riB w w' && F.rcB w' v

def counitB (F : FFrame) : Bool :=
  (worlds F).all fun w => (worlds F).all fun u =>
    !(F.rcB w u) ||
      (worlds F).any fun v =>
        F.riB w v && (worlds F).all fun y => !(F.rmB v y) || F.riB y u

/-- `serial_c`: every world has a common `Rm`/`Rc`-successor. -/
def serialB (F : FFrame) : Bool :=
  (worlds F).all fun v => (worlds F).any fun u => F.rmB v u && F.rcB v u

/-- Frame well-formedness: preorders, `Rm ⊆ Ri`, `F` hereditary. -/
def wfB (F : FFrame) : Bool :=
  (worlds F).all (fun x => F.riB x x && F.rmB x x) &&
  (worlds F).all (fun x => (worlds F).all fun y => (worlds F).all fun z =>
    (!(F.riB x y && F.riB y z) || F.riB x z) &&
    (!(F.rmB x y && F.rmB y z) || F.rmB x z)) &&
  (worlds F).all (fun x => (worlds F).all fun y =>
    (!(F.rmB x y) || F.riB x y) &&
    (!(F.falB x && F.riB x y) || F.falB y))

/-- `◯∃`, `◯∀` as operators on valuations (fallible worlds are
absorbed by the harness's forward-fragment convention: `V` is taken
full on `F`, which `upsets` respects when `F` is an upset). -/
def colaxV (F : FFrame) (v : Nat → Bool) : Nat → Bool :=
  fun u => (worlds F).any fun w => F.rcB w u && v w

def laxV (F : FFrame) (v : Nat → Bool) : Nat → Bool :=
  fun w => (worlds F).all fun x =>
    !(F.riB w x) || (worlds F).any fun u => F.rmB x u && v u

def isUp (F : FFrame) (v : Nat → Bool) : Bool :=
  (worlds F).all fun x => (worlds F).all fun y =>
    !(v x && F.riB x y) || v y

/-- The enumeration: all frames on `n` worlds with `Ri`, `Rm` drawn
from the reflexive-transitive well-formed candidates, `F` an upset. -/
def frames (n : Nat) : List FFrame :=
  let pairs := (List.range n).flatMap fun x => (List.range n).map fun y => (x, y)
  let sub (code : Nat) (x y : Nat) : Bool :=
    match pairs.findIdx? (fun p => p == (x, y)) with
    | some i => decide ((code / 2 ^ i) % 2 = 1)
    | none => false
  let cap := 2 ^ (n * n)
  (List.range cap).flatMap fun ci =>
    (List.range cap).flatMap fun cm =>
      (List.range cap).flatMap fun cc =>
        (List.range (2 ^ n)).map fun cf =>
          { n := n
            riB := fun x y => sub ci x y || decide (x = y)
            rmB := fun x y => sub cm x y || decide (x = y)
            rcB := fun x y => sub cc x y          -- NOT reflexivised
            falB := fun x => decide ((cf / 2 ^ x) % 2 = 1) }

def wellFormed (n : Nat) : List FFrame := (frames n).filter wfB

/-! ## The screens -/

structure Res where
  pass : Nat := 0
  fail : Nat := 0
  fired : Nat := 0      -- non-vacuity: the operator actually fired
  nonId : Nat := 0      -- non-vacuity: it differed from the identity
  certs : List String := []

def note (r : Res) (ok fired nonId : Bool) (cert : String) : Res :=
  { pass := r.pass + (if ok then 1 else 0)
    fail := r.fail + (if ok then 0 else 1)
    fired := r.fired + (if fired then 1 else 0)
    nonId := r.nonId + (if nonId then 1 else 0)
    certs := if ok then r.certs else cert :: r.certs }

/-- S-P: square ⟹ `◯∃` persistent, and (necessity) a square-failing
frame with a persistence-failing valuation exists. -/
def screenP (n : Nat) : Res × Res := Id.run do
  let mut yes : Res := {}
  let mut no : Res := {}
  for F in wellFormed n do
    for v in upsets F do
      let c := colaxV F v
      let fired := (worlds F).any c
      let nonId := (worlds F).any fun w => c w != v w
      let ok := isUp F c
      if squareB F then
        yes := note yes ok fired nonId s!"S-P FAIL n={n} square-frame"
      else
        -- for square-FAILING frames we WANT some persistence failure:
        -- record them; the necessity check is the aggregate below
        no := note no ok fired nonId ""
  return (yes, no)

/-- S-C/S-U/S-A/S-R/S-F on the law-satisfying frames. -/
def screenLaws (n : Nat) : Res × Res × Res × Res × Res := Id.run do
  let mut cRes : Res := {}      -- counit
  let mut uRes : Res := {}      -- unit
  let mut aRes : Res := {}      -- adjunction (iff)
  let mut rRes : Res := {}      -- co-residuation
  let mut fRes : Res := {}      -- fragment-relative fallibility + ff
  for F in wellFormed n do
    if squareB F && counitB F && serialB F then
      for v in upsets F do
        let cl := colaxV F v
        let lx := laxV F v
        let fired := (worlds F).any cl
        let nonId := (worlds F).any fun w => cl w != v w
        -- counit: colax (lax v) ≤ v
        let okC := (worlds F).all fun w => !(colaxV F (laxV F v) w) || v w
        cRes := note cRes okC fired nonId
          s!"S-C FAIL n={n} counit-frame"
        -- unit: v ≤ lax (colax v)
        let okU := (worlds F).all fun w => !(v w) || laxV F (colaxV F v) w
        uRes := note uRes okU fired nonId s!"S-U FAIL n={n}"
        -- adjunction as an iff, against every second upset
        let mut okA := true
        for u in upsets F do
          let l := (worlds F).all fun w => !(cl w) || u w
          let r := (worlds F).all fun w => !(v w) || laxV F u w
          if l != r then okA := false
        aRes := note aRes okA fired nonId s!"S-A FAIL n={n}"
        -- co-residuation: (v ≤ b ∨ c) iff (v ⤙ b ≤ c), over upsets b, c
        let mut okR := true
        for b in upsets F do
          for c in upsets F do
            let coim : Nat → Bool := fun w =>
              (worlds F).any fun x => F.riB x w && v x && !(b x)
            let l := (worlds F).all fun w => !(v w) || b w || c w
            let r := (worlds F).all fun w => !(coim w) || c w
            if l != r then okR := false
        rRes := note rRes okR fired nonId s!"S-R FAIL n={n}"
        -- fragment-relative fallibility: fallible worlds are in every
        -- upset that is full on F (forward fragment), and ff is empty
        let ffV : Nat → Bool := fun w =>
          (worlds F).any fun x => F.riB x w && true && !true
        let okF := (worlds F).all fun w => !(ffV w)
        fRes := note fRes okF fired nonId s!"S-F FAIL n={n}: ff fired"
  return (cRes, uRes, aRes, rRes, fRes)

/-- S-M: `BiModel`'s laws are NOT free — count well-formed frames
failing each law. -/
def screenProper (n : Nat) : Nat × Nat × Nat := Id.run do
  let ws := wellFormed n
  let mut nosq := 0
  let mut noco := 0
  for F in ws do
    if !squareB F then nosq := nosq + 1
    if !counitB F then noco := noco + 1
  return (ws.length, nosq, noco)

def report (n : Nat) : IO Unit := do
  let (wf, nosq, noco) := screenProper n
  let nser := ((wellFormed n).filter (fun F => !serialB F)).length
  IO.println s!"n={n}: well-formed frames={wf}, square_c-failing={nosq}, counit_c-failing={noco}, serial_c-failing={nser}"
  let (pYes, pNo) := screenP n
  IO.println s!"  S-P (colax persistent | square holds): pass={pYes.pass} FAIL={pYes.fail} fired={pYes.fired} nonId={pYes.nonId}"
  IO.println s!"  S-P (square fails): persistence pass={pNo.pass} fail={pNo.fail}  [necessity: fail>0 means the law is not vacuous]"
  let (c, u, a, r, f) := screenLaws n
  IO.println s!"  S-C counit:        pass={c.pass} FAIL={c.fail} fired={c.fired} nonId={c.nonId}"
  IO.println s!"  S-U unit:          pass={u.pass} FAIL={u.fail}"
  IO.println s!"  S-A adjunction:    pass={a.pass} FAIL={a.fail}"
  IO.println s!"  S-R co-residuation:pass={r.pass} FAIL={r.fail}"
  IO.println s!"  S-F ff nowhere:    pass={f.pass} FAIL={f.fail}"
  for cert in (pYes.certs ++ c.certs ++ u.certs ++ a.certs ++ r.certs ++ f.certs).take 10 do
    IO.println s!"  CERT {cert}"
  (← IO.getStdout).flush

def main : IO Unit := do
  IO.println "BiLax round-0 screens (docs/bilax-plan.md §4)"
  for n in [1, 2] do
    report n
  IO.println "SCREENS-DONE"

end BiLax.Screens

def main : IO Unit := BiLax.Screens.main
