/-
THE (R) SCREEN — can a countermodel always be made REDUCED?

`Reject.built_countermodel_of_reduced` (T2) needs a finite REDUCED
countermodel.  Neither of the repo's two finite-countermodel sources
supplies one: the filtration orders worlds by inclusion on theories
while distinguishing them by a modal component, and the emitter's
`canonCMof` does the same (`ri := val ⊆ val'`, worlds are `FTheory`
triples).  So the open item is

  (R) every underivable sequent has a finite REDUCED countermodel.

The proposed route: REFINE `Rᵢ` so that `Rᵢ`-equivalent worlds are
separated by their modal data.  Per doctrine a screen sweeps a LATTICE
of variants, not one statement — a failure may be repairable by
changing the refinement:

  V1  Fm-inclusion   w ≤ v  when  Fm(w) ⊆ Fm(v)
      (`Fm(w)` = closure formulas refuted at every `Rₘ`-successor of
      `w` — the emitter's `mfal`, computed semantically)
  V2  cone-inclusion w ≤ v  when  Rₘ-cone(w) ⊆ Rₘ-cone(v)
  V3  index order    w ≤ v  when  w ≤ v as numbers (guaranteed
      antisymmetric; the control for "does antisymmetry alone cost
      forcing?")
  V4  V1 with the index as tie-break (antisymmetric AND modal)

Each variant is judged on three things, all decidable:
  (a) is the refined frame still WELL-FORMED?
  (b) is it REDUCED?
  (c) is FORCING PRESERVED at every world for every closure formula?
Only (c) can make the route fail, and a failure is a certificate.

Controls: the refinement must actually CHANGE something on the
non-reduced models (else the sweep is vacuous), and the §E obstruction
model of `t2screen` is run explicitly.
-/
import LaxLogic.PLLCountermodelEmit

open PLLND PLLND.FinCM

namespace RScreen

abbrev F := PLLFormula

def vd (b : Bool) : String := if b then "pass" else "FAIL"

def wf (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all (fun x => ws.all fun y => ws.all fun z =>
    (!(M.riB x y && M.riB y z) || M.riB x z) &&
    (!(M.rmB x y && M.rmB y z) || M.rmB x z)) &&
  ws.all (fun x => ws.all fun y =>
    (!(M.rmB x y) || M.riB x y) &&
    (!(M.fallB x && M.riB x y) || M.fallB y)) &&
  M.val.all (fun p => ws.all fun v => !(M.riB p.1 v) || M.valB v p.2)

/-- Which clause of well-formedness fails, if any. -/
def wfWhy (M : FinCM) : List String :=
  let ws := List.range M.n
  (if ws.all (fun x => ws.all fun y => ws.all fun z =>
      !(M.riB x y && M.riB y z) || M.riB x z) then [] else ["Ri-trans"]) ++
  (if ws.all (fun x => ws.all fun y => ws.all fun z =>
      !(M.rmB x y && M.rmB y z) || M.rmB x z) then [] else ["Rm-trans"]) ++
  (if ws.all (fun x => ws.all fun y => !(M.rmB x y) || M.riB x y) then []
   else ["Rm⊆Ri"]) ++
  (if ws.all (fun x => ws.all fun y =>
      !(M.fallB x && M.riB x y) || M.fallB y) then [] else ["hered-F"]) ++
  (if M.val.all (fun p => ws.all fun v => !(M.riB p.1 v) || M.valB v p.2) then []
   else ["hered-V"])

def reduced (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all fun x => ws.all fun y => !(M.riB x y && M.riB y x) || decide (x = y)

/-! ## The closure and the modal fingerprint -/

def bot : F := .falsePLL
def oBot : F := .somehow bot
def nOBot : F := .ifThen oBot bot
def nnOBot : F := .ifThen nOBot bot
def pv : F := .prop "p"

def closure : List F :=
  [bot, .ifThen bot bot, oBot, nOBot, nnOBot, .or nOBot oBot,
   .somehow nOBot, .ifThen nnOBot oBot, .or nnOBot nOBot,
   pv, .somehow pv, .ifThen pv bot, .or pv (.ifThen pv bot),
   .somehow (.somehow pv), .ifThen (.somehow pv) pv, .ifThen pv (.somehow pv)]

/-- `Fm(w)`: closure formulas refuted at EVERY `Rₘ`-successor of `w`.
The semantic form of the emitter's `mfal` component. -/
def FmOf (M : FinCM) (w : Nat) : List F :=
  closure.filter fun N =>
    (List.range M.n).all fun u => !(M.rmB w u) || !(M.forceB u N)

def coneOf (M : FinCM) (w : Nat) : List Nat :=
  (List.range M.n).filter fun u => M.rmB w u

def subF (a b : List F) : Bool := a.all (fun x => b.contains x)
def subN (a b : List Nat) : Bool := a.all (fun x => b.contains x)

/-! ## The four refinements -/

/-- `Rₘ`-RANK: the size of a world's `Rₘ`-down-set.  On an
`Rₘ`-acyclic model `Rm v w` with `v ≠ w` gives a STRICTLY smaller
down-set, so rank is a linear extension of `Rₘ` — which is what the
tie-break needs: V5 failed `Rᵢ`-transitivity because "Rₘ wins, else
index" can CYCLE (witness: a 3-element `Rᵢ`-class with `Rm 2 0`, where
0 < 1 < 2 < 0). -/
def rmRank (M : FinCM) (w : Nat) : Nat :=
  ((List.range M.n).filter fun v => M.rmB v w).length

def refineBy (M : FinCM) (le : Nat → Nat → Bool) : FinCM :=
  { M with
    ri := (List.range M.n).flatMap fun w =>
      (List.range M.n).filterMap fun v =>
        if M.riB w v && (!(M.riB v w) || le w v) then some (w, v) else none }

def variants (M : FinCM) : List (String × FinCM) :=
  [("V1 Fm-incl", refineBy M (fun w v => subF (FmOf M w) (FmOf M v))),
   ("V2 cone-incl", refineBy M (fun w v => subN (coneOf M w) (coneOf M v))),
   ("V3 index", refineBy M (fun w v => decide (w ≤ v))),
   ("V4 Fm+index", refineBy M (fun w v =>
      (subF (FmOf M w) (FmOf M v) && !(subF (FmOf M v) (FmOf M w)))
      || (subF (FmOf M w) (FmOf M v) && subF (FmOf M v) (FmOf M w) && decide (w ≤ v)))),
   -- V5: V4's tie-break made Rₘ-COMPATIBLE.  V4 broke `Rm ⊆ Ri` when
   -- `Rm w v` held with `Fm(w) = Fm(v)` and `w > v` as indices; here
   -- `Rm` wins the tie, and the index only breaks what `Rm` leaves.
   ("V5 Fm+Rm+index", refineBy M (fun w v =>
      (subF (FmOf M w) (FmOf M v) && !(subF (FmOf M v) (FmOf M w)))
      || (subF (FmOf M w) (FmOf M v) && subF (FmOf M v) (FmOf M w) &&
          (M.rmB w v || (!(M.rmB v w) && decide (w ≤ v)))))),
   -- V6: Fm-inclusion, then a LINEAR EXTENSION of Rₘ (by rank), then
   -- the index.  Total on each equal-Fm group, so transitive; extends
   -- Rₘ, so `Rm ⊆ Ri` survives; antisymmetric, so REDUCED.
   ("V6 Fm+rank+index", refineBy M (fun w v =>
      (subF (FmOf M w) (FmOf M v) && !(subF (FmOf M v) (FmOf M w)))
      || (subF (FmOf M w) (FmOf M v) && subF (FmOf M v) (FmOf M w) &&
          (decide (rmRank M w < rmRank M v)
           || (decide (rmRank M w = rmRank M v) && decide (w ≤ v))))))]

/-- A PROPER `Rₘ`-cycle: two distinct worlds each `Rₘ`-below the
other.  No refinement of `Rᵢ` can be antisymmetric while containing
`Rₘ`, so these models must be QUOTIENTED first — and the quotient is
sound, because `Rₘ`-equivalent worlds are BISIMILAR (equal up-sets,
equal cones). -/
def rmAcyclic (M : FinCM) : Bool :=
  (List.range M.n).all fun w => (List.range M.n).all fun v =>
    !(M.rmB w v && M.rmB v w) || decide (w = v)

/-- Forcing preserved at every world for every closure formula? -/
def forcingPreserved (M M' : FinCM) : Bool :=
  (List.range M.n).all fun w => closure.all fun φ => M.forceB w φ == M'.forceB w φ

/-- A certificate of failure: the first (world, formula) that moves. -/
def firstMove (M M' : FinCM) : Option (Nat × F) :=
  (List.range M.n).findSome? fun w =>
    (closure.find? fun φ => M.forceB w φ != M'.forceB w φ).map fun φ => (w, φ)

/-! ## The battery -/

def pairsOf (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun x => (List.range n).map fun y => (x, y)

def subsetOf (l : List (Nat × Nat)) (code : Nat) : List (Nat × Nat) :=
  (l.zipIdx.filter fun p => (code / 2 ^ p.2) % 2 = 1).map (·.1)

def framesN (n : Nat) : List FinCM :=
  let ps := (pairsOf n).filter (fun e => e.1 != e.2)
  let cap := 2 ^ ps.length
  (List.range cap).flatMap fun ci =>
    (List.range cap).flatMap fun cm =>
      (List.range (2 ^ n)).flatMap fun cf =>
        (List.range (2 ^ n)).map fun cv =>
          (⟨n, subsetOf ps ci, subsetOf ps cm,
            (List.range n).filter fun x => (cf / 2 ^ x) % 2 = 1,
            ((List.range n).filter fun x => (cv / 2 ^ x) % 2 = 1).map
              fun w => (w, "p")⟩ : FinCM)

def battery (maxN : Nat) : List FinCM :=
  ((List.range maxN).flatMap fun k => framesN (k + 1)).filter wf

/-! ## The sweep -/

structure Tally where
  n : Nat := 0
  wfOk : Nat := 0
  redOk : Nat := 0
  forceOk : Nat := 0
  changed : Nat := 0
  cert : Option String := none

def sweep (bat : List FinCM) : IO Unit := do
  let nonred := bat.filter (fun M => !(reduced M))
  let acyc := nonred.filter rmAcyclic
  IO.println s!"battery {bat.length} well-formed frames; NON-reduced {nonred.length}; of those Rₘ-ACYCLIC {acyc.length}"
  IO.println ""
  let names := (variants (bat.headD ⟨1, [], [], [], []⟩)).map (·.1)
  for (idx, name) in names.zipIdx.map (fun p => (p.2, p.1)) do
    let mut t : Tally := {}
    for M in nonred do
      let M' := (variants M)[idx]!.2
      t := { t with n := t.n + 1 }
      if wf M' then t := { t with wfOk := t.wfOk + 1 }
      if reduced M' then t := { t with redOk := t.redOk + 1 }
      if M'.ri.length != M.ri.length then t := { t with changed := t.changed + 1 }
      if forcingPreserved M M' then t := { t with forceOk := t.forceOk + 1 }
      else if t.cert.isNone then
        t := { t with cert := some s!"{repr M} moves at {repr (firstMove M M')}" }
    IO.println s!"{name}"
    IO.println s!"   (a) still well-formed : {t.wfOk}/{t.n}  {vd (t.wfOk == t.n)}"
    IO.println s!"   (b) REDUCED           : {t.redOk}/{t.n}  {vd (t.redOk == t.n)}"
    IO.println s!"   (c) forcing preserved : {t.forceOk}/{t.n}  {vd (t.forceOk == t.n)}"
    IO.println s!"   control: refinement actually changed Rᵢ on {t.changed}/{t.n}"
    match t.cert with
    | some c => IO.println s!"   certificate: {c}"
    | none => pure ()
    -- the same variant restricted to the Rₘ-acyclic models
    let mut a : Tally := {}
    for M in acyc do
      let M' := (variants M)[idx]!.2
      a := { a with n := a.n + 1 }
      if wf M' then a := { a with wfOk := a.wfOk + 1 }
      if reduced M' then a := { a with redOk := a.redOk + 1 }
      if forcingPreserved M M' then a := { a with forceOk := a.forceOk + 1 }
      else if a.cert.isNone then
        a := { a with cert := some s!"{repr M} moves at {repr (firstMove M M')}" }
    IO.println s!"   on Rₘ-ACYCLIC only: wf {a.wfOk}/{a.n}, reduced {a.redOk}/{a.n}, forcing {a.forceOk}/{a.n}  {vd (a.wfOk == a.n && a.redOk == a.n && a.forceOk == a.n)}"
    match a.cert with
    | some c => IO.println s!"   acyclic certificate: {c}"
    | none => pure ()
    let badwf := acyc.filter (fun M => !(wf (variants M)[idx]!.2))
    if !badwf.isEmpty then
      let whys := (badwf.flatMap (fun M => wfWhy (variants M)[idx]!.2)).eraseDups
      IO.println s!"   acyclic wf-failures: {badwf.length}, clauses {whys}"
      IO.println s!"   first source: {repr badwf.head!}"
      IO.println s!"   refined to  : {repr (variants badwf.head!)[idx]!.2}"
    (← IO.getStdout).flush

/-- The §E obstruction of `t2screen`, run explicitly. -/
def obstruction : FinCM := ⟨3, [(0,1),(1,0),(0,2),(1,2)], [(0,2)], [], [(2,"p")]⟩

def sectionObs : IO Unit := do
  let M := obstruction
  IO.println "OBSTRUCTION (t2screen §E): 0 ≈ᵢ 1 with different Rₘ-cones"
  for (name, M') in variants M do
    IO.println s!"  {name}: wf={wf M'} reduced={reduced M'} forcing-preserved={forcingPreserved M M'}"
    match firstMove M M' with
    | some (w, φ) => IO.println s!"    moves at world {w}, formula {repr φ}"
    | none => pure ()

def main : IO Unit := do
  IO.println "(R) SCREEN — can Rᵢ be refined to make a countermodel REDUCED?"
  IO.println s!"closure: {closure.length} formulas"
  IO.println ""
  sectionObs
  IO.println ""
  sweep (battery 3)
  IO.println ""
  IO.println "R-SCREEN-DONE"

end RScreen

def main : IO Unit := RScreen.main
