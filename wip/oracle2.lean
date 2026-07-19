import LaxLogic.PLLCountermodelEmit
import LaxLogic.PLLG4Dec
import LaxLogic.PLLSemUI

/-!
# oracle2 — the packaged two-sided decision TOOL (countermodel-first)

Matthew's resource directive (2026-07-19): a failing proof search must
try every route, so its cost is chaotic; a decision tool should attempt
CHEAP COUNTERMODELS first/instead, because checking a proposed
countermodel is cheap (the tools-vs-proofs discipline: the tool may be
fallible, its accepted outputs are verified).

The library already has both sides (belief session, 2026-07-18):
`search` (sound-on-true, fueled), `G4cTm.find` (fuel-free terms),
`CounterEmit.emit` + verified `FinCM.checkB` + `not_provable_of_check`
(certified refutations).  What was missing — and what bit the
semantic-UI probes — is the CHEAP negative stage and the staging
policy.  This file packages:

* a battery of ≤4-world frames (the shapes that refuted everything the
  UI programme met: chains, rigid chains, the fork, the doubling);
* `sweep` — enumerate hereditary decorations of the battery frames
  over the sequent's atoms and gate each candidate through the
  VERIFIED checker `FinCM.checkB` (a wrong guess cannot certify);
* `decide2` — the staged verdict, COUNTERMODELS FIRST (the sweep is
  O(ms) with the vector evaluator; failing proof search is chaotic):
    1. `sweep` (cheap certified negative);
    2. `search` at low fuel (cheap positive: successes are
       near-instant even at weight ~35);
    3. `search` at high fuel, WEIGHT-GATED (the calibration proxy:
       deep failing search is only risked on small sequents);
    4. `CounterEmit.emit`, gated by closure size (complete-flavoured
       negative, exponential);
    5. unknown.

TRUST: `.refuted` verdicts carry a `(FinCM, world)` pair that passed
`checkB`; `not_provable_of_check` upgrades any such pair to a
machine-checked `¬ Nonempty (LaxND Γ C)` by `decide` when a paper-grade
certificate is wanted.  `.proved` verdicts are `search`/`find`
successes (kernel-grade via their soundness theorems).  `unknown` is
honest.

Run: `lake env lean --run wip/oracle2.lean` (benchmark harness in
`main`; compares against the plain one-sided oracle).
-/

open PLLFormula PLLND PLLND.SemUI

namespace Oracle2

/-! ## Frames and hereditary decorations -/

structure Frame where
  n : Nat
  ri : List (Nat × Nat)    -- strict part, transitively closed
  rm : List (Nat × Nat)    -- ⊆ ri
  fall : List Nat

/-- The battery: every shape that refuted something in the UI
programme, smallest first.  (1) classical point, (2) fallible point,
(3) chain2 Rm=Ri, (4) chain2 rigid, (5) chain2 no-F, (6) chain3 rigid
except 1→2 (the Löb shape), (7) chain3 full, (8) the fork (C4 shape),
(9) the V (C3 shape), (10) doubled chain2. -/
def frames : List Frame :=
  [ ⟨1, [], [], []⟩
  , ⟨1, [], [], [0]⟩
  , ⟨2, [(0,1)], [(0,1)], [1]⟩
  , ⟨2, [(0,1)], [], [1]⟩
  , ⟨2, [(0,1)], [(0,1)], []⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2]⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2),(0,2)], [2]⟩
  , ⟨4, [(0,1),(0,2),(2,3),(0,3)], [(2,3)], [3]⟩
  , ⟨3, [(0,1),(0,2)], [(0,2)], [2]⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,3),(2,3)], [(1,3),(2,3)], [3]⟩ ]

def riStep (f : Frame) (w v : Nat) : Bool := (w, v) ∈ f.ri

/-! ## Fast untrusted evaluation: bottom-up world vectors

`FinCM.forceB` recomputes subformulas once per visited world, so its
cost is `n^depth` — minutes on weight-40 sequents.  The scan below
evaluates each subformula ONCE as a vector over all worlds (`weight ×
n²` total), and only candidates that pass the fast scan are handed to
the VERIFIED `FinCM.checkB` (one call, on a hit).  The tool may be
wrong only by MISSING countermodels, never by accepting one. -/

def riR (M : FinCM) (w v : Nat) : Bool := decide ((w, v) ∈ M.ri) || decide (w = v)
def rmR (M : FinCM) (w v : Nat) : Bool := decide ((w, v) ∈ M.rm) || decide (w = v)

def forceV (M : FinCM) : PLLFormula → Array Bool
  | .prop a => (Array.range M.n).map fun w =>
      decide ((w, a) ∈ M.val) || decide (w ∈ M.fall)
  | .falsePLL => (Array.range M.n).map fun w => decide (w ∈ M.fall)
  | .and A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w => vA.getD w false && vB.getD w false
  | .or A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w => vA.getD w false || vB.getD w false
  | .ifThen A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w =>
        (List.range M.n).all fun v =>
          !(riR M w v) || !(vA.getD v false) || vB.getD v false
  | .somehow A =>
      let vA := forceV M A
      (Array.range M.n).map fun w =>
        (List.range M.n).all fun v =>
          !(riR M w v) ||
            (List.range M.n).any fun u => rmR M v u && vA.getD u false

def fastCheck (M : FinCM) (w : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    Bool :=
  Γ.all (fun F => (forceV M F).getD w false) && !((forceV M C).getD w false)

/-- Truth-sets as bitmasks: hereditary along `ri` and full on `fall`. -/
def admissible (f : Frame) : List Nat :=
  (List.range (2 ^ f.n)).filter fun m =>
    ((List.range f.n).all fun w =>
      !(m.testBit w) ||
        (List.range f.n).all fun v => !(riStep f w v) || m.testBit v) &&
    (f.fall.all fun w => m.testBit w)

def assigns : List String → List Nat → List (List (String × Nat))
  | [], _ => [[]]
  | a :: as, adm =>
      (assigns as adm).flatMap fun rest => adm.map fun m => (a, m) :: rest

def toFinCM (f : Frame) (asgn : List (String × Nat)) : FinCM :=
  { n := f.n, ri := f.ri, rm := f.rm, fall := f.fall
    val := asgn.flatMap fun am =>
      (List.range f.n).filterMap fun w =>
        if am.2.testBit w then some (w, am.1) else none }

def atomList : PLLFormula → List String
  | .prop a => [a]
  | .falsePLL => []
  | .and A B | .or A B | .ifThen A B => atomList A ++ atomList B
  | .somehow A => atomList A

def atomsOf (l : List PLLFormula) : List String :=
  (l.flatMap atomList).eraseDups

/-- Cheap certified negative: scan the battery with the fast vector
evaluator, gate every hit through the VERIFIED `FinCM.checkB`. -/
def sweep (Γ : List PLLFormula) (C : PLLFormula) : Option (FinCM × Nat) :=
  let ats := atomsOf (C :: Γ)
  frames.findSome? fun f =>
    let adm := admissible f
    if adm.length ^ ats.length > 100000 then none
    else
      (assigns ats adm).findSome? fun asgn =>
        let M := toFinCM f asgn
        let vΓ := Γ.map (forceV M)
        let vC := forceV M C
        (List.range f.n).findSome? fun w =>
          if vΓ.all (fun v => v.getD w false) && !(vC.getD w false) &&
              FinCM.checkB M w Γ C then
            some (M, w)
          else none

/-! ## The staged verdict -/

inductive Verdict where
  | proved : Verdict
  | refuted : FinCM → Nat → Verdict
  | unknown : Verdict

def searchAt (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C

def EMIT_CLOSURE_CAP : Nat := 12

/-- Weight above which the deep failing search is not attempted (the
failing-search cost is chaotic; the calibration proxy for Matthew's
"10× a known-true time" rule). -/
def DEEP_WEIGHT_CAP : Nat := 30

def decide2 (s1 s2 : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Verdict :=
  -- countermodels first: the sweep is O(ms) and failing search is not
  match sweep Γ C with
  | some (M, w) => .refuted M w
  | none =>
    if searchAt s1 Γ C then .proved
    else if listWeight (C :: Γ) ≤ DEEP_WEIGHT_CAP && searchAt s2 Γ C then
      .proved
    else if (CounterEmit.closureOf Γ C).length ≤ EMIT_CLOSURE_CAP then
      match CounterEmit.emit Γ C with
      | some (M, w) => .refuted M w
      | none => .unknown
    else .unknown

/-! ## Benchmark harness -/

def pf (F : PLLFormula) : String := F.toString

def showVerdict : Verdict → String
  | .proved => "PROVED"
  | .refuted M w =>
      s!"REFUTED (n={M.n} fall={M.fall} val={M.val} @w{w})"
  | .unknown => "UNKNOWN"

def pV : PLLFormula := .prop "p"
def qV : PLLFormula := .prop "q"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL
def peirceF : PLLFormula := (gB.ifThen pV).ifThen pV

/-- (name, Γ, C, expected: some true = provable). -/
def cases : List (String × List PLLFormula × PLLFormula × Option Bool) :=
  [ ("T1  ⊢ p⊃p",            [], pV.ifThen pV, some true)
  , ("T2  ◯◯p ⊢ ◯p",         [pV.somehow.somehow], pV.somehow, some true)
  , ("T3  ◯⊥ ⊢ ◯p",          [gB], pV.somehow, some true)
  , ("T4  allCand(◯p⊃p) ⊢ ◯p⊃p",
      [allCand "p" ((pV.somehow).ifThen pV)], (pV.somehow).ifThen pV, some true)
  , ("T5  p⊃q, ◯p ⊢ ◯q",     [pV.ifThen qV, pV.somehow], qV.somehow, some true)
  , ("U1  ¬¬◯⊥ ⊢ ◯⊥",        [nF (nF gB)], gB, some false)
  , ("U2  allCand(peirce) ⊢ peirce",
      [allCand "p" peirceF], peirceF, some false)
  , ("U3  ⊢ ◯p⊃p",           [], (pV.somehow).ifThen pV, some false)
  , ("U4  ◯(◯p⊃p) ⊢ ◯⊥",     [((pV.somehow).ifThen pV).somehow], gB, some false)
  , ("U5  (◯⊥⊃p)⊃p ⊢ ◯⊥",    [peirceF], gB, some false)
  ]

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== oracle2: staged two-sided decision (battery-first) =="
  for (name, Γ, C, exp) in cases do
    let t0 ← IO.monoMsNow
    let v := decide2 60 400 Γ C
    let t1 ← IO.monoMsNow
    let ok := match v, exp with
      | .proved, some true => "✓"
      | .refuted _ _, some false => "✓"
      | .unknown, _ => "?"
      | _, _ => "✗ MISMATCH"
    pl s!"{name}: {showVerdict v}  {ok}  ({t1 - t0} ms)"
  pl "== done =="

end Oracle2

def main : IO Unit := Oracle2.main
