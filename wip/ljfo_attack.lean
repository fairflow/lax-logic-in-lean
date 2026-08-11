/-
The CimpAnt frontier attack (2026-08-11, the review round).

Purpose: attack the STATEMENT `CimpAnt` (LJFO.lean:1342) as a statement,
per the testing doctrine — not re-check the cells the bank already
passed.  Three directions the existing bank did not cover:

  1. CORPUS REPLAY — the hard instances of the OTHER routes, translated
     into CimpAnt stations: the G4iLL blocker station `[◯p→r, ◯((◯p→r)→◯p)]`
     itself (the ①/② double-use configuration with the p-CARRYING modal
     implication), the join shape `↓◯p ⊃ ◯p`, the unboxed blocker.
  2. FRONTIER EXTENSION — strata the bank never reached: stations with
     TWO modal implications (crossed χ), station size 3, χ at non-head
     positions (all splits swept), `Q′` of modal depth 2–3 (the GZ
     ladder direction), p-carrying `Q′` beside p-carrying stations.
  3. BOUNDARY / BRANCH COVERAGE — the no-row corner (`Q′ = ↓(imp)`,
     where forced change #2 assigns NO lax goal-inversion row), `Q′ = ⊥`,
     or-shaped `Q′` (the 3-row family), boxes with implication content
     on the kept side.

Verdict discipline: `.fail` and `.no` only ever on CERTIFICATES
(refute? countermodels); `.flag` = hypothesis certified derivable but
conclusion unsettled at budget — the frontier marker, to be re-run at
higher budget, never a verdict.

Caveat on refutation strength: the engines decide PLL (G4c-complete).
A certified fail refutes CimpAnt's semantic content; to refute the Lean
statement itself, rebuild the hypothesis derivation as a `Stab` witness
via `LJFOSearch.search` (the decider round-trip) — escalation step,
done per-fail, not in the sweep.
-/
import LaxLogic.LJFOCore
import LaxLogic.PLLG4Dec
import LaxLogic.PLLSearch
import LaxLogic.LJFOFuel

open LJFO PLLND

namespace LJFOAttack

deriving instance Repr for LJFO.Pos
deriving instance Repr for LJFO.Neg

/-! ## Kit (as in wip/ljfo_eval.lean) -/

mutual
def posF : Pos → PLLFormula
  | .atom a => .prop a
  | .fls => .falsePLL
  | .or P Q => .or (posF P) (posF Q)
  | .down M => negF M
def negF : Neg → PLLFormula
  | .up P => posF P
  | .imp Q N => .ifThen (posF Q) (negF N)
  | .and M N => .and (negF M) (negF N)
  | .circ P => .somehow (posF P)
end

inductive V | yes | no | unk
deriving Repr, DecidableEq

def nodeBudget : Nat := 40000

def verdict (Γ : List PLLFormula) (C : PLLFormula) : V :=
  match PLLND.Search.prove?Bounded nodeBudget Γ C with
  | some _ => .yes
  | none =>
    match PLLND.Search.refute? {} Γ C with
    | some _ => .no
    | none => .unk

def provN (Γ : List Neg) (C : PLLFormula) : V :=
  verdict (Γ.map negF) C

def pv : String := "p"

inductive C3 | pass | fail | flag
deriving Repr, DecidableEq

def cell (hyp : V) (concl : V) : C3 :=
  match hyp, concl with
  | .yes, .no => .fail
  | .yes, .unk => .flag
  | _, _ => .pass

/-! ## Legality: parked shapes + saturation (the statement's hypotheses) -/

def isParked : Neg → Bool
  | .up (.atom _) => true
  | .imp (.atom _) _ => true
  | .imp (.down (.imp _ _)) _ => true
  | .circ _ => true
  | .imp (.down (.circ _)) _ => true
  | _ => false

def isSat (done : List Neg) : Bool :=
  match findFire done (splits done) with
  | some _ => false
  | none => true

def legal (done : List Neg) : Bool :=
  done.all isParked && isSat done

def pfreeN : Neg → Bool
  | .up P => pfreeP P
  | .imp Q N => pfreeP Q && pfreeN N
  | .and M N => pfreeN M && pfreeN N
  | .circ P => pfreeP P
where
  pfreeP : Pos → Bool
    | .atom a => a != pv
    | .fls => true
    | .or P Q => pfreeP P && pfreeP Q
    | .down M => pfreeN M

/-! ## THE cell: the full CimpAnt statement, χ at an arbitrary split -/

/-- `E(done), K ⊢ A(rest ⇒ ↑↓◯Q′)` demanded whenever `done, K ⊢ ◯Q′`,
for `(↓◯Q′ ⊃ N, rest) ∈ splits done` — exactly `CimpAnt`'s cell with
`Γ′ = done ++ K` (the maximal legal `Γ′`, so the most instances). -/
def cimpAntCell (done rest : List Neg) (Q' : Pos) (K : List Neg) : C3 :=
  cell (provN (done ++ K) (.somehow (posF Q')))
       (provN (interp pv [] done none :: K)
         (negF (interp pv [] rest (some (.up (.down (.circ Q')))))))

/-- Sweep one station against one kept context: every ◯-implication
member, at its own split (so χ-position is covered by construction). -/
def sweepStation (done : List Neg) (K : List Neg) :
    List (C3 × Pos × List Neg) :=
  if legal done && K.all pfreeN then
    (splits done).foldr (fun (X, rest) acc =>
      match X with
      | .imp (.down (.circ Q')) _ =>
          let r := cimpAntCell done rest Q' K
          if r != .pass then (r, Q', rest) :: acc else acc
      | _ => acc) []
  else []

/-! ## Building blocks -/

def aP : Pos := .atom pv
def aQ : Pos := .atom "q"
def aR : Pos := .atom "r"
def uQ : Neg := .up aQ
def uR : Neg := .up aR
def boxP : Neg := .circ aP
def boxQ : Neg := .circ aQ
def boxOr : Neg := .circ (.or aP aQ)
def boxBoxP : Neg := .circ (.down (.circ aP))

/-- `◯p → r` — the blocker's p-carrying modal implication. -/
def hyp : Neg := .imp (.down (.circ aP)) uR
/-- `◯q → r` — its p-free twin. -/
def hypQ : Neg := .imp (.down (.circ aQ)) uR
/-- `◯q → p` — p in the consequent. -/
def hypQP : Neg := .imp (.down (.circ aQ)) (.up aP)
/-- `◯p → ◯p` — the join shape (monad multiplication territory). -/
def joinP : Neg := .imp (.down (.circ aP)) (.circ aP)
def joinQ : Neg := .imp (.down (.circ aQ)) (.circ aQ)
/-- `(◯p→r) → ◯p` — the blocker's Dyckhoff implication. -/
def chi : Neg := .imp (.down hyp) (.circ aP)
/-- `◯((◯p→r)→◯p)` — the blocker's box. -/
def bchi : Neg := .circ (.down chi)
/-- Dyckhoff, p-free, box body: `(q→r) → ◯q`. -/
def dq : Neg := .imp (.down (.imp aQ uR)) (.circ aQ)
/-- qimp on p: `p → ↑q`. -/
def qimpP : Neg := .imp aP uQ

/-- GZ-ladder modal implications: `Q′` at modal depth 2 and 3. -/
def cimpNest : Neg := .imp (.down (.circ (.down (.circ aP)))) uR
def cimpNest2 : Neg := .imp (.down (.circ (.down (.circ (.down (.circ aP)))))) uR
/-- Or-shaped `Q′` (the 3-row family): `◯(p∨q) → r`. -/
def cimpOr : Neg := .imp (.down (.circ (.or aP aQ))) uR
/-- The NO-ROW corner: `Q′ = ↓(q ⊃ ↑r)` — lax implications have no
goal-inversion row (forced change #2). -/
def cimpImp : Neg := .imp (.down (.circ (.down (.imp aQ uR)))) uR
def cimpImpP : Neg := .imp (.down (.circ (.down (.imp aP uR)))) uR
/-- Boundary: `Q′ = ⊥`. -/
def cimpFls : Neg := .imp (.down (.circ .fls)) uR

/-! ## Banks -/

/-- Kept contexts, all p-free; the last carries a box with implication
content (a kept box that must be OPENED and its content used). -/
def kBank : List (List Neg) :=
  [[], [uQ], [boxQ], [hypQ], [dq], [.circ (.down (.imp aQ uR))]]

/-- Stations.  Corpus first, then frontier strata, then boundary. -/
def stationBank : List (List Neg) :=
  [ -- corpus
    [hyp, bchi],            -- THE blocker station (①/② live)
    [bchi, hyp],            -- position swap
    [hyp, chi],             -- blocker unboxed: cimp + dyk
    [joinP],                -- join alone
    [joinP, boxQ],
    [joinP, bchi],          -- join meets the blocker box
    -- frontier: two modal implications (crossed χ)
    [hyp, hypQ],
    [hyp, joinQ],
    [joinP, hyp],
    [hypQP, hyp],           -- p in one consequent, p in the other antecedent
    -- frontier: size 3
    [hyp, dq, boxQ],
    [hyp, bchi, boxQ],
    [hyp, hypQ, boxP],
    [hyp, .up (.atom "q"), boxQ],
    -- frontier: p-placements
    [hypQP, boxP],
    [hyp, boxP],
    [hyp, boxOr],
    [hyp, boxBoxP],
    [hyp, qimpP],
    -- GZ ladder
    [cimpNest, boxP],
    [cimpNest],
    [cimpNest2, boxP],
    -- boundary / branch coverage
    [cimpOr, boxP],
    [cimpOr],
    [cimpImp, boxQ],
    [cimpImp],
    [cimpImpP, boxP],
    [cimpFls],
    [cimpFls, boxQ],
    -- controls (bank territory, kept for calibration)
    [hypQ],
    [hyp] ]

/-! ## Sweeps (streamed in chunks so partial output survives) -/

def runChunk (stations : List (List Neg)) :
    List (List Neg × List Neg × C3 × Pos × List Neg) := Id.run do
  let mut out := []
  for done in stations do
    for K in kBank do
      for (r, Q', rest) in sweepStation done K do
        out := (done, K, r, Q', rest) :: out
  return out

-- corpus + join (stations 1–6)
#eval runChunk (stationBank.take 6)
-- crossed-χ + size 3 (stations 7–14)
#eval runChunk ((stationBank.drop 6).take 8)
-- p-placements + GZ ladder (stations 15–22)
#eval runChunk ((stationBank.drop 14).take 8)
-- boundary + controls (stations 23–31)
#eval runChunk (stationBank.drop 22)

/-! ## E2/A2 minimality on the extended stations (a different direction:
the frontier may force change #4 in the aggregates rather than in the
miner).  ψ/P p-free. -/

def e2cell (done Δ : List Neg) (ψ : Neg) : C3 :=
  cell (provN (done ++ Δ) (negF ψ))
       (provN (interp pv [] done none :: Δ) (negF ψ))

def a2cellT (done Δ : List Neg) (P : Pos) : C3 :=
  cell (provN (done ++ Δ) (posF P))
       (provN (interp pv [] done none :: Δ)
         (negF (interp pv [] done (some (.up P)))))

def a2cellL (done Δ : List Neg) (P : Pos) : C3 :=
  cell (provN (done ++ Δ) (.somehow (posF P)))
       (provN (interp pv [] done none :: Δ)
         (negF (interp pv [] done (some (.circ P)))))

def psiBank : List Neg := [uQ, uR, boxQ, hypQ, .up (.or aQ aR)]
def pBank : List Pos := [aQ, aR, .fls, .or aQ aR, .down boxQ]

def runMinChunk (stations : List (List Neg)) :
    List (String × List Neg × List Neg × C3) := Id.run do
  let mut out := []
  for done in stations do
    if legal done then
      for Δ in [([] : List Neg), [uQ], [boxQ], [hypQ]] do
        for ψ in psiBank do
          let r := e2cell done Δ ψ
          if r != .pass then out := ("E2", done, Δ, r) :: out
        for P in pBank do
          let rT := a2cellT done Δ P
          let rL := a2cellL done Δ P
          if rT != .pass then out := ("A2T", done, Δ, rT) :: out
          if rL != .pass then out := ("A2L", done, Δ, rL) :: out
  return out

#eval runMinChunk (stationBank.take 10)
#eval runMinChunk ((stationBank.drop 10).take 11)
#eval runMinChunk (stationBank.drop 21)

end LJFOAttack
