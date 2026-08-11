/-
The CimpAnt frontier attack, v2 (2026-08-11, the review round).

Purpose: attack the STATEMENT `CimpAnt` (LJFO.lean:1342) as a statement,
per the testing doctrine (CLAUDE.md §Testing for counterexamples):

  1. CORPUS REPLAY — the hard instances of the OTHER routes: the G4iLL
     blocker station `[◯p→r, ◯((◯p→r)→◯p)]` (the ①/② double-use
     configuration, p-CARRYING modal implication), the join shape
     `↓◯p ⊃ ◯p`, the unboxed blocker.
  2. FRONTIER EXTENSION — strata the marathon bank never reached:
     TWO modal implications (crossed χ), station size 3, χ at non-head
     positions (all splits swept), `Q′` at modal depth 2–3 (the GZ
     ladder), p-carrying `Q′` beside p-carrying stations.
  3. BOUNDARY / BRANCH COVERAGE — the no-row corner (`Q′ = ↓(imp)`),
     `Q′ = ⊥`, or-shaped `Q′`, kept boxes with implication content.

v2 adds the SCREENING-HORIZON GATES, after v1 established (by hanging)
that corpus stations with `bchi` sit past the horizon: `sum3 [hyp,bchi]
= 177,390` and the interp values blow up super-linearly with sum3
(E[hyp]=35 nodes but E[hyp,chi]=4,689).  Gates: `sum3 done ≤ 25,000`,
then constructed value sizes `szE + szA ≤ 6,000`; gated-out cells are
REPORTED as skipW/skipSz records (no silent caps), never ground.
This mirrors the G4c room finding: the discriminating regime of the
blocked lemma is expensive to screen there too.

Verdict discipline: `fail`/`no` only on refute? certificates; `flag` =
hypothesis certified derivable, conclusion unsettled at budget (re-run
at raised budget, never a verdict).  A certified fail refutes CimpAnt's
semantic content; to refute the Lean statement, rebuild the hypothesis
as a `Stab` witness via `LJFOSearch.search` (escalation, per-fail).
-/
import LaxLogic.LJFOCore
import LaxLogic.PLLG4Dec
import LaxLogic.PLLSearch

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

mutual
def szP : Pos → Nat
  | .atom _ => 1
  | .fls => 1
  | .or P Q => szP P + szP Q + 1
  | .down M => szN M + 1
def szN : Neg → Nat
  | .up P => szP P + 1
  | .imp Q N => szP Q + szN N + 1
  | .and M N => szN M + szN N + 1
  | .circ P => szP P + 1
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

/-! ## Legality + gates -/

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

def wCap : Nat := 25000
def szCap : Nat := 6000

/-! ## THE cell: the full CimpAnt statement, χ at an arbitrary split.
Output records: (tag, Q′, rest) with tag ∈ FAIL/flag/skipW/skipSz. -/

def sweepStation (done K : List Neg) : List (String × Pos × List Neg) :=
  if !(legal done && K.all pfreeN) then []
  else if sum3 done > wCap then
    if K.isEmpty then [(s!"skipW sum3={sum3 done}", .fls, [])] else []
  else
    let e := interp pv [] done none
    let esz := szN e
    (splits done).foldr (fun XR acc =>
      match XR with
      | (.imp (.down (.circ Q')) _, rest) =>
          let a := interp pv [] rest (some (.up (.down (.circ Q'))))
          if esz + szN a > szCap then
            (s!"skipSz E={esz} A={szN a}", Q', rest) :: acc
          else
            let hy := provN (done ++ K) (.somehow (posF Q'))
            let co := verdict ((e :: K).map negF) (negF a)
            match cell hy co with
            | .pass => acc
            | .fail => ("FAIL", Q', rest) :: acc
            | .flag => ("flag", Q', rest) :: acc
      | _ => acc) []

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

def hyp : Neg := .imp (.down (.circ aP)) uR       -- ◯p → r (blocker)
def hypQ : Neg := .imp (.down (.circ aQ)) uR      -- ◯q → r
def hypQP : Neg := .imp (.down (.circ aQ)) (.up aP) -- ◯q → p
def joinP : Neg := .imp (.down (.circ aP)) (.circ aP) -- ◯p → ◯p
def joinQ : Neg := .imp (.down (.circ aQ)) (.circ aQ)
def chi : Neg := .imp (.down hyp) (.circ aP)      -- (◯p→r) → ◯p
def bchi : Neg := .circ (.down chi)               -- ◯((◯p→r)→◯p)
def dq : Neg := .imp (.down (.imp aQ uR)) (.circ aQ)
def qimpP : Neg := .imp aP uQ

def cimpNest : Neg := .imp (.down (.circ (.down (.circ aP)))) uR
def cimpNest2 : Neg := .imp (.down (.circ (.down (.circ (.down (.circ aP)))))) uR
def cimpOr : Neg := .imp (.down (.circ (.or aP aQ))) uR
def cimpImp : Neg := .imp (.down (.circ (.down (.imp aQ uR)))) uR
def cimpImpP : Neg := .imp (.down (.circ (.down (.imp aP uR)))) uR
def cimpFls : Neg := .imp (.down (.circ .fls)) uR

/-! ## Banks, cheap strata first -/

def kBank : List (List Neg) :=
  [[], [uQ], [boxQ], [hypQ], [dq], [.circ (.down (.imp aQ uR))]]

/-- sum3 ≤ ~2,500: the engine-cheap regime. -/
def smallBank : List (List Neg) :=
  [ [hypQ], [hyp], [joinP],                       -- controls
    [cimpFls], [cimpFls, boxQ],                   -- boundary Q′=⊥
    [hyp, boxQ], [hyp, boxP], [hyp, boxOr], [hyp, boxBoxP],
    [hyp, qimpP], [hyp, uQ],
    [hyp, hypQ], [hyp, joinQ], [joinP, hyp], [hypQP, hyp],  -- crossed χ
    [hypQP, boxP],
    [hyp, uQ, boxQ], [hyp, hypQ, boxP], [hyp, dq, boxQ],    -- size 3
    [cimpNest, boxP], [cimpNest],                 -- GZ depth 2
    [cimpOr, boxP], [cimpOr] ]                    -- or-family

/-- sum3 2,500–25,000: mid-scale, engines slower. -/
def midBank : List (List Neg) :=
  [ [cimpImp, boxQ], [cimpImp], [cimpImpP, boxP],  -- the no-row corner
    [cimpNest2, boxP], [cimpNest2],                -- GZ depth 3
    [hyp, chi] ]                                   -- unboxed blocker

/-- Past the screening horizon (reported, not run). -/
def horizonBank : List (List Neg) :=
  [ [hyp, bchi], [bchi, hyp], [joinP, bchi], [hyp, bchi, boxQ] ]

def runChunk (stations : List (List Neg)) :
    List (List Neg × List Neg × String × Pos × List Neg) := Id.run do
  let mut out := []
  for done in stations do
    for K in kBank do
      for (tag, Q', rest) in sweepStation done K do
        out := (done, K, tag, Q', rest) :: out
  return out


/-! ## E2/A2 minimality on the extended stations (the frontier may force
change #4 in the aggregates rather than the antecedent obligation). -/

def gateMin (done : List Neg) (goalV : Neg) : Bool :=
  sum3 done ≤ wCap && szN (interp pv [] done none) + szN goalV ≤ szCap

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
    List (String × List Neg × List Neg) := Id.run do
  let mut out := []
  for done in stations do
    if legal done && sum3 done ≤ 2500 then
      for Δ in [([] : List Neg), [uQ], [boxQ], [hypQ]] do
        for ψ in psiBank do
          if e2cell done Δ ψ != .pass then out := ("E2", done, Δ) :: out
        for P in pBank do
          if gateMin done (interp pv [] done (some (.up P))) then
            if a2cellT done Δ P != .pass then out := ("A2T", done, Δ) :: out
          if gateMin done (interp pv [] done (some (.circ P))) then
            if a2cellL done Δ P != .pass then out := ("A2L", done, Δ) :: out
  return out


end LJFOAttack
