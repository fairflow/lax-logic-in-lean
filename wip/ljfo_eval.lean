/-
The LJF◯ evaluator bank (reviewer recommendation §4).

Imports point INWARDS only: the frozen core supplies `interp`, the G4c
decider supplies complete PLL provability.  Nothing here taints the
development; this file is a test harness.

Purpose: test the interpolant DEFINITIONS extensionally, in seconds, on
degenerate cells — before proofs are attempted.  Immediate question (per
docs/ljfo-plan.md): is the E-row antecedent `A(rest ⇒ ◯Q′)` minimality-
adequate, i.e. does

    done, K ⊢ ◯Q′   imply   E(done), K ⊢ A(rest ⇒ ◯Q′)     (CimpAnt-cell)

hold on the bank?  Also re-checks the two known forced changes (#2, #3)
as calibration, and sweeps E2/A2 minimality cells.
-/
import LJF.OCore
import LaxLogic.PLLG4Dec
import LaxLogic.PLLSearch
import LJF.OFuel

open LJFO PLLND

deriving instance Repr for LJFO.Pos
deriving instance Repr for LJFO.Neg

/-! ## Translation `LJF◯ → PLL` (polarity-forgetting) -/

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

/-- Three-valued bounded provability from the certificate engines
(`prove?Bounded` / `refute?`): `.yes` and `.no` are CERTIFIED; `.unk`
means neither settled within budget (never a verdict). -/
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

/-- The interpolation variable throughout. -/
def pv : String := "p"

/-! ## Cells -/

/-- A cell outcome: `pass` (hyp not-yes, or concl yes), `fail` (certified
violation), `flag` (hyp yes, concl unknown at this budget). -/
inductive C3 | pass | fail | flag
deriving Repr, DecidableEq

def cell (hyp : V) (concl : V) : C3 :=
  match hyp, concl with
  | .yes, .no => .fail
  | .yes, .unk => .flag
  | _, _ => .pass


/-- E2-minimality cell: `done, Δ ⊢ ψ` (all of `Δ`, `ψ` p-free) implies
`E(done), Δ ⊢ ψ`.  Returns `true` when the cell PASSES (vacuously or
really). -/
def e2cell (done Δ : List Neg) (ψ : Neg) : C3 :=
  cell (provN (done ++ Δ) (negF ψ))
       (provN (interp pv [] done none :: Δ) (negF ψ))

/-- A2-minimality cell at `tru`: `done, Δ ⊢ P` implies
`E(done), Δ ⊢ A(done ⇒ ↑P)`. -/
def a2cellT (done Δ : List Neg) (P : Pos) : C3 :=
  cell (provN (done ++ Δ) (posF P))
       (provN (interp pv [] done none :: Δ)
         (negF (interp pv [] done (some (.up P)))))

/-- A2-minimality cell at `lax`: `done, Δ ⊢ ◯P` implies
`E(done), Δ ⊢ A(done ⇒ ◯P)`. -/
def a2cellL (done Δ : List Neg) (P : Pos) : C3 :=
  cell (provN (done ++ Δ) (.somehow (posF P)))
       (provN (interp pv [] done none :: Δ)
         (negF (interp pv [] done (some (.circ P)))))

/-- THE CimpAnt cell: with `χ = ↓◯Q′ ⊃ N` at the head of `done`
(so `rest = done.tail`): `done, K ⊢ ◯Q′` implies
`E(done), K ⊢ A(rest ⇒ ◯Q′)`. -/
def cimpCell (Q' : Pos) (N : Neg) (rest K : List Neg) : C3 :=
  let χ : Neg := .imp (.down (.circ Q')) N
  let done := χ :: rest
  cell (provN (done ++ K) (.somehow (posF Q')))
       (provN (interp pv [] done none :: K)
         (negF (interp pv [] rest (some (.circ Q')))))

/-- The (b)-alternative for the same cell: the guard at the FULL station,
in truth mode: `E(done), K ⊢ A(done ⇒ ↑↓◯Q′)`. -/
def cimpCellB (Q' : Pos) (N : Neg) (rest K : List Neg) : C3 :=
  let χ : Neg := .imp (.down (.circ Q')) N
  let done := χ :: rest
  cell (provN (done ++ K) (.somehow (posF Q')))
       (provN (interp pv [] done none :: K)
         (negF (interp pv [] done (some (.up (.down (.circ Q')))))))

/-! ## The bank: degenerate ends of every axis -/

def aP : Pos := .atom pv          -- the eliminated atom
def aQ : Pos := .atom "q"
def aR : Pos := .atom "r"
def uQ : Neg := .up aQ
def uP : Neg := .up aP
def boxQ : Neg := .circ aQ        -- p-free box
def boxP : Neg := .circ aP        -- p-carrying box
def qimpP : Neg := .imp aP uQ     -- p ⊃ q  (parked, guards on p)
def qimpQ : Neg := .imp aQ (.up aR)

/-- Saturation guard: only saturated stations are legal cells. -/
def isSat (done : List Neg) : Bool :=
  match findFire done (splits done) with
  | some _ => false
  | none => true

def negBank : List Neg :=
  [uQ, uP, boxQ, boxP, qimpP, qimpQ,
   .up (.or aQ aR), .up .fls, .up (.down boxQ),
   .imp (.down boxQ) uQ, .imp (.down boxP) uQ]

def posBank : List Pos :=
  [aQ, aP, .fls, .or aQ aR, .down boxQ, .down uQ]

/-- p-free members only, for `Δ`/`K` sides. -/
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

def kBank : List (List Neg) :=
  [[], [uQ], [boxQ], [qimpQ], [.imp (.down boxQ) uQ]]

def stationBank : List (List Neg) :=
  ([[], [qimpP], [boxP], [boxQ], [qimpP, boxQ], [uP], [uP, qimpP]]).filter isSat

/-! ## Sweeps -/

def e2res : List (C3 × List Neg × List Neg × Neg) := Id.run do
  let mut out := []
  for done in stationBank do
    for Δ in kBank do
      for ψ in negBank.filter pfreeN do
        let r := e2cell done Δ ψ
        if r != .pass then out := (r, done, Δ, ψ) :: out
  return out

def a2res : List (C3 × List Neg × List Neg × Pos × Bool) := Id.run do
  let mut out := []
  for done in stationBank do
    for Δ in kBank do
      for P in posBank do
        let rT := a2cellT done Δ P
        let rL := a2cellL done Δ P
        if rT != .pass then out := (rT, done, Δ, P, true) :: out
        if rL != .pass then out := (rL, done, Δ, P, false) :: out
  return out

def cimpRes : List (C3 × Pos × Neg × List Neg × List Neg) := Id.run do
  let mut out := []
  for Q' in [aQ, aP, .or aQ aR, .down boxQ] do
    for N in [uQ, uP, boxQ, .up (.or aQ aR)] do
      for rest in [([] : List Neg), [uQ], [boxQ], [qimpP]] do
        for K in kBank do
          if isSat (Neg.imp (.down (.circ Q')) N :: rest) then
            let r := cimpCell Q' N rest K
            if r != .pass then out := (r, Q', N, rest, K) :: out
  return out

def cimpBRes : List (C3 × Pos × Neg × List Neg × List Neg) := Id.run do
  let mut out := []
  for Q' in [aQ, aP, .or aQ aR, .down boxQ] do
    for N in [uQ, uP, boxQ, .up (.or aQ aR)] do
      for rest in [([] : List Neg), [uQ], [boxQ], [qimpP]] do
        for K in kBank do
          if isSat (Neg.imp (.down (.circ Q')) N :: rest) then
            let r := cimpCellB Q' N rest K
            if r != .pass then out := (r, Q', N, rest, K) :: out
  return out

/-! ## Calibration: forced change #3's cell must PASS with the wrapped
aggregate, and the UNWRAPPED (pre-#3) value must FAIL certified. -/

def calib3_now : C3 := a2cellL [] [boxQ] aQ
def calib3_old : C3 :=
  cell (provN [boxQ] (.somehow (posF aQ)))
       (provN [interp pv [] [] none, boxQ]
         (negF (interp pv [] [] (some (.up aQ)))))

#eval (calib3_now, calib3_old)   -- expect (C3.pass, C3.fail)
#eval e2res
#eval a2res
#eval cimpRes
#eval cimpBRes

/-- Route-(3) cell: the uniformised antecedent `A(rest ⇒ ↑↓◯Q′)`
(tru-mode at the residual station).  Minimality direction. -/
def cimpCellC (Q' : Pos) (N : Neg) (rest K : List Neg) : C3 :=
  let χ : Neg := .imp (.down (.circ Q')) N
  let done := χ :: rest
  cell (provN (done ++ K) (.somehow (posF Q')))
       (provN (interp pv [] done none :: K)
         (negF (interp pv [] rest (some (.up (.down (.circ Q')))))))

/-- Route-(3) soundness spot: the new antecedent value, beside its
station, yields the fire argument: `A(rest ⇒ ↑↓◯Q′), rest ⊢ ◯Q′`. -/
def cimpSoundC (Q' : Pos) (rest : List Neg) : C3 :=
  cell V.yes
       (provN (interp pv [] rest (some (.up (.down (.circ Q')))) :: rest)
         (.somehow (posF Q')))

def cimpCRes : List (C3 × Pos × Neg × List Neg × List Neg) := Id.run do
  let mut out := []
  for Q' in [aQ, aP, .or aQ aR, .down boxQ] do
    for N in [uQ, uP, boxQ, .up (.or aQ aR)] do
      for rest in [([] : List Neg), [uQ], [boxQ], [qimpP]] do
        for K in kBank do
          if isSat (Neg.imp (.down (.circ Q')) N :: rest) then
            let r := cimpCellC Q' N rest K
            if r != .pass then out := (r, Q', N, rest, K) :: out
  return out

def cimpCSound : List (C3 × Pos × List Neg) := Id.run do
  let mut out := []
  for Q' in [aQ, aP, .or aQ aR, .down boxQ] do
    for rest in [([] : List Neg), [uQ], [boxQ], [qimpP]] do
      if isSat rest then
        let r := cimpSoundC Q' rest
        if r != .pass then out := (r, Q', rest) :: out
  return out

#eval cimpCRes
#eval cimpCSound

/-! ## Route (B) layer 4a cells: the fuel-founded retention interpolant -/

-- NOTE (2026-08-11 03:20): fuel 24 makes the retention values large
-- enough to grind the bounded prover on this bank; the stations here are
-- 1-2 members, for which small fuel stabilises.  Start the fresh-session
-- run at 6 and raise only if cells flag.
def fuel0 : Nat := 6

def e2cellF (done Δ : List Neg) (ψ : Neg) : C3 :=
  cell (provN (done ++ Δ) (negF ψ))
       (provN (interpF pv fuel0 [] done none :: Δ) (negF ψ))

def a2cellFT (done Δ : List Neg) (P : Pos) : C3 :=
  cell (provN (done ++ Δ) (posF P))
       (provN (interpF pv fuel0 [] done none :: Δ)
         (negF (interpF pv fuel0 [] done (some (.up P)))))

def a2cellFL (done Δ : List Neg) (P : Pos) : C3 :=
  cell (provN (done ++ Δ) (.somehow (posF P)))
       (provN (interpF pv fuel0 [] done none :: Δ)
         (negF (interpF pv fuel0 [] done (some (.circ P)))))

/-- The retention-miner cell: `done, K ⊢ ◯Q′` implies
`E_F(done), K ⊢ A_F(done ⇒ ↑↓◯Q′)` — the (b)-guard the rows now carry. -/
def cimpCellF (Q' : Pos) (N : Neg) (rest K : List Neg) : C3 :=
  let χ : Neg := .imp (.down (.circ Q')) N
  let done := χ :: rest
  cell (provN (done ++ K) (.somehow (posF Q')))
       (provN (interpF pv fuel0 [] done none :: K)
         (negF (interpF pv fuel0 [] done (some (.up (.down (.circ Q')))))))

/-- Soundness spots for the retention rows. -/
def cimpSoundF (Q' : Pos) (N : Neg) (rest : List Neg) : C3 :=
  let χ : Neg := .imp (.down (.circ Q')) N
  let done := χ :: rest
  cell V.yes
       (provN (interpF pv fuel0 [] done (some (.up (.down (.circ Q')))) :: done)
         (.somehow (posF Q')))

def e2resF : List (C3 × List Neg × List Neg × Neg) := Id.run do
  let mut out := []
  for done in stationBank do
    for Δ in kBank do
      for ψ in negBank.filter pfreeN do
        let r := e2cellF done Δ ψ
        if r != .pass then out := (r, done, Δ, ψ) :: out
  return out

def a2resF : List (C3 × List Neg × List Neg × Pos × Bool) := Id.run do
  let mut out := []
  for done in stationBank do
    for Δ in kBank do
      for P in posBank do
        let rT := a2cellFT done Δ P
        let rL := a2cellFL done Δ P
        if rT != .pass then out := (rT, done, Δ, P, true) :: out
        if rL != .pass then out := (rL, done, Δ, P, false) :: out
  return out

def cimpResF : List (C3 × Pos × Neg × List Neg × List Neg) := Id.run do
  let mut out := []
  for Q' in [aQ, aP, .or aQ aR, .down boxQ] do
    for N in [uQ, uP, boxQ, .up (.or aQ aR)] do
      for rest in [([] : List Neg), [uQ], [boxQ], [qimpP]] do
        for K in kBank do
          if isSat (Neg.imp (.down (.circ Q')) N :: rest) then
            let r := cimpCellF Q' N rest K
            if r != .pass then out := (r, Q', N, rest, K) :: out
  return out

def cimpSoundResF : List (C3 × Pos × Neg × List Neg) := Id.run do
  let mut out := []
  for Q' in [aQ, aP, .or aQ aR] do
    for N in [uQ, uP, boxQ] do
      for rest in [([] : List Neg), [uQ], [boxQ], [qimpP]] do
        if isSat (Neg.imp (.down (.circ Q')) N :: rest) then
          let r := cimpSoundF Q' N rest
          if r != .pass then out := (r, Q', N, rest) :: out
  return out

/-- The ①/② blocker-shaped cell family: the station carries BOTH the
modal implication AND a box whose opening re-uses it — the configuration
that defeated every consumed-χ design. -/
def howeCell (K : List Neg) : C3 :=
  -- χ = ↓◯p ⊃ ↑r ;  box ◯q ;  goal ◯p from the pair, K kept
  let χ : Neg := .imp (.down (.circ aP)) (.up aR)
  let done := [χ, boxQ]
  cell (provN (done ++ K) (.somehow (posF aP)))
       (provN (interpF pv fuel0 [] done none :: K)
         (negF (interpF pv fuel0 [] done (some (.up (.down (.circ aP)))))))

def howeRes : List (C3 × List Neg) := Id.run do
  let mut out := []
  for K in kBank do
    let r := howeCell K
    if r != .pass then out := (r, K) :: out
  return out

#eval e2resF
#eval a2resF
#eval cimpResF
#eval cimpSoundResF
#eval howeRes
