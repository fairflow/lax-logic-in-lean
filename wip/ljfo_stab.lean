/- The stabilisation probe (Matthew's core-of-the-obstacle question,
2026-08-11): compute the fuel chains of the retention interpolant
interpF and test consecutive levels — syntactic equality first, kernel
interderivability (LJFOSearch, both directions) where they differ.
Stabilisation at finite fuel is the statement W that all three route
blockers factor through; a station with certified strict growth is the
Ghilardi–Zawadowski candidate. -/
import LaxLogic.LJFOSearch
import LaxLogic.LJFOFuel
import wip.ljfo_attack

open LJFO LJFOAttack

def maxF : Nat := 10

/- One station's A-chain at its head cimp's Q′, plus the E-chain. -/
def chainRow (S : List Neg) (Q' : Pos) (f : Nat) : Neg × Neg :=
  (interpF pv f [] S none,
   interpF pv f [] S (some (.up (.down (.circ Q')))))

def eqTag (a b : Neg) : String := if a = b then "=" else "≠"

def kernelBoth (fuel : Nat) (a b : Neg) : String :=
  let fwd := LSeq.search fuel (.inv [a] [] .tru b)
  let bwd := LSeq.search fuel (.inv [b] [] .tru a)
  s!"⊢fwd={fwd} ⊢bwd={bwd}"

def probe (name : String) (S : List Neg) (Q' : Pos) : IO Unit := do
  IO.println s!"== {name}"
  let mut prev : Option (Neg × Neg) := none
  for f in List.range (maxF + 1) do
    let (e, a) := chainRow S Q' f
    match prev with
    | none => IO.println s!"  f={f}: |E|={szN e} |A|={szN a}"
    | some (e0, a0) =>
        IO.println s!"  f={f}: |E|={szN e} |A|={szN a}  E{eqTag e0 e}E' A{eqTag a0 a}A'"
    prev := some (e, a)
    (← IO.getStdout).flush

/- Kernel interderivability for the first syntactically-unstable pairs,
called explicitly per finding (kept separate so the cheap syntactic
pass streams first). -/
def kprobe (name : String) (S : List Neg) (Q' : Pos) (f g sfuel : Nat) :
    IO Unit := do
  let (_, a1) := chainRow S Q' f
  let (_, a2) := chainRow S Q' g
  IO.println s!"== kernel {name} A_{f} vs A_{g}: {kernelBoth sfuel a1 a2}"
  (← IO.getStdout).flush

def main : IO Unit := do
  probe "[◯q→r] Q'=q (p-free control)" [hypQ] aQ
  probe "[◯p→r] Q'=p (the minimal p-cell)" [hyp] aP
  probe "[◯p→◯p] Q'=p (join)" [joinP] aP
  probe "[◯p→r, ◯q] Q'=p (howe shape)" [hyp, boxQ] aP
  probe "[◯⊥→r] Q'=⊥ (boundary)" [cimpFls] .fls
  probe "[◯p→r, ◯p] Q'=p (the flagged family)" [hyp, boxP] aP
  probe "[◯p→r, ◯(↓◯p)] Q'=p (the fuel-48 cell)" [hyp, boxBoxP] aP
  -- kernel + engine interderivability at SMALL f (inside proven search
  -- reach); fwd = A_f ⊢ A_{f+1} (the monotonicity direction), bwd = the
  -- stabilisation direction.
  for (nm, S, Q') in [("[◯q→r]", [hypQ], aQ), ("[◯p→r]", [hyp], aP),
                      ("[◯p→r, ◯q]", [hyp, boxQ], aP)] do
    for f in [1, 2, 3, 4] do
      let (_, a1) := chainRow S Q' f
      let (_, a2) := chainRow S Q' (f+1)
      let eng1 := provN [a1] (negF a2)
      let eng2 := provN [a2] (negF a1)
      IO.println s!"== {nm} A_{f} vs A_{f+1}: eng fwd={repr eng1} bwd={repr eng2}"
      (← IO.getStdout).flush
      IO.println s!"   kernel: {kernelBoth 48 a1 a2}"
      (← IO.getStdout).flush
  IO.println "STAB-DONE"
