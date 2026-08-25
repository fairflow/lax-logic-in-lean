/- The stabilisation probe (Matthew's core-of-the-obstacle question,
2026-08-11): compute the fuel chains of the retention interpolant
interpF and test consecutive levels — syntactic equality first, kernel
interderivability (LJFOSearch, both directions) where they differ.
Stabilisation at finite fuel is the statement W that all three route
blockers factor through; a station with certified strict growth is the
Ghilardi–Zawadowski candidate. -/
import LJF.OSearch
import LJF.OFuel
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

def provB (budget : Nat) (Γ : List Neg) (C : PLLFormula) : String :=
  match PLLND.Search.prove?Bounded budget (Γ.map negF) C with
  | some _ => "yes"
  | none =>
    match PLLND.Search.refute? {} (Γ.map negF) C with
    | some _ => "NO-certified"
    | none => "unk"

def main : IO Unit := do
  -- The push: [◯p→r, ◯q] showed A_2 ⟛ A_3 then a certified strict step
  -- at 3→4.  Chase the chain at raised budget (200k).
  for f in [4, 5, 6, 7] do
    let (_, a1) := chainRow [hyp, boxQ] aP f
    let (_, a2) := chainRow [hyp, boxQ] aP (f+1)
    IO.println s!"== [◯p→r, ◯q] A_{f} (|{szN a1}|) vs A_{f+1} (|{szN a2}|): fwd={provB 200000 [a1] (negF a2)} bwd={provB 200000 [a2] (negF a1)}"
    (← IO.getStdout).flush
  -- Soundness guard: each A_f must itself be sufficient
  -- (A_f, S ⊢ ◯p), or the ascent happens outside the relevant set.
  for f in [2, 4, 6] do
    let (_, a) := chainRow [hyp, boxQ] aP f
    IO.println s!"== sound A_{f}: {provB 200000 (a :: [hyp, boxQ]) (.somehow (posF aP))}"
    (← IO.getStdout).flush
  IO.println "PUSH-DONE"
