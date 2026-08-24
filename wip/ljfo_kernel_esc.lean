/- Kernel-level escalation of the two surviving cells (Matthew's
direction, 2026-08-11): drive LJFOSearch's fueled backward search on
the LJF◯ sequents themselves.  `search_sound` means a `true` here is a
kernel derivation; fuel is streamed upward (search_mono), so the
frontier of feasibility is visible even if a level hangs.
Cell A: the [◯p→r, ◯(↓◯p)] CimpAnt conclusion.
Cell B: φ★'s minimality direction  E(φ★-station) ⊢ ¬¬◯⊥.  -/
import LJF.OSearch
import wip.ljfo_attack
import wip.ljfo_crosscheck

open LJFO LJFOAttack

def doneA : List Neg := [hyp, boxBoxP]
def restA : List Neg := [boxBoxP]
def eA : Neg := interp pv [] doneA none
def aA : Neg := interp pv [] restA (some (.up (.down (.circ aP))))
def seqA : LSeq := .inv [eA] [] .tru aA

/- ¬¬◯⊥ as a negative. -/
def nnN : Neg := .imp (.down (.imp (.down (.circ .fls)) (.up .fls))) (.up .fls)
def seqB : LSeq := .inv [X.E] [] .tru nnN

/- Sanity cell: the hypothesis side of A, which the PLL engines certify
derivable — the kernel search should find it at small fuel. -/
def sanity : LSeq := .stab doneA .tru (.down (.circ aP))

/- Cell A over the EMPTY context: if ⊢ A holds, E ⊢ A follows by
weakening at the same height, and this search space is far smaller. -/
def seqA0 : LSeq := .inv [] [] .tru aA

def main (args : List String) : IO Unit := do
  let fuels := match args.filterMap String.toNat? with
    | [] => [2, 4, 6, 8, 10, 12, 14, 16, 18, 20]
    | fs => fs
  for n in fuels do
    IO.println s!"fuel {n}: A0={LSeq.search n seqA0}"
    (← IO.getStdout).flush
    IO.println s!"fuel {n}: A={LSeq.search n seqA}"
    (← IO.getStdout).flush
  IO.println "KERNEL-ESC-DONE"
