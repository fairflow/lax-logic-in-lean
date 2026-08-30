/-
# Item 2: does the seam-1 prime-goal gap explain the 6-cell residue?

    lake env lean --run wip/gbu_residue_probe.lean

Syntactic diagnostics over all 462 ρ-cells `G = ρᵢ ⊃ ρⱼ`, to be
cross-tabulated against the FRJX sweep's verdicts
(`wip/frjx_sweep_out.txt`).  Nothing here is a claim: it is a
classifier, and the point is whether ANY of these columns separates the
six missed cells from the 297 found ones.

Seam 1 (`docs/gbu-circ-seams.md`) is the configuration

    Ω ⇒g F      F prime,   ◯Y ∈ Ω,   Ω ⊆ Ĝ

where no `Gbu◯` rule can apply.  A `◯` reaches the left zone only by
`R⊃ₙᵢ` (the left rules only decompose), so the configuration is
reachable iff `Sf^R(G)` contains an implication `◯Y ⊃ B`; and ONE such
step lands in it exactly when that `B` is prime.  Hence the columns
`circAnte` and `s1prime`.
-/
import FRJ.Bridge
import LaxLogic.RN.Rho

namespace FRJ.GbuResidue

open FRJ Form RhoOrder

def goal (i j : Nat) : Form := ofPLL (PLLFormula.ifThen (rhoF i) (rhoF j))

/-- Positive implications with a `◯` antecedent: `R⊃ₙᵢ` on one of these
is the only way a `◯` enters the left zone. -/
def circAnteR (G : Form) : List Form :=
  (sfR G).filter (fun X => match X with | .imp (.circ _) _ => true | _ => false)

/-- ... and with a PRIME consequent: one step lands in seam 1. -/
def circAntePrimeR (G : Form) : List Form :=
  (sfR G).filter (fun X => match X with | .imp (.circ _) B => B.isPrime | _ => false)

/-- Disjunctive goals: the other critical case (Lemma 12). -/
def orR (G : Form) : List Form :=
  (sfR G).filter (fun X => match X with | .or _ _ => true | _ => false)

/-- Positive implications whose antecedent is itself an implication —
the `Υ`-enrichment shape the hand work needed. -/
def impAnteR (G : Form) : List Form :=
  (sfR G).filter (fun X => match X with | .imp (.imp _ _) _ => true | _ => false)

def row (i j : Nat) : String :=
  let G := goal i j
  s!"rho {i} {j}\tcirc={(gCirc G).length}\timp={(gImp G).length}" ++
  s!"\tsfR={(sfR G).length}\tcircAnte={(circAnteR G).length}" ++
  s!"\ts1prime={(circAntePrimeR G).length}\tor={(orR G).length}" ++
  s!"\timpAnte={(impAnteR G).length}"

def main : IO Unit := do
  for i in [0:22] do
    for j in [0:22] do
      if i ≠ j then IO.println (row i j)

end FRJ.GbuResidue

def main : IO Unit := FRJ.GbuResidue.main
