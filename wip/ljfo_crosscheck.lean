/- Cross-route validation cell: the semantic campaign PROVED
`∃p.φ★ = ¬¬◯⊥` (wip/phistar.lean).  φ★ polarises into a legal parked
station, so interp's E-value must be PLL-EQUIVALENT to ¬¬◯⊥ if the two
routes agree: both directions tested with the certificate engines.
Gated by sum3/size per the screening-horizon discipline. -/
import LJF.OCore
import LaxLogic.PLLG4Dec
import LaxLogic.PLLSearch

open LJFO PLLND

namespace X

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
  | .atom _ => 1 | .fls => 1
  | .or P Q => szP P + szP Q + 1
  | .down M => szN M + 1
def szN : Neg → Nat
  | .up P => szP P + 1
  | .imp Q N => szP Q + szN N + 1
  | .and M N => szN M + szN N + 1
  | .circ P => szP P + 1
end

def pv : String := "p"
def aP : Pos := .atom pv

/- φ★'s two conjuncts as parked negatives. -/
def oBot : Neg := .circ .fls
def impOP : Neg := .imp (.down oBot) (.up aP)          -- ◯⊥ ⊃ p
def conjA : Neg := .imp (.down impOP) (.and oBot (.up aP)) -- (◯⊥⊃p) ⊃ (◯⊥ ∧ p)
def negP : Neg := .imp (.down (.imp aP (.up .fls))) (.up .fls) -- ¬¬p
def station : List Neg := [conjA, negP]

def nnOBot : PLLFormula :=
  .ifThen (.ifThen (.somehow .falsePLL) .falsePLL) .falsePLL


def E : Neg := interp pv [] station none

def nodeBudget : Nat := 40000

def verdict (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match PLLND.Search.prove?Bounded nodeBudget Γ C with
  | some _ => "yes"
  | none =>
    match PLLND.Search.refute? {} Γ C with
    | some _ => "NO (certified)"
    | none => "unk"


end X

namespace X
/- Escalation of the flagged direction at 10x budget (doctrine: flags
are re-run at raised budget, never dropped). -/
def verdictBig (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match PLLND.Search.prove?Bounded 400000 Γ C with
  | some _ => "yes"
  | none =>
    match PLLND.Search.refute? {} Γ C with
    | some _ => "NO (certified)"
    | none => "unk"
end X

namespace X
def sum3probe : Nat := sum3 station
def szEprobe : Nat := szN E
end X
