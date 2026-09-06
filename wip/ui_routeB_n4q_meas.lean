/-
Route (B), node **N4**, WP9, **stage 0**: the candidate measure for
`QBound` (`wip/ui_routeB_n4q_thm.lean`), written as a COMPUTABLE function,
and checked on the designed cells before any proof is scoped.

`docs/n4-loopcheck.md` §4 forces the shape

    μ s  =  (K s − |seen|, ν s)   lexicographic,
    ν (todo, done, goal, _) = 2·sum3 todo + sum3 done + goalW goal,

with `K s` a bound on the compound antecedents ever recordable at `s`.  A
lexicographic pair over `Nat ×ₗ Nat` is not a `Nat`, and `QBound` asks for a
`Nat`.  It CAN be flattened, because the second component is bounded ALONG
THE RECURSION by a quantity that is itself non-increasing:

    μ s  =  κ s · W s + ν s,
    κ s  =  the number of DISTINCT antecedents of the closure not in `seen`,
    W s  =  3 ^ (mxW (clSt s) + 1),

where `clSt s` is the subformula closure of `todo ++ done ++ goal`, closed
under the Dyckhoff residual, and `mxW` its maximum weight.  The arithmetic
that makes the flattening work is `qMu_lt_of_guard` /
`qMu_lt_of_step` (`wip/ui_routeB_n4q_bound.lean` Part 4):

* a NON-GUARD edge has `κ ≤`, `W ≤`, `ν <`, so `κ·W + ν` drops;
* a GUARD edge has `κ` down by at least one and `ν' < W`, so
  `κ'·W' + ν' ≤ (κ−1)·W + ν' < κ·W ≤ κ·W + ν`.

This module builds the three components, MIRRORS the states `stepQ`
consults as `edgesQ`, kernel-checks that the mirror is adequate (a level
masked to `edgesQ s` gives the same step at `s`), and then kernel-checks
the strict descent along every edge of the reachable set of the designed
cells (i)–(vi) and (m1), (m6), (m10).  Two gates are watched failing in
`wip/ui_routeB_n4q_gate.lean`.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_n4q_thm
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The closure

`subN M` is the list of negatives that can ever occupy a `todo`, `done` or
`goal` slot of a state reached from a state carrying `M`.  It is the
subformula closure in the polarised sense — `↑P` AND `◯P` for every positive
subformula `P`, since the lax prefix moves a `◯` goal to `◯` of a
subformula — closed in addition under the **Dyckhoff residual**
`↓(Q′ ⊃ N′) ⊃ N ↦ ↓N′ ⊃ N`, which is the one row of `interpQ` that
manufactures an implication not already present (`eRowsQ`, the `res`
argument of `parkRowE`).  That closure is finite because the residual
strictly shrinks its own antecedent. -/

mutual
/-- The closure of a positive: `↑P`, `◯P`, and the closure of its parts. -/
def subP : Pos → List Neg
  | .atom a => [.up (.atom a), .circ (.atom a)]
  | .fls => [.up .fls, .circ .fls]
  | .or P₁ P₂ => .up (.or P₁ P₂) :: .circ (.or P₁ P₂) :: (subP P₁ ++ subP P₂)
  | .down M => .up (.down M) :: .circ (.down M) :: subN M
termination_by P => sizePos P
decreasing_by
  all_goals (simp only [sizePos]; omega)

/-- The closure of a negative. -/
def subN : Neg → List Neg
  | .up P => .up P :: subP P
  | .circ P => .circ P :: subP P
  | .and M₁ M₂ => .and M₁ M₂ :: (subN M₁ ++ subN M₂)
  | .imp Q N => .imp Q N :: (subP Q ++ subN N ++ subD Q N)
termination_by M => sizeNeg M
decreasing_by
  all_goals (simp only [sizeNeg]; omega)

/-- The Dyckhoff residual of `Q ⊃ N`, closed: the one row of `interpQ` that
manufactures an implication (`parkRowE`'s `res`) is absorbed here. -/
def subD : Pos → Neg → List Neg
  | .down (.imp Q' N'), N => subN (.imp (.down N') N)
  | _, _ => []
termination_by Q N => sizePos Q + sizeNeg N
decreasing_by
  all_goals
    (try simp only [sizePos, sizeNeg])
    first
      | omega
      | (have := sizePos_pos Q'; omega)
end

/-- The closure of a station slot. -/
def subL (l : List Neg) : List Neg := l.flatMap subN

/-- The closure of a goal slot. -/
def subG : Option Neg → List Neg
  | none => []
  | some G => subN G

/-- **The closure of a state**: every negative reachable in any slot. -/
def clSt (s : QState) : List Neg := subL s.1 ++ subL s.2.1 ++ subG s.2.2.1

/-! # Part 2 · The three components -/

/-- The largest weight in a list of negatives. -/
def mxW : List Neg → Nat
  | [] => 0
  | M :: l => max (wNeg M) (mxW l)

/-- **The bound component** `W`: a power of three strictly above every
weight of the closure, hence strictly above `3 ^ wPos Q′` for every
antecedent `Q′` the guard rows can take. -/
def bigW (s : QState) : Nat := 3 ^ (mxW (clSt s) + 1)

/-- The antecedents occurring in a list of negatives. -/
def caOf : List Neg → List Pos
  | [] => []
  | .imp Q _ :: l => Q :: caOf l
  | _ :: l => caOf l

/-- Duplicate removal on positives, by hand (`seenMem`, no `DecidableEq`
instance search, no `Classical`). -/
def ddup : List Pos → List Pos
  | [] => []
  | Q :: l => let r := ddup l; if seenMem r Q then r else Q :: r

/-- The candidate antecedents of a state not yet recorded in `seen`. -/
def caFree (s : QState) : List Pos :=
  (caOf (clSt s)).filter (fun Q => !seenMem s.2.2.2 Q)

/-- **The guard-deficiency component** `κ`: how many DISTINCT antecedents of
the closure have not yet had their own goal attacked. -/
def kap (s : QState) : Nat := (ddup (caFree s)).length

/-- **The weight component** `ν`: the measure `eMinPP`/`aMinPP` run on. -/
def nu (s : QState) : Nat := 2 * sum3 s.1 + sum3 s.2.1 + goalW s.2.2.1

/-- **The candidate measure.** -/
def qMu (s : QState) : Nat := kap s * bigW s + nu s

/-! # Part 3 · The consulted states, mirrored

`edgesQ s` lists the states `stepQ id p prev s` reads `prev` at.  It is NOT
used in the descent proof — that proof unfolds `stepQ` itself — but it makes
stage 0 possible: the descent can be decided on a designed cell only against
an explicit edge list, and the list's adequacy is itself kernel-checked
(`edges_adequate_*` below). -/

/-- The `∃p` rows of one parked compound implication. -/
def parkEdgesE (done : List Neg) (Qa : Pos) (N : Neg) (rest res : List Neg)
    (seen : List Pos) : List QState :=
  (if seenMem seen Qa then []
   else [([], done, some (.up Qa), Qa :: seen), ([N], rest, none, seen)])
  ++ [(res, rest, none, seen)]

/-- The `∀p` rows of one parked compound implication. -/
def parkEdgesA (done : List Neg) (Qa : Pos) (N : Neg) (rest : List Neg)
    (goal : Neg) (seen : List Pos) : List QState :=
  if seenMem seen Qa then []
  else [([], done, some (.up Qa), Qa :: seen), ([N], rest, some goal, seen)]

/-- One row of `eRowsQ`, as states. -/
def eRowBody (done : List Neg) (seen : List Pos) : Neg → List Neg → List QState
  | .imp (.atom _) N, rest => [([N], rest, none, seen)]
  | .imp (.down (.imp Q' N')) N, rest =>
      parkEdgesE done (.down (.imp Q' N')) N rest [.imp (.down N') N] seen
  | .circ Q, rest => [([.up Q], rest, none, seen)]
  | .imp (.down (.circ Q')) N, rest => parkEdgesE done (.down (.circ Q')) N rest [] seen
  | .imp (.or Qa Qb) N, rest => parkEdgesE done (.or Qa Qb) N rest [] seen
  | .imp (.down (.up Pa)) N, rest => parkEdgesE done (.down (.up Pa)) N rest [] seen
  | .imp (.down (.and Ma Mb)) N, rest => parkEdgesE done (.down (.and Ma Mb)) N rest [] seen
  | _, _ => []

/-- `eRowsQ`, as states. -/
def eRowEdges (done : List Neg) (seen : List Pos) : List QState :=
  (splits done).flatMap (fun Xr => eRowBody done seen Xr.1 Xr.2)

/-- One row of `aRowsQ`, as states. -/
def aRowBody (done : List Neg) (goal : Neg) (box : Bool) (seen : List Pos) :
    Neg → List Neg → List QState
  | .imp (.atom _) N, rest => [([N], rest, some goal, seen)]
  | .imp (.down (.imp Q' N')) N, rest =>
      parkEdgesA done (.down (.imp Q' N')) N rest goal seen
  | .imp (.down (.circ Q')) N, rest => parkEdgesA done (.down (.circ Q')) N rest goal seen
  | .imp (.or Qa Qb) N, rest => parkEdgesA done (.or Qa Qb) N rest goal seen
  | .imp (.down (.up Pa)) N, rest => parkEdgesA done (.down (.up Pa)) N rest goal seen
  | .imp (.down (.and Ma Mb)) N, rest => parkEdgesA done (.down (.and Ma Mb)) N rest goal seen
  | .circ R, rest =>
      if box then [([.up R], rest, none, seen), ([.up R], rest, some goal, seen)] else []
  | _, _ => []

/-- `aRowsQ`, as states. -/
def aRowEdges (done : List Neg) (goal : Neg) (box : Bool) (seen : List Pos) :
    List QState :=
  (splits done).flatMap (fun Xr => aRowBody done goal box seen Xr.1 Xr.2)

/-- `laxPrefixQ`, as states. -/
def laxEdges (done : List Neg) (seen : List Pos) : Pos → List QState
  | .atom q => [([], done, some (.up (.atom q)), seen)]
  | .fls => [([], done, some (.up .fls), seen)]
  | .or P₁ P₂ => [([], done, some (.circ P₁), seen),
                  ([], done, some (.circ P₂), seen),
                  ([], done, some (.up (.or P₁ P₂)), seen)]
  | .down (.up P') => [([], done, some (.circ P'), seen)]
  | .down (.circ P') => [([], done, some (.circ P'), seen)]
  | .down (.and M₁ M₂) => [([], done, some (.up (.down (.and M₁ M₂))), seen)]
  | .down (.imp Q₀ N₀) => [([], done, some (.up (.down (.imp Q₀ N₀))), seen)]

/-- `aggQ`, as states. -/
def aggEdges (done : List Neg) (g : Option Neg) (seen : List Pos) : List QState :=
  match g with
  | none => eRowEdges done seen
  | some (.imp Q N) =>
      (invertPos Q).flatMap (fun b => [(b, done, none, seen), (b, done, some N, seen)])
  | some (.and M N) => [([], done, some M, seen), ([], done, some N, seen)]
  | some (.up (.atom q)) =>
      if atomMem q done then [] else aRowEdges done (.up (.atom q)) false seen
  | some (.up .fls) => aRowEdges done (.up .fls) false seen
  | some (.up (.or P₁ P₂)) =>
      [([], done, some (.up P₁), seen), ([], done, some (.up P₂), seen)] ++
        aRowEdges done (.up (.or P₁ P₂)) false seen
  | some (.up (.down M)) =>
      [([], done, some M, seen)] ++ aRowEdges done (.up (.down M)) false seen
  | some (.circ Q) => laxEdges done seen Q ++ aRowEdges done (.circ Q) true seen

/-- **The consulted states of one `stepQ` unfolding**, at `rst = id`. -/
def edgesQ : QState → List QState
  | (.up (.atom a) :: todo, done, g, s) => [(todo, .up (.atom a) :: done, g, s)]
  | (.up .fls :: _, _, _, _) => []
  | (.up (.or P Q) :: todo, done, none, s) =>
      (invertPos (.or P Q)).map (fun b => (b ++ todo, done, none, s))
  | (.up (.or P Q) :: todo, done, some G, s) =>
      (invertPos (.or P Q)).flatMap (fun b =>
        [(b ++ todo, done, none, s), (b ++ todo, done, some G, s)])
  | (.up (.down M) :: todo, done, g, s) => [(M :: todo, done, g, s)]
  | (.and M N :: todo, done, g, s) => [(M :: N :: todo, done, g, s)]
  | (.imp .fls _ :: todo, done, g, s) => [(todo, done, g, s)]
  | (.imp (.atom a) N :: todo, done, g, s) => [(todo, .imp (.atom a) N :: done, g, s)]
  | (.imp (.or Q₁ Q₂) N :: todo, done, g, s) =>
      [(todo, .imp (.or Q₁ Q₂) N :: done, g, s)]
  | (.imp (.down (.up P')) N :: todo, done, g, s) =>
      [(todo, .imp (.down (.up P')) N :: done, g, s)]
  | (.imp (.down (.and M₁ M₂)) N :: todo, done, g, s) =>
      [(todo, .imp (.down (.and M₁ M₂)) N :: done, g, s)]
  | (.imp (.down (.imp Q' N')) N :: todo, done, g, s) =>
      [(todo, .imp (.down (.imp Q' N')) N :: done, g, s)]
  | (.circ Q :: todo, done, g, s) => [(todo, .circ Q :: done, g, s)]
  | (.imp (.down (.circ Q')) N :: todo, done, g, s) =>
      [(todo, .imp (.down (.circ Q')) N :: done, g, s)]
  | ([], done, g, seen) =>
      match findFire done (splits done) with
      | some (_, N, rest) => [([N], rest, g, seen)]
      | none => aggEdges done g seen

/-! # Part 4 · Stage 0, on the designed cells

Rule 9: designed cells, no enumeration.  The cells are those of
`wip/ui_routeB_n4q_cells.lean` — ◯-free FIRST (rule 8), then modal. -/

/-- A level masked to a state list: `⊤` off the list. -/
def maskAt (E : List QState) (F : ApproxQ) : ApproxQ :=
  fun todo done g seen => if (todo, done, g, seen) ∈ E then F todo done g seen else nTop

/-- The bounded reachable set of a state, along `edgesQ`. -/
def reachQ : Nat → List QState → List QState
  | 0, front => front
  | n + 1, front => front ++ reachQ n (front.flatMap edgesQ)

/-- **The stage-0 predicate**: `qMu` strictly decreases along every edge out
of every state reachable within `n` steps. -/
def descOK (n : Nat) (s : QState) : Bool :=
  (reachQ n [s]).all (fun t => (edgesQ t).all (fun u => decide (qMu u < qMu t)))

/-- **Adequacy of the mirror**: masking the level below to `edgesQ s`
changes nothing at `s`, so `edgesQ s` covers every state `stepQ` consults
there.  (An edge list too SMALL fails this; the gate module watches it.) -/
def adeqOK (p : String) (f : Nat) (s : QState) : Bool :=
  decide (atSt (stepQ id p (interpQ p f)) s
        = atSt (stepQ id p (maskAt (edgesQ s) (interpQ p f))) s)

/-- The state of a cell in `∀p` mode. -/
def stA (done : List Neg) (G : Neg) : QState := ([], done, some G, [])
/-- The state of a cell in `∃p` mode. -/
def stE (done : List Neg) : QState := ([], done, none, [])

/-! ## The ◯-free cells (rule 8: the fragment first) -/

/-- (i)–(vi): the mirror is adequate at the cell's own state. -/
theorem adeq_circFree :
    adeqOK "p" 3 (stA cell1 goal1) = true ∧
    adeqOK "p" 3 (stE cell1) = true ∧
    adeqOK "p" 3 (stA cell2 goal2ab) = true ∧
    adeqOK "p" 3 (stA cell3 goal3) = true ∧
    adeqOK "p" 3 (stE cell3) = true ∧
    adeqOK "p" 3 (stA cell4 goal4) = true ∧
    adeqOK "p" 3 (stA cell5 goal5) = true ∧
    adeqOK "p" 3 (stA cell6 goal6d) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- (i)–(vi): `qMu` strictly decreases along every edge of the reachable set. -/
theorem desc_circFree :
    descOK 3 (stA cell1 goal1) = true ∧
    descOK 3 (stE cell1) = true ∧
    descOK 3 (stA cell2 goal2ab) = true ∧
    descOK 3 (stA cell2 goal2cd) = true ∧
    descOK 3 (stA cell3 goal3) = true ∧
    descOK 3 (stE cell3) = true ∧
    descOK 3 (stA cell4 goal4) = true ∧
    descOK 3 (stA cell5 goal5) = true ∧
    descOK 3 (stA cell6 goal6d) = true ∧
    descOK 3 (stA cell6 goal6ab) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## The modal cells -/

/-- (m1), (m6), (m10): the mirror is adequate. -/
theorem adeq_modal :
    adeqOK "p" 3 (stA m1 (.circ (.atom "b"))) = true ∧
    adeqOK "p" 3 (stA m6 (.up (.atom "c"))) = true ∧
    adeqOK "p" 3 (stE m6) = true ∧
    adeqOK "p" 3 (stA m10 (.circ (.atom "g"))) = true ∧
    adeqOK "p" 3 (stE m10) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- (m1), (m6), (m10): `qMu` strictly decreases along every edge. -/
theorem desc_modal :
    descOK 2 (stA m1 (.circ (.atom "b"))) = true ∧
    descOK 2 (stA m6 (.up (.atom "c"))) = true ∧
    descOK 2 (stE m6) = true ∧
    descOK 2 (stA m10 (.circ (.atom "g"))) = true ∧
    descOK 2 (stE m10) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end LJFO

/-! ## Pins -/

#axioms_within LJFO.adeq_circFree [propext]
#axioms_within LJFO.desc_circFree [propext, Quot.sound]
#axioms_within LJFO.adeq_modal [propext]
#axioms_within LJFO.desc_modal [propext, Quot.sound]
