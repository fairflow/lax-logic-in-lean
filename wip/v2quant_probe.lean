import LaxLogic.PLLG4Dec
import LaxLogic.PLLSemUILayered
import LaxLogic.PLLSearch

/-!
# Cross-route probe: rank-bounded ∀p/∃p in the old one-variable harness

Matthew's experiment (2026-07-20): the syntactic route's sole open
lemma was H2 = `itpE_stab` (wip/onevar_descent_dev.lean) — the
∃-interpolant's budget-stabilisation, stuck at the ◯-goal truncation
disjunct where the budget sits in negative position, with the X9
recursion `E_{b+1} = ¬◯(E_b ⊃ A_b)` climbing one ◯/¬-alternation per
step.  The semantic route's wall (route doc §0(hh)) is the sharp
one-rank descent at dead-end i-successors: rank-n facts about
successors (¬◯⊥) are rank-(n+1) facts at the base (¬¬◯⊥).  Both live
on the ◯⊃-alternation tower of RN(◯,{}).

This probe plugs the NEW candidates — the Litak–Visser-style
rank-bounded fragment join and meet at one variable,

    ∀p.φ at rank r  :=  ⋁ { D variable-free, crank D ≤ r | D ⊢ φ }
    ∃p.φ at rank r  :=  ⋀ { D variable-free, crank D ≤ r | φ ⊢ D }

— into the old oracle harness and asks the old question of them:
do they STABILISE in r at the formula's own budget (2ν+1), and do the
stabilised values match the old route's frozen dictionary (X9:
A-side ◯(¬◯⊥ ⊃ ◯¬¬◯⊥), E-side ¬◯⊥)?

Method: generate equivalence-class representatives of RN(◯,{}) with
min-seen crank (canonise-as-you-go, oracle dedupe as in
wip/slick_probe.lean), then per battery formula print the r-table of
nf'd joins/meets with the classes newly entering at each rank (the
tower walk), plus oracle match tests.  Caveats: the oracle is
sound-on-true only; min-seen crank over-estimates true class crank,
so a class can enter the join late; the dictionary is truncated.

Run: `lake build v2quant && .lake/build/bin/v2quant`.
-/

open PLLFormula

namespace PLLND
namespace V2Quant

open SemUI

/-! ## Oracle and sound simplifier (as in wip/onevar_probe.lean) -/

def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C
def entails (X Y : PLLFormula) : Bool := provF 4000 [X] Y
def equivO (X Y : PLLFormula) : Bool := entails X Y && entails Y X

/-! ## Two-sided escalation (PLLSearch's countermodel-first oracle)

`search`'s `true` is sound at any fuel, so only FALSE verdicts need
escalation: `dec2` answers with a proof certificate, a countermodel
certificate, or an honest unknown. -/

def cfg2 : Search.Config := { findBudget := some 40000 }

inductive V2 | proved | refuted | unknown
deriving Repr, DecidableEq

def dec2 (Γ : List PLLFormula) (C : PLLFormula) : V2 :=
  match Search.decide cfg2 Γ C with
  | .proved _ => .proved
  | .refuted _ _ _ => .refuted
  | .unknown => .unknown

/-- Two-sided entailment verdict as a string tag. -/
def tag2 (X Y : PLLFormula) : String :=
  match dec2 [X] Y with
  | .proved => "proved"
  | .refuted => "REFUTED(countermodel)"
  | .unknown => "unknown"

/-- Two-sided PRIMARY entailment test: `true` only on a proof
certificate.  The countermodel sweep short-circuits the failing cases
that eat hand-fuel, so this is also the FAST path. -/
def entT (X Y : PLLFormula) : Bool :=
  match dec2 [X] Y with
  | .proved => true
  | _ => false

def isTop (X : PLLFormula) : Bool := decide (X = truePLL)
def isBot (X : PLLFormula) : Bool := decide (X = falsePLL)

def simp : PLLFormula → PLLFormula
  | .and a b =>
      let a := simp a; let b := simp b
      if isBot a || isBot b then falsePLL
      else if isTop a then b else if isTop b then a
      else if a = b then a else .and a b
  | .or a b =>
      let a := simp a; let b := simp b
      if isTop a || isTop b then truePLL
      else if isBot a then b else if isBot b then a
      else if a = b then a else .or a b
  | .ifThen a b =>
      let a := simp a; let b := simp b
      if a = b then truePLL
      else if isTop a then b
      else if isTop b then truePLL
      else if isBot a then truePLL
      else .ifThen a b
  | .somehow a =>
      let a := simp a
      if isTop a then truePLL
      else match a with
        | .somehow c => .somehow c
        | _ => .somehow a
  | X => X

def norm : Nat → PLLFormula → PLLFormula
  | 0, X => X
  | n + 1, X => let Y := simp X; if Y = X then X else norm n Y
def nf (X : PLLFormula) : PLLFormula := norm 12 X

def sz : PLLFormula → Nat
  | .and a b => sz a + sz b + 1
  | .or a b => sz a + sz b + 1
  | .ifThen a b => sz a + sz b + 1
  | .somehow a => sz a + 1
  | _ => 1

/-! ## The RN(◯,{}) class dictionary, crank-stratified -/

def RMAX : Nat := 9
def SZMAX : Nat := 16
def DICTMAX : Nat := 40
def ROUNDS : Nat := 6

/-- Dedupe fuel — smaller than the verdict fuel: failing searches pay
full fuel, and the dedupe path is almost always failing. -/
def entailsD (X Y : PLLFormula) : Bool := provF 600 [X] Y
def equivD (X Y : PLLFormula) : Bool := entailsD X Y && entailsD Y X

/-- One generation round: close the dictionary under ◯, ⊃, ∧, ∨,
nf-simplify, cap by crank and size, dedupe first syntactically then by
oracle equivalence (keeping the MINIMUM seen crank per class). -/
def round (dict : List (PLLFormula × Nat)) : List (PLLFormula × Nat) := Id.run do
  let mut d := dict
  let mut cands : List (PLLFormula × Nat) := []
  for (D, c) in dict do
    cands := cands ++ [(nf D.somehow, c + 2)]
    for (D', c') in dict do
      cands := cands ++ [(nf (D.ifThen D'), max c c' + 1),
                         (nf (D.and D'), max c c'),
                         (nf (D.or D'), max c c')]
  for (X, c) in cands do
    if c ≤ RMAX && sz X ≤ SZMAX && d.length < DICTMAX then
      -- the nf'd form may have smaller crank than the bookkept bound
      let c := min c (crank X)
      match d.find? (fun (D, _) => D == X) with
      | some _ =>
          d := d.map fun (D, c₀) => if D == X then (D, min c₀ c) else (D, c₀)
      | none =>
          match d.find? (fun (D, _) => equivD D X) with
          | some (D₀, c₀) =>
              if c < c₀ then
                d := d.map fun (D, cc) => if D == D₀ then (D, c) else (D, cc)
          | none => d := d ++ [(X, c)]
  return d

def dict0 : List (PLLFormula × Nat) := [(falsePLL, 0), (truePLL, 0)]

def flush : IO Unit := do (← IO.getStdout).flush

/-- Build the dictionary with per-round progress (IO for flushing —
compiled stdout to a file is block-buffered). -/
def mkDictIO : IO (List (PLLFormula × Nat)) := do
  let mut d := dict0
  for i in List.range ROUNDS do
    d := round d
    IO.println s!"  [dict] round {i+1}: {d.length} classes"
    flush
  return d

/-! ## The rank-bounded quantifier candidates -/

def joinOf : List PLLFormula → PLLFormula
  | [] => falsePLL
  | [D] => D
  | D :: l => D.or (joinOf l)

def meetOf : List PLLFormula → PLLFormula
  | [] => truePLL
  | [D] => D
  | D :: l => D.and (meetOf l)

def allQ (dict : List (PLLFormula × Nat)) (r : Nat) (φ : PLLFormula) :
    PLLFormula :=
  nf (joinOf ((dict.filter fun (D, c) => c ≤ r && entT D φ).map (·.1)))

def exQ (dict : List (PLLFormula × Nat)) (r : Nat) (φ : PLLFormula) :
    PLLFormula :=
  nf (meetOf ((dict.filter fun (D, c) => c ≤ r && entT φ D).map (·.1)))

/-! ## Budget count ν (generator subformulas, their n_X) -/

def subs : PLLFormula → List PLLFormula
  | .and a b => .and a b :: (subs a ++ subs b)
  | .or a b => .or a b :: (subs a ++ subs b)
  | .ifThen a b => .ifThen a b :: (subs a ++ subs b)
  | .somehow a => .somehow a :: subs a
  | X => [X]

def nu (φ : PLLFormula) : Nat :=
  ((subs φ).eraseDups.filter (fun ψ => isBudget ψ)).length

/-! ## Battery -/

def op : PLLFormula := .prop "p"
def bb : PLLFormula := falsePLL.somehow                  -- ◯⊥
def nbb : PLLFormula := bb.ifThen falsePLL               -- ¬◯⊥
def nnbb : PLLFormula := nbb.ifThen falsePLL             -- ¬¬◯⊥
/-- The old route's frozen X9 A-value: ◯(¬◯⊥ ⊃ ◯¬¬◯⊥). -/
def a9 : PLLFormula := (nbb.ifThen nnbb.somehow).somehow

def battery : List (String × PLLFormula) :=
  [("◯p", op.somehow),
   ("¬p", op.ifThen falsePLL),
   ("p∨¬p", op.or (op.ifThen falsePLL)),
   ("◯(◯p⊃p) [GAP ROW]", (op.somehow.ifThen op).somehow),
   ("◯p⊃p", op.somehow.ifThen op),
   ("¬◯⊥⊃◯p [X9]", nbb.ifThen op.somehow),
   ("(◯p⊃p)⊃p", (op.somehow.ifThen op).ifThen op),
   ("◯◯p⊃p", op.somehow.somehow.ifThen op),
   ("◯¬p", (op.ifThen falsePLL).somehow),
   ("¬◯p", op.somehow.ifThen falsePLL)]

def pf (F : PLLFormula) : String := toString F

def mainLoop : IO Unit := do
  IO.println "=== cross-route probe: rank-bounded ∀p/∃p on the old harness ==="
  flush
  let dict ← mkDictIO
  IO.println s!"dictionary: {dict.length} classes (crank ≤ {RMAX}, {ROUNDS} rounds)"
  for (D, c) in dict do
    IO.println s!"  class crank≤{c}: {pf D}"
  flush
  for (name, φ) in battery do
    let v := nu φ
    IO.println s!"--- {name}   (ν = {v}, 2ν+1 = {2*v+1}) ---"
    let mut prevA : Option PLLFormula := none
    let mut prevE : Option PLLFormula := none
    for r in List.range (RMAX + 1) do
      let A := allQ dict r φ
      let E := exQ dict r φ
      -- one-sided `true` is sound; escalate FALSE to the two-sided oracle
      let sameA := match prevA with
        | some P =>
            if entT P A && entT A P then " (=)"
            else s!" (CLIMB: new⊢old {tag2 A P}, old⊢new {tag2 P A})"
        | none => ""
      let sameE := match prevE with
        | some P =>
            if entT P E && entT E P then " (=)"
            else s!" (CLIMB: new⊢old {tag2 E P}, old⊢new {tag2 P E})"
        | none => ""
      let enter := (dict.filter fun (D, c) =>
        c == r && entT D φ).map (fun (D, _) => pf D)
      IO.println s!"  r={r}: ∀={pf A}{sameA}  ∃={pf E}{sameE}  enters:{enter}"
      flush
      prevA := some A
      prevE := some E
  -- match tests against the old frozen values and the known laws
  let x9 := nbb.ifThen op.somehow
  let aX9 := allQ dict RMAX x9
  IO.println "=== match tests (two-sided verdicts) ==="
  IO.println s!"∀p(X9) ⊢ old A-value ◯(¬◯⊥⊃◯¬¬◯⊥): {tag2 aX9 a9};  converse: {tag2 a9 aX9}"
  IO.println s!"∀p(X9) ⊢ ¬◯⊥⊃◯⊥: {tag2 aX9 (nbb.ifThen bb)};  converse: {tag2 (nbb.ifThen bb) aX9}"
  let aGap := allQ dict RMAX ((op.somehow.ifThen op).somehow)
  IO.println s!"∀p(GAP ROW) ⊢ ◯⊥: {tag2 aGap bb};  converse: {tag2 bb aGap}"
  let aBox := allQ dict RMAX op.somehow
  IO.println s!"∀p(◯p) ⊢ ◯⊥: {tag2 aBox bb};  converse: {tag2 bb aBox}"
  let aTnd := allQ dict RMAX (op.or (op.ifThen falsePLL))
  IO.println s!"∀p(p∨¬p) ⊢ ⊥: {tag2 aTnd falsePLL}"
  IO.println "=== done ==="

end V2Quant
end PLLND

def main : IO Unit := PLLND.V2Quant.mainLoop
