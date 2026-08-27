/-
# Round 3 live: the kept chain adopts a `◯`-antecedent implication

    G3 = (◯w ⊃ q) ⊃ ◯w

The self-referential flight shape in its smallest dress: the goal
violates the round-3 guard (`◯w` sits inside a left-implication
antecedent), the single-world countermodel makes `w`'s corner fire with
`◯w ∈ seen` in flight, and the `Λ*`-member `M = ◯w ⊃ q` must be
retained in the very `w`-row that serves `◯w`.

The relaxed calculus does it in FOUR nodes: `Ax^I w` puts `w` into `Υ`;
the `⋈^At`'s kept chain then adopts `M` through

    RefAt (◯w)  =  circ → ups (w ∈ Υ)

— a retention `keptChain_of_ups` (the paper's `Θ^⊃/Υ` restriction) can
NEVER perform, since it would demand an `I(◯w)`-premise, the in-flight
demand itself.  `◯∈` and `⊃∈` close the goal; `M_kept` certifies the
adoption.

(No separation claim: THIS cell is also servable through the
chosen-valuation `Ax^I◯` — `◯w` is not poisoned — so it demonstrates
the round-3 mechanism, not an incompleteness of round 2.  The
discriminating cell would need the poison and the flight together;
that hunt is the next screening step.)
-/
import wip.minmodv_seen
import FRJ.WitnessKit
import FRJ.Fallible

set_option maxRecDepth 4000

namespace FRJ.Round3Demo

open FRJ Form

def wf : Form := .atom "w"
def qf : Form := .atom "q"
def Ow : Form := .circ wf
/-- The in-flight member: `◯w ⊃ q`. -/
def M : Form := .imp Ow qf
def G3 : Form := .imp M Ow

/-- `G3` violates the round-3 guard: its left implication `M` carries a
`◯` in antecedent position — the guarded theorem does not apply, and
this file serves the cell anyway. -/
theorem G3_unguarded : guardB G3 = false := by decide

/-- Consistency control: `G3` is refuted on the one-world infallible
model, so it is no PLL theorem and the refutation calculus SHOULD
derive it. -/
theorem G3_not_valid : ¬ Kripke.point.valid G3 := by
  change ¬ Kripke.point.force Kripke.point.root G3
  decide

/-! ## The four-node witness -/

def Θw : List Form := FRJ.rm (gAt G3) wf ++ gImp G3 ++ gCirc G3

def R1 : FRJVi G3 [] Θw wf :=
  .axI wf (by decide) (by decide) (CtxEq.refl _)

def stab1 : Fin 1 → List Form := fun _ => []
def th1 : Fin 1 → List Form := fun _ => Θw
def rhs1 : Fin 1 → Form := fun _ => wf

def keptw : List Form :=
  keptOf (upsilon rhs1) (joinCtxAtVBase stab1 th1 wf) (thPool th1)

/-- **THE ROUND-3 DEVICE, LIVE**: the greedy kept chain adopted the
in-flight member `M = ◯w ⊃ q` — its antecedent `◯w` is `RefAt`-refuted
through the `circ`-clause over `w ∈ Υ`. -/
theorem M_kept : M ∈ keptw := by decide

/-- The certified contrast: the PAPER second zone (`Θ^⊃/Υ`) does NOT
contain `M` — its antecedent `◯w` is no premise right formula, and
before round 3 no barren join could carry `M` here. -/
theorem M_not_ups_kept : M ∉ restrict (thPool th1) (upsilon rhs1) := by
  decide

def Rw : FRJVr G3 .barren
    (joinCtxAtVBase stab1 th1 wf ++ keptw) wf :=
  .joinAt (fun _ => R1) (by decide) (hJ2R_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

def ROw : FRJVr G3 .barren
    (joinCtxAtVBase stab1 th1 wf ++ keptw) Ow :=
  .circIn Rw (Or.inl rfl) (by decide)

def goal : FRJVr G3 .barren
    (joinCtxAtVBase stab1 th1 wf ++ keptw) G3 :=
  .impIn ROw (.base (by decide)) (by decide)

/-- **The flight-shaped cell, derived** — through the relaxed calculus's
kept chain, with the retention the strict second zone cannot express. -/
theorem provableV_selfref : ProvableV G3 := ⟨.barren, _, ⟨goal⟩⟩

/-- info: 'FRJ.Round3Demo.provableV_selfref' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_selfref

end FRJ.Round3Demo
