/-
# `Play/SubTab.lean`: the subframe tableau, a move at a time

Matthew's file.  Claude prepared it (2026-11-19) and does not edit it again.
It is in no library, so no `lake build` builds it and nothing imports it;
open it in VS Code and type.  (Build `SubTabExplore` first:
`lake build SubTabExplore`.)

`subtab` is `apply_move` of `proof-tools`, fixed to the subframe tableau
(`LaxLogic/PLL/SubTab/Explore.lean`).  A goal is an attempt
`Explore.Att STab true s`, shown as its sequent:

    Γ ⇒ Δ         a world outside S: the formulas of Γ true, those of Δ false
    Γ ⇒ ◯[Δ]      an S-point

To close a goal is to show that no world is like that.  Read as a statement
to derive, `Γ ⇒ Δ` is `Γ ⊢ ⋁Δ` and `Γ ⇒ ◯[Δ]` is `Γ ⊢ ◯⋁Δ`.

**How to type a line.**

    subtab             the moves that apply at goal 0; none is made
    subtab im          those whose names begin with `im`
    subtab impR        `impR` with its formulas left out: made if only one
                       move of that form applies, else each is offered
    subtab impL p _    `_` or `?_` for any argument
    subtab … at 1      the same at goal 1

Click an offered line to write it in place of yours.  A line that offers
makes no move; only a line that nothing completes is an error.

**The twelve rules** (the table is in
`LaxLogic/PLL/SubTab/campaign/record.md`).  Closing: `bot`, `ax A`.  On a
true formula: `andL`, `orL`, `impL`, and `boxL` at an S-point only.  On a
false formula, staying at the world: `andR`, `orR`, `impLoc` (when `A` is
true), `boxLoc` (at an S-point).  On a false formula, to a new world, which
keeps the true formulas and drops the false ones: `impR` (to a world
outside S) and `boxR` (to an S-point).

`all_goals leave_open` at the end leaves what is not yet proved open,
without an error.  When a proof is done, delete that line and change
`Explore.Att STab true` to `Explore.Der STab`: a derivation, from which
`holds_of_der` gives provability and `term` the natural-deduction proof.

`set_option apply_move.tryThis false` (below) stops the "Try this" that
shows how each line was filled.  Delete the option to see the fills.

Reference derivations: `LaxLogic/PLL/SubTab/ExploreTest.lean`.
-/
import LaxLogic.PLL.SubTab.ExploreTactic

set_option apply_move.tryThis false
set_option linter.unusedTactic false

open PLLFormula ProofTools PLLND PLLND.SubTab

def p : PLLFormula := .prop "p"
def q : PLLFormula := .prop "q"
def r : PLLFormula := .prop "r"

/-- The sequent `⇒ φ` at a world outside S. -/
abbrev goal (φ : PLLFormula) : SSeq := ⟨false, [], [φ]⟩

-- Unit: p ↠ ◯p
example : Explore.Att STab true (goal (p ↠ ◯p)) := by
  subtab
  all_goals leave_open

-- Multiplication: ◯◯p ↠ ◯p
example : Explore.Att STab true (goal (◯◯p ↠ ◯p)) := by
  subtab
  all_goals leave_open

-- Functoriality: (p ↠ q) ↠ (◯p ↠ ◯q)
example : Explore.Att STab true (goal ((p ↠ q) ↠ (◯p ↠ ◯q))) := by
  subtab
  all_goals leave_open

-- Strength: (◯p ∧ ◯q) ↠ ◯(p ∧ q)
example : Explore.Att STab true (goal ((◯p ∧ ◯q) ↠ ◯(p ∧ q))) := by
  subtab
  all_goals leave_open

-- Not a theorem: ◯p ↠ p.  After `impR` no move applies.
example : Explore.Att STab true (goal (◯p ↠ p)) := by
  subtab
  all_goals leave_open

-- Not a theorem: ◯(p ∨ q) ↠ (◯p ∨ ◯q).  `boxR p` and `boxR q` each leave
-- the other behind.
example : Explore.Att STab true (goal (◯(p ∨ q) ↠ (◯p ∨ ◯q))) := by
  subtab
  all_goals leave_open

-- Not a theorem: Peirce's law, ((p ↠ q) ↠ p) ↠ p.
example : Explore.Att STab true (goal (((p ↠ q) ↠ p) ↠ p)) := by
  subtab
  all_goals leave_open
