import LaxLogic.PLL.SubTab.ExploreTactic
import LaxLogic.PLL.SubTab.ExploreEngine
import Meta.Audit

/-!
# Tests of the subframe tableau as an instance of the proof explorer

2026-11-19.  Pinned here: the four laws of `◯` and two more theorems as
derivations by `subtab`, each with its closed tableau, its script and its
proof of provability; three formulas that are not theorems, each with the
side condition that stops it and with the engine's countermodel; queries
and patterns; a script checked by the kernel with no tactic; every closed
tableau the search finds, turned into a script that `derives` accepts; a
proof by hand of 16 moves where the search's has 403; a corrupted script
rejected; the goal shown as its sequent; the axioms.
-/

-- a query makes no move, which the linter would remark on at every one
set_option linter.unusedTactic false

open PLLFormula ProofTools

namespace PLLND
namespace SubTab
namespace ExploreTest

def p : PLLFormula := .prop "p"
def q : PLLFormula := .prop "q"
def r : PLLFormula := .prop "r"

/-- The sequent `⇒ φ` at a world outside S. -/
abbrev goal (φ : PLLFormula) : SSeq := ⟨false, [], [φ]⟩

/-! ## The laws of `◯`, by `subtab` -/

set_option apply_move.tryThis false

/-- Unit: `p ↠ ◯p`. -/
def unit : Explore.Der STab (goal (p ↠ ◯p)) := by
  subtab impR p (◯p)
  subtab boxR p
  subtab ax p

/-- Multiplication: `◯◯p ↠ ◯p`. -/
def mult : Explore.Der STab (goal (◯◯p ↠ ◯p)) := by
  subtab impR (◯◯p) (◯p)
  subtab boxR p
  subtab boxL (◯p)
  subtab boxL p
  subtab ax p

/-- Functoriality: `(p ↠ q) ↠ (◯p ↠ ◯q)`. -/
def functor : Explore.Der STab (goal ((p ↠ q) ↠ (◯p ↠ ◯q))) := by
  subtab impR (p ↠ q) (◯p ↠ ◯q)
  subtab impR (◯p) (◯q)
  subtab boxR q
  subtab boxL p
  subtab impL p q
  subtab ax p
  subtab ax q

/-- Strength: `(◯p ∧ ◯q) ↠ ◯(p ∧ q)`. -/
def strength : Explore.Der STab (goal ((◯p ∧ ◯q) ↠ ◯(p ∧ q))) := by
  subtab impR (◯p ∧ ◯q) (◯(p ∧ q))
  subtab andL (◯p) (◯q)
  subtab boxR (p ∧ q)
  subtab boxL p
  subtab boxL q
  subtab andR p q
  subtab ax p
  subtab ax q

/-- `◯(p ↠ q) ↠ (◯p ↠ ◯q)`. -/
def kAxiom : Explore.Der STab (goal (◯(p ↠ q) ↠ (◯p ↠ ◯q))) := by
  subtab impR
  subtab impR
  subtab boxR
  subtab boxL (p ↠ q)
  subtab boxL p
  subtab impL
  subtab ax
  subtab ax

/-- `◯⊥ ↠ ◯p`. -/
def exFalso : Explore.Der STab (goal (◯⊥ ↠ ◯p)) := by
  subtab impR
  subtab boxR
  subtab boxL
  subtab bot

set_option apply_move.tryThis true

/-! ## A derivation, its closed tableau, its script, its proof -/

-- The closed tableau of a derivation checks, in the kernel.
example : check (goal ((◯p ∧ ◯q) ↠ ◯(p ∧ q))) (cert strength) = true := by decide +kernel

-- The numbers of moves.
#guard [unit.script.length, mult.script.length, functor.script.length, strength.script.length,
  kAxiom.script.length, exFalso.script.length] == [3, 5, 7, 8, 8, 4]

/-- Provability from the tactic proof, by the tableau's own rules. -/
theorem strength_holds : Holds ((◯p ∧ ◯q) ↠ ◯(p ∧ q)) := holds_of_der strength

/-- The natural-deduction derivation the tactic proof computes. -/
def strengthTerm : [] ⊢ (◯p ∧ ◯q) ↠ ◯(p ∧ q) := term strength

/-- The same from the script alone: the kernel runs it. -/
theorem strength_holds' : Holds ((◯p ∧ ◯q) ↠ ◯(p ∧ q)) :=
  yesScript.verdict ((◯p ∧ ◯q) ↠ ◯(p ∧ q))
    [⟨0, .impR (◯p ∧ ◯q) (◯(p ∧ q))⟩, ⟨0, .andL (◯p) (◯q)⟩, ⟨0, .boxR (p ∧ q)⟩, ⟨0, .boxL p⟩,
     ⟨0, .boxL q⟩, ⟨0, .andR p q⟩, ⟨0, .ax p⟩, ⟨0, .ax q⟩]

-- The attempt after three lines, as text.
/--
info: ⇒ ((◯p ∧ ◯q) ↠ ◯(p ∧ q))   by impR (◯p ∧ ◯q) (◯(p ∧ q))
  (◯p ∧ ◯q) ⇒ ◯(p ∧ q)   by andL (◯p) (◯q)
    (◯p ∧ ◯q), ◯p, ◯q ⇒ ◯(p ∧ q)   by boxR (p ∧ q)
      ? (◯p ∧ ◯q), ◯p, ◯q ⇒ ◯[(p ∧ q)]
-/
#guard_msgs in
#eval IO.println ((Explore.run STab (goal ((◯p ∧ ◯q) ↠ ◯(p ∧ q))) (strength.script.take 3)).att.render)

/-! ## Queries, patterns, and the goal as its sequent -/

/--
info: subtab: at goal 0, 1 move applies; no move is made. Try these:
  [apply] subtab impR (p ↠ q) (◯p ↠ ◯q)
---
info: Try this:
  [apply] subtab impR (p ↠ q) (◯p ↠ ◯q)
---
info: subtab: at goal 0, 2 moves whose names begin with `im` apply; no move is made. Try these:
  [apply] subtab impL p q
  [apply] subtab impR (◯p) (◯q)
---
info: Try this:
  [apply] subtab impR (◯p) (◯q)
---
info: subtab: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] subtab impL p q
  [apply] subtab boxR q
---
trace: ⊢ Att STab   (p ↠ q), ◯p ⇒ ◯q
-/
#guard_msgs in
example : Explore.Att STab true (goal ((p ↠ q) ↠ (◯p ↠ ◯q))) := by
  subtab
  subtab impR
  subtab im
  subtab impR _ (◯q)
  trace_state
  subtab
  all_goals leave_open

-- `impL` leaves two goals; the second is closed first, by `at 1`.
/--
info: Try this:
  [apply] subtab impR (p ↠ q) (◯p ↠ ◯q)
---
info: Try this:
  [apply] subtab impR (◯p) (◯q)
---
info: Try this:
  [apply] subtab boxR q
---
info: Try this:
  [apply] subtab boxL p
---
info: Try this:
  [apply] subtab impL p q
---
trace: ⊢ Att STab   (p ↠ q), ◯p, p ⇒ ◯[q, p]

⊢ Att STab   (p ↠ q), ◯p, p, q ⇒ ◯[q]
---
trace: ⊢ Att STab   (p ↠ q), ◯p, p ⇒ ◯[q, p]
-/
#guard_msgs in
example : Explore.Att STab true (goal ((p ↠ q) ↠ (◯p ↠ ◯q))) := by
  subtab impR
  subtab impR
  subtab boxR
  subtab boxL
  subtab impL
  trace_state
  subtab ax q at 1
  trace_state
  leave_open

/-! ## Three formulas that are not theorems

Each attempt stops at a side condition; the engine's answer is a finite
subframe countermodel, checked by the kernel. -/

-- `◯p ↠ p`: outside S a true `◯p` gives nothing, and `p` is not true.
/--
info: Try this:
  [apply] subtab impR (◯p) p
---
error: the move does not apply to goal 0: the world is not an S-point
-/
#guard_msgs in
example : Explore.Att STab true (goal (◯p ↠ p)) := by
  subtab impR
  subtab boxL p

/--
info: Try this:
  [apply] subtab impR (◯p) p
---
error: subtab: no move applies at goal 0
-/
#guard_msgs in
example : Explore.Att STab true (goal (◯p ↠ p)) := by
  subtab impR
  subtab

-- `◯(p ∨ q) ↠ (◯p ∨ ◯q)`: `boxR p` leaves `◯q` behind, and the branch for `q` stays open.
/--
info: Try this:
  [apply] subtab impR (◯(p ∨ q)) (◯p ∨ ◯q)
---
info: Try this:
  [apply] subtab orR (◯p) (◯q)
---
info: Try this:
  [apply] subtab boxL (p ∨ q)
---
info: Try this:
  [apply] subtab orL p q
---
info: Try this:
  [apply] subtab ax p
---
info: subtab: at goal 0, 2 moves apply; no move is made. Try these:
  [apply] subtab boxL (p ∨ q)
  [apply] subtab orL p q
---
trace: ⊢ Att STab   ◯(p ∨ q), (p ∨ q), q ⇒ ◯[p]
-/
#guard_msgs in
example : Explore.Att STab true (goal (◯(p ∨ q) ↠ (◯p ∨ ◯q))) := by
  subtab impR
  subtab orR
  subtab boxR p
  subtab boxL
  subtab orL
  subtab ax
  trace_state
  subtab
  leave_open

-- Peirce's law: the second `impR` leaves the false `p` behind, and from
-- there the one move that applies leads back to the same sequent.
/--
info: Try this:
  [apply] subtab impR ((p ↠ q) ↠ p) p
---
info: Try this:
  [apply] subtab impL (p ↠ q) p
---
info: Try this:
  [apply] subtab ax p at 1
---
info: Try this:
  [apply] subtab impR p q
---
info: subtab: at goal 0, 1 move applies; no move is made. Try these:
  [apply] subtab impL (p ↠ q) p
---
trace: ⊢ Att STab   ((p ↠ q) ↠ p), p ⇒ q
-/
#guard_msgs in
example : Explore.Att STab true (goal (((p ↠ q) ↠ p) ↠ p)) := by
  subtab impR
  subtab impL
  subtab ax at 1
  subtab impR
  trace_state
  subtab
  leave_open

/-- The engine's countermodels, checked by the kernel. -/
theorem not_unbox : Holds (◯p ↠ p) → False :=
  no.verdict (◯p ↠ p) ⟨2, 0, [[true, true], [false, true]], [false, false], [[], []]⟩

-- What the search answers on each of the three.
#guard (engineScript.produce (◯p ↠ p) 0 matches .fail _)
#guard (engineScript.produce (◯(p ∨ q) ↠ (◯p ∨ ◯q)) 0 matches .fail _)
#guard (engineScript.produce (((p ↠ q) ↠ p) ↠ p) 0 matches .fail _)

/-! ## Every closed tableau of the search is a script -/

/-- A tested formula: the search closes it, its closed tableau becomes a
derivation, the derivation's script derives, and its tableau is the one
the search found. -/
def roundTrip (φ : PLLFormula) : Bool :=
  match _root_.SubTab.solve φ with
  | .ok c =>
    if h : check (goal φ) c = true then
      let d := ofCert c (goal φ) h
      Explore.derives STab (goal φ) d.script && (tcertSrc' (cert d) == tcertSrc' c)
    else false
  | .error _ => false
where
  /-- A closed tableau as text, to compare two. -/
  tcertSrc' : TCert → String
    | .bot => "bot"
    | .ax A => "ax " ++ showF A
    | .andL A B c => "andL " ++ showF A ++ showF B ++ "(" ++ tcertSrc' c ++ ")"
    | .orL A B c₁ c₂ => "orL " ++ showF A ++ showF B ++ "(" ++ tcertSrc' c₁ ++ ")(" ++ tcertSrc' c₂ ++ ")"
    | .impL A B c₁ c₂ => "impL " ++ showF A ++ showF B ++ "(" ++ tcertSrc' c₁ ++ ")(" ++ tcertSrc' c₂ ++ ")"
    | .boxL A c => "boxL " ++ showF A ++ "(" ++ tcertSrc' c ++ ")"
    | .andR A B c₁ c₂ => "andR " ++ showF A ++ showF B ++ "(" ++ tcertSrc' c₁ ++ ")(" ++ tcertSrc' c₂ ++ ")"
    | .orR A B c => "orR " ++ showF A ++ showF B ++ "(" ++ tcertSrc' c ++ ")"
    | .impLoc A B c => "impLoc " ++ showF A ++ showF B ++ "(" ++ tcertSrc' c ++ ")"
    | .boxLoc A c => "boxLoc " ++ showF A ++ "(" ++ tcertSrc' c ++ ")"
    | .impR A B c => "impR " ++ showF A ++ showF B ++ "(" ++ tcertSrc' c ++ ")"
    | .boxR A c => "boxR " ++ showF A ++ "(" ++ tcertSrc' c ++ ")"

#guard roundTrip (p ↠ ◯p) && roundTrip (◯◯p ↠ ◯p) && roundTrip ((p ↠ q) ↠ (◯p ↠ ◯q))
#guard roundTrip ((◯p ∧ ◯q) ↠ ◯(p ∧ q)) && roundTrip (◯(p ↠ q) ↠ (◯p ↠ ◯q))
#guard roundTrip (◯⊥ ↠ ◯p) && roundTrip ((p ∨ q) ↠ (q ∨ p)) && roundTrip ((p ∧ q) ↠ (q ∧ p))
#guard roundTrip (((p ↠ ⊥) ↠ ⊥) ↠ ((p ↠ ⊥) ↠ ⊥)) && roundTrip (◯(p ∧ q) ↠ (◯p ∧ ◯q))
#guard roundTrip ((◯p ∨ ◯q) ↠ ◯(p ∨ q)) && roundTrip ((p ↠ (q ↠ r)) ↠ ((p ↠ q) ↠ (p ↠ r)))
#guard !roundTrip (◯p ↠ p)

-- The engine by scripts answers with a script on a theorem.
#guard (engineScript.produce ((◯p ∧ ◯q) ↠ ◯(p ∧ q)) 0 matches .pass _)

/-! ## A proof by hand against the search's

The search is depth-first and shares nothing between branches.  On a chain
of implications under `◯` it branches on every implication before its
antecedent is there, and its closed tableau has 403 moves.  Made in the
order of the chain, the proof has 16. -/

def p0 : PLLFormula := .prop "p0"
def p1 : PLLFormula := .prop "p1"
def p2 : PLLFormula := .prop "p2"
def p3 : PLLFormula := .prop "p3"
def p4 : PLLFormula := .prop "p4"

/-- `(p0 ↠ p1) ↠ (p1 ↠ p2) ↠ (p2 ↠ p3) ↠ (p3 ↠ p4) ↠ (◯p0 ↠ ◯p4)`. -/
def chain4 : PLLFormula :=
  (p0 ↠ p1) ↠ ((p1 ↠ p2) ↠ ((p2 ↠ p3) ↠ ((p3 ↠ p4) ↠ (◯p0 ↠ ◯p4))))

set_option apply_move.tryThis false in
/-- The chain, by hand. -/
def chain4Der : Explore.Der STab (goal chain4) := by
  subtab impR
  subtab impR
  subtab impR
  subtab impR
  subtab impR
  subtab boxR
  subtab boxL
  subtab impL p0 p1
  subtab ax p0
  subtab impL p1 p2
  subtab ax p1
  subtab impL p2 p3
  subtab ax p2
  subtab impL p3 p4
  subtab ax p3
  subtab ax p4

/-- The number of moves of the search's closed tableau. -/
def searchMoves (φ : PLLFormula) : Nat :=
  match _root_.SubTab.solve φ with
  | .ok c => if h : check (goal φ) c = true then (scriptOf φ c h).length else 0
  | .error _ => 0

#guard chain4Der.script.length == 16
#guard searchMoves chain4 == 403
#guard searchMoves ((◯p ∧ ◯q) ↠ ◯(p ∧ q)) == 9 && strength.script.length == 8

/-! ## A corrupted script is rejected (negative test) -/

/-- The script of strength with its last line corrupted (`q` replaced by
`p`): rejected, in the kernel. -/
theorem bad_script_rejected :
    yesScript.check ((◯p ∧ ◯q) ↠ ◯(p ∧ q))
      [⟨0, .impR (◯p ∧ ◯q) (◯(p ∧ q))⟩, ⟨0, .andL (◯p) (◯q)⟩, ⟨0, .boxR (p ∧ q)⟩, ⟨0, .boxL p⟩,
       ⟨0, .boxL q⟩, ⟨0, .andR p q⟩, ⟨0, .ax p⟩, ⟨0, .ax p⟩] = false := by
  decide +kernel

-- The same corrupted script as a `verdict` term does not elaborate: the gate
-- is watched failing here, on the term that `strength_holds'` above has with
-- the right last line.
example : True := by
  fail_if_success
    have : Holds ((◯p ∧ ◯q) ↠ ◯(p ∧ q)) :=
      yesScript.verdict ((◯p ∧ ◯q) ↠ ◯(p ∧ q))
        [⟨0, .impR (◯p ∧ ◯q) (◯(p ∧ q))⟩, ⟨0, .andL (◯p) (◯q)⟩, ⟨0, .boxR (p ∧ q)⟩,
         ⟨0, .boxL p⟩, ⟨0, .boxL q⟩, ⟨0, .andR p q⟩, ⟨0, .ax p⟩, ⟨0, .ax p⟩]
  trivial

/-- … and a script that stops early: rejected. -/
theorem short_script_rejected :
    yesScript.check ((◯p ∧ ◯q) ↠ ◯(p ∧ q))
      [⟨0, .impR (◯p ∧ ◯q) (◯(p ∧ q))⟩, ⟨0, .andL (◯p) (◯q)⟩] = false := by
  decide +kernel

end ExploreTest
end SubTab
end PLLND

/-! ## The axioms -/

#axioms_within PLLND.SubTab.ExploreTest.strength_holds [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.strength_holds' [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.strengthTerm [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.not_unbox [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.bad_script_rejected [propext, Quot.sound]
#axioms_within PLLND.SubTab.yesScript [propext, Quot.sound]
#axioms_within PLLND.SubTab.complete_script [propext, Quot.sound]

/-! ## Lean certify gates (R2, R3) -/

#certify_structural PLLND.SubTab.yesScript
#certify_statement PLLND.SubTab.yesScript
