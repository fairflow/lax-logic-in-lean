import LaxLogic.PLLDecide

/-!
# G4iLL is incomplete: a machine-checked separation from G3iLL

Iemhoff's calculus G4iLL (*Proof Theory for Lax Logic*, arXiv:2209.08976,
Fig. 2.3 — our `G4`) was claimed equivalent to G3iLL (our `SC`) via the
general Theorem 1 of *The G4i analogue of a G3i calculus*
(arXiv:2011.11847).  This file refutes the equivalence, with both sides
machine-checked:

* `SC [◯G', F'] r` is derived below, where `F' = ◯p → r` and
  `G' = F' → ◯p`;
* `decide (G4 [◯G', F'] r) = false` by the *verified* decision procedure
  of `PLLDecide` (whose completeness over the `G4` rules is a theorem).

The sequent is PLL-valid: bind on `◯G'` — inside the box, `G'` and the
(reused!) hypothesis `F'` give `◯p` — so `◯p` holds outright, and `F'`
then yields `r`.  The G3 derivation below uses `F'` **twice**: once
inside the `laxL` box-opening, once as the final implication.  G4iLL's
`L◯→` (`impLLaxLax`) reuses the *box* across its premises but *consumes
the implication*, and its first premise `G' ⇒ ◯p` is invalid — so no G4
rule instance closes the sequent.  This is Howe's duplication phenomenon
(MSCS 2001) one level up: the formula needing contraction is the
`◯`-antecedent implication itself, straddling a box-opening.

Consequently the modal case of Theorem 1 of arXiv:2011.11847 fails as
stated (its premises `Sᵢ` carry an extra copy of `◯φ→ψ`, so `Sᵢ ≪ S`
does not hold, and the copy cannot be dropped), and Corollary 1 of
arXiv:2209.08976 with it.  A `⊥`-instantiated variant is included to
show even the constant-only fragment separates.  The decidability
development of `PLLDecide` is untouched — it decides `G4` — but a
repaired calculus is needed before it decides PLL.
-/

open PLLFormula PLLND

namespace PLLG4Gap

/-- `F' := ◯p ⊃ r`. -/
def Fa : PLLFormula := ((prop "p").somehow).ifThen (prop "r")

/-- `G' := F' ⊃ ◯p = (◯p ⊃ r) ⊃ ◯p`. -/
def Ga : PLLFormula := Fa.ifThen (prop "p").somehow

-- Control: `◯G', F' ⇒ ◯p` is G4-derivable (the boxed detour exists).
/-- info: true -/
#guard_msgs in
#eval decide (G4 [Ga.somehow, Fa] ((prop "p").somehow))

-- **The separation**: `◯G', F' ⇒ r` is *not* G4-derivable.
/-- info: false -/
#guard_msgs in
#eval decide (G4 [Ga.somehow, Fa] (prop "r"))

/-- … but it *is* derivable in the G3 calculus `SC`, reusing `F'` on
both sides of the box-opening. -/
example : SC [Ga.somehow, Fa] (prop "r") := by
  -- impL on F' : premises ◯G', F' ⇒ ◯p and r, ◯G', F' ⇒ r
  refine SC.impL (A := (prop "p").somehow) (.tail _ (.head _)) ?_ ?_
  · -- ◯G', F' ⇒ ◯p : open the box, then impL on G'
    refine SC.laxL (A := Ga) (.head _) ?_
    refine SC.impL (A := Fa) (.head _) ?_ ?_
    · -- G', ◯G', F' ⇒ F' : the second use of F'
      refine SC.impR ?_
      refine SC.impL (A := (prop "p").somehow)
        (.tail _ (.tail _ (.tail _ (.head _)))) ?_ ?_
      · exact SC.iden _ (.head _)
      · exact SC.iden _ (.head _)
    · exact SC.iden _ (.head _)
  · exact SC.iden _ (.head _)

/-! ## The `⊥`-only variant: `F = ◯⊥ ⊃ ⊥`, `G = F ⊃ ◯⊥` -/

/-- `F := ◯⊥ ⊃ ⊥` (i.e. `¬◯⊥`). -/
def Fm : PLLFormula := (falsePLL.somehow).ifThen falsePLL

/-- `G := F ⊃ ◯⊥`. -/
def Gm : PLLFormula := Fm.ifThen falsePLL.somehow

/-- info: true -/
#guard_msgs in
#eval decide (G4 [Gm.somehow, Fm] falsePLL.somehow)

/-- info: false -/
#guard_msgs in
#eval decide (G4 [Gm.somehow, Fm] (prop "q"))

/-- `◯G, F` is PLL-inconsistent, and `SC` sees it. -/
example : SC [Gm.somehow, Fm] (prop "q") := by
  refine SC.impL (A := falsePLL.somehow) (.tail _ (.head _)) ?_ ?_
  · refine SC.laxL (A := Gm) (.head _) ?_
    refine SC.impL (A := Fm) (.head _) ?_ ?_
    · refine SC.impR ?_
      refine SC.impL (A := falsePLL.somehow)
        (.tail _ (.tail _ (.tail _ (.head _)))) ?_ ?_
      · exact SC.iden _ (.head _)
      · exact SC.botL (.head _)
    · exact SC.iden _ (.head _)
  · exact SC.botL (.head _)

end PLLG4Gap
