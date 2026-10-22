import LaxLogic.PLL.SubTab.Sound

/-!
# Negative tests for the two certifiers (lean-certify R9)

2026-10-15.  One corrupted certificate per checker; the kernel
proves that the checker rejects it.  (As `Certifier.verdict` terms both were
watched failing with "Tactic `decide` proved that the proposition … = true
is false".)
-/

open PLLFormula

/-- The closed tableau for `◯p ∧ ◯q ↠ ◯(p ∧ q)` with its last leaf corrupted
(`q` replaced by `p`): rejected. -/
theorem PLLND.SubTab.bad_yes_rejected :
    PLLND.SubTab.yes.check
      ((((PLLFormula.prop "p").somehow).and ((PLLFormula.prop "q").somehow)).ifThen
        (((PLLFormula.prop "p").and (PLLFormula.prop "q")).somehow))
      (.impR (((PLLFormula.prop "p").somehow).and ((PLLFormula.prop "q").somehow))
        (((PLLFormula.prop "p").and (PLLFormula.prop "q")).somehow)
        (.andL ((PLLFormula.prop "p").somehow) ((PLLFormula.prop "q").somehow)
          (.boxR ((PLLFormula.prop "p").and (PLLFormula.prop "q"))
            (.boxL (PLLFormula.prop "p") (.boxL (PLLFormula.prop "q")
              (.andL ((PLLFormula.prop "p").somehow) ((PLLFormula.prop "q").somehow)
                (.andR (PLLFormula.prop "p") (PLLFormula.prop "q")
                  (.ax (PLLFormula.prop "p")) (.ax (PLLFormula.prop "p"))))))))) = false := by
  decide +kernel

/-- Peirce's countermodel with its valuation emptied: rejected. -/
theorem PLLND.SubTab.bad_no_rejected :
    PLLND.SubTab.no.check
      ((((PLLFormula.prop "p").ifThen (PLLFormula.prop "q")).ifThen (PLLFormula.prop "p")).ifThen
        (PLLFormula.prop "p"))
      { n := 2, root := 0, le := [[true, true], [false, true]], S := [false, false],
        val := [[], []] } = false := by
  decide +kernel
