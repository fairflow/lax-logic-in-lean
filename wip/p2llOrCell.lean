import LaxLogic.PLL.Semantics.Frames
import Meta.Audit

/-!
# C6: the J-grammar has no `∨`-clause

File 5 of the P2LL definability campaign (`wip/p2ll-STATUS.md`).  The
fixed-point set of a nucleus is closed under meets and under `x ↠ (−)`, not
under joins.  A clause `IsJ Θ φ → IsJ Θ ψ → IsJ Θ (φ ∨ ψ)` would make the key
lemma (Fix) of `wip/p2llStatements.lean` demand

    ◯A → A,  ◯B → B   ⊢   ◯(A ∨ B) → (A ∨ B),

and that fails already in PLL: on F&M's three-world model `modelOrSplit`
(`LaxLogic/PLL/Semantics/Frames.lean`: a root `r` below two maximal points, `A`
at one, `B` at the other, both frames equal, no fallible world) `A` and `B` are
◯-fixpoints everywhere, `r` forces `◯(A ∨ B)` and forces neither `A` nor `B`.

The cell is a PLL fact, kernel-checked through `soundness_valid` and `decide`
as the three counter-models of `Frames.lean`.  Its transfer to P2LL (the
guarded calculus translated into P2LL) waits for the plan's M2, soundness of
P2LL for second-order constraint models, which is not built; as the algebraic
reason for the design it needs no transfer.
-/

namespace P2LL

open PLLND PLLFormula

/-- C6: `⊬ ((◯A → A) ∧ (◯B → B)) → (◯(A ∨ B) → (A ∨ B))` in PLL. -/
theorem or_not_fixed :
    [] ⊬ ((((◯(prop "A")) ↠ (prop "A")) ∧ ((◯(prop "B")) ↠ (prop "B"))) ↠
      ((◯((prop "A") ∨ (prop "B"))) ↠ ((prop "A") ∨ (prop "B")))) := by
  rintro ⟨p⟩
  exact absurd (soundness_valid p modelOrSplit .r) (by decide)

end P2LL

/-! The profile of `PLLND.not_provable_somehow_or_dist` in `docs/status-ledger.jsonl`:
choice enters through the model machinery of `Frames.lean`, not through the cell. -/
#axioms_within P2LL.or_not_fixed [propext, Classical.choice, Quot.sound]
