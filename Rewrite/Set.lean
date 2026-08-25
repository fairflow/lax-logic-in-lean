/-
THE STARTER SIMPSET — small, irredundant, PLL-only.

Every rule carries an `Interd` proof, so membership is enforced by
type: a PCLL-only equation (the catalogue's four distribution merges)
CANNOT be added here.  That stratification is the point — a PLL goal
must never be silently simplified by a non-PLL fact.

Orientation: big-to-small by `crank`, checked by `pllSet_oriented`.
Note `crank` charges ◯ two and ⊃ one, so orienting by it is exactly
"reduce ◯/⊃ nesting", which is the shape that makes search expensive.

Content of round 1 — the modal laws.  These are the ones the ad-hoc
`nfc` folding in wip/closed_frag.lean applies WITHOUT certificates;
here they are proved once and reusable everywhere, including under
arbitrary contexts (via `box_congr` etc. in `norm`).
-/
import Rewrite.Core

namespace Rewrite

open PLLND PLLND.SemUI

/-! ## The certified laws -/

/-- `◯◯φ ⊣⊢ ◯φ` — idempotence of the modality.  Forward by `laxElim`
(peel one box), backward by `laxIntro`. -/
theorem box_idem (φ : PLLFormula) :
    Interd (.somehow (.somehow φ)) (.somehow φ) :=
  ⟨⟨.laxElim (.iden (.head _)) (.iden (.head _))⟩,
   ⟨.laxIntro (.iden (.head _))⟩⟩

/-- `◯⊥ ⊣⊢ ◯⊥` is trivial; the useful `⊥`-law is `◯`-monotone and
lives in the catalogue.  Instead: `◯⊤ ⊣⊢ ⊤` (settled by the
closed-fragment probe as the crank 3 → 1 collapse). -/
theorem box_top :
    Interd (.somehow (.ifThen .falsePLL .falsePLL))
           (.ifThen .falsePLL .falsePLL) :=
  ⟨⟨.impIntro (.iden (.head _))⟩,
   ⟨.laxIntro (.impIntro (.iden (.head _)))⟩⟩

/-- `⊥ ⊃ φ ⊣⊢ ⊤` — constant folding, certified. -/
theorem bot_imp (φ : PLLFormula) :
    Interd (.ifThen .falsePLL φ) (.ifThen .falsePLL .falsePLL) :=
  ⟨⟨.impIntro (.iden (.head _))⟩,
   ⟨.impIntro (.falsoElim _ (.iden (.head _)))⟩⟩

/-! ## The set -/

/-- Round-1 PLL simpset.  Deliberately tiny and irredundant; grow it
from CERTIFIED catalogue entries, never from conjecture. -/
def pllSet : List RwRule :=
  [ ⟨_, _, box_idem (.prop "x")⟩ ]

/-- The set is crank-oriented (a screen, not a hypothesis:
`norm_interd` holds regardless). -/
theorem pllSet_oriented : allOriented pllSet = true := by decide

/-! ## Demonstration: the simpset shrinks a goal, certified

`◯◯x` normalises to `◯x`, and — the point Matthew made — it does so
INSIDE a context, by congruence. -/

example : norm pllSet 3 (.somehow (.somehow (.prop "x"))) = .somehow (.prop "x") := by
  decide

/-- Under a context: `(◯◯x ⊃ q) ⊣⊢ (◯x ⊃ q)` follows from the SAME
rule, with no new search — this is the subformula payoff. -/
example :
    norm pllSet 3 (.ifThen (.somehow (.somehow (.prop "x"))) (.prop "q"))
      = .ifThen (.somehow (.prop "x")) (.prop "q") := by
  decide

/-- And the goal-level consequence, certified by `deriv_iff_norm`:
proving the normalised sequent proves the original. -/
theorem context_reduction (q : PLLFormula) :
    Nonempty (LaxND [.somehow (.somehow (.prop "x"))] q) ↔
    Nonempty (LaxND [norm pllSet 3 (.somehow (.somehow (.prop "x")))]
      (norm pllSet 3 q)) :=
  deriv_iff_norm pllSet 3 _ q

/-! ## Pins -/

/--
info: 'Rewrite.box_idem' does not depend on any axioms
-/
#guard_msgs in
#print axioms box_idem

/--
info: 'Rewrite.context_reduction' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms context_reduction

end Rewrite
