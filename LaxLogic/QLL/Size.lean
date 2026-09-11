/-
# `LaxLogic.QLL.Size` — the size of a formula

Hoisted from `Complete1.lean`, whose truth lemma recurses on it, so that
`Horn.lean` recurses on the same measure.  The point in both places:
`A⟨t⟩` is not a subformula of `∀x. A`, but it has the same size.
-/
import LaxLogic.QLL.Syntax

namespace LaxLogic.QLL

/-- The number of connectives and binders. -/
def Form.size : Form → Nat
  | .top | .bot | .pred _ _ => 0
  | .and A B | .or A B | .imp A B => A.size + B.size + 1
  | .circ _ A | .forall_ A | .exists_ A => A.size + 1

theorem Form.size_openAt (t : Tm) : ∀ (A : Form) (k : Nat), (A.openAt k t).size = A.size
  | .top, _ | .bot, _ | .pred _ _, _ => rfl
  | .and A B, k | .or A B, k | .imp A B, k => by
      show (A.openAt k t).size + (B.openAt k t).size + 1 = A.size + B.size + 1
      rw [Form.size_openAt t A k, Form.size_openAt t B k]
  | .circ _ A, k => by
      show (A.openAt k t).size + 1 = A.size + 1
      rw [Form.size_openAt t A k]
  | .forall_ A, k | .exists_ A, k => by
      show (A.openAt (k + 1) t).size + 1 = A.size + 1
      rw [Form.size_openAt t A (k + 1)]

theorem Form.size_openWith (a : String) (A : Form) : (A.openWith a).size = A.size :=
  Form.size_openAt (.fvar a) A 0

/-- info: 'LaxLogic.QLL.Form.size_openAt' does not depend on any axioms -/
#guard_msgs in #print axioms Form.size_openAt

end LaxLogic.QLL
