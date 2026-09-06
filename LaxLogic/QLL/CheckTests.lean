/-
# `LaxLogic.QLL.CheckTests` — the checker, run

Pinned behaviour of `checkTop`.  The accepting cells are the `Smoke.lean`
derivations put through the checker instead of built by hand, which is the
direction of travel: once a searcher exists, `Smoke.lean` goes away.

The rejecting cells are gates, and every one of them has been watched failing.
They are not decoration: an earlier version of `check` returned
`notInferable "λz.p"` for `forall_identity`, because `gen` was only inferable
and its body is a `lam`.  Running the checker is what found that; reading it
did not.
-/
import LaxLogic.QLL.Check

namespace LaxLogic.QLL.CheckTests

open Form Pf

/-! ## Accepted -/

/-- info: Except.ok [] -/
#guard_msgs in #eval checkTop [] (lam (bvar 0)) (imp top top)

/-- info: Except.ok [] -/
#guard_msgs in #eval checkTop [] (val Q.all star) (circ Q.all top)

-- `⟨λz.z | x⟩ : ∀x. P(x) ⊃ P(x)` — both binder sorts at once.
/-- info: Except.ok [] -/
#guard_msgs in
#eval checkTop [] (gen (lam (bvar 0)))
        (forall_ (imp (pred "P" [Tm.bvar 0]) (pred "P" [Tm.bvar 0])))

-- The monad's left unit.
/-- info: Except.ok [] -/
#guard_msgs in
#eval checkTop [(fvar "p", circ Q.ex top)]
        (letQ Q.ex (fvar "p") (val Q.ex (bvar 0))) (circ Q.ex top)

/-! ## Obligations

A context carrying a supplied constraint term — the shape `Subst` leaves
behind.  The check succeeds and the outstanding refinement comes back. -/

/-- info: Except.ok [(LaxLogic.QLL.Pf.pair (LaxLogic.QLL.Pf.star) (LaxLogic.QLL.Pf.star), LaxLogic.QLL.Form.pred "C" [])] -/
#guard_msgs in
#eval checkTop [(pair star star, pred "C" []), (fvar "z", top)] (fvar "z") top

/-! ## Gates — each watched failing -/

/-- info: Except.error (LaxLogic.QLL.Err.mismatch (LaxLogic.QLL.Form.bot) (LaxLogic.QLL.Form.top)) -/
#guard_msgs in #eval checkTop [] (lam (bvar 0)) (imp top bot)

-- The two modalities may not be mixed; Fig. 5's `◯E` carries one `Q`.
/-- info: Except.error (LaxLogic.QLL.Err.modalityClash (LaxLogic.QLL.Q.all) (LaxLogic.QLL.Q.ex)) -/
#guard_msgs in #eval checkTop [] (val Q.all star) (circ Q.ex top)

/-- info: Except.error (LaxLogic.QLL.Err.expected "∧" (LaxLogic.QLL.Form.top)) -/
#guard_msgs in #eval checkTop [] (fst star) top

/-- info: Except.error (LaxLogic.QLL.Err.expected "∨" (LaxLogic.QLL.Form.top)) -/
#guard_msgs in #eval checkTop [] (inl star) top

-- A term that is not locally closed.
/-- info: Except.error (LaxLogic.QLL.Err.looseIndex 3) -/
#guard_msgs in #eval checkTop [] (bvar 3) top

end LaxLogic.QLL.CheckTests
