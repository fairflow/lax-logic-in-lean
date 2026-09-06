/-
# `LaxLogic.QLL.JudgementTests` — the judgement round trip

Same property as `SurfaceTests.lean`, one level up: whatever `renderJ` prints
can be pasted back inside `qj[…]`.

A judgement is a `Prop`, so it cannot be compared with `==`.  The round trip is
therefore checked in two halves — the printed string by `#guard`, and the
placement of the pieces by `rfl` against the explicit `Derivable` application.
Together those say that printing and parsing agree.
-/
import LaxLogic.QLL.Judgement

namespace LaxLogic.QLL.JudgementTests

open LaxLogic.QLL LaxLogic.QLL.Surface

/-! ## Contexts

Written leftmost-bound-first; the list holds the most recent entry at its head,
so the macro reverses. -/

#guard qc[] == ([] : Ctx)
#guard qc[u : A] == [(qp[u], qf[A])]
#guard qc[u : A, v : B] == [(qp[v], qf[B]), (qp[u], qf[A])]

#guard renderCtx qc[u : A, v : B] == "u : A, v : B"
#guard renderCtx qc[u : A ⊃ B, v : ∀a. P(a)] == "u : A ⊃ B, v : ∀x. P(x)"

-- an obligation need not be a variable
#guard renderCtx qc[π₁ (*, *) : ⊤] == "π₁ (*, *) : ⊤"

/-! ## Judgements -/

#guard renderJ qp[λa. a] qc[] qf[⊤ ⊃ ⊤] == "⊢ λu. u : ⊤ ⊃ ⊤"
#guard renderJ qp[u v] qc[u : A ⊃ B, v : A] qf[B] == "u : A ⊃ B, v : A ⊢ u v : B"

-- and the parse of that text puts the pieces exactly there
example : qj[u : A ⊃ B, v : A ⊢ u v : B]
        = Derivable qp[u v] [(qp[v], qf[A]), (qp[u], qf[A ⊃ B])] qf[B] := rfl

example : qd[⊢ λu. u : ⊤ ⊃ ⊤] = Derives qp[λu. u] [] qf[⊤ ⊃ ⊤] := rfl

/-! ## `qj` is `Nonempty` of `qd`

Not a separate definition — the same one, read twice. -/

example : qj[u : A ⊢ u : A] = Nonempty qd[u : A ⊢ u : A] := rfl

/-! ## The notation is usable, not merely well-formed -/

example : qj[u : A ⊢ u : A] := ⟨.var (by decide)⟩

example : qd[⊢ λu. u : ⊤ ⊃ ⊤] :=
  .impI "u" ⟨by decide, by decide⟩ (.var (by decide))

/-! ## Individual and proof names stay free, and stay distinct -/

#guard renderJ qp[⟨π[x] u | y⟩] qc[u : ∀a. P(a)] qf[∀a. P(x)]
        == "u : ∀x. P(x) ⊢ ⟨π[x] u | y⟩ : ∀y. P(x)"

end LaxLogic.QLL.JudgementTests
