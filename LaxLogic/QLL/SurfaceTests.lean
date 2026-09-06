/-
# `LaxLogic.QLL.SurfaceTests` — the printed form is the input form

The property, stated so it can fail: for every formula below, `render` produces
a string, and pasting that string back inside `qf[…]` yields **the same
`Form`**.  Each case therefore appears twice — once as the rendered text, once
as that text re-parsed — and the second `#guard` is the round trip.

Bound names are not preserved, and should not be: they are arbitrary, so the
printer imposes its own alphabet.  What is preserved is the term.
-/
import LaxLogic.QLL.Surface

namespace LaxLogic.QLL.SurfaceTests

open LaxLogic.QLL LaxLogic.QLL.Surface

/-! ## Atoms and connectives -/

#guard render qf[⊤] == "⊤"
#guard render qf[P] == "P"
#guard render qf[P(x, y)] == "P(x, y)"
#guard render qf[f(g(x), y)] == "f(g(x), y)"

/-! ## Precedence and parenthesisation

`∧` binds tighter than `∨`, which binds tighter than `⊃`; `⊃` is right
associative.  The printer parenthesises exactly when re-parsing would otherwise
give a different tree — which the second `#guard` of each pair checks. -/

#guard render qf[A ∧ B ∨ C] == "A ∧ B ∨ C"
#guard qf[A ∧ B ∨ C] == qf[(A ∧ B) ∨ C]

#guard render qf[A ⊃ B ⊃ C] == "A ⊃ B ⊃ C"
#guard qf[A ⊃ B ⊃ C] == qf[A ⊃ (B ⊃ C)]

#guard render qf[(A ⊃ B) ⊃ C] == "(A ⊃ B) ⊃ C"
#guard qf[(A ⊃ B) ⊃ C] == qf[(A ⊃ B) ⊃ C]

#guard render qf[(A ∨ B) ∧ C] == "(A ∨ B) ∧ C"
#guard qf[(A ∨ B) ∧ C] == qf[(A ∨ B) ∧ C]

/-! ## The two modalities, kept visibly distinct -/

#guard render qf[◯∀ P] == "◯∀P"
#guard render qf[◯∃ P] == "◯∃P"
#guard qf[◯∀ P] != qf[◯∃ P]
#guard render qf[◯∀ (A ⊃ B)] == "◯∀(A ⊃ B)"
#guard qf[◯∀ (A ⊃ B)] == qf[◯∀ (A ⊃ B)]

/-! ## Binders

Input names are discarded; the printer supplies `x y z x₁ …`.  The round trip
is up to the *term*, which is the only thing that was ever meaningful. -/

#guard render qf[∀a. P(a)] == "∀x. P(x)"
#guard qf[∀x. P(x)] == qf[∀a. P(a)]

#guard render qf[∀a. ∃b. R(a, b)] == "∀x. ∃y. R(x, y)"
#guard qf[∀x. ∃y. R(x, y)] == qf[∀a. ∃b. R(a, b)]

#guard render qf[∀a. P(a) ⊃ P(a)] == "∀x. P(x) ⊃ P(x)"
#guard qf[∀x. P(x) ⊃ P(x)] == qf[∀a. P(a) ⊃ P(a)]

/-! ## Shadowing

An inner binder of the same name must capture, and the printer must then give
the two binders different names. -/

#guard render qf[∀a. ∀a. P(a)] == "∀x. ∀y. P(y)"
#guard qf[∀x. ∀y. P(y)] == qf[∀a. ∀a. P(a)]

/-! ## Capture avoidance

`x` occurs free, so the printer must not name a binder `x` — otherwise the
printed text would parse to a different formula.  This is the case that makes
the round trip a real property rather than a formality. -/

#guard render qf[∀q. P(x, q)] == "∀y. P(x, y)"
#guard qf[∀y. P(x, y)] == qf[∀q. P(x, q)]

/-! ## A formula using every construct at once -/

#guard render qf[∀a. ◯∀ (P(a) ∧ Q) ⊃ ∃b. ◯∃ R(a, b) ∨ ⊥]
        == "∀x. ◯∀(P(x) ∧ Q) ⊃ ∃y. ◯∃R(x, y) ∨ ⊥"
#guard qf[∀x. ◯∀ (P(x) ∧ Q) ⊃ ∃y. ◯∃ R(x, y) ∨ ⊥]
        == qf[∀a. ◯∀ (P(a) ∧ Q) ⊃ ∃b. ◯∃ R(a, b) ∨ ⊥]

end LaxLogic.QLL.SurfaceTests
