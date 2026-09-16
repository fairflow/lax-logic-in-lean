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

#guard render qf[A ↠ B ↠ C] == "A ↠ B ↠ C"
#guard qf[A ↠ B ↠ C] == qf[A ↠ (B ↠ C)]

#guard render qf[(A ↠ B) ↠ C] == "(A ↠ B) ↠ C"
#guard qf[(A ↠ B) ↠ C] == qf[(A ↠ B) ↠ C]

#guard render qf[(A ∨ B) ∧ C] == "(A ∨ B) ∧ C"
#guard qf[(A ∨ B) ∧ C] == qf[(A ∨ B) ∧ C]

/-! ## The two modalities, kept visibly distinct -/

#guard render qf[◯[∀] P] == "◯[∀] P"
#guard render qf[◯[∃] P] == "◯[∃] P"
#guard qf[◯[∀] P] != qf[◯[∃] P]
#guard render qf[◯[∀] (A ↠ B)] == "◯[∀] (A ↠ B)"
#guard qf[◯[∀] (A ↠ B)] == qf[◯[∀] (A ↠ B)]

/-! ## Binders

Input names are discarded; the printer supplies `x y z x₁ …`.  The round trip
is up to the *term*, which is the only thing that was ever meaningful. -/

#guard render qf[∀ a, P(a)] == "∀ x, P(x)"
#guard qf[∀ x, P(x)] == qf[∀ a, P(a)]

#guard render qf[∀ a, ∃ b, R(a, b)] == "∀ x, ∃ y, R(x, y)"
#guard qf[∀ x, ∃ y, R(x, y)] == qf[∀ a, ∃ b, R(a, b)]

#guard render qf[∀ a, P(a) ↠ P(a)] == "∀ x, P(x) ↠ P(x)"
#guard qf[∀ x, P(x) ↠ P(x)] == qf[∀ a, P(a) ↠ P(a)]

/-! ## Shadowing

An inner binder of the same name must capture, and the printer must then give
the two binders different names. -/

#guard render qf[∀ a, ∀ a, P(a)] == "∀ x, ∀ y, P(y)"
#guard qf[∀ x, ∀ y, P(y)] == qf[∀ a, ∀ a, P(a)]

/-! ## Capture avoidance

`x` occurs free, so the printer must not name a binder `x` — otherwise the
printed text would parse to a different formula.  This is the case that makes
the round trip a real property rather than a formality. -/

#guard render qf[∀ q, P(x, q)] == "∀ y, P(x, y)"
#guard qf[∀ y, P(x, y)] == qf[∀ q, P(x, q)]

/-! ## A formula using every construct at once -/

#guard render qf[∀ a, ◯[∀] (P(a) ∧ Q) ↠ ∃ b, ◯[∃] R(a, b) ∨ ⊥]
        == "∀ x, ◯[∀] (P(x) ∧ Q) ↠ ∃ y, ◯[∃] R(x, y) ∨ ⊥"
#guard qf[∀ x, ◯[∀] (P(x) ∧ Q) ↠ ∃ y, ◯[∃] R(x, y) ∨ ⊥]
        == qf[∀ a, ◯[∀] (P(a) ∧ Q) ↠ ∃ b, ◯[∃] R(a, b) ∨ ⊥]

/-! # Proof terms

Same property, same shape of test: `renderPf` emits a string, and pasting it
back inside `qp[…]` gives the same `Pf`. -/

/-! ## Atoms, prefix formers, application -/

#guard renderPf qp[λa. a] == "λu. u"
#guard qp[λu. u] == qp[λa. a]

#guard renderPf qp[(*, *)] == "(*, *)"
#guard renderPf qp[π₁ (*, *)] == "π₁ (*, *)"
#guard renderPf qp[f x] == "f x"
#guard renderPf qp[λa. λb. a b] == "λu. λv. u v"
#guard qp[λu. λv. u v] == qp[λa. λb. a b]

-- application is left associative and a `λ` in head position needs its parens
#guard renderPf qp[(λa. a) *] == "(λu. u) *"
#guard qp[(λu. u) *] == qp[(λa. a) *]

/-! ## The Fig. 5 formers -/

#guard renderPf qp[val[∀] *] == "val[∀] *"
#guard renderPf qp[ι[c] *] == "ι[c] *"
#guard renderPf qp[π[c] ⟨* | y⟩] == "π[c] ⟨* | x⟩"
#guard qp[π[c] ⟨* | x⟩] == qp[π[c] ⟨* | y⟩]

#guard renderPf qp[let[∃] a ⇐ h in val[∃] a] == "let[∃] u ⇐ h in val[∃] u"
#guard qp[let[∃] u ⇐ h in val[∃] u] == qp[let[∃] a ⇐ h in val[∃] a]

#guard renderPf qp[case r of [ι₁(a) → a, ι₂(b) → b]]
        == "case r of [ι₁(u) → u, ι₂(v) → v]"
#guard qp[case r of [ι₁(u) → u, ι₂(v) → v]] == qp[case r of [ι₁(a) → a, ι₂(b) → b]]

#guard renderPf qp[case r of [ι[y](a) → a]] == "case r of [ι[x](u) → u]"
#guard qp[case r of [ι[x](u) → u]] == qp[case r of [ι[y](a) → a]]

#guard renderPf qp[exf[⊥ ↠ ⊤] h] == "exf[⊥ ↠ ⊤] h"

/-! ## Shadowing, in each sort -/

#guard renderPf qp[λa. λa. a] == "λu. λv. v"
#guard qp[λu. λv. v] == qp[λa. λa. a]

#guard renderPf qp[⟨⟨π[y] * | y⟩ | y⟩] == "⟨⟨π[y] * | y⟩ | x⟩"
#guard qp[⟨⟨π[y] * | y⟩ | x⟩] == qp[⟨⟨π[y] * | y⟩ | y⟩]

/-! ## Capture avoidance, in each sort

A free `u` must stop a proof binder taking `u`; a free `x` must stop an
individual binder taking `x`.  These are the cases where a careless printer
produces text that parses to a *different* term. -/

#guard renderPf qp[λa. u] == "λv. u"
#guard qp[λv. u] == qp[λa. u]

#guard renderPf qp[⟨π[x] * | y⟩] == "⟨π[x] * | y⟩"
#guard qp[⟨π[x] * | y⟩] == qp[⟨π[x] * | y⟩]

/-! ## The two sorts do not interfere

`⟨p | x⟩` binds an individual and `λu. p` binds a proof variable, in
independent index spaces.  The printer draws them from separate alphabets, so
which is which is visible on the page. -/

#guard renderPf qp[⟨λa. π[y] a | y⟩] == "⟨λu. π[x] u | x⟩"
#guard qp[⟨λu. π[x] u | x⟩] == qp[⟨λa. π[y] a | y⟩]

end LaxLogic.QLL.SurfaceTests
