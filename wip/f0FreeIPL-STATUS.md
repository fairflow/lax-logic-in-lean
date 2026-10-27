# wip/f0FreeIPL.lean — status

Does the interval `[t3, ⊤]` of F0 contain a copy of the free Heyting algebra
on countably many generators?  (Matthew, 2026-10-27.)  Pure order theory about
F0, in the public library.

## The statement (`FreeIPLInAboveT3`)

    ∃ x : String → PLLFormula,
      (∀ a, atomFree (x a)) ∧ (∀ a, [t3] ⊢ x a) ∧
      ∀ A B, boxFree A → boxFree B → ([A] ⊢ B ↔ [h A] ⊢ h B),

    h A := A[a := x a, ⊥ := t3]                                   (`relG x`)

The variables are the strings `a`; `x a` is the generator for `a`.  Candidate
generators (the brief): the odd gaps `oddGap i = g(2i+1)`.

Companion statements: `TwoGenFaithful x₀ x₁` (no signed conjunction
`x₀^ε₁ ∧ x₁^ε₂` lies below `t3`; necessary for two generators),
`FreeIPL1InAboveT3` (one generator, `h₁ A = σ(A[p := ◯⊥])`).

## Status table

| statement                       | status | theorem |
|---------------------------------|--------|---------|
| `FreeIPLInAboveT3`              | OPEN   |         |
| `TwoGenFaithful (g1) (g3)`      | OPEN   |         |
| `FreeIPL1InAboveT3`             | OPEN   |         |

## Log

* 2026-10-27: statement written and committed before any proof (METHOD.md §1).
  Designed cells for the odd gaps decided with the subframe tableau
  (`pllfast`, `refbench fact`; untrusted producers, facts to be kernel-checked
  in the module): `(g3 ↠ t3) ↠ t3` PROVED, `(g1 ↠ t3) ↠ t3` REFUTED,
  `g1 ∨ (g1 ↠ t3)` REFUTED, `u ∧ t4 ↠ t3` PROVED.
