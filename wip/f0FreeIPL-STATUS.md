# wip/f0FreeIPL.lean — status

Does the interval `[t3, ⊤]` of F0 contain a copy of the free Heyting algebra
on countably many generators?  (Matthew, 2026-10-27.)  Pure order theory about
F0, in the public library.  Every pin `[propext, Quot.sound]`; no
`Classical.choice`.

## The statement (`FreeIPLInAboveT3`)

    ∃ x : String → PLLFormula,
      (∀ a, atomFree (x a)) ∧ (∀ a, [t3] ⊢ x a) ∧
      ∀ A B, boxFree A → boxFree B → ([A] ⊢ B ↔ [h A] ⊢ h B),

    h A := A[a := x a, ⊥ := t3]                                   (`relG x`)

The variables are the strings `a`; `x a` is the generator for `a`.  Candidate
generators (the brief): the odd gaps `oddGap i = g(2i+1)`.

## Status table

| statement                                  | formula                                                              | theorem                  | status  |
|--------------------------------------------|----------------------------------------------------------------------|--------------------------|---------|
| `FreeIPLInAboveT3`                         | (above)                                                              | `not_FreeIPLInAboveT3`   | REFUTED |
| every assignment fails                     | ∀ x vf, ∃ A B ◯-free, [A] ⊬ B ∧ [h A] ⊢ h B                          | `not_faithful`           | PROVED  |
| no free pair                               | ∀ x₀ x₁ vf, ∃ ε, ⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3                              | `noFreeHA2`              | PROVED  |
| `TwoGenFaithful x₀ x₁`                     | ∀ ε, ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3                                          | `not_twoGenFaithful`     | REFUTED |
| `FreeIPL1InAboveT3` (one generator)        | [t3] ⊢ h₁ p ∧ ∀ A B ◯-free over p, [A] ⊢ B ↔ [h₁ A] ⊢ h₁ B            | `freeIPL1`               | PROVED  |

`x^true = x`, `x^false = x ↠ t3`; `h₁ A = σ(A[p := ◯⊥])`, `h₁ p = ◯t3`.

## The designed cells (odd gaps; kernel-checked certificates from `refbench fact`)

| cell                              | verdict | theorem         |
|-----------------------------------|---------|-----------------|
| `(g3 ↠ t3) ↠ t3`, i.e. h(¬¬q) = ⊤ for q ↦ g3 | PROVED (closed tableau) | `cell_g3_dneg` |
| `(g1 ↠ t3) ↠ t3`                  | REFUTED (3 worlds)      | `cell_g1_dneg` |
| `g1 ∨ (g1 ↠ t3)`, h(p ∨ ¬p) for p ↦ g1 | REFUTED (6 worlds) | `cell_g1_lem`  |
| `u ∧ t4 ↠ t3`, h(¬(p ∧ q)) = ⊤ for (u, t4) | PROVED (closed tableau) | `cell_u_t4` |
| IPC: `⊬ ¬¬q`, `[⊤] ⊬ ¬(p^ε₁ ∧ q^ε₂)` | PROVED (one-world models) | `ipc_dneg`, `ipc_negConj` |

The odd gaps are refuted by the first cell with the first IPC cell
(`oddGaps_refuted`): `g3 ↠ t3 ⊣⊢ t3`, so `g3` is REFUTED as a generator.
`g1` survives the one-variable cells; the general theorem kills every pair.

## The reason (the proof of `noFreeHA2`)

In a subframe model, `G = {t3 holds} = Gₑ ⊔ Gₙ` with `Gₑ = {◯⊥}`,
`Gₙ = {¬◯⊥}`, and every variable-free formula is constant on each
(`force_e_iff_Te`: classical value with `◯A ↦ ⊤`; `force_ne_iff_Tn`: with
`◯A ↦ A`).  A world maximal among those refuting `t3` has a theory
determined by two bits (`rmax_force`): `InS` (an `R`-world above it is in `S`)
and `HasN` (a `Gₙ`-world lies above it); `(false, false)` is impossible
(`rmax_inS_or_hasN`).  Three types of maximal world, four sign patterns
(`pattern`, `missing_not_mem`): the signed conjunction of a missing pattern
fails at every `R`-world of every finite subframe model (`exists_rmax`, by
descent on `Normal.nProper`), so its relative negation is a theorem
(`SubTab.complete`, choice-free).  Type patterns: `oddGap_patterns`
(`(g1, g3)`: `(1,1), (1,1), (0,1)`), `u_t4_patterns` (`(u, t4)`:
`(0,0), (0,1), (1,0)`), both by `decide`.

With `⊥` for `t3` there are two types (the two kinds of maximal world), so F0
itself has no free pair either; relativising to `t3` adds exactly one type.

## Gates (all three watched failing, 2026-10-27, `_out/f0FreeIPL_gate.lean`)

* `#axioms_within noFreeHA2 [propext]`, likewise `not_FreeIPLInAboveT3`,
  `freeIPL1`: FAIL (need `Quot.sound`); `[propext, Quot.sound]` passes.
* the closed tableau of `(g3 ↠ t3) ↠ t3` offered for `(g1 ↠ t3) ↠ t3`:
  REJECTED by `decide +kernel` ("proved that the proposition ... is false").
* `pattern true true uF t4 = (true, true)`: REJECTED by `decide`.

## Log

* 2026-10-27 09:3x: statement written and committed before any proof
  (METHOD.md §1), `c5c0246`.  Designed cells decided with the subframe tableau
  (`pllfast`, `refbench fact`; untrusted producers).
* 2026-10-27 10:03: cells kernel-checked; `noFreeHA2`, `not_faithful`,
  `not_FreeIPLInAboveT3` PROVED (the statement is REFUTED for every choice of
  generators); `freeIPL1` PROVED (one generator).  `lake build wip.f0FreeIPL`
  clean; gates watched failing.
