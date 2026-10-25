# wip/f0Normal.lean — status

A filter of F0 that is not normal: the designed witness

    d k := ρ k ↠ t7,    F₇ := ⋃_{k ≥ 2} ↑(d k) = { y | ∃ k, d (k+2) ≤ y },

with ρ k = rel (rn (2k+1)) the relativised odd rungs of `wip/f0T6.lean`.
A filter F is normal when F = upperBounds (lowerBounds F).

Pure order theory about F0 = `RNClass`, in the public library.  Every pin
`[propext, Quot.sound]`; no `Classical.choice`.

## Statements (`def … : Prop`) and their theorems

| statement            | formula                                                        | theorem                | status |
|----------------------|----------------------------------------------------------------|------------------------|--------|
| `NotAllNormal`       | ∃ F, IsFilter F ∧ upperBounds (lowerBounds F) ≠ F              | `notAllNormal`         | PROVED |
| `Star`               | every world of every finite subframe model forces some ρ k     | `star`                 | PROVED |
| `StarOdd`            | the same for the odd rungs t (2k+1)                            | `starOdd`              | PROVED |
| `SupRho`             | IsLUB (range ρ) ⊤                                              | `supRho`               | PROVED |
| `SupOddRungs`        | IsLUB (range odd) ⊤                                            | `supOddRungs`          | PROVED |
| `Descending`         | ∀ k, d (k+1) ≤ d k                                             | `descending`           | PROVED |
| `StrictlyDescending` | ∀ k ≥ 2, ¬ d k ≤ d (k+1)                                       | `strictlyDescending`   | PROVED |
| `LowerBound`         | ∀ k, t7 ≤ d k                                                  | `lowerBound`           | PROVED |
| `GreatestLowerBound` | ∀ y, (∀ k, y ≤ d (k+2)) → y ≤ t7                               | `greatestLowerBound`   | PROVED |
| `F7IsFilter`         | IsFilter F₇                                                    | `F7_isFilter`          | PROVED |
| `F7Meet`             | IsGLB F₇ t7                                                    | `F7_meet`              | PROVED |
| `F7NonPrincipal`     | ∀ m, F₇ ≠ Ici m                                                | `F7_nonPrincipal`      | PROVED |
| `F7NotNormal`        | upperBounds (lowerBounds F₇) ≠ F₇                              | `F7_not_normal`        | PROVED |

Also PROVED: `lowerBounds F₇ = Iic t7`, `upperBounds (lowerBounds F₇) = Ici t7`,
`t7 ∉ F₇`, `⊥ ∉ F₇` (the filter is proper).

## Route

* Order facts on `RNClass` unfold to the semantic `Le` (truth in every
  constraint model), so (a), (b), (c) are direct model arguments; no
  derivations are built.
* (b): the model family `M k` = `cmU` + `z ≤ oE, fl` + `x ≤ z, lad i (i < k),
  tops`; `force_base` (old worlds unchanged); at `x`: `d k`, not `t7`, no
  `ρ j` for `j ≤ k`, and `ρ (k+1)` for `k ≥ 2`.
* (d), `SupRho`, `SupOddRungs` go through the choice-free bridge
  `SubframeModel.CF.completeness_imp` / `completeness` (pinned
  `[propext, Quot.sound]`), NOT through `le_iff_nonempty` /
  `consequence_iff_derivable`, which carry `Classical.choice` (checked
  2026-10-25 by `#print axioms` in `_out/probe.lean`).  The transfer
  `SubframeModel.toConstraint_force` is also choice-tainted (a classical
  case split on `S`); re-proved here as `toConstraint_force_fd` for `FinDec`
  models, where `S` is decidable.
* (★) by descent on the number of proper successors
  (`nProper`, `FRJ.countP_lt_countP`), generic in the sequence
  (`exists_force_chain`), instantiated at ρ and at the odd rungs.

## Gates (both watched failing, 2026-10-25)

* `_out/f0Normal_gate.lean`: the template proof of `x ⊩ ρ (k+1)` run at
  `k = 1` FAILS at the `z` case (`omega` cannot prove `1 ≤ 0`); and in `M 1`
  `¬ x ⊩ ρ 2`, `x ⊩ ρ 3` are kernel-checked `[propext, Quot.sound]` (x has
  type 3, not 2).
* `_out/f0Normal_pin_gate.lean`: `#axioms_within notAllNormal [propext]`
  FAILS (needs `Quot.sound`); `[propext, Quot.sound]` passes.

## Log

* 2026-10-25: statements written and elaborated; lakefile registration.
* 2026-10-25: model family `M k` and forcing lemmas; k = 1 gate watched failing.
* 2026-10-25: all thirteen statements PROVED, pins `[propext, Quot.sound]`;
  pin gate watched failing at `[propext]`.  `lake build wip.f0Normal`: 10 s.
