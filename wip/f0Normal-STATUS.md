# wip/f0Normal.lean — status

A filter of F0 that is not normal: the designed witness

    d k := ρ k ↠ t7,    F₇ := ⋃_{k ≥ 2} ↑(d k),

with ρ k = rel (rn (2k+1)) the relativised odd rungs of `wip/f0T6.lean`.
A filter F is normal when F = upperBounds (lowerBounds F).

Pure order theory about F0 = `RNClass`, in the public library.  Pins
expected `[propext, Quot.sound]`, no `Classical.choice`.

## Statements (`def … : Prop`)

| name                 | statement                                                      | status |
|----------------------|----------------------------------------------------------------|--------|
| `NotAllNormal`       | ∃ F, IsFilter F ∧ upperBounds (lowerBounds F) ≠ F              | OPEN   |
| `Star`               | every world of every finite subframe model forces some ρ k     | OPEN   |
| `StarOdd`            | the same for the odd rungs t (2k+1)                            | OPEN   |
| `SupRho`             | IsLUB (range ρ) ⊤                                              | OPEN   |
| `SupOddRungs`        | IsLUB (range odd) ⊤                                            | OPEN   |
| `Descending`         | ∀ k, d (k+1) ≤ d k                                             | OPEN   |
| `StrictlyDescending` | ∀ k ≥ 2, ¬ d k ≤ d (k+1)                                       | OPEN   |
| `LowerBound`         | ∀ k, t7 ≤ d k                                                  | OPEN   |
| `GreatestLowerBound` | ∀ y, (∀ k, y ≤ d (k+2)) → y ≤ t7                               | OPEN   |
| `F7IsFilter`         | IsFilter F₇                                                    | OPEN   |
| `F7Meet`             | IsGLB F₇ t7                                                    | OPEN   |
| `F7NonPrincipal`     | ∀ m, F₇ ≠ Ici m                                                | OPEN   |
| `F7NotNormal`        | upperBounds (lowerBounds F₇) ≠ F₇                              | OPEN   |

## Route

* Order facts on `RNClass` unfold to the semantic `Le` (truth in every
  constraint model), so (a), (b), (c) are direct model arguments.
* (d), `SupRho`, `SupOddRungs` go through the choice-free bridge
  `SubframeModel.CF.completeness_imp` / `completeness` (pinned
  `[propext, Quot.sound]`), NOT through `le_iff_nonempty` /
  `consequence_iff_derivable`, which carry `Classical.choice` (checked
  2026-10-25 by `#print axioms` in `_out/probe.lean`).  The transfer
  `SubframeModel.toConstraint_force` is also choice-tainted (a classical
  case split on `S`); it is re-proved here for `FinDec` models, where `S`
  is decidable.
* (★) by descent on the number of proper successors
  (`FRJ.countP_lt_countP`), generic in the sequence, instantiated at ρ
  and at the odd rungs.

## Gates

* Strictness countermodel at k = 1 must FAIL (x has type 3, not 2):
  `_out/f0Normal_gate.lean` — pending.
* Pin at `[propext]` must fail — pending.

## Log

* 2026-10-25: statements written and elaborated; lakefile registration;
  no proofs yet.
