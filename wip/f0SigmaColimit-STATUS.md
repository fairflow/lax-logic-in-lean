# S2: the colimit of the σ-chain — status

Branch `f0-sigma-colimit` (local, no upstream).  Module
`wip/f0SigmaColimit.lean`, registered at the end of the `wipshared` globs.

## Stage 1 — statements (2026-11-02 14:10 CET)

The construction and the statements are committed before any proof.
Every statement is a `Prop` definition in `PLLND.F0.SigmaColimit.Stmt`,
stated on representatives `(n, φ)` (`Pre`: a stage and a closed formula),
with `leP` for the order and `rP` for equality in the colimit:

    (n, φ) ≤ (m, ψ)   iff   σᵐ φ ⊢ σⁿ ψ
    (n, φ) ~ (m, ψ)   iff   σᵐ φ ⊣⊢ σⁿ ψ
    (n, φ) ⊓ (m, ψ) = (n + m, σᵐ φ ∧ σⁿ ψ),   ⊔ and ↠ likewise
    j (n, φ) = (n, ◯φ),   ⊤ = (0, ⊤)
    ιₙ φ = (n, φ),   S (n, φ) = (n, σφ),   S⁻¹ (n, φ) = (n + 1, φ)

`SigCol := Quot rP`.  A *nuclear implicative lattice* is a lattice with
top and relative pseudocomplement (an implicative lattice; Rasiowa's
relatively pseudo-complemented lattice) with a nucleus (inflationary,
idempotent, meet-preserving); its axioms are the fields of
`NucImpLatPre` / `NucImpLat`.

| id | statement | Lean |
|---|---|---|
| C1 | the representatives satisfy the nuclear implicative lattice axioms up to `~` | `Stmt.C1` |
| C2 | `ιₙ₊₁ ∘ σ ~ ιₙ` | `Stmt.StageCompat` |
| C2 | `ιₙ φ ≤ ιₙ ψ ↔ φ ⊢ ψ` | `Stmt.StageEmb` |
| C2 | `ιₙ` preserves `⊤ ∧ ∨ ↠ ◯` | `Stmt.StageHom` |
| C2 | universal property, for every type `A` and cocone `(fₙ)` (`⊣⊢`-invariant, `fₙ₊₁ ∘ σ = fₙ`): unique `u` with `u ∘ ιₙ = fₙ`; `u` a homomorphism for any `Ops A` when every `fₙ` is; `u` monotone for any `Prop`-valued relation when every `fₙ` is | `Stmt.Universal` |
| C3 | `S ∘ ιₙ = ιₙ ∘ σ`; `S`, `S⁻¹` order embeddings; `S S⁻¹ ~ id ~ S⁻¹ S`; `S` a homomorphism; `S⁻¹ ιₙ = ιₙ₊₁` | `Stmt.ShiftExtends`, `ShiftOrderIso`, `UnshiftOrderIso`, `ShiftInverse`, `ShiftHom`, `UnshiftStage` |
| C4 | `ιₙ₊₁ ⊥ < ιₙ ⊥`; `(m, χ) ≰ ιₘ₊₁ ⊥`; `ιₘ ⊥ ≤ (m, χ)`; no least element | `Stmt.BotStrict`, `NoLowerBound`, `Coinitial`, `NoLeast` |
| C5 | `x ~ ⊤ ↔ ⊢ x.fm`; `S x ~ x ↔ x ~ ⊤` | `Stmt.TopIff`, `FixedTop` |
| C6 (conjecture) | `grP k y ~ Sᵏ (ι₀ y)`; `S (grP k y) ~ grP (k+1) y`; `grP k y ≁ ⊤` for `y ∈ L₀`; uniqueness of `(k, y)`; existence for every `x ≁ ⊤`; membership in `σᵈ(F0)` decided | `Stmt.GradePow`, `GradeShift`, `GradeNotTop`, `GradeInj`, `GradeSurj`, `SigImageDec` |
| C7 (question) | `ι₀(F0)` not an up-set (`ι₀ ⊥ ≤ ι₁ t5 ∉ ι₀(F0)`); not a down-set (`ι₁ ⊥ ≤ ι₀ ⊥`, `ι₁ ⊥ ∉ ι₀(F0)`); the colimit is the union of the principal filters `↑ιₙ ⊥`, `S⁻¹` carrying each onto the next | `Stmt.NotUpset`, `NotDownset`, `FilterUnion` |
| cell | `ι₁ ⊥ < ι₀ ⊥` | `Stmt.CellBot` |
| cell | `S ⊤ ~ ⊤`, `S (ι₀ ◯⊥) ≁ ι₀ ◯⊥` | `Stmt.CellShiftTop` |
| cell | `ι₀ t5 ≁ S (ι₀ z)` for every closed `z`; `t5 ∈ L₀` | `Stmt.CellT5` |

Checked: `lake env lean wip/f0SigmaColimit.lean` exit 0 (statements only).

## Stage 2 — designed cells (2026-11-02 14:13 CET)

All three cells PASS, kernel-checked, each pinned `[propext, Quot.sound]`.

| cell | verdict | proof | pin |
|---|---|---|---|
| `cellBot`: `ι₁ ⊥ < ι₀ ⊥` | pass | `sigN_bot_strict 0` (`⊥ ⊢ t3`, `t3 ⊬ ⊥`) | [pext,Q] |
| `cellShiftTop`: `S ⊤ ~ ⊤`; `S (ι₀ ◯⊥) = ι₀ ◯t3 ≁ ι₀ ◯⊥` | pass | `σ⊤ = t3 ↠ t3`; `◯t3 ⊬ ◯⊥` refuted by `M1` (one world, in `S`), `decide +kernel` (`nd_oT3_oBot`) | [pext,Q] |
| `cellT5`: `ι₀ t5 ≁ S (ι₀ z)` for closed `z`; `t5 ∈ L₀` | pass | `sig_not_onto` | [pext,Q] |

Gates and controls, watched failing:

* `gate_M1`: `M1` does not refute the derivable `◯⊥ ↠ ◯t3` (`refutes = false`).
* `gate_M0`: the one-world model outside `S` does not refute `◯t3 ↠ ◯⊥`.
* `ctrl_t3`: with `t3 = σ⊥` in place of `t5` the statement of `cellT5`
  fails: `ι₀ t3 ~ S (ι₀ ⊥)`.
* The swapped `CellBot` (`ι₀ ⊥ ≤ ι₁ ⊥` from the same proof term) is
  rejected; the error is pinned by `#guard_msgs`.

Run: `gtimeout 900 lake env lean wip/f0SigmaColimit.lean`, exit 0.
