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

## Stage 3 — proofs (2026-11-02 14:28 CET)

Every statement of stage 1 is PROVED, each pinned `[propext, Quot.sound]`
by `#axioms_within` (no `Classical.choice`, no `sorryAx`, no
`native_decide`); the pin gate is watched failing (`#guard_msgs` on the
empty bound for `graded_exists`).

| id | representatives | quotient | status |
|---|---|---|---|
| C1 | `c1` | `sigCol_nucImpLat : NucImpLat leQ opsQ`, `nucQ_meet` | PROVED [pext,Q] |
| C2 | `stageCompat`, `stageEmb`, `stageHom`, `universal` | `iotaQ_compat`, `iotaQ_le_iff`, `iotaQ_eq_iff`, mediating map `liftU` | PROVED [pext,Q] |
| C3 | `shiftExtends`, `shiftOrderIso`, `unshiftOrderIso`, `shiftInverse`, `shiftHom`, `unshiftStage` | `shiftQ_iotaQ`, `unshiftQ_iotaQ`, `shiftQ_unshiftQ`, `unshiftQ_shiftQ`, `shiftQ_le_iff`, `shiftQ_hom` | PROVED [pext,Q] |
| C4 | `botStrict`, `noLowerBound`, `coinitial`, `noLeast` | `iotaQ_bot_strict`, `no_lower_bound`, `no_least` | PROVED [pext,Q] |
| C5 | `topIff`, `fixedTop` | `shiftQ_fixed_iff : S X = X ↔ X = ⊤` | PROVED [pext,Q] |
| C6 | `gradePow`, `gradeShift`, `gradeNotTop`, `gradeInj`, `gradeSurj`, `sigImageDec` | `graded_exists`, `graded_unique`, `shiftQ_powQ`, `graded_ne_top` | PROVED [pext,Q] |
| C7 | `notUpset`, `notDownset`, `filterUnion` | `iota0_not_convex`, `iota0_not_downset`, `filter_union` | PROVED [pext,Q] |

Findings.

* **The common-stage lemma** (`leP_iff_at`) carries every law: for
  `n + k = m + j`, `(n, φ) ≤ (m, ψ) ⟺ σᵏ φ ⊢ σʲ ψ` (from `sigN_faithful`).
* **C4 needs no finite-model argument.**  `(m, χ) ≤ ιₘ₊₁ ⊥` reduces by
  faithfulness to `σχ ⊢ ⊥`, and `t3 ⊢ σχ`, `t3 ⊬ ⊥`.  So the stage bottoms
  have no lower bound and the colimit has no least element; they are also
  coinitial (`ιₘ ⊥ ≤ (m, χ)`).
* **C6 survives and is PROVED, choice-free.**  `SigCol ∖ {⊤}` is in
  bijection with `ℤ × (L₀/⊣⊢)`, `(k, y) ↦ Sᵏ (ι₀ y)`, with `S` acting as
  `k ↦ k + 1`.  The decision procedure for `x ∈ σᵈ(F0)` (needed for
  existence, not for uniqueness): `τ` (`tau`), the restriction of a formula
  to the old worlds of the two-top extension `ext M` of
  `wip/f0SelfSim.lean`, is a syntactic left inverse of `σ`
  (`tau_sig : τ (σψ) ⊣⊢ ψ`, for every formula), whence
  `x ∈ σ(F0) ⟺ σ(τ x) ⊣⊢ x` (`inSig1_iff`) and
  `x ∈ σᵈ⁺¹(F0) ⟺ x ∈ σ(F0) ∧ τ x ∈ σᵈ(F0)` (`inSig_succ_iff`); `⊣⊢` is
  decided by `FRJ.Gbu.W.decideLaxND` (`decInSig`, a `Decidable`).  The bound
  on `d` is `InsideOut.orbit_order_limit` (choice-free).  `orbits_vs_L0`
  (excluded middle) is not used.  Validation: `ι₀ t3`, `ι₀ t5`, `ι₁ ⊥` at
  grades `1`, `0`, `−1` (`grade_t3`, `grade_t5`, `grade_bot1`,
  `grades_distinct`; `bot_L0`, `cellT5`).
* **C7.**  `ι₀(F0)` is a subalgebra, but not convex (`ι₀ ⊥ ≤ ι₁ t5 ≤ ι₀ ⊤`,
  `ι₁ t5 ∉ ι₀(F0)`) and not a down-set (`ι₁ ⊥ ≤ ι₀ ⊥`, `ι₁ ⊥ ∉ ι₀(F0)`): not
  an up-set, an interval or a principal filter.  The colimit is the
  increasing union of the principal filters `↑ιₙ ⊥`, each carried onto the
  next by `S⁻¹`, all order-isomorphic to `↑ι₀ ⊥` (the colimit of the
  intervals `[σⁿ⊥, ⊤]`).  OPEN: whether `↑ι₀ ⊥ ≅ F0` as posets.

Runs.

* `gtimeout 900 lake env lean wip/f0SigmaColimit.lean`: exit 0, no
  warnings (several iterations; the last clean).
* `gtimeout 3600 lake build wip.f0SigmaColimit`: exit 0, 14:27:16 to
  14:27:53 CET (37 s wall; the module itself 19 s; one module built, the
  rest replayed from the seeded cache).  `df` before: 100610 MB available.
