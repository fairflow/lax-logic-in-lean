# wip/f0RelCriterion.lean — status

The relative criterion for a faithful copy of PLL in an interval `[ξ, ζ]`.
Brief from the LaxLogic manager, 2026-11-02, conjecture approved by Matthew
the same day.  Branch `f0-relative-criterion`, cut from `origin/f0-nest-pll`
(PR #120, not yet on `main`: `wip/f0NestPLL.lean` is needed).

## Stage 1: the statements (committed before any proof, METHOD.md §1)

`rel ξ ζ y` the interval translation (`⊥ ↦ ξ`, `p ↦ y p`, `∧ ∨` kept,
`A → B ↦ (rel A ↠ rel B) ∧ ζ`, `◯A ↦ ◯(rel A) ∧ ζ`), `coreGen ξ ζ ρ p = (ρ p ∨ ξ) ∧ ζ`,
`gR = relB σ³⊥ xr`.  A formula `ξ` is *stable* when `◯ξ ⊣⊢ ξ`.

    (R0) RelClauses ξ ζ :     [ζ] ⊬ ◯ξ ↠ ξ  ∧  [ζ] ⊬ (◯ξ ↠ ξ) ↠ ξ
    (R1) RelNecessary :       FreeInPLL ξ ζ x  ⟹  RelClauses ξ ζ
    (R2) RelSufficient :      [ξ] ⊢ ζ,  RelClauses ξ ζ,  Fresh ρ ξ ζ  ⟹  FreeInPLL ξ ζ (coreGen ξ ζ ρ)
    (R3) RelCriterion :       [ξ] ⊢ ζ,  Fresh ρ ξ ζ  ⟹  (FreeInPLL ξ ζ (coreGen ξ ζ ρ) ⟺ RelClauses ξ ζ)

Corollaries of (R3), each stated on its own:

    ClausesStrict :        RelClauses ξ ζ  ⟹  [ζ] ⊬ ξ  ∧  [ζ] ⊬ ◯ξ
    ClausesBoxFree :       ξ, ζ ◯-free  ⟹  (RelClauses ξ ζ ⟺ [ζ] ⊬ ξ)
    RelCriterionBoxFree :  (R3) for ◯-free ξ, ζ          (the form of coreLemmaPLL)
    RelCriterionTop :      (R3) at ζ = ⊤, every ξ        (closed ξ: the form of baseCriterion)
    RelClausesMono :       [ζ′] ⊢ ζ,  RelClauses ξ ζ  ⟹  RelClauses ξ ζ′

Transport (R4):

    RelMain :     a, b, x variable-free,  FreeInPLL a b x,  [ξ] ⊢ ζ,  RelClauses ξ ζ
                    ⟹  FreePLLIn (rel a b x ξ) (rel a b x ζ)
    RelInGR :     [ξ] ⊢ ζ,  RelClauses ξ ζ  ⟹  FreePLLIn (gR ξ) (gR ζ)
    RelNestAll :  the tower NestPLL.towerP with  ∀ d, [ξ_d] ⊢ ζ_d ∧ RelClauses ξ_d ζ_d
                    ⟹  the conclusions of NestAllPLL at every depth

Weakenings (expected REFUTED):

    RelSufficientFirst :   (R2) with the first clause only    (witness ξ = ¬◯⊥, ζ = ⊤)
    RelSufficientSecond :  (R2) with the second clause only   (witness ξ = ◯p, ζ = ⊤)

Added at Stage 1 from the pen refutation stage:

    RelSufficientDisj :    (R2) with the one clause  [ζ] ⊬ (◯ξ ↠ ξ) ∨ ((◯ξ ↠ ξ) ↠ ξ)
    RelCopyNecessary :     FreeInPLL ξ ζ x  ⟹  TopAvoid ξ ζ
                             (TopAvoid ξ ζ :  ∀ C closed,  [ζ] ⊢ C[⊥ := ξ]  ⟹  ⊢ C)
    RelCopyCriterion :     [ξ] ⊢ ζ,  Fresh ρ ξ ζ  ⟹  (FreeInPLL ξ ζ (coreGen ξ ζ ρ) ⟺ TopAvoid ξ ζ)

Status of every statement at Stage 1: OPEN (`Prop` definitions only, no
theorem, no `sorry`).

### Pen refutation stage (to be kernel-checked at Stage 2)

The manager's route for ⟸ attaches two different up-sets above the copy of a
countermodel `K`: the worlds that see `S` get one, the worlds that see a world
with no `S` above get the other.  A world of `K` that sees both must then
force `ζ`, and nothing in the two clauses controls that.

* `ξ = ⊥`, `ζ = t3 = ◯⊥ ∨ ¬◯⊥` (closed).  Both clauses hold (`[t3] ⊬ ¬◯⊥` on
  one world outside `S`; `[t3] ⊬ ¬¬◯⊥` on one world in `S`).  But
  `[rel ⊤] ⊢ rel t3` while `⊬ t3`, so `[⊥, t3]` carries no faithful copy for
  any generators.  Expected: (R2), (R3), (R4) REFUTED.
* `ξ = ⊥`, `ζ = t6`: even the one-clause form `RelSufficientDisj` holds
  (the root of `Tfork` forces `t6` and refutes `¬◯⊥ ∨ ¬¬◯⊥`), and `C = t6`
  kills the copy.  Expected: `RelSufficientDisj` REFUTED.
* `ζ = p ∨ ¬p` (◯-free), `ξ = (p ∧ ¬◯⊥) ∨ (¬p ∧ ◯⊥)`: the first clause holds
  only on the `p` side, the second only on the `¬p` side; `C = ¬◯⊥ ∨ ¬¬◯⊥`
  gives `[rel ⊤] ⊢ rel C`, `⊬ C`.  Expected: (R2) REFUTED with a ◯-free top.
* At `ζ = ⊤` the copy of `K` forces `ζ` trivially, and the two-sided
  construction `TS` goes through with atoms (terminal clusters take the atoms
  of the matching side).  Expected: `RelCriterionTop` PROVED for open `ξ`.
* Monotonicity: `[ζ] ⊬ D` implies `⊬ D`, so a pair whose clauses hold
  relative to `ζ` but fail at `⊤` cannot exist (`RelClausesMono`).

## Builds

| stage | command | exit | wall time | free disk before |
|-------|---------|------|-----------|------------------|
| 1 | `gtimeout 3600 lake build wip.f0RelCriterion -q` | 0 | 59.2 s (builds `wip.f0NestPLL` too) | 100,194 MB |
