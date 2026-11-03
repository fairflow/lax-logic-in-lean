# wip/f0RelCriterion.lean — status

The relative criterion for a faithful copy of PLL in an interval `[ξ, ζ]`.
Brief from the LaxLogic manager, 2026-11-02, conjecture approved by Matthew
the same day.  Branch `f0-relative-criterion`, cut from `origin/f0-nest-pll`
(PR #120, not yet on `main`: `wip/f0NestPLL.lean` is needed).  Public order
theory about F0.

## Summary

All pins `[propext, Quot.sound]`; no `Classical.choice`, no `sorry`, no
`native_decide`.

**The conjecture is REFUTED** (`not_relSufficient`, `not_relCriterion`).  The
two clauses

    [ζ] ⊬ ◯ξ ↠ ξ        [ζ] ⊬ (◯ξ ↠ ξ) ↠ ξ

are necessary for a faithful copy of PLL in `[ξ, ζ]` (PROVED,
`relNecessary`), but not sufficient.  The smallest witness is closed:

    ξ = ⊥,  ζ = t3 = ◯⊥ ∨ ¬◯⊥:     [t3] ⊬ ¬◯⊥,   [t3] ⊬ ¬¬◯⊥,   yet   [t3] ⊢ t3   and   ⊬ t3,

so the interval `[⊥, t3]` carries no faithful copy of PLL for any generators.
It fails with a ◯-free top as well: `ζ = p ∨ ¬p`, `ξ = (p ∧ ¬◯⊥) ∨ (¬p ∧ ◯⊥)`,
where the first clause holds only on the `p` side and the second only on the
`¬p` side (`not_relSufficientBoxFreeTop`).  Strengthening the two clauses to
the one clause `[ζ] ⊬ (◯ξ ↠ ξ) ∨ ((◯ξ ↠ ξ) ↠ ξ)` does not help:
`ξ = ⊥`, `ζ = t6` (`not_relSufficientDisj`).

**Inside Matthew's range `σ³⊥ ≤ ξ < ζ ≤ ⊤`** it fails as well
(`not_relSufficientInRange`, stated with `∃ x`, any generators).  The readers'
copy `gR = relB σ³⊥ xr`, which is `σ³` on closed formulas, keeps both clauses
and the closed part, for all `ξ`, `ζ` (`relTransportGR`; closed form
`relTransportSig3`), because `gR(◯ξ ↠ ξ) = ◯gR ξ ↠ gR ξ`,
`gR(C[⊥ := ξ]) = C[⊥ := gR ξ]` for closed `C` (`gR_subBot`), and `gR` is
faithful.  So

    (σ³⊥, σ³t3) = σ³(D1),     (σ³⊥, σ³t6) = σ³(D2),     (gR ξ₃, gR (p ∨ ¬p)) = gR(D3)

all lie in the range, satisfy both clauses, and carry no faithful copy
(`sig3_D1`, `sig3_D2`, `gR_D3`).  The manager's pen argument was right.

**What is true.**  At the top `ζ = ⊤` the criterion holds for every `ξ`, open
or closed (PROVED, `relCriterionTop`):

    FreeInPLL ξ ⊤ (coreGen ξ ⊤ ρ)   ⟺   ⊬ ◯ξ ↠ ξ   ∧   ⊬ (◯ξ ↠ ξ) ↠ ξ,

extending `Endpoints.baseCriterion` from closed to open `ξ` (and giving it back,
`selfTopIff`).  For ◯-free `ξ`, `ζ` it holds too, and there the clauses say
just `[ζ] ⊬ ξ` (`relCriterionBoxFree`, `clausesBoxFree`).  Both kinds of pair
nest to every depth inside the readers' copy, mixed freely
(`goodNestAll`, `goodInGR`).

**The necessary condition in full** is `TopAvoid ξ ζ`: every closed `C` with
`[ζ] ⊢ C[⊥ := ξ]` is a theorem (PROVED necessary, `relCopyNecessary`; the two
clauses are its instances `C = ¬◯⊥`, `¬¬◯⊥`).  Whether it is sufficient for
the core generators is OPEN (`RelCopyCriterion`; at closed `ξ`, `ζ` it is the
OPEN `Endpoints.CopySelf`).  At `ζ = ⊤` the two instances already imply all of
it; for a general top they do not (D1, D2, D3).

## Status table

| statement | declaration | status |
|-----------|-------------|--------|
| (R0) `RelClauses` | definition | — |
| **(R1) `RelNecessary`** | `relNecessary` | **PROVED** |
| **(R2) `RelSufficient`** | `not_relSufficient` (D1) | **REFUTED** |
| **(R3) `RelCriterion`** | `not_relCriterion` (D1, direction `⟸`) | **REFUTED** |
| `ClausesStrict` | `clausesStrict` | PROVED |
| `ClausesBoxFree` | `clausesBoxFree` | PROVED |
| `RelCriterionBoxFree` | `relCriterionBoxFree` | PROVED |
| **`RelCriterionTop`** (open `ξ`) | `relCriterionTop` | **PROVED** |
| `RelClausesMono` (Stage 1, inclusion the wrong way round) | `not_relClausesMono` (cell E) | REFUTED |
| (R4) `RelMain` | `not_relMain` (D1 in the readers' copy) | **REFUTED** |
| (R4) `RelInGR` | `not_relInGR` (`[σ³⊥, σ³t3]`) | **REFUTED** |
| (R4) `RelNestAll` | `not_relNestAll` (depth one) | **REFUTED** |
| `RelSufficientFirst` | `not_relSufficientFirst` | REFUTED |
| `RelSufficientSecond` | `not_relSufficientSecond` | REFUTED |
| `RelSufficientDisj` | `not_relSufficientDisj` (D2) | REFUTED |
| `RelCopyNecessary` | `relCopyNecessary` | PROVED |
| `RelCopyCriterion` | direction `⟹` is `relCopyNecessary`; `⟸` | **OPEN** |
| `RelClausesUp` (stage 3) | `relClausesUp` | PROVED |
| `SelfTopIff` (stage 3) | `selfTopIff` | PROVED |
| `RelSufficientBoxFreeTop` (stage 3) | `not_relSufficientBoxFreeTop` (D3) | REFUTED |
| `RelSufficientBoxFreeBot` (stage 3) | `not_relSufficientBoxFreeBot` (D1) | REFUTED |
| `RelSufficientClosed` (stage 3) | `not_relSufficientClosed` (D1) | REFUTED |
| `NestOfCore` (stage 3) | `nestOfCore` | PROVED |
| `GoodCore`, `GoodMain`, `GoodInGR`, `GoodNestAll` (stage 3) | `goodCore`, `goodMain`, `goodInGR`, `goodNestAll` | PROVED |
| `RelTransportGR` (addition) | `relTransportGR` | PROVED |
| `RelTransportSig3` (addition) | `relTransportSig3` | PROVED |
| **`RelSufficientInRange`** (addition) | `not_relSufficientInRange` (`σ³(D1)`; also `sig3_D1`, `sig3_D2`, `gR_D3`) | **REFUTED** |

No theorem is sorried; the open statement is a `Prop` definition.

Estate check: `#axiom_sweep [wip.f0RelCriterion] allowing [propext, Quot.sound]`
passes on all 159 declarations; with `allowing []` 83 of 159 escape, and the
pin `#axioms_within relCriterionTop [propext]` is rejected (both gates watched
failing, `_out/rcsweep.lean`, untracked).

Addition (Matthew via the manager, 2026-11-02), stated as `Prop`s before the
proofs, in the same commit:

    RelTransportGR :        RelClauses (gR ξ) (gR ζ) ⟺ RelClauses ξ ζ,   TopAvoid (gR ξ) (gR ζ) ⟺ TopAvoid ξ ζ
    RelTransportSig3 :      ξ, ζ closed  ⟹  the same with σ³ in place of gR
    RelSufficientInRange :  [σ³⊥] ⊢ ξ,  [ξ] ⊢ ζ,  RelClauses ξ ζ  ⟹  ∃ x, FreeInPLL ξ ζ x

Added at stage 3, each stated as a `Prop` before its proof, in the same
commit:

    RelClausesUp :             [ζ] ⊢ ζ′,  RelClauses ξ ζ  ⟹  RelClauses ξ ζ′
    SelfTopIff :               a closed  ⟹  (SelfStep a ⊤ ⟺ RelClauses a ⊤)
    RelSufficientBoxFreeTop :  (R2) for ◯-free ζ
    RelSufficientBoxFreeBot :  (R2) for ◯-free ξ
    RelSufficientClosed :      (R2) for closed ξ, ζ
    NestOfCore :   FreeInPLL a b x,  FreeInPLL ξ ζ y  ⟹  FreeInPLL (rel a b x ξ) (rel a b x ζ) (rel a b x ∘ y)
    GoodPair ξ ζ : (ξ, ζ ◯-free ∧ [ξ] ⊢ ζ ∧ [ζ] ⊬ ξ)  ∨  (ζ = ⊤ ∧ RelClauses ξ ⊤)
    GoodCore :     GoodPair ξ ζ  ⟹  FreeInPLL ξ ζ (coreGen ξ ζ (freshRen ξ ζ))
    GoodMain, GoodInGR, GoodNestAll :  (R4) with GoodPair in place of [ξ] ⊢ ζ ∧ RelClauses ξ ζ

## Stage 3: the proofs

* (R1): faithfulness at the closed formulas `C = ¬◯⊥` and `C = ¬¬◯⊥` (both
  non-theorems): `[ζ] ⊢ ◯ξ ↠ ξ` gives `[rel ⊤] ⊢ rel ¬◯⊥`, and
  `[ζ] ⊢ (◯ξ ↠ ξ) ↠ ξ` gives `[rel ⊤] ⊢ rel ¬¬◯⊥`, semantically.  The generators
  are not read.
* `clausesBoxFree`: a ◯-free formula does not read `S` (`force_withS`); with
  `S = ∅` the formula `◯ξ` holds everywhere, with `S` everything `◯ξ ↠ ξ` does,
  so either clause failing gives `[ζ] ⊢ ξ`.  With `coreLemmaPLL` this is
  `relCriterionBoxFree`.
* `relCriterionTop`, direction `⟸`: the two-sided extension `TS` of
  `wip/f0Endpoints.lean`, unchanged in order and `S`, with a valuation
  (`TSA`).  A copy world `x` carries the fresh atom `ρ p` iff `x ⊩ p`, and an
  old atom `c` iff `c` holds at `m₁` when `x` sees `S` and at `m₂` when `x` sees
  a world with no `S` above it; the attached worlds keep their own atoms and
  carry every fresh atom.  This is hereditary (`taV_hered`).  The
  bisimulations of `TS` are bisimulations of `TSA` (`isBisim_TSA`) and respect
  every old atom (`atoms_K₁`, `atoms_K₂`, `atoms_In`, `atoms_Out`): a terminal
  cluster sees exactly one of the two sides.  So formulas without fresh atoms
  are invariant (`bisim_forceR`, `bisim_force` with an atom condition), `ξ`
  fails on the copy and holds above it, and the relativisation lemma with `◯`
  (`relB_transferO`) gives `rel A ⟺ A` on the copy (`tsa_transfer`).  The two
  sides come from the two clauses as in `sidesOfNd`, whose proof never read
  closedness (`sidesOfNdOpen`).  Nothing has to be checked against `ζ = ⊤`,
  which is why this case goes through and a general top does not.
* The refutations: `no_copy` is `Endpoints.necClosed` read through
  `copy_of_free`.  (R4): `gR t3 = t3[⊥ := σ³⊥]` (`relB_closed`), so `C = t3`
  kills `[σ³⊥, σ³t3]`; `rel σ³⊥ ⊤ xr` is `gR` up to `⊣⊢` (`rel_top_interd_gR`),
  which carries it to `RelMain` and to depth one of the tower.
* The corrected transport: `nestOfCore` is the proof of `NestPLL.nestPLL` with
  any inner copy in place of the core lemma; `goodCore` takes the copy from
  `coreLemmaPLL` or `relCriterionTop`; the tower is `NestPLL.towerP`.

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
  relative to `ζ` but fail at `⊤` cannot exist (`RelClausesUp`, stage 3; the Stage 1 `RelClausesMono` has the inclusion of tops the wrong way round, see the status table).


## Stage 2: the designed cells (refutation stage, CLAUDE.md rules 7 and 9)

Read off the rules; no sweep, no decider run.  Every cell is kernel-checked
(`SubTab.no` by `decide +kernel`, or a semantic derivation); pins
`[propext, Quot.sound]`.  `p = ""`, `q = "\x00"`; copy cells use the renaming
`Interval.Cells.ρc1` (`p ↦ "\x01"`, `q ↦ "\x02"`).  `no_copy` is the closed-part
necessary condition (`Endpoints.necClosed`): a closed `C` with `⊬ C` and
`[ζ] ⊢ C[⊥ := ξ]` leaves `[ξ, ζ]` without a faithful copy, whatever the
generators.

### (A) `ξ = ¬◯⊥`

| `ζ` | first clause | second clause | copy | declarations |
|-----|--------------|---------------|------|--------------|
| `⊤` | holds (`K0`) | fails (`⊢ (◯¬◯⊥ ↠ ¬◯⊥) ↠ ¬◯⊥`) | none (`C = ¬¬◯⊥`) | `a_top_c1`, `a_c2`, `a_no_copy` |
| `¬◯⊥ ∨ p` | holds (`K0p`: one world outside `S`, `p`) | fails | none | `a_neP_c1`, `a_c2`, `a_no_copy` |
| `t6` | holds (`K0`) | fails | none | `a_t6_c1`, `a_c2`, `a_no_copy` |

Consistent with the conjecture (both sides say "no copy").

### (B) the weakenings

| statement | witness | verdict | declaration |
|-----------|---------|---------|-------------|
| `RelSufficientFirst` | `ξ = ¬◯⊥`, `ζ = ⊤` | **REFUTED** | `not_relSufficientFirst` |
| `RelSufficientSecond` | `ξ = ◯p`, `ζ = ⊤` (second clause on `KS`; `⊢ ◯◯p ↠ ◯p`) | **REFUTED** | `not_relSufficientSecond` (`b_c1`, `b_c2`) |

### (C) non-stable `ξ` containing `◯`, clauses holding: the copy separates

| `ξ`, `ζ` | clauses | `[rel ⊤] ⊬ rel(◯q → q)` | `[rel ⊤] ⊬ rel O3` |
|----------|---------|-------------------------|--------------------|
| `t3`, `⊤` | hold (`c_t3_top`, from `baseYes_t3`) | `c_t3_top_Cq` (`ext K1`, 3 worlds) | `c_t3_top_O3` (`ext K3r`, 5 worlds) |
| `t3`, `t6` | hold (`c_t3_t6`: `Tfork`, `ext KS`) | `c_t3_t6_Cq` | `c_t3_t6_O3` |
| `◯p ∨ ¬◯p` (open), `⊤` | hold (`c_O2_top`: `Tfork`, `K2`) | `c_O2_top_Cq` (`TOq`, 3 worlds) | `c_O2_top_O3` (`TO3`, 4 worlds) |

The open cells are the two-sided construction by hand: `TOq` puts the
strict successors of the `Tfork` root (a world of `S` with `p` false, a world
outside `S`) above the one world of `K1`, which sees no `S`; `TO3` puts the
strict successor of the `K2` root (a world outside `S`) above the copy of
`K3`, all of whose worlds see `S`.  The copy worlds carry the matching side's
`p` (false) and `K`'s atoms renamed; the attached worlds carry every renamed
atom.

### (D) the counterexamples to (R2)

| pair | clauses | direct cell | declarations |
|------|---------|-------------|--------------|
| (D1) `ξ = ⊥`, `ζ = t3` | hold: `[t3] ⊬ ¬◯⊥` (`K0`), `[t3] ⊬ ¬¬◯⊥` (`KS`) | `C = t3`: `[t3] ⊢ t3`, `⊬ t3`: **no copy** | `d_t3_clauses`, `d_t3_no_copy` |
| (D2) `ξ = ⊥`, `ζ = t6` | `[t6] ⊬ ¬◯⊥ ∨ ¬¬◯⊥` (`Tfork`), so both clauses and the one-clause form hold | `C = t6`: **no copy** | `d_t6_disj`, `d_t6_clauses`, `d_t6_no_copy` |
| (D3) `ξ = (p ∧ ¬◯⊥) ∨ (¬p ∧ ◯⊥)`, `ζ = p ∨ ¬p` (◯-free top) | hold: first on the `p` side (`K0p`), second on the `¬p` side (`KS`) | `C = ¬◯⊥ ∨ ¬¬◯⊥` (`⊬`, `Tfork`; `[ζ] ⊢ C[⊥ := ξ]`, semantic): **no copy** | `d3_le`, `d3_clauses`, `nd_ne_nne`, `d3_disj`, `d3_no_copy` |

So (R2) and the `⟸` of (R3) FAIL on designed cells; the stage 3 theorems
`not_relSufficient`, `not_relCriterion` record it.  The shape: `ζ` lets the two
clauses be witnessed in different regions (D3: the `p` and `¬p` sides), or
`ζ` forces a closed non-theorem pushed down to `ξ` (D1, D2: `[ζ] ⊢ C[⊥ := ξ]`,
`⊬ C`), which the two instances `C = ¬◯⊥`, `¬¬◯⊥` do not detect.  At `ζ = ⊤`
the second shape is excluded by the base criterion and the first cannot
occur, since no top separates regions.

### (E) relative against absolute clauses

`RelClauses ⊥ ⊤` holds and `RelClauses ⊥ ◯⊥` fails (`[◯⊥] ⊢ ¬¬◯⊥`;
`e_top`, `e_not`).  A pair with the clauses relative to `ζ` but not at `⊤`
cannot exist: `[ζ] ⊬ D` implies `⊬ D` (`RelClausesUp`, stage 3).  The Stage 1 statement `RelClausesMono` had the inclusion of tops the wrong way round, and this cell refutes it (`not_relClausesMono`).

### Gates, watched failing

`gate_cells`: the checker returns `false` on derivable cells for the copy
tables (`TOq`, `TO3`, `ext K3r` on the image of the theorem `◯◯p → ◯p`), the
clause tables (`Tfork` on `[t3] ⊢ t3`, `KS` on `[◯⊥] ⊢ ¬¬◯⊥`) and the (D3)
clause tables on the derivable disjunction of `d3_disj`.

## Builds

Registered in `lakefile.toml` (the `wip` glob list, its own last line after
`wip.f0NestPLL`).  Build cache seeded by `cp -Rc` from
`~/Lean/nightly/lax-logic-in-lean/.lake`.

| stage | command | exit | wall time | free disk before |
|-------|---------|------|-----------|------------------|
| 1 | `gtimeout 3600 lake build wip.f0RelCriterion -q` | 0 | 59.2 s (builds `wip.f0NestPLL` too) | 100,194 MB |
| 2, body | `gtimeout 900 lake env lean wip/f0RelCriterion.lean` | 0 | 11.6 s | — |
| 2 | `gtimeout 3600 lake build wip.f0RelCriterion -q` | 0 | 15.4 s | 100,150 MB |
| 3, body | `gtimeout 900 lake env lean _out/rc3.lean` (stage 3 over the built module) | 1 (two elaboration errors, fixed) | 11.7 s | — |
| 3, body | the same, after the fixes | 0 | 12.7 s | — |
| 3 | `gtimeout 3600 lake build wip.f0RelCriterion -q` | 0 | 15.9 s | 100,124 MB |
| 3, sweep | `gtimeout 900 lake env lean _out/rcsweep.lean` | 1 (the two gate lines, by design) | 12.3 s | — |
| addition, body | `gtimeout 900 lake env lean _out/rc4.lean` (over the built module) | 0 | 11.5 s | — |
| addition | `gtimeout 3600 lake build wip.f0RelCriterion -q` | 0 | 15.9 s | 100,127 MB |
| addition, sweep | `gtimeout 900 lake env lean _out/rcsweep.lean` | 1 (the two gate lines, by design) | 12.3 s | — |

Only `wip.f0RelCriterion` (and, at stage 1, its new dependency
`wip.f0NestPLL`) was built; every other module replayed.  No `lake exe`.  No
decider was run: every table was designed by hand.  Skips and caps: none.
