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
cannot exist: `[ζ] ⊬ D` implies `⊬ D` (`RelClausesMono`, stage 3).

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

Only `wip.f0RelCriterion` (and, at stage 1, its new dependency
`wip.f0NestPLL`) was built; every other module replayed.  No `lake exe`.  No
decider was run.  Skips and caps: none.
