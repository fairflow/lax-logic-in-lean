# wip/f0MeetCount.lean — status

The meet-only counting criterion (Matthew, 2026-10-27), on top of
`wip/f0FreeHAn.lean` (PR #99).  Public order theory about F0.  Pins
`[propext, Quot.sound]`; no `sorry`, no `native_decide`, no `Classical.choice`.
Statements committed before any proof (2071022); proofs in the following
commit.  Build: `gtimeout 900 lake build wip.f0MeetCount` (the module itself
15 s, 0 errors).

## Statements (`def … : Prop`, committed before any proof)

    MeetEmb n f      = f has vf values on the ◯-free formulas in p0 … p(n-1),
                       A ⊣⊢ B ⟺ f A ⊣⊢ f B, and f (A ∧ B) ⊣⊢ f A ∧ f B
    MeetCounting     = ∀ n K f, MeetEmb n f → TypeBound (f ⊥) K → 2ⁿ ≤ K
    NoMeetCopyH2 b   = ¬ ∃ f, MeetEmb 2 f ∧ f ⊥ ⊣⊢ b
    NoFreeHA2AnyNeg  = ∀ x₀ x₁ vf, ∀ y₀ y₁, [x₀ ∧ y₀] ⊢ t3 → [x₁ ∧ y₁] ⊢ t3 →
                         ∃ ε, ⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3   (x^false read as y)
    MeetEmbH1        = MeetEmb 1 h₁

with `d_ε = signedConj n ε = ⋀_{i<n} pᵢ^εᵢ` (`conjUpTo`, `padB`), `p^true = p`,
`p^false = p ↠ ⊥`.  `TypeBound b K` is `f0FreeHAn`'s: a table of `K` variable-free
theories and a type function such that every `b`-maximal world has the theory of
its type.  Nothing is assumed about `∨`, `↠` or `⊥` under `f`.

## Status table

| statement | formula | status |
|-----------|---------|--------|
| `meet_counting`, `meetCounting : MeetCounting` | `MeetEmb n f → TypeBound (f ⊥) K → 2ⁿ ≤ K` | PROVED |
| `typeBound_bot` | `TypeBound ⊥ 2` (k(⊥) ≤ 2) | PROVED |
| `typeBound_t3` | `TypeBound t3 3` (k(t3) ≤ 3) | PROVED |
| `typeBound_interd` | `b ⊣⊢ b' → TypeBound b K → TypeBound b' K` | PROVED |
| `noMeetCopyH2_bot` | `NoMeetCopyH2 ⊥` | PROVED |
| `noMeetCopyH2_t3` | `NoMeetCopyH2 t3` | PROVED |
| `countingCriterion` | `CountingCriterion` (of `f0FreeHAn`) | PROVED |
| `noFreeHA2_anyNeg` | `NoFreeHA2AnyNeg` | PROVED |
| `meetEmb_h1`, `meetEmbH1 : MeetEmbH1` | `MeetEmb 1 h₁` | PROVED |
| `pvar_injective` | `pvar i = pvar j → i = j` | PROVED |
| `signedConj_not_bot`, `signedConj_disj` | `⊬ d_ε ↠ ⊥`; `[d_ε ∧ d_ε'] ⊢ ⊥` for `ε ≠ ε'` | PROVED |
| the ◯-free instance (rule 8) | see "Refutation stage" (iii) | degenerate, recorded, not mechanised |

Every pin is `#axioms_within … [propext, Quot.sound]` (19 pins, all pass in the
build).  `typeBound_t3` in fact lies within `[propext]` (gate log below); the
uniform pin is kept as ordered.

## The proof of `meet_counting`

For `ε : Fin n → Bool` let `d_ε = ⋀_{i<n} pᵢ^εᵢ` and `a = f ⊥`.

1. `⊬ d_ε ↠ ⊥` (`signedConj_not_bot`): the one-world IPC model with
   `v(pᵢ) = εᵢ` forces `d_ε`; soundness (`SubframeModel.CF.soundness₁`).
   The valuation is a lookup `valB n ε a = lookup (padB n ε) a n` over
   `pvar 0 … pvar (n-1)`, correct at `pvar l` because `pvar` is injective.
2. `[d_ε ∧ d_ε'] ⊢ ⊥` for `ε ≠ ε'` (`signedConj_disj`): a bit `l < n` differs;
   project `pₗ` and `pₗ ↠ ⊥` out of the two conjunctions.
3. `f` is monotone (`MeetEmb.mono`): `[A] ⊢ B` gives `A ⊣⊢ A ∧ B`, faithfulness
   gives `f A ⊣⊢ f (A ∧ B) ⊣⊢ f A ∧ f B`, so `[f A] ⊢ f B`.
4. For every `ε` there is an `a`-maximal world forcing `f d_ε` (`exists_cell`):
   `[f d_ε] ⊬ a`, since otherwise `f d_ε ⊣⊢ a` (3) and by faithfulness
   `d_ε ⊣⊢ ⊥`, against (1); completeness `SubTab.complete` (choice-free) gives a
   finite subframe model with a world forcing `f d_ε` and refuting `a`;
   `exists_bmax` (descent, the copy of `exists_rmax` at base `a`) gives an
   `a`-maximal world above it, which still forces `f d_ε` (`force_mono`).
5. Two patterns of one type coincide: if the worlds of (4) for `ε, ε'` have
   the same type, the first forces `f d_ε'` too (a type is the variable-free
   theory, and `f d_ε'` is variable-free), hence forces
   `f d_ε ∧ f d_ε' ⊣⊢ f (d_ε ∧ d_ε')` and by (2), (3) forces `a`, against
   `BMax`.  So `ε = ε'`, bit by bit (`Nat.eq_of_testBit_eq`,
   `Nat.testBit_lt_two_pow`; the patterns are indexed by `i < 2ⁿ`).
6. `rel_pigeon`: `N` indices, each related to some `k < K`, no `k` shared by
   two indices, give `N ≤ K`.  Nothing is chosen: the cells exist in `Prop`
   only and the relation is `∃ M w, BMax a M w ∧ force w (f d_ε) ∧ ty w = k`.

## Corollaries

* (a) `typeBound_bot : TypeBound ⊥ 2`: a top world forces `◯⊥` or `¬◯⊥`
  (`hasS`), and then has theory `Tn` or `Te` (`force_ne_of_hasS`,
  `force_e_of_not_hasS`, from `force_e_iff_Te`, `force_ne_iff_Tn` of
  `f0FreeIPL`).  `typeBound_t3 : TypeBound t3 3`: a `t3`-maximal world is
  `RMax` and has one of the theories `Tmax S N` with `(S, N) ∈ {(1,0), (1,1),
  (0,1)}` (`rmax_force`, `rmax_inS_or_hasN`).
* (b) `noMeetCopyH2_bot`, `noMeetCopyH2_t3`: a `MeetEmb 2 f` with
  `f ⊥ ⊣⊢ ⊥` (resp. `t3`) would give `4 ≤ 2` (resp. `4 ≤ 3`) by
  `meet_counting` and `typeBound_interd`.
* (c) `countingCriterion`: a faithful relativisation `relB b x` is a
  `MeetEmb n` (`relB` of `A ∧ B` is `relB A ∧ relB B`, so (meet) is `Interd.refl`),
  hence `FreeHAnAbove b n → TypeBound b K → 2ⁿ ≤ K`.
* (d) `noFreeHA2_anyNeg`: from `noFreeHA2` (`f0FreeIPL`), because
  `[x ∧ y] ⊢ t3` gives `[y] ⊢ x ↠ t3`, so `x^ε` read with `y` is below `x^ε`
  read with `↠ t3` (`sgnY_le_sgn`), and `(x₀^ε₁ ∧ x₁^ε₂) ↠ t3` is antitone in
  the conjunction.

## Refutation stage (designed checks, METHOD.md; no sweep)

* (i) Non-vacuity: `meetEmb_h1 : MeetEmb 1 h₁`, with `h₁ A = σ(embed A)`
  (`f0FreeIPL`), `h₁ ⊥ = t3`; vf by `sig_vf`, faithful by `freeIPL1`, meet
  by `Interd.refl`.  The criterion reads `2 ≤ k(t3) = 3`: consistent.
* (ii) `n = 2` over `σ²⊥`: the four cells `cell_00 … cell_11` of
  `twoGenPatterns_x0_x1` (`f0FreeHAn`) are four pairwise separated
  `σ²⊥`-maximal worlds; the criterion needs `4 ≤ k(σ²⊥)`, and
  `base2_unbounded` gives `k(σ²⊥) = ∞`: consistent.  No refutation.
* (iii) Rule 8, the ◯-free instance: the variable-free ◯-free formulas are
  `⊥` and `⊤` up to `⊣⊢`, so a `MeetEmb n f` with ◯-free values exists only
  for `n = 0` (for `n ≥ 1`, `f p₀` would be `⊥` or `⊤`, and `p₀` is neither:
  faithfulness fails), where the criterion reads `1 ≤ K`, and the IPC type
  count at `⊥` is `k(⊥) = 1`.  Degenerate; recorded, not mechanised.  In PLL
  `k(⊥) = 2`, since `◯⊥` separates the top worlds.

## Gates (watched failing)

`_out/f0MeetCount_gate.lean` (git-ignored; `gtimeout 540 lake env lean
_out/f0MeetCount_gate.lean`), run 2026-10-27 against the final build; every
check fails as expected:

* `#axioms_within meet_counting [propext]` → "depends on Quot.sound, which
  the bound does not allow".
* `#axioms_within typeBound_t3 []` → "depends on propext".  (The first run
  tried `[propext]` for `typeBound_t3` and it PASSED: `typeBound_t3` uses no
  `Quot.sound`; the gate was tightened to `[]`.)
* `#axioms_within countingCriterion [propext]` → "depends on Quot.sound".
* Tampered bound `TypeBound t3 2` by the same script as `typeBound_t3` with a
  two-row table (`t3Ts2 = [Tmax 1 0, Tmax 1 1]`, the `¬ InS` worlds sent to
  row 1): rejected at the `¬ InS` case,
  "Type mismatch … has type `M.force w φ ↔ Tmax false true φ = true` but is
  expected to have type `M.force w φ ↔ Tmax true true φ = true`".

Earlier, during development: the first `valB` read the sign off
`String.length`; `String.length_ofList` (also `String.toList_ofList`,
`String.ofList_inj`, `String.ofList_injective`, `List.utf8Decode?_utf8Encode`)
is `[propext, Classical.choice, Quot.sound]`, and the pins of
`signedConj_not_bot` and everything downstream FAILED with "depends on
Classical.choice".  Replaced by the lookup valuation and `pvar_injective`
from the UTF-8 byte size (`String.toByteArray_ofList`, `List.utf8Encode_cons`,
`ByteArray.size_append`, all within `[propext, Quot.sound]`).

## Skips

None.  No `lake exe`, no full build, no sweep.

## Log

* 2026-10-27: statements written and committed before any proof (METHOD.md §1), 2071022.
* 2026-10-27 19:52 GMT: all proofs in; module built, 19 pins pass; gates run
  and watched failing; this note.
