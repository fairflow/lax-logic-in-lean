# wip/f0EmbedForms.lean — status

Three forms of a copy of a Heyting algebra in F0 (Matthew, approved
2026-10-28), the pairwise lemma, and the shift for `H₂`.  Public order theory
about F0.  No `sorry`, no `native_decide`, no `Classical.choice`.  Statements
committed before any proof (b1ee732); proofs in 66025dd.  Build:
`gtimeout 1800 lake build wip.f0EmbedForms` (the module itself 10 s, 0 errors,
0 warnings, 19 pins pass).

## The framework

A copy of a Heyting algebra `H` in F0 is a map `e : H → F0` of one of three
strengths:

| form | preserved | order | the rest |
|------|-----------|-------|----------|
| (H) Heyting embedding into `[b, ⊤]` | F0's `∧`, `∨`, `↠`; `⊥ ↦ b` | reflected | none |
| (L) lattice embedding | F0's `∧`, `∨` | reflected | `→` computed in the image |
| (O) order embedding | none | preserved and reflected | all operations computed in the image |

    (H) ⟹ (L) ⟹ (O)
    (H) with bottom b  ⟹  (O) with any bottom b' ≤ b        (the shift)

(H) ⟹ (L) and (L) ⟹ (O) hold by definition (`∧`-preservation makes `e`
monotone, `MeetEmb.mono` in `wip/f0MeetCount.lean`).  The shift is `shift`
below.

`FreeHAnAbove b n` (`wip/f0FreeHAn.lean`) is (H): `relB b x` is a
substitution, so it preserves `∧`, `∨`, `↠` by definition and sends `⊥` to `b`;
`[A] ⊢ B ⟺ [relB b x A] ⊢ relB b x B` is order preservation (⟹) plus order
reflection (⟸).

## Which results sit at which level

| result | form | `n` | bottom | status |
|--------|------|-----|--------|--------|
| `freeIPL1 : FreeIPL1InAboveT3` (`wip/f0FreeIPL.lean`) | (H) | 1 | `t3` | PROVED |
| `freePair : FreePair`, `freeHAnAbove_base2_two : FreeHAnAbove (base 2) 2` (`wip/f0FreePair.lean`) | (H) | 2 | `σ²⊥` | PROVED |
| `noFreeHA2`, `not_faithful`, `not_FreeIPLInAboveT3` (`wip/f0FreeIPL.lean`): no two variable-free generators are free over `t3` (some signed conjunction lies below `t3`) | not (H) | 2 | `t3` | PROVED |
| `meet_counting`, `noMeetCopyH2_bot`, `noMeetCopyH2_t3` (`wip/f0MeetCount.lean`): no (L) | not (L) | 2 | `⊥`, `t3` | PROVED |
| `shiftH2`, `shift2_orderEmb` (this module) | (O) | 2 | `⊥` | PROVED |
| `shiftMeetFails` (this module): the (O) copy above does not preserve `∧` | not (L) for this map | 2 | `⊥` | PROVED |
| (H) for `n ≥ 3` (`Conjecture` of `wip/f0FreeHAn.lean` beyond `n = 2`) | (H) | ≥ 3 | some `σᵐ⊥` | OPEN (an attempt over `σ³⊥` is in progress elsewhere) |
| (O) for `n ≥ 3` with bottom `⊥` | (O) | ≥ 3 | `⊥` | OPEN; follows from (H) at any base by the shift |

`¬ FreeHAnAbove t3 2` (variables `p`, `pp`) is not a named theorem; it is one
line from `countingCriterion` and `typeBound_t3` (`4 ≤ 3`), and also follows
from `noMeetCopyH2_t3`, since (H) ⟹ (L).

Why no (L) at `n = 2` with bottom `⊥` or `t3`: an (L)-copy is injective and
`∧`-preserving, so it is a `MeetEmb 2 f`, and `meet_counting` needs
`k(f ⊥) ≥ 2ⁿ = 4` types of `f ⊥`-maximal world; but `k(⊥) ≤ 2`
(`typeBound_bot`) and `k(t3) ≤ 3` (`typeBound_t3`).  At `σ²⊥` there is no
obstruction: `k(σ²⊥)` is unbounded (`base2_unbounded`), and (H), hence (L),
holds there (`freePair`).  The shift moves the bottom of that copy from `σ²⊥`
down to `⊥` at the price of (L): `h p ∧ h ¬p ⊣⊢ σ²⊥ ≠ ⊥`, while
`p ∧ ¬p ⊣⊢ ⊥` (`shiftMeetFails`), as `noMeetCopyH2_bot` requires.

## Lemma 1, the pairwise lemma (why (L) and (H) agree pairwise)

For Heyting algebras `H`, `K` and `e : H → K` with
`∀ x y, e x ≤ e y ⟺ x ≤ y` and `e (x ⊓ y) = e x ⊓ e y`, for all `a`, `c`:

    e (a ⇨ c) ≤ e a ⇨ e c
    e a ⇨ e c = e (a ⇨ c)  ⟺  ∃ d, e d = e a ⇨ e c

(`himp_le`, `himp_eq_iff`, packaged as `pairwiseHimp : PairwiseHimp`).  So
closing the image of an (L)-copy under `↠` is preservation of `↠` at every
pair, nothing more global.  Proof: `e (a ⇨ c) ⊓ e a = e ((a ⇨ c) ⊓ a) ≤ e c`;
if `e d = e a ⇨ e c` then `e (d ⊓ a) = e d ⊓ e a ≤ e c`, so `d ⊓ a ≤ c`,
`d ≤ a ⇨ c`, `e d ≤ e (a ⇨ c)`.  Stated over Mathlib's `HeytingAlgebra`
(`le_himp_iff`, `himp_inf_le`); F0 is not instantiated as a Mathlib
`HeytingAlgebra` in this module.

## The shift

Abstract (`shift_le`, `shift : Shift`): for a partial order `H` with `⊥` and
decidable equality, a preorder `K`, `e` with `∀ x y, e x ≤ e y ⟺ x ≤ y` and
`b' ≤ e ⊥`,

    ∀ x y,  e' x ≤ e' y ⟺ x ≤ y,        e' x = if x = ⊥ then b' else e x.

The only case with content is `x ≠ ⊥`, `y = ⊥`: `e x ≤ b' ≤ e ⊥` would give
`x ≤ ⊥`.

## Lemma 2, the shift for `H₂` with bottom `⊥`

With `h = relB σ²⊥ xs` of `wip/f0FreePair.lean` (`x₀ = ◯σ²⊥`,
`x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3)`), for ◯-free `A`, `B` in `p`, `pp`
(`boxFree`, `varsBelow 2`):

    (i)   [A] ⊬ ⊥ → [B] ⊬ ⊥ → ([A] ⊢ B ⟺ [h A] ⊢ h B)      shift2_pos
    (ii)  [A] ⊬ ⊥ → [h A] ⊬ ⊥                                shift2_sep
    (iii) [⊥] ⊢ h B                                          shift2_bot

packaged as `shiftH2 : ShiftH2`.  So sending the class of `⊥` to `⊥` and every
other class `A` to `h A` is an order embedding of `H₂` into F0.  No decision
procedure is used: the map is given as the relation

    ShiftVal A φ  :=  ([A] ⊢ ⊥ ∧ φ = ⊥) ∨ ([A] ⊬ ⊥ ∧ φ = h A)

and `shift2_orderEmb : ShiftOrderEmb` states

    ShiftVal A φ → ShiftVal B ψ → ([A] ⊢ B ⟺ [φ] ⊢ ψ).

Route for (ii): `[h A] ⊢ ⊥` gives `[h A] ⊢ h ⊥ = σ²⊥` by ex falso, and
`freePair_reflects` gives `[A] ⊢ ⊥`.  This does not use the consistency of
`σ²⊥`; it is the abstract shift with `b' = ⊥ ≤ σ²⊥`.

The `∧` observation (`shiftMeetFails : ShiftMeetFails`):

    [p ∧ ¬p] ⊢ ⊥                      ipc_meet_bot
    [p] ⊬ ⊥,  [¬p] ⊬ ⊥                ipc_p_imp_bot, ipc_np_imp_bot (one-world models)
    h p ∧ h ¬p ⊣⊢ σ²⊥                  shift2_meet_le, shift2_meet_ge
    [σ²⊥] ⊬ ⊥                          b2_consistent (one world, no S-point)
    [h p ∧ h ¬p] ⊬ ⊥                   shift2_meet_not_bot

so `e p ∧ e ¬p ≰ e (p ∧ ¬p) = ⊥`.

## Pins

| declarations | pin |
|--------------|-----|
| `himp_le`, `himp_eq_iff`, `pairwiseHimp`, `shift_le`, `shift`, `shift2_bot`, `ipc_meet_bot`, `shift2_meet_le`, `shift2_meet_ge` | `[]` (no axioms) |
| `shift2_pos`, `shift2_sep`, `shiftH2`, `shift2_orderEmb`, `b2_imp_bot`, `b2_consistent`, `ipc_p_imp_bot`, `ipc_np_imp_bot`, `shift2_meet_not_bot`, `shiftMeetFails` | `[propext, Quot.sound]` |

Every pin is `#axioms_within`; the sets were read off `#print axioms`.

## Gates (watched failing)

A scratch file run with `lake env lean` against the final build, 2026-10-28:

* A tampered certificate (`⊬ p ↠ ⊥` with `p` false at the one world) is
  rejected: "Tactic `decide` proved that the proposition
  `SubTab.no.check (pP ↠ ⊥) {…} = true` is false".
* Tightened pins `#axioms_within … []` fail for `shift2_sep`,
  `shift2_orderEmb`, `b2_consistent`: "depends on propext, Quot.sound, which
  the bound does not allow".  The same tightening passes for the abstract
  lemmas, which use no axioms; their pins were set to `[]`.

## Rule 8 (◯-free instance)

The ◯-free variable-free fragment is `{⊥, ⊤}`, which holds no copy of `H_n`
for `n ≥ 1` in any of the three forms; the fragment-first stage is degenerate,
as in `wip/f0FreePair.lean`.  Lemma 1 and the abstract shift are pure order
theory and carry no modal content.

## Skips

None.  No `lake exe`, no full build, no sweep.

## Log

* 2026-10-28: statements committed before any proof, b1ee732.
* 2026-10-28 15:13 GMT: proofs in (66025dd); module built, 19 pins pass;
  gates watched failing; this note.
