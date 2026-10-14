# Uniform interpolation for PLL: PROVED

2026-10-14.  Branch `subframe-ui-ex`.  Module
`LaxLogic/PLL/SemUI/SubframeUI.lean` (15 ledger rows, none sorried).
Context: `docs/subframe-step2-2026-10-14.md` (step 2),
`docs/subframe-step3-2026-10-14.md` (step 3).

## 0. Status

**PROVED** (kernel-checked, each `[propext, Classical.choice, Quot.sound]`).
For every formula `φ` and atom `p` there are formulas `∃p φ` and `∀p φ` in the
atoms of `φ` other than `p` such that, for every formula `χ` with
`p ∉ atoms(χ)`,

    ⊢ φ ⊃ ∃p φ,       ⊢ φ ⊃ χ  ⟹  ⊢ ∃p φ ⊃ χ          (uniform_ex)
    ⊢ ∀p φ ⊃ φ,       ⊢ χ ⊃ φ  ⟹  ⊢ χ ⊃ ∀p φ          (uniform_all)

`⊢` is derivability in `LaxND`, the repository's reference system for PLL
(`docs/calculus-map.md`).  `χ` ranges over all `p`-free formulas, in any atoms.
This is uniform interpolation in Pitts's sense.  The ◯-free instances came
first (`uniform_exI`, `uniform_allI`, rule 8): for ◯-free `φ`, ◯-free
interpolants against ◯-free `χ`, which is Pitts's theorem for IPC read inside
PLL.

## 1. The common set-up

Put `X := {⊥} ∪ subformulas(φ)`, `V := atoms(φ) ∖ {p}`, `ν := ν(X)` (atoms,
implications and `◯`-formulas of `X`), `L := 3ν + 2` (the level of the
amalgamation lemma) and `r := 3L + 1` (the crank at which agreement gives a
link at level `L`, step 2).  Representatives are taken up to
interderivability over `V` (`SemUI.frag_reps_exist'`).  `L` enters only
through the crank of the representatives, so the amalgamation level affects
the size of the interpolants, not their existence.  The ◯-free instances use
`L := 2ν + 1`, `r := L + 1` and representatives erased to ◯-free ones
(`SemUI.eraseBox`).

The proofs are semantic, over subframe models
(`x ⊩ ◯φ ⟺ ∀ y ≥ x, y ∈ S → y ⊩ φ`, no fallible worlds), for which `LaxND` is
sound and complete (`SubframeModel.derivable_iff_valid`).

## 2. The `∃`-side

    ∃p φ  :=  ⋀ { D  |  D a representative of crank ≤ r + 1,  ⊢ φ ⊃ D }.

`⊢ φ ⊃ ∃p φ` is immediate.  For `⊢ ∃p φ ⊃ χ`, let `w` force `∃p φ` and let
`θ⁺ ⊃ θ⁻` be the character of `w` over the representatives of crank ≤ `r`
(`charImp`).

1. `⊬ φ ⊃ (θ⁺ ⊃ θ⁻)`: otherwise the representative of `θ⁺ ⊃ θ⁻` is a conjunct
   of `∃p φ`, so `w` forces `θ⁺ ⊃ θ⁻`, which it refutes.
2. Completeness gives a world `k ⊩ φ` with the `r`-type of `w`.
3. Step 2 links `k` and `w` at level `L` (`layered_of_agree`).
4. Step 3 gives a `p`-variant of `w`'s model whose copy of `w` agrees with `k`
   on `X` (`amalgamation`), so forces `φ`, so forces `χ`.
5. `χ` is `p`-free, so `w ⊩ χ` (`PBisim.force_iff`).

## 3. The `∀`-side

Let `R` list the representatives of crank ≤ `r`.  For `T ⊆ R` put
`char(T) := ⋀T ⊃ ⋁(R ∖ T)` (`charT`).  A world refutes `char(T)` exactly when
some world above it has `R`-type exactly `T` (`type_of_char`).

    ∀p φ  :=  ⋀ { char(T)  |  T ⊆ R,  ⊬ ⋀T ⊃ (⋁(R ∖ T) ∨ φ) }.

The side condition says that some world of type `T` refutes `φ`; it is
Litak and Visser's `Θ⁺ ⊬ Θ⁻ ∨ φ`.

* `⊢ ∀p φ ⊃ φ`, without amalgamation: a world `w` refuting `φ` qualifies its
  own type `T` (`good_posL`), so it forces `char(T)` while having type `T`,
  which is impossible.
* `⊢ χ ⊃ φ ⟹ ⊢ χ ⊃ ∀p φ`: if `w ⊩ χ` refutes `char(T)`, some `v ≥ w` has type
  `T`.  A countermodel world `k` has type `T` and refutes `φ`.  Step 2 links
  `k` and `v` at level `L`; step 3 gives a `p`-variant of `v`'s model whose
  copy of `v` agrees with `k` on `X`, so refutes `φ`.  It forces `χ`
  (persistence, then invariance), so it forces `φ`: a contradiction.

Semantically the two sides are independent; neither uses the other.  (In
Pitts's syntactic proof they are defined by a simultaneous recursion.)  No
gluing (push-down) lemma is needed: the characters `char(T)` express "no
world above has a bad type" directly.

## 4. What made the difference

The constraint-model route had the amalgamation lemma (at `4ν + 2`, this
morning) but not step 2, which is refuted there in every form the
amalgamation lemma can consume.  In the subframe semantics step 2 holds by the
standard character argument, step 3 holds at `3ν + 2`, and PLL is complete, so
both sides close.  The level constant was never the obstacle.

## 5. Owed

* Prose that discusses the status of uniform interpolation for PLL and needs
  rereading: it is stated OPEN in `docs/ljfo-fidelity.md`,
  `docs/llm-formalisation-case-study.md`, `docs/iemhoff-note.md` and
  `docs/commentary.md`; `docs/belief-paper-draft.md` and
  `docs/belief-bib-map.md` discuss Iemhoff's claim.  Left for Matthew: some
  are drafts or notes to others.  (`docs/semantic-ui-route.md`'s OPEN
  definability targets are the constraint-model ones, `SemExDefinable` and
  `SemAllDefinable`; they stay OPEN.)
* Literature check before any external claim: whether uniform interpolation
  for PLL (or for the corresponding nuclear or subframe logics) has appeared
  elsewhere since Iemhoff's withdrawal.
* Review by Matthew of the statements of `uniform_ex` and `uniform_all`.

## 6. Reproduce

    lake build LaxLogic.PLL.SemUI.SubframeUI

About 40 seconds on top of the built dependencies.  The `#guard_msgs` pins
were watched failing: in the first compilation of the `∃`-side two
elaboration errors left `sorryAx` in both theorems, and the pins rejected
them.
