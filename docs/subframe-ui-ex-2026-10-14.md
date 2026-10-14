# The `∃`-side of uniform interpolation for PLL: PROVED

2026-10-14.  Branch `subframe-ui-ex`.  Module
`LaxLogic/PLL/SemUI/SubframeUI.lean` (6 ledger rows, none sorried).
Context: `docs/subframe-step2-2026-10-14.md` (step 2),
`docs/subframe-step3-2026-10-14.md` (step 3).

## 0. Status

**PROVED** (kernel-checked, `[propext, Classical.choice, Quot.sound]`):

`uniform_ex`.  For every formula `φ` and atom `p` there is a formula `ψ`, call
it `∃p φ`, with

    atoms(ψ) ⊆ atoms(φ) ∖ {p},
    ⊢ φ ⊃ ψ,
    ⊢ φ ⊃ χ  ⟹  ⊢ ψ ⊃ χ        for every χ with p ∉ atoms(χ).

`⊢` is derivability in `LaxND`, the repository's reference system for PLL
(`docs/calculus-map.md`).  `χ` ranges over all `p`-free formulas, in any
atoms.  The ◯-free instance came first (`uniform_exI`, rule 8): for ◯-free
`φ` a ◯-free `ψ` with the same properties against ◯-free `χ`, which is Pitts's
`∃p` for IPC read inside PLL.

**OPEN**: the `∀`-side, and with it uniform interpolation for PLL in full.

## 1. The interpolant

Put `X := {⊥} ∪ subformulas(φ)`, `V := atoms(φ) ∖ {p}`, `ν := ν(X)` (atoms,
implications and `◯`-formulas of `X`), `L := 3ν + 2` (the level of the
amalgamation lemma) and `r := 3L + 1` (the crank at which agreement gives a
link at level `L`).  Let `R` list representatives, up to interderivability,
of the formulas of crank ≤ `r + 1` over `V` (`SemUI.frag_reps_exist'`).  Then

    ∃p φ  :=  ⋀ { D ∈ R  |  ⊢ φ ⊃ D }.

`atoms(∃p φ) ⊆ V` and `⊢ φ ⊃ ∃p φ` are immediate.  `L` enters only through
the crank of `R`, so the size of the amalgamation level affects the size of
`∃p φ`, not whether it exists.  For the ◯-free instance, `L := 2ν + 1`,
`r := L + 1`, and the representatives are erased to ◯-free ones
(`SemUI.eraseBox`).

## 2. The proof that `⊢ ∃p φ ⊃ χ`

By completeness for subframe models it suffices that every world `w` forcing
`∃p φ` forces `χ`.  Let `θ⁺ ⊃ θ⁻` be the character of `w` over the
representatives of crank ≤ `r` (`charImp`).

1. `⊬ φ ⊃ (θ⁺ ⊃ θ⁻)`.  Otherwise the representative `D ∈ R` of `θ⁺ ⊃ θ⁻`
   (crank ≤ `r + 1`) is a conjunct of `∃p φ`; `w` forces it, hence
   `θ⁺ ⊃ θ⁻`, which `w` refutes (`not_force_charImp`).
2. Completeness gives a model `K` and a world `k ⊩ φ` above a refutation of
   `θ⁺ ⊃ θ⁻`, with the `r`-type of `w` (`exists_of_not_force_charImp`).
3. Step 2: agreement at crank `r = 3L + 1` links `k` and `w` at level `L`
   (`layered_of_agree`).
4. Step 3: a `p`-variant `N` of `w`'s model has a copy `n₀` of `w` agreeing
   with `k` on `X` (`amalgamation`), so `n₀ ⊩ φ`, so `n₀ ⊩ χ` by soundness.
5. `χ` is `p`-free, so `w ⊩ χ` (`PBisim.force_iff`).

## 3. What made the difference

The constraint-model route had the amalgamation lemma (at `4ν + 2`) but not
step 2, which is refuted there in every form the amalgamation lemma can
consume.  In the subframe semantics (`x ⊩ ◯φ ⟺ ∀ y ≥ x, y ∈ S → y ⊩ φ`, no
fallible worlds) both hold, and PLL is complete for it, so the route closes on
the `∃`-side.  The level constant was never the obstacle: any level at which
amalgamation holds gives an interpolant.

## 4. The `∀`-side

Not attempted.  The candidate is the dual,
`∀p φ := ⋁ { D ∈ R | ⊢ D ⊃ φ }`, and the missing step is a world above `w`
with the type of a countermodel to `θ⁺ ⊃ φ`: Visser's push-down (gluing)
lemma.  Craig interpolation for PLL (`LaxLogic/PLL/Sequent/Craig.lean`)
should let `χ` be restricted to the atoms of `φ`.

## 5. Reproduce

    lake build LaxLogic.PLL.SemUI.SubframeUI

About 12 seconds on top of the built dependencies.  The `#guard_msgs` pins
were watched failing: in the first compilation two elaboration errors left
`sorryAx` in both theorems, and the pins rejected them.
