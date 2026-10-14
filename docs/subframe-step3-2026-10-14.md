# Step 3 of the semantic route in the subframe semantics: PROVED

2026-10-14.  Branch `subframe-amalg`.  Module
`LaxLogic/PLL/SemUI/SubframeAmalg.lean` (110 ledger rows, none sorried).
Context: `docs/subframe-step2-2026-10-14.md` (step 2) and
`docs/semui-amalgamation-2026-10-14.md` (the constraint-model amalgamation).

## 0. Status

**PROVED** (kernel-checked, axioms pinned in the module):

* `amalgamation`: the amalgamation lemma for PLL in the subframe semantics at
  level `3ν + 2` (`[propext, Classical.choice, Quot.sound]`).
* `amalgamationI`: the ◯-free instance, at level `2ν + 1` (rule 8; this is
  Visser's lemma as Litak–Visser state it).
* `PBisim.force_iff`: `p`-free formulas are invariant under a `p`-variant
  (`[propext, Quot.sound]`).  This was the "easy, not yet stated" lemma of the
  step-2 record.

Every level inequality in the proof is an `omega` obligation checked by the
kernel; none is argued in prose only.

**OPEN**: the level `2ν + 1` for PLL; the assembly of steps 1 to 3 into the
`∃`-side of uniform interpolation (§4, all ingredients PROVED); the `∀`-side;
uniform interpolation for PLL.

## 1. The statement

`ν` is the number of atoms, implications and `◯`-formulas in the
subformula-closed set `X` (`SemUI.nu`).  `⇄ₙ` is linkage at level `n` by a
layered bisimulation over the atoms of `X` other than `p` (step 2).  A
*`p`-variant* of `M` is a model `N` with an unbounded bisimulation between
`M` and `N` respecting every atom except `p`, with the `S`-clauses
(`PBisim`).

    k₀ ⇄_{3ν+2} m₀   ⟹   there are a p-variant N of M and a copy n₀ of m₀
                          with  n₀ ⊩ φ ⟺ k₀ ⊩ φ  for every φ ∈ X.

The ◯-free instance: `X` ◯-free, `⇄°_{2ν+1}` in place of `⇄_{3ν+2}`, and the
`p`-variant without `S`-clauses.

`N` reads every atom other than `p` from `M`, so it is a `p`-variant for the
whole alphabet whatever `K` does off `X`.  That is the form the route needs:
`K` comes from completeness and knows nothing of `M`.

## 2. The refutation stage

Answered from the rules: the statement was tested case by case against the
level budget of the construction below before any Lean was written, and the
case that failed over constraint models was located first.

* **The constraint obstruction.**  Over constraint models a world `k` refuting
  `◯ξ` has a successor none of whose `Rₘ`-successors forces `ξ`; when that
  successor has the same `X`-theory as `k`, the depth does not drop and
  nothing pays for the move.  The constraint proof answered it with `X`-rigid
  worlds and paid two levels per unit of depth (`4ν + 2`).
* **In the subframe semantics** a world refuting `◯ξ` has an `S`-point
  `s ≥ k` refuting `ξ`.  If `s` has the same `X`-theory as `k`, one `S`-move
  reaches an *`S`-world* (current pair with both ends `S`-points), and an
  `S`-world refutes every further such `◯ξ` in place: `k ⊮ ξ` by persistence
  and the world is its own `S`-successor.  So same-theory `◯`-moves never
  chain, and they cost one level, not two.

## 3. The construction

A world of the amalgam over `m ∈ M` is a reservoir pair `k′ Z m′` and a
current pair `k Z m` with `k′ ≤ k`, `m′ ≤ m`, `k′` and `k` forcing the same
formulas of `X`.  `d` is the depth of `k′`: the number of budget formulas of
`X` it does not force (`dep`).

| | reservoir | current pair |
|---|---|---|
| ◯-free | `2d + 1` | `2d` |
| PLL, normal world | `3d + 2` | `3d + 1` |
| PLL, `S`-world | `3d + 2` | `3d`, both ends `S`-points |

The order is componentwise on the `M`-coordinate and on the `X`-theory of the
current `K`-world; `S` of the amalgam is the set of worlds whose current pair
has both ends in `S`; atoms other than `p` are read from `M`, `p` from the
current `K`-world.

* *Truth lemma* (`amal_force`): a world forces `φ ∈ X` iff its current
  `K`-world does.  For `φ ⊃ ψ` and `◯ξ` refuted at `k`, either the world
  refutes in place, or the refuting `K`-world has a larger `X`-theory, the
  depth drops (`dep_lt`), and the current link one level down lands on a fresh
  reservoir (`land_strict`); or, for `◯ξ` with the same theory, the world moves
  to the `S`-world over the refuting `S`-point.
* *`p`-variant* (`amal_pbisim`): the projection to `M`.  Moves of `M`, to
  `S`-points or not, are answered from the reservoir by the link's back and
  `S`-back clauses (`land_reservoir`), so they cost nothing.

The budget, with `d′ < d` the depth after a theory-enlarging move:

| move | from | lands at | needs |
|---|---|---|---|
| move of `M`, same theory | reservoir `3d + 2` | current `3d + 1` | equal |
| move of `M`, larger theory | reservoir `3d + 2` | reservoir `3d′ + 2` | `3d′ + 2 ≤ 3d + 1` |
| same-theory `◯`-move | normal current `3d + 1` | `S`-world current `3d` | equal |
| larger-theory move | current `3d` (either kind) | reservoir `3d′ + 2` | `3d′ + 2 ≤ 3d − 1` |

The last row is the tight one, and it is where the factor 3 comes from.  The
◯-free table is the same with `2d + 1`, `2d` and `2d′ + 1 ≤ 2d − 1`.

## 4. What this does to the route

| step | statement | status |
|---|---|---|
| 1 | fragment finiteness up to interderivability | PROVED (`SemUI.frag_reps_exist'`) |
| 2 | `≡_{3n+1} ⊆ ⇄ₙ ⊆ ≡ₙ` | PROVED (`layered_of_agree`, `agree_of_layered`) |
| 3 | amalgamation at `3ν + 2` | PROVED today (`amalgamation`) |
| inv. | `p`-variants preserve `p`-free formulas | PROVED today (`PBisim.force_iff`) |
| compl. | PLL sound and complete for subframe models | PROVED (`SubframeModel.derivable_iff_valid`) |
| 4 | the `∀`-side gluing | OPEN |

**The `∃`-side assembly** (OPEN, not built; every ingredient is PROVED).  Put
`V` the atoms of `φ` other than `p`, `X` the subformulas of `φ` with `⊥`,
`L := 3ν + 2`, `r := 3L + 1`, and let `∃p φ` be the conjunction of the
representatives `D` of crank ≤ `r + 1` over `V` with `⊢ φ ⊃ D`.  Then
`p ∉ atoms(∃p φ)` and `⊢ φ ⊃ ∃p φ` are immediate.  For a `p`-free `χ` with
`⊢ φ ⊃ χ`, and a world `w` forcing `∃p φ`: with `θ⁺`, `θ⁻` the
representatives of crank ≤ `r` forced and refuted at `w`, `⊬ φ ⊃ (θ⁺ ⊃ θ⁻)`
(else that formula, of crank ≤ `r + 1`, is a conjunct and `w` forces `θ⁻`), so
completeness gives a world `k ⊩ φ` with the `r`-type of `w`; step 2 links `k`
and `w` at level `L`; step 3 gives a `p`-variant of `w` forcing `φ`, hence
`χ`; invariance gives `w ⊩ χ`; completeness gives `⊢ ∃p φ ⊃ χ`.

## 5. Reproduce

    lake build LaxLogic.PLL.SemUI.SubframeAmalg

About 15 seconds on top of the built dependencies.  The `#guard_msgs` pins
were watched failing (the pin of `PBisim.force_iff` first asserted
`[propext]`; the kernel reports `[propext, Quot.sound]`).
