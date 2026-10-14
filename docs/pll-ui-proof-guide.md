# How the proof of uniform interpolation for PLL works

2026-10-14.  A guide to the proof in `LaxLogic/PLL/SemUI/` (`SubframeLayered`,
`SubframeAmalg`, `SubframeUI`) and `LaxLogic/PLL/Semantics/Subframe.lean`.
Every result named here is kernel-checked with no `sorry`; the axioms are
`[propext, Classical.choice, Quot.sound]` or fewer (§8).

**The theorem.**  For every formula `φ` and atom `p` there are formulas `∃p φ`
and `∀p φ` in the atoms of `φ` other than `p` such that, for every `p`-free `χ`,

    ⊢ φ ↠ ∃p φ,       ⊢ φ ↠ χ  ⟹  ⊢ ∃p φ ↠ χ          (uniform_ex)
    ⊢ ∀p φ ↠ φ,       ⊢ χ ↠ φ  ⟹  ⊢ χ ↠ ∀p φ          (uniform_all)

where `⊢` is derivability in `LaxND`.  The proof is semantic, in the style of
Visser (*Uniform interpolation and layered bisimulation*, Gödel '96) and
Litak–Visser (arXiv:2404.11969).  It has five ingredients:

1. a semantics for which `LaxND` is complete;
2. **fragment finiteness**: up to interderivability there are finitely many
   formulas of bounded rank over finitely many atoms;
3. a **Hennessy–Milner theorem with bounds**: agreement on formulas of bounded
   rank and bounded bisimilarity bracket each other;
4. an **amalgamation lemma**: a bounded bisimulation can be traded for an
   unbounded one that ignores `p`;
5. the **interpolants**, chosen so that 2–4 apply.

Ingredients 2–4 are textbook for modal logic and for intuitionistic logic.  The
work for PLL was to find a semantics in which ingredient 3 holds, and to adapt
ingredient 4 to it.

## 1. Hennessy–Milner, the original argument

For the modal logic K over models with finitely many successors, two worlds
satisfy the same formulas iff they are bisimilar (Hennessy and Milner, 1985).
The bounded version needs no finiteness of models: with finitely many atoms,

    w and w′ agree on all formulas of modal depth ≤ n
        ⟺   w and w′ are n-bisimilar.

The direction from agreement to bisimilarity is the one that needs an idea.
Up to equivalence there are finitely many formulas of depth ≤ n.  For a world
`v` let `χ_v` be the conjunction of those true at `v` and the negations of those
false at `v`: the *character* of `v`.  If `w R v` then `w ⊨ ◇χ_v`, a formula of
depth `n + 1`; if `w′` agrees with `w` at depth `n + 1`, then `w′ ⊨ ◇χ_v`, so some
`v′` with `w′ R v′` satisfies `χ_v` and agrees with `v` at depth `n`.  That is
the forth clause; back is symmetric.

## 2. The intuitionistic version

In intuitionistic Kripke models (a preorder `≤`, persistent valuation) there is
no negation of a type: `¬D` does not say "`D` fails here".  Visser's
replacement for `◇χ_v` is an implication.  Let `L` list the formulas of rank
≤ r up to equivalence, and for a world `v` put

    θ⁺ := ⋀ { D ∈ L | v ⊩ D },      θ⁻ := ⋁ { D ∈ L | v ⊮ D }.

Then a world `u` refutes `θ⁺ ↠ θ⁻` exactly when some `v′ ≥ u` forces all of
`θ⁺` and none of `θ⁻`, that is, has the `r`-type of `v`.  Intuitionistic
implication quantifies over successors, so it does the work of `◇`, and the
type is pinned by forcing `θ⁺` and refuting `θ⁻`.

* *Forth*: if `u ≤ v` then `u ⊮ θ⁺ ↠ θ⁻`.  If `u′` agrees with `u` at rank
  `r + 1` it also refutes it, so some `v′ ≥ u′` has the type of `v`.
* *Back*: by symmetry.

So, with `≡°ᵣ` agreement on ◯-free formulas of rank ≤ r and `⇄°ₙ` linkage at
level `n` by a bounded (layered) bisimulation:

    ≡°_{n+1}   ⊆   ⇄°ₙ   ⊆   ≡°ₙ

In Lean: `AgreeI.forth`, `layeredI_of_agree` and `agreeI_of_layeredI`
(`SubframeLayered.lean`), proved first by rule 8.  The rank is `crank`
(`↠` costs 1, `◯` costs 2), and the finite list `L` comes from
`SemUI.frag_reps_exist'` (`SemUIFrag.lean`, 2026-07-20): representatives up to
interderivability of all formulas of crank ≤ r over a finite atom set.  The
characters are `charImp`, with `not_force_charImp`,
`exists_of_not_force_charImp` and `agree_of_char`.

## 3. Why PLL needed a different semantics

In Fairtlough and Mendler's constraint models, `x ⊩ ◯φ` iff every
`Rᵢ`-successor of `x` has an `Rₘ`-successor forcing `φ`, and some worlds are
fallible.  The quantifier pattern `∀∃` has no character formula of the kind
above, and the bounded Hennessy–Milner theorem is false there: a two-world
model with a fallible top agrees with a single world on every atom-free
formula of crank ≤ 1, but no layered bisimulation links them at level 1
(`SemUI.layered_of_frag_agree_refuted`); a fork agrees with a single world on
*every* formula, yet no link survives an `Rₘ`-move into its fallible branch
(`SemUI.pair_escape_not_from_agreement`).  This is why the earlier semantic
route stopped, whatever the amalgamation level.

**Subframe models** remove both features: `(W, ≤, S, V)` with `S ⊆ W` arbitrary,
no fallible worlds, and

    x ⊩ ◯φ   ⟺   ∀ y ≥ x, y ∈ S → y ⊩ φ.

So `◯` is the universal modality over `≤ ∩ S` (the subframe reading of a
nucleus).  `LaxND` is sound and complete for them
(`SubframeModel.derivable_iff_valid`, `Semantics/Subframe.lean`), by two
translations through the existing constraint-model theorems: a subframe model
is a constraint model with one fallible top added (`toConstraint_force`), and
a finite constraint model is a subframe model on its non-fallible worlds with
`S` the `Rₘ`-final ones (`toSubframe_force`).

## 4. Hennessy–Milner for PLL

`◯` now quantifies over one relation, so it has a character:

    u ⊮ θ⁺ ↠ ◯θ⁻   ⟺   some S-point above u has the type of v (for v ∈ S).

*S-forth*: if `u ≤ v ∈ S` then `u ⊮ θ⁺ ↠ ◯θ⁻` (witness `v` itself).  A world `u′`
agreeing with `u` at rank `r + 3` refutes it too: some `x ≥ u′` forces `θ⁺` and
some `y ≥ x` in `S` refutes `θ⁻`; `y` forces `θ⁺` by persistence, so `y` is an
`S`-point above `u′` with the type of `v` (`Agree.sforth`,
`exists_of_not_force_charBox`).  The character costs three ranks (`↠` one, `◯`
two), so level `n` needs rank `3n + 1`:

    ≡_{3n+1}   ⊆   ⇄ₙ   ⊆   ≡ₙ

(`layered_of_agree`, `agree_of_layered`), where `⇄ₙ` is linkage by a layered
bisimulation with `≤`-forth/back and `S`-forth/back clauses (`LayeredBisim`).
The `S`-clauses cannot be dropped: two one-point models, one point in `S` and
one not, are `≤`-bisimilar at every level and are separated by `◯⊥`
(`S_clause_needed`).

The second inclusion is the invariance (rank preservation) lemma
`LayeredBisim.force_iff`, the only structural induction in the chain: the
◯-free version is its corollary through the models with `S` emptied
(`LayeredBisimI.noS`), and invariance under unbounded bisimulations is its
corollary for the constant family (`PBisim.toLayered`).

## 5. Amalgamation

**Statement** (`amalgamation`, `SubframeAmalg.lean`).  Let `X` be
subformula-closed and `ν` the number of its atoms, implications and
`◯`-formulas.  If `k₀ ∈ K` and `m₀ ∈ M` are linked at level `3ν + 2` over the
atoms of `X` other than `p`, then some `p`-variant `N` of `M` (an *unbounded*
bisimulation off `p`, `PBisim`) contains a copy `n₀` of `m₀` that forces
exactly the formulas of `X` that `k₀` forces.

**The ◯-free case** (`amalgamationI`, level `2ν + 1`) is Visser's lemma in
Litak–Visser's form.  A world of `N` pairs a *reservoir* link `k′ Z m′` with a
*current* link `k Z m`, where `k′ ≤ k`, `m′ ≤ m`, and `k′`, `k` force the same
formulas of `X`.  The certificate is indexed by the *depth* `d` of `k′`: the
number of budget formulas of `X` it does not force (`dep`).  `N` is ordered by
the `M`-coordinate and by inclusion of `X`-theories; atoms other than `p` are
read from `M`, `p` from `K`.  Two facts carry the proof:

* moves of `M` are answered from the reservoir, so they cost nothing
  (`land_reservoir`);
* a move that enlarges the `X`-theory lowers the depth (`dep_lt`), and lands on
  a fresh reservoir (`land_strict`).

The *truth lemma* (`amal_force`) says a world of `N` forces `φ ∈ X` iff its
current `K`-world does; the projection to `M` is the `p`-variant
(`amal_pbisim`).

**For PLL** one kind of world is added: an *`S`-world*, whose current link has
both ends `S`-points.  A same-theory `◯`-move lands on an `S`-world, and an
`S`-world refutes every further such `◯ξ` in place, since it is its own
`S`-successor.  So same-theory `◯`-moves never chain.  The budget:

| | reservoir | current link |
|---|---|---|
| ◯-free | `2d + 1` | `2d` |
| PLL, normal world | `3d + 2` | `3d + 1` |
| PLL, `S`-world | `3d + 2` | `3d`, both ends `S`-points |

The tight case is a theory-enlarging move from a current link at `3d`, landing
on a reservoir at `3d′ + 2 ≤ 3d − 1` for the smaller depth `d′`.  Every such
inequality is an `omega` obligation the kernel checks.

## 6. Realisation

Steps 2, 3 and invariance combine into one statement (`realise`,
`SubframeUI.lean`).  Put `X := {⊥} ∪ subformulas(φ)` and
`r := 3(3ν + 2) + 1`.

> If `k` and `v` agree on all formulas of crank ≤ `r` over the atoms of `φ`
> other than `p`, then some world `n₀` agrees with `v` on every `p`-free
> formula and with `k` on `φ`.

Proof: step 2 links `k` and `v` at level `3ν + 2`; step 3 gives the
`p`-variant of `v`'s model and the copy `n₀`; invariance carries the `p`-free
formulas from `v` to `n₀`.  The ◯-free version is `realiseI`.

## 7. The interpolants

Both interpolants are finite conjunctions over representatives; the work is
choosing formulas that pin a world's `r`-type.

**`∃p φ`** is the conjunction of the representatives `D` of crank ≤ `r + 1`
with `⊢ φ ↠ D`.  Clearly `⊢ φ ↠ ∃p φ`.  For `⊢ ∃p φ ↠ χ`: let `w` force `∃p φ`.
The character `θ⁺ ↠ θ⁻` of `w` is not a consequence of `φ`, for otherwise its
representative would be a conjunct, and `w` would force a formula it refutes.
Completeness gives a world `k ⊩ φ` with the `r`-type of `w`.  Realisation gives
`n₀`: it forces `φ` (from `k`), hence `χ`, hence `w` forces `χ` (`χ` is
`p`-free).  (`uniform_ex`.)

**`∀p φ`.**  For `T ⊆ R` (the representatives of crank ≤ r) put
`char(T) := ⋀T ↠ ⋁(R ∖ T)`; a world refutes `char(T)` exactly when some world
above it has type exactly `T` (`charT`, `type_of_char`).  Then

    ∀p φ := ⋀ { char(T) | T ⊆ R,  ⊬ ⋀T ↠ (⋁(R ∖ T) ∨ φ) },

the side condition saying that some world of type `T` refutes `φ` (Litak and
Visser's `Θ⁺ ⊬ Θ⁻ ∨ φ`).  `⊢ ∀p φ ↠ φ`: a world refuting `φ` qualifies its own
type, so it would force `char(T)` while having type `T`.  For `⊢ χ ↠ ∀p φ`: if
`w ⊩ χ` refuted `char(T)`, some `v ≥ w` would have type `T`, and a countermodel
world `k` of type `T` refutes `φ`; realisation gives `n₀` forcing `χ` (from `v`,
by persistence) and refuting `φ` (from `k`), against `⊢ χ ↠ φ`.
(`uniform_all`.)

The two sides are independent; no gluing lemma is needed, because `char(T)`
says "no world above has a bad type" directly.  The ◯-free instances
(`uniform_exI`, `uniform_allI`) are Pitts's theorem for IPC read inside PLL.

## 8. Axioms

The headline theorems depend on `[propext, Classical.choice, Quot.sound]`.  In
Lean the law of excluded middle is derived from `Classical.choice`
(Diaconescu), so "choice" in this report also records every classical case
split.  A trace of the first use in each place (2026-10-14):

| place | first classical step | needed? |
|---|---|---|
| fragment finiteness | `Finset.toList`; `Nonempty.some` in `Deriv.bigOrElim`; a Mathlib `Finset` union lemma | no |
| soundness for subframe models | `by_cases v ∈ S` in the translation `toConstraint_force` (constraint soundness itself is choice-free) | no: prove directly by induction |
| completeness | `Classical.byContradiction` in the finite-countermodel theorem | no: the choice-free dichotomy `FRJ.Gbu.W.dichotomyW` exists |
| step 2's characters | deciding `v ⊩ D` for each representative | only over arbitrary models |
| the amalgam | the depth and the truth lemma's case splits on forcing | only over arbitrary models |

The last two disappear when the argument runs over finite models with
decidable valuation and `S`, which the finite model property allows.  A
choice-free version is therefore expected to be possible; it is not built.

## 9. Where to look

| result | Lean | file |
|---|---|---|
| completeness for subframe models | `SubframeModel.derivable_iff_valid` | `Semantics/Subframe.lean` |
| fragment finiteness | `SemUI.frag_reps_exist'` | `SemUI/SemUIFrag.lean` |
| HM for IPC | `layeredI_of_agree`, `agreeI_of_layeredI` | `SemUI/SubframeLayered.lean` |
| HM for PLL | `layered_of_agree`, `agree_of_layered`, `S_clause_needed` | `SemUI/SubframeLayered.lean` |
| invariance | `LayeredBisim.force_iff`, `PBisim.force_iff` | `SemUI/SubframeLayered.lean`, `SemUI/SubframeAmalg.lean` |
| amalgamation | `amalgamationI` (2ν+1), `amalgamation` (3ν+2) | `SemUI/SubframeAmalg.lean` |
| realisation | `realiseI`, `realise` | `SemUI/SubframeUI.lean` |
| uniform interpolation | `uniform_ex`, `uniform_all` (and `…I`) | `SemUI/SubframeUI.lean` |

Records: `docs/subframe-step2-2026-10-14.md`,
`docs/subframe-step3-2026-10-14.md`,
`docs/pll-uniform-interpolation-2026-10-14.md`.

References: M. Hennessy and R. Milner, *Algebraic laws for nondeterminism and
concurrency*, JACM 32 (1985); A. M. Pitts, *On an interpretation of second
order quantification in first order intuitionistic propositional logic*, JSL
57 (1992); A. Visser, *Uniform interpolation and layered bisimulation*, in
Gödel '96, Lecture Notes in Logic 6 (1996); T. Litak and A. Visser, *Lewis
and Brouwer meet Strong Löb*, arXiv:2404.11969; M. Fairtlough and M. Mendler,
*Propositional lax logic*, Inf. Comput. 137 (1997).
