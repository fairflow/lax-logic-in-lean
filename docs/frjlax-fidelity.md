# FRJ◯ — fidelity table

*Started 2026-08-16 on branch `claude/frj-redevelopment-69005f`.  Source
of truth: Camillo Fiorentini and Mauro Ferrari, "Duality between
Unprovability and Provability in Forward Refutation-search for IPL",
**ACM TOCL 21(3), Article 22, 2020**.  Numbering and section references
are the published journal's throughout; the transcription was
cross-read against the arXiv LaTeX source (arXiv:1804.06689,
`frj-corr.tex`), which is a close variant and not the same text.  The
differences are set out in `docs/frj-lax-plan.md` §1.*

This document maps every Lean definition and theorem to the numbered item
it encodes, and records every divergence as a divergence.  It is the
deliverable that makes the formalisation checkable against the original.

**This is not `docs/frj-fidelity.md`.**  That document records the IPC-only
development in `FRJ/` (branch `frj-ipc`), which is `Finset`-based and
carries computed indices in its constructors.  Nothing in `FRJLax/`
imports it, or `FRJO/`, or `Reject/`, or `BiLax/`.

## Status

| Stage | Content | Status |
|---|---|---|
| W0 | source read; plan | **done** — `docs/frj-lax-plan.md` |
| W1 | §2: syntax, subformulas, closure, models, forcing | **done** — builds, pinned |
| W2 | §3, Figure 1: the rule table, and its screen | **done** — builds, pinned, every constructor exercised |
| W3 | §3.2: Lemma 3.5, `Mod(D)`, Lemma 3.10, Theorem 3.12, Theorem 3.1 | not started |
| W4 | §6: Lemma 6.7, Lemma 6.3, completeness | not started |
| W5 | the `◯` rules | not started; statements are Matthew's |
| W6 | searcher and certificate | not started |

## W1 — §2 Preliminaries → `FRJLax/Core.lean`, `FRJLax/Model.lean`

| Paper | Lean | Status |
|---|---|---|
| language `L`; `∧ ∨ ⊃ ⊥`; `PV` | `Form` (+ `circ`) | done |
| `¬A := A ⊃ ⊥` | `Form.neg` | done |
| `\|A\|`, the size of `A` | `Form.size`, `Form.size_pos` | PROVED |
| `Prime = PV ∪ {⊥}` | `Form.isPrime` (`Bool`) | done |
| `Fm⊃` | `Form.isImp` (`Bool`) | done |
| `Sf(G)`, `Sf⁻(C) = Sf(C) \ {C}` | `sf`, `sfm`, `self_mem_sf` | PROVED |
| `X ∈ Sf(A)` implies `\|X\| ≤ \|A\|` | `size_le_of_mem_sf` | PROVED |
| `X ∈ Sf⁻(A)` implies `\|X\| < \|A\|` | `size_lt_of_mem_sfm` | PROVED |
| `Sf(A) ⊆ Sf⁻(A ⊃ B)`; the `∧`, `∨`, `⊃` variants | `sf_subset_sfm_impL`, `sfm_subset_sfm_*` | PROVED |
| `Sf^L(G)`, `Sf^R(G)`: the defining clauses | `sfL`, `sfR` computed; `SfClosed`; `sfPos_closed`, `sfNeg_closed` | PROVED |
| `G ∈ Sf^R(G)` | `sfR_self` | PROVED |
| the `∧`/`∨` clause, both polarities | `sfR_and`, `sfR_or`, `sfL_and`, `sfL_or` | PROVED |
| the two `⊃` clauses | `sfR_imp`, `sfL_imp` | PROVED |
| `Ĝ_at`, `Ĝ_imp`, `Ĝ` | `gAt`, `gImp`, `gHat` | done |
| `Γ^at`, `Γ^⊃` | `atPart`, `impPart` | done |
| `Γ = Γ^at ∪ Γ^⊃` for `Γ ⊆ Ĝ` | `atPart_union_impPart` | PROVED |
| Kripke model: finite poset, minimum `ρ`, monotone `V` | `Model` | done |
| the five forcing clauses | `Model.force` | done |
| monotonicity property | `Model.force_mono` | PROVED |
| `K,α ⊩ Γ` | `Model.forces` | done |
| validity; the valid formulas; countermodel | `Model.valid`, `PLL`, `Countermodel`, `not_PLL_of_countermodel` | PROVED |
| closure `Cl(Γ)` by the grammar | `Clo` | done |
| (Cl1) `α ⊩ Γ` implies `α ⊩ Cl(Γ)` | `clo_forces` | PROVED |
| (Cl2) `A ∈ Cl(Γ)` implies `A ∈ Cl(Γ ∩ Sf(A))` | `clo_sf` | PROVED |
| (Cl3) `Γ ⊆ Cl(Γ)`, `Cl(Cl(Γ)) = Cl(Γ)` | `clo_subset`, `clo_trans` | PROVED |
| (Cl4) monotone | `clo_mono` | PROVED |
| (Cl5) `Cl(Γ) ∩ PV = Γ ∩ PV` | `clo_pv` | PROVED |
| (Cl6) `Γ₁ ⊆ Cl(Γ₂)` implies `Cl(Γ₁) ⊆ Cl(Γ₂)` | `clo_trans` | PROVED |

### Not the paper's, and marked as such in the source

| Item | Lean | Why |
|---|---|---|
| `◯` in the syntax | `Form.circ`, `Form.size` clause, `sf` clause | the decision of 2026-08-16 |
| `◯A ∈ Sx(G)` implies `A ∈ Sx(G)`, both polarities | `sfPos`/`sfNeg` `circ` clauses; `sfR_circ`, `sfL_circ`; `SfClosed.rCirc`/`.lCirc` | `◯` is monotone, so `A` inherits the polarity of the `◯A` occurrence.  Forced, not chosen |
| `Sf(A) ⊆ Sf⁻(◯A)` | `sf_subset_sfm_circ` | the analogue of `sf_subset_sfm_impL` |
| `Ĝ_◯`, `Γ^◯`, `isCirc` | `gCirc`, `circPart`, `Form.isCirc` | vocabulary for W5.  **Defined and unused**; `gHat` is still `gAt ++ gImp`, the paper's |
| the second relation and the fallible worlds | `Model.Rm`, `Model.Fal`, `sub_mi`, `rm_refl`, `rm_trans`, `hered_F`, `full_F` | Fairtlough–Mendler constraint models |
| the `◯` forcing clause | `Model.force` `circ` clause | Fairtlough–Mendler |
| a fallible world forces everything | `Model.force_of_fallible` | coherence check on the structure: `full_F` is stated for atoms only |
| `α ⊩ X` implies `α ⊩ ◯X` | `force_circ_of_force` | the whole content of the candidate `Cl` clause `X ::= … \| ◯X`.  **Used nowhere**; see divergence 4 |

## W2 — §3 and Figure 1 → `FRJLax/Calculus.lean`, `FRJLax/Paper.lean`

| Paper | Lean | Status |
|---|---|---|
| regular and irregular sequents; `Lhs(σ)`, `Rhs(σ)` | `Sequent`, `.lhs`, `.rhs`, `.isReg` | done |
| `Ax^⇒` `⊢ Ĝ_at \ {F} ⇒ F`, `F ∈ Prime` | `FRJr.axR` | done |
| `Ax^→` `⊢ · ; Ĝ_at \ {F}, Ĝ_imp → F` | `FRJi.axI` | done |
| `∧` regular, `k = 1, 2` | `FRJr.andR₁`, `FRJr.andR₂` | done |
| `∧` irregular, `k = 1, 2` | `FRJi.andI₁`, `FRJi.andI₂` | done |
| `∨`, sides `Σ₁ ⊆ Σ₂ ∪ Θ₂`, `Σ₂ ⊆ Σ₁ ∪ Θ₁` | `FRJi.orI` | done |
| `⊃∈` regular, side `A ∈ Cl(Γ)` | `FRJr.impInR` | done |
| `⊃∈` irregular, sides `Θ ∩ Λ = ∅`, `A ∈ Cl(Σ ∪ Λ)` | `FRJi.impInI` | done |
| `⊃∉`, sides `Θ ⊆ Cl(Γ) ∩ Ĝ`, `A ∈ Cl(Γ) \ Cl(Θ)` | `FRJi.impNotIn` | done |
| `⋈^At`, sides (J1), (J2), (J3) | `FRJr.joinAt` | done |
| `⋈^∨`, sides (J1), (J2), (J4) | `FRJr.joinOr` | done |
| the `n ≥ 1` premises of a join | `Prems`, `Prems.ne_nil` | done |
| `Υ`, `Σ^At`, `Σ^⊃`, `Θ^At`, `Θ^⊃` | `ups`, `sigAt`, `sigImp`, `thAt`, `thImp`, `interAll` | done |
| `Γ^⊃/Υ = { Y ⊃ Z ∈ Γ^⊃ \| Y ∈ Υ }` | `restrict`, `mem_restrict` | PROVED |
| the two join conclusion contexts | `joinCtxAt`, `joinCtxOr` | done |
| `⊢_FRJ(G) G` | `Refutation` (`Type`), `Provable` (`Prop`) | done |
| (RS1)–(RS4) | **deliberately absent** | see `docs/frj-lax-plan.md` §1 |

### Divergences at W2

6. **The `n ≥ 1` of the join rules is structural.**  The premises are a
   vector `Prems G l` whose index list is nonempty by construction, in
   place of the paper's indexed family and in place of the `Fin (n+1)`
   encoding of `FRJ/Calculus.lean`.  Induction over the premises is then
   structural, and the zone operations are ordinary list operations
   needing no decidable quantifier over `Fin`.

7. **(J1) is stated over all pairs**, including `i = j`, where it reads
   `Σ_i ⊆ Σ_i ∪ Θ_i` and holds trivially.  Equivalent to the paper's
   `i ≠ j`, and cheaper to check.

8. **(J2) is stated through a `Bool` test** `suppB` rather than as the
   quantifier "`Y ⊃ Z ∈ Σ^⊃` implies `Y ∈ Υ`" over all `Y`, `Z`, so that
   it is a decidable field.  The test is vacuously true on non-implications,
   which cannot occur in `Σ^⊃`.

9. **`Σ` is written `St`** in binder positions: `Σ` is reserved notation
   in Lean.

### The no-green-slime property

Every constructor returns one of

    FRJr G Γ F                FRJr G Γ (.and A₁ A₂)
    FRJr G Γ (.imp A B)       FRJr G Γ (.or C₁ C₂)
    FRJi G St Th F            FRJi G St Th (.and A₁ A₂)
    FRJi G St Th (.or C₁ C₂)  FRJi G St Th (.imp A B)
    Prems G [⟨St, Th, A⟩]     Prems G (⟨St, Th, A⟩ :: l)

No `++`, `rm`, `cap`, `filter` or `nf` appears in any return type; all ten
computed contexts of Figure 1 enter through `≐`, `⊆` or `∈` hypotheses.
Compare `FRJ/Calculus.lean` on `frj-choicefree`, which reaches index
equality the other way — by normalising the computed index with `nf G`,
as in `FRJi G (nf G (St ++ Lam)) (nf G Th) (.imp A B)`.

## The W2 screen — round A of the counterexample mandate

`FRJLax/Paper.lean` replays **the paper's own worked refutations** as
kernel-checked terms, in the corpus-replay and branch-coverage directions.
Every side condition is discharged by `decide`; every conclusion context
agrees with the paper's displayed sequent up to membership.

| Paper | Content | Result |
|---|---|---|
| Example 3.6 | `G = (p ∧ H) ⊃ (q₁ ∨ q₂)`, `H = p ⊃ q₁ ∨ q₂`; `Sf^L(G)`, `Sf^R(G)`, `Ĝ_at`, `Ĝ_imp` | reproduced on the nose |
| Example 3.6 | `p ⇒ q₁ ∨ q₂` by `⋈^∨`, "`H` is left out since it is not supported" | `joinCtxOr` computes exactly `{p}` |
| Example 3.6 | `H ⇒ q₁ ∨ q₂` by `⋈^∨` with three premises, "`p` is omitted since it does not occur as left formula in the right-most premise" | `joinCtxOr` computes exactly `{H}` |
| Example 3.15 | `p, H ; · → (p ∧ H) ⊃ (q₁ ∨ q₂)` — an irregular sequent whose right formula is VALID | refutable, as the paper says it must be |
| §3 prose | `p₁, p₂ ⇒ p₁ ∧ p₂ ⊃ q`, the cell that motivates `A ∈ Cl(Γ)` | refuted in two steps |
| Example 3.7, Figure 2 | Scott's principle `S`, all twelve lines of `D_S` | every line type-checks; `Refutation S` is inhabited |

Every constructor is exercised: `axR`, `axI`, `andR₁`, `andR₂`, `andI₁`,
`andI₂`, `orI`, `impInR`, `impInI`, `impNotIn`, `joinAt`, `joinOr`.

**What the screen does not do.**  It is a positive screen: it shows the
table admits what the paper says it admits.  The negative half — that
`p, H ⇒ q₁ ∨ q₂` is *not* refutable, which is what keeps the calculus
sound — is an underivability claim, proved in the paper from Lemma 3.5(i),
and belongs to W3.

## Divergences

1. **The `⊃`-clause of forcing is an implication**, not the paper's
   disjunction "`K,β ⊮ A` or `K,β ⊩ B`".  Equivalent; the disjunction
   would put excluded middle into the definition.

2. **Finiteness is a constructive enumeration.**  `Model` carries
   `elems`/`complete` plus `decEq`, `decRi`, `decRm`, `decFal`, `decV`
   rather than a `Finite` instance, because eliminating `Finite` needs
   `Fintype.ofFinite`, which costs `Classical.choice`.  The gain is
   `Model.decForce`: forcing is a **computation**, `◯`-clause included,
   with no axioms at all.

3. **`R_i` is antisymmetric** (the paper's "poset"), though
   Fairtlough–Mendler ask only for a preorder.  Posets suffice for PLL and
   `Mod(D)` will be antisymmetric by construction.  Consequence to
   remember at W6: a `FinCM` countermodel found by another engine must be
   collapsed before it can be fed to the completeness theorem.

4. **`Cl` has no `◯` clause.**  Transcribed verbatim.  A `◯` clause is
   available and (Cl1) would survive it (`force_circ_of_force`), but `Cl`
   occurs in the side conditions of `⊃∈` and `⊃∉`, so extending it changes
   the *rules*.  Rule statements are W5 and are Matthew's.

5. **`Ĝ` is still two zones.**  `gHat = gAt ++ gImp`, the paper's.  `◯`
   fits neither zone and is not absorbed by `Cl` the way `∧` and `∨` are:
   `◯A` can be forced at `α` without `A` being forced there, exactly as
   `A ⊃ B` can be forced without `B`.  So the W5 design is not "add a `◯`
   right-introduction rule" but `Ĝ = Ĝ_at ∪ Ĝ_imp ∪ Ĝ_◯` with a join rule
   over three zones and an analogue of the support condition (J2).
   Recorded in `FRJLax/Core.lean` under "The third zone"; nothing is
   proposed.

## Axiom pins

`collectAxioms` is the only sound oracle.  Every pin below is
`#guard_msgs`-guarded **in the module itself**, so a regression is a build
failure.  `Classical.choice` is absent throughout.

**No axioms at all** — `clo_subset`, `clo_mono`, `clo_pv`, `clo_trans`,
`Model.force`, `Model.decForce`, `Model.force_mono`,
`Model.force_of_fallible`, `Model.forces_mono`, `clo_forces`,
`force_circ_of_force`, `not_PLL_of_countermodel`.

**`[propext]`** — `mem_rm`, `mem_cap`, `sfPos_closed`, `sfR_imp`,
`sfR_circ`, `sfL_circ`, `atPart_union_impPart`, `clo_sf`.

**`[propext, Quot.sound]`** — `Form.size_pos`, `size_le_of_mem_sf`,
`size_lt_of_mem_sfm`, `sf_subset_sfm_impL`, `sf_subset_sfm_circ`,
`mem_interAll`.

At W2, `FRJr`, `FRJi`, `Prems`, `Provable`, `joinCtxAt`, `joinCtxOr`,
`decJ1`, `decJ2` and the four replayed refutations all sit at
`[propext]`.

`FRJLax/Core.lean` has **zero imports**, on the model of
`LaxLogic/LJFOCore.lean`: no other calculus in this repo can carry any
part of the syntax or the closure.  `FRJLax/Model.lean` imports
`FRJLax.Core` and nothing else.  `lake build FRJLax` takes under two
seconds.
