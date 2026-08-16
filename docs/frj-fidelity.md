# FRJ(G) for IPC — fidelity table and proof architecture

*Started 2026-08-16.  Source of truth: Camillo Fiorentini and Mauro
Ferrari, "Duality between unprovability and provability in forward
proof-search for Intuitionistic Propositional Logic", ACM TOCL 21(3),
2020 — read from the arXiv LaTeX source of arXiv:1804.06689
(`frj-corr.tex`, 6682 lines), which is the full journal version.  The
in-repo note `docs/frj-lifting.md` is a PARAPHRASE written for
orientation and is **not** a source for this formalisation; formalising
from it is exactly what produced the unsound FRJ◯ rule table.*

This document is the deliverable that makes the formalisation checkable
against the original: every Lean definition and theorem is listed
against the numbered item of the paper it encodes, and every divergence
is recorded as a divergence.

## Scope

**In scope**: §2 (preliminaries), §3 (the calculus and its soundness),
and the completeness of FRJ(G).

**Route chosen for completeness, and why.**  The paper proves
completeness of FRJ(G) twice.

* *Journal main text* (Thm. `theo:GBU-FRJ`, then "Completeness of
  FRJ(G) and GBU(G)"): as a corollary of the DUALITY
  `⊢_GBU(G) G  iff  ⊬_FRJ(G) G`, which needs the whole second calculus
  GBU(G) (§5), the saturated-database machinery (§4) and the
  correctness of the `Search` procedure.
* *§6 Minimality* (Lemma `lemma:minMod`, Thm `theo:minMod`): a DIRECT
  construction from an arbitrary countermodel, by induction on the
  height of its worlds.  The paper states in a footnote that this is
  how completeness was proved in the TABLEAUX 2017 conference version.

We take the **direct route**.  It is equally published, it is a
fraction of the work, and it does not require formalising a second
calculus and a search procedure to obtain a theorem about the first.

**Not in scope**: GBU(G), saturated databases, `Search`, the
minimal-height results of §6 beyond what completeness itself needs, and
the termination/complexity material of §3.2.

**No IPC proof system is needed anywhere.**  The paper defines IPL
semantically — "Intuitionistic Propositional Logic IPL coincides with
the set of valid formulas" — so both theorems in scope are statements
about Kripke semantics alone.  This removes the whole question of which
in-repo IPC development to consume, and with it the risk that a
borrowed notion means something subtly different.  (A bridge to a
syntactic IPC would be an optional extra, and would consume an existing
completeness theorem read-only.)

## Divergences, in full

1. **Worlds of `Mod(D)` are p-sequent OCCURRENCES, not p-sequents.**
   The paper sets `PS(D)` to be the *set* of p-sequents occurring in
   `D`, identifying two occurrences of the same sequent; we keep them
   distinct.  Both are finite posets with a minimum and a monotone
   valuation, and `Mod(D)` is a countermodel for `G` iff its quotient
   is, so soundness is insensitive to the choice.  The identification
   matters for the minimal-height results of §6, which are out of
   scope.  Recorded in `FRJ/Model.lean`.

2. **The ⊃-clause of forcing is written as an implication.**  The paper
   writes "for every β ≥ α, `K,β ⊮ A` or `K,β ⊩ B`"; we write
   `∀ β ≥ α, K,β ⊩ A → K,β ⊩ B`.  Standard, and equivalent; writing the
   disjunction would put excluded middle into the definition itself.

3. **`k ∈ {1,2}` in the `∧` rules is encoded as two constructors**
   (`andR1`/`andR2`, `andI1`/`andI2`).  One rule with a parameter, two
   constructors: the same rule instances.

4. **Sequent well-formedness is a lemma, not a type.**  The paper
   defines the sequent *set* by the constraints `Γ ⊆ Ĝ`,
   `Σ ∪ Θ ⊆ Ĝ`, `C ∈ Sf^R(G)`.  We index the judgment by plain
   `Finset`s and carry the figure's blanket condition
   `Rhs(σ) ∈ Sf^R(G)` as a field `hgoal` on every constructor; the
   context constraints then propagate from the axioms and are a lemma
   rather than an index.  This keeps the inductive family free of proof
   indices.  (The Finite Rule Property, which the constraints exist to
   give, is only needed for proof-search — out of scope here.)

## §2 Preliminaries → `FRJ/Basic.lean`

| Paper | Lean | Status |
|---|---|---|
| language `L`, connectives `∧ ∨ ⊃ ⊥`, variables `PV` | `Form` | done |
| `¬A := A ⊃ ⊥` | `Form.neg` | done |
| `size A` | `Form.size` | done |
| `Prime = PV ∪ {⊥}` | `Form.isPrime` | done |
| `Fm⊃` | `Form.isImp` | done |
| Kripke model: finite poset, minimum `ρ`, monotone `V` | `Kripke` | done |
| the five forcing clauses | `Kripke.force` | done |
| monotonicity property | `Kripke.force_mono` | PROVED |
| `K,α ⊩ Γ` | `Kripke.forces` | done |
| validity; `IPL` = the valid formulas | `Kripke.valid`, `IPL` | done |
| countermodel | `Countermodel`, `not_IPL_of_countermodel` | PROVED |
| `Sf^L(G)`, `Sf^R(G)`: the four defining clauses | `sfL`, `sfR` computed; `SfClosed` | PROVED (`sfPos_closed`) |
| `G ∈ Sf^R(G)` | `sfR_self` | PROVED |
| the ∧/∨ clause, both polarities | `sfR_and/sfR_or/sfL_and/sfL_or` | PROVED |
| the two ⊃ clauses | `sfR_imp`, `sfL_imp` | PROVED |
| `Ĝ_at`, `Ĝ_imp`, `Ĝ` | `gAt`, `gImp`, `gHat` | done |
| `Γ^at`, `Γ^⊃` notation | `atPart`, `impPart` | done |
| closure `Cl(Γ)` by the grammar | `Clo` | done |
| (Cl1) `α ⊩ Γ ⟹ α ⊩ Cl(Γ)` | `clo_forces` | PROVED |
| (Cl3) `Γ ⊆ Cl(Γ)` | `clo_subset` | PROVED |
| (Cl4) monotone | `clo_mono` | PROVED |
| (Cl5) `Cl(Γ) ∩ PV = Γ ∩ PV` | `clo_pv` | PROVED |
| (Cl2) `A ∈ Cl(Γ) ⟹ A ∈ Cl(Γ ∩ Sf(A))` | — | **TODO** (needed by the `⊃∈` irregular case) |
| `Sf(A)`, `Sf⁻(A) = Sf(A) \ {A}` | — | **TODO** (needed by Lemma 3.9(ii)) |

## §3 The calculus → `FRJ/Calculus.lean`

Figure "The calculus FRJ(G)", every rule, with side conditions:

| Rule | Lean constructor |
|---|---|
| `Ax^R`  `⊢ Ĝ_at \ {F} ⇒ F`, `F ∈ Prime` | `FRJr.axR` |
| `Ax^I`  `⊢ ∅ ; Ĝ_at\{F}, Ĝ_imp → F` | `FRJi.axI` |
| `∧` regular, `k = 1,2` | `FRJr.andR1/andR2` |
| `∧` irregular, `k = 1,2` | `FRJi.andI1/andI2` |
| `∨`, sides `Σ₁ ⊆ Σ₂∪Θ₂`, `Σ₂ ⊆ Σ₁∪Θ₁` | `FRJi.orI` |
| `⊃∈` regular, side `A ∈ Cl(Γ)` | `FRJr.impIn` |
| `⊃∈` irregular, sides `Θ∩Λ = ∅`, `A ∈ Cl(Σ∪Λ)` | `FRJi.impInI` |
| `⊃∉`, sides `Θ ⊆ Cl(Γ)∩Ĝ`, `A ∈ Cl(Γ)\Cl(Θ)` | `FRJi.impNotIn` |
| `⋈^At`, sides (J1),(J2), `F ∈ Prime \ Σ^at` | `FRJr.joinAt` |
| `⋈^∨`, sides (J1),(J2), `{C₁,C₂} ⊆ Υ` | `FRJr.joinOr` |
| `Γ⊃/Υ = {Y⊃Z ∈ Γ⊃ | Y ∈ Υ}` | `restrict` |
| `⊢_{FRJ(G)} G` | `Provable` | done |

## §3.1 Soundness → `FRJ/Model.lean` (kit done) + `FRJ/Sound.lean` (TODO)

`Mod(D)`, `φ`, and Lemma 3.9 are what the remaining work encodes.  The
architecture below was derived from the paper's own proof (Appendix,
"Soundness of FRJ(G)") and is the plan to follow.

**Why a plain Kripke model is not enough.**  The join case of Lemma 3.9
applies the main induction hypothesis at an *arbitrary* p-sequent above
the join, and uses both that that world forces its own left formulas
and that labels shrink modulo closure as one goes down.  So the
construction must carry the labelling.  Hence `PModel`: the model, the
map `lhs` sending each world to `Lhs` of its p-sequent, and

* `val_eq`  — `V(σ) = Lhs(σ) ∩ PV`;
* `lhs_clo` — Lemma 3.4(iii): `w ≤ v ⟹ lhs w ⊆ Cl(lhs v)`;
* `forces_lhs` — Lemma 3.9(i) at every world.

Done so far: `ARLe`, `addRoot` (fresh root below a finite disjoint union
of models, with the empty index giving the `Ax^R` leaf),
`addRoot_force_comp` (**forcing is preserved at component worlds**,
because each component is upward closed — this is what lets a premise's
model be treated in isolation), and `PModel.solo`.

**The two statements to prove, by mutual induction.**

* **(R)** for `d : FRJr G Γ C`: a `PModel` `P` and a world `r` with
  `P.lhs r = Γ` and `¬ P.K.force r C`.  (`P.K.forces r Γ` is then
  `forces_lhs`.)  The distinguished world is the paper's `φ(σ)`, and
  `lhs r = Γ` holds because `andR`/`impIn` do not change the context.

* **(I)** for `d : FRJi G St Th C`: for every `PModel` `P` and world `w`
  with `Realises P w d`, `(∀ X ∈ P.lhs w, Clo (St ∪ Th) X)` and
  `P.K.forces w (St ∩ Sf⁻(C))`, we have `¬ P.K.force w C`.

  `Realises P w d` is defined by recursion on `d` and says exactly what
  the `⊃∉` case needs: at each `impNotIn` inside `d`, with regular
  premise `Γ ⇒ B`, there is `v ≥ w` in `P` with `v ⊩ Γ` and `v ⊮ B`.
  Defining it by recursion avoids having to reify an abstract embedding
  of a forest of sub-models.

**Case checks already done on paper** (these are the propagation
obligations, and they all go through):

* the hypothesis `∀ X ∈ lhs w, Clo (St ∪ Th) X` propagates to premises —
  for `∨` because `Σ∪Θ ⊆ Σ_k ∪ Θ_k` follows from the two side
  conditions, for `⊃∈` irregular because `Σ∪Λ∪Θ` equals the premise's
  `Σ∪(Θ∪Λ)`;
* `w ⊩ St ∩ Sf⁻(C)` propagates because `Sf⁻(C_k) ⊆ Sf⁻(C₁∨C₂)` and
  `Sf⁻(A_k) ⊆ Sf⁻(A₁∧A₂)`;
* the `⊃∈` irregular case needs **(Cl2)**, still to be proved.

**The join case is the substantial one** and needs a *secondary*
induction on `size H`, proving simultaneously

* (P2) `H ∈ Γ^imp ⟹ σ ⊩ H`, and
* (P3) `H = A_j ⟹ σ ⊮ A_j`,

where (P2) at `H = A_k ⊃ B` calls (P3) at `A_k` (strictly smaller), and
(P3) at `A_j` calls (P2) at the members of `Σ^imp_j ∩ Sf⁻(A_j)`
(strictly smaller).  (P2) additionally applies the *main* induction
hypothesis at a world `σ_p` above the join, which is where `forces_lhs`
and `lhs_clo` are consumed.

## §6 Completeness → `FRJ/Complete.lean` (TODO)

Lemma `lemma:minMod`, existence half only (the rank bounds (i) and (iii)
are needed for minimality, not for completeness): for a countermodel
`K` of `G`, a world `α` and `C ∈ Ω_α`, derivations of an irregular
`σ^irr(α,C) = Σ;Θ → C` with `Σ ⊆ Λ*_α ⊆ Σ∪Θ`, and of a regular
`σ^reg(α,C) = Γ ⇒ C` with `∃β ≥ α`, `Λ*_β ⊆ Γ`, where

* `α ⊩* H` iff `α ⊩ H` and either `H ∈ PV` or `H = A ⊃ B` and `α ⊮ A`;
* `Λ*_α = {A ∈ Sf^L(G) | α ⊩* A}`, `Ω_α = {C ∈ Sf^R(G) | α ⊮ C}`.

Induction: worlds in increasing order of height (well-founded on a
finite poset), and for each world the formulas of `Ω_α` in increasing
order of size.  Then completeness is `σ^reg(ρ, G)`.
