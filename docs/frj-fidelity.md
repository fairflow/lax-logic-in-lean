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

   **Outstanding obligation this creates.**  The join rules split each
   premise's zones with `atPart`/`impPart`, which filter for variables
   and for `⊃`-formulas.  If a premise's context could contain anything
   else — `⊥`, a conjunction — both filters would silently drop it, and
   the encoded rule would differ from the paper's.  It cannot, because
   `Ĝ = Ĝ_at ∪ Ĝ_imp` holds of every derivable sequent; but that is
   exactly the well-formedness lemma

       `wf : FRJr G Γ C → Γ ⊆ gHat G`  (and the `FRJi` analogue)

   which is **TODO**.  Until it is proved, the claim "the encoded joins
   are the paper's joins" rests on an unverified invariant.  It is the
   first thing to prove alongside soundness.

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
| (Cl2) `A ∈ Cl(Γ) ⟹ A ∈ Cl(Γ ∩ Sf(A))` | `clo_sf` | PROVED |
| `Sf(A)`, `Sf⁻(A) = Sf(A) \ {A}` | `sf`, `sfm`, `size_le_of_mem_sf` | PROVED |

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

## §3.1 Soundness → `FRJ/Model.lean` (construction) + `FRJ/Sound.lean`

**Correction, 2026-08-16.**  An earlier version of this section proposed
a `PModel` structure carrying `forces_lhs` — which *is* Lemma 3.9(i) —
as an invariant of the construction, turning part of the conclusion into
something assumed by the object being built.  That is a restructuring of
the proof, not the proof, and it has been removed.  The rule is: the
paper's definitions are definitions here, and the paper's lemmas are
theorems here.

**The paper's proof, which is the one to follow.**

`Mod(D) = ⟨PS(D), ≤, ρ, V⟩` with `PS(D)` the p-sequents of `D`,
`σ₁ ≤ σ₂ iff σ₂ ↦* σ₁`, `V(σ) = Lhs(σ) ∩ PV`; and `φ(σ)` the p-sequent
immediately above a regular `σ`.  Then:

* **Lemma 3.4** (`lemma:lhs`), on `↦`: (i) `σ₁ ↦_R σ₂` with `R ≠ ⊃∉`
  implies `Lhs(σ₂) ⊆ Lhs(σ₁)`; (ii) `σ₁ ↦ σ₂` implies
  `Lhs(σ₂) ⊆ Cl(Lhs(σ₁))`; (iii) the same for `↦*`.
* **Lemma 3.9**, for every sequent `σ` occurring in `D`: (i) if
  `σ = Γ ⇒ C` then `φ(σ) ⊩ Γ` and `φ(σ) ⊮ C`; (ii) if
  `σ = Σ;Θ → C`, then for every `σ_p ∈ PS(D)` with `σ ↦ σ_p` and
  `σ_p ⊩ Σ ∩ Sf⁻(C)`, we have `σ_p ⊮ C`.
* **Theorem 3.10**: `Mod(D)` is a countermodel for `G`; hence
  Theorem 3.1, `⊢_FRJ(G) G` implies `G ∉ IPL`.

The proof of Lemma 3.9 is a **main induction (IH1) on the height of `σ`
in `D`**, by cases on the last rule, with a **secondary induction (IH2)
on `size H`** inside the join case proving (P2) `H ∈ Γ^⊃ ⟹ σ ⊩ H` and
(P3) `H = A_j ⟹ σ ⊮ A_j` simultaneously.  Note where IH1 is applied in
(P2): at a p-sequent `σ_p` *above* the join, not at an immediate
premise.

**What is built so far, and how it relates to the paper's `Mod(D)`.**

`addRoot` is not a reformulation: a `⋈` rule's conclusion is a fresh
p-sequent lying below exactly the p-sequents of its premises, and every
p-sequent has a unique p-sequent immediately below it, so
`⟨PS(D), ≤⟩` *is* computed by placing a fresh root below the disjoint
union of the premises' p-sequent posets.  `ARLe` is the paper's `≤`
and `solo` (empty index) is the one-world `Mod(D)` of an `Ax^R`
derivation.

`addRoot_force_comp` — forcing agrees at component worlds — is an
artefact of computing `Mod(D)` in pieces rather than all at once; the
paper never needs it because it works in the single model `Mod(D)`
throughout.  It is a proved lemma about the construction, not an
assumption, and it is what will let the induction refer to a premise's
part of `Mod(D)`.

PROVED so far: `addRoot` is a Kripke model; `addRoot_force_comp`;
`solo_forces_root`; and `axR_sound`, the `Ax^R` case of Lemma 3.9(i)
(`φ(σ) = σ`, `V(σ) = Ĝ_at \ {F}`).

**OPEN**: `wf` (see divergence 4 above), Lemma 3.4, the remaining cases
of Lemma 3.9, Theorem 3.10, Theorem 3.1.  To state Lemma 3.9 as the
paper states it — "for every sequent `σ` occurring in `D`" — the
occurrences of `D` must be reified, since IH1 is used at p-sequents
above `σ` rather than at immediate premises.  That reification is the
next piece of work and must be done before the induction is attempted.

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
