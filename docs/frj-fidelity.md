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

**Lemma 3.4 is PROVED** (`FRJ/Step.lean`), together with the reification
that `↦` needs:

| Paper | Lean | Status |
|---|---|---|
| sequents as data; `Lhs(σ)`, `Rhs(σ)` | `Sequent`, `Sequent.lhs`, `.rhs` | done |
| `σ₁ ↦_R σ₂` | `Step`, indexed by `RuleName` | done |
| `σ₁ ↦₀ σ₂` | `Step₀` | done |
| `↦*` | `StepsRfl` (`Relation.ReflTransGen`) | done |
| "σ occurs in D" | `OccR`, `OccI` | done |
| Lemma 3.4(i) | `lhs_subset_of_step` | PROVED |
| Lemma 3.4(ii) | `lhs_clo_of_step₀` | PROVED |
| Lemma 3.4(iii) | `lhs_clo_of_steps` | PROVED |
| occurrence reaches the root by `↦*` | `occR_steps`, `occI_steps` | PROVED |
| 3.4(iii) as soundness uses it | `lhs_clo_of_occR` | PROVED |
| (Cl6) | `clo_trans` | PROVED |

`Step` is indexed by a rule name precisely so that part (i)'s condition
"`R ≠ ⊃∉`" is statable as written; `Ax^R`/`Ax^I` have no premises and so
contribute no constructor.  The join conclusion contexts are factored
out as `joinCtxAt`/`joinCtxOr` and both the rules and `↦` refer to them,
so the relation cannot drift from the calculus.  `occR_steps` supplies
each upward step from the side conditions stored in the derivation.

**SOUNDNESS IS PROVED** (2026-08-16).  `wf` (`wfR`/`wfI`, with
`atPart_union_impPart`) discharges divergence 4's obligation, and:

| Paper | Lean | Status |
|---|---|---|
| `Mod(D) = ⟨PS(D), ≤, ρ, V⟩` | `PreModel`, `preR`/`preI`, `modR` | done |
| `V(σ) = Lhs(σ) ∩ PV` sound (needs 3.4(iii)+(Cl5)) | `preR_closed`, `toKripke` | PROVED |
| the root of `Mod(d)` is `φ` of its root sequent | `preR_root_lbl` | PROVED |
| components are the regular sub-derivations | `preI_spec` | PROVED |
| forcing transfers to a component | `join_force_comp` | PROVED |
| **Lemma 3.9(i)** | `lemma39R`, `lemma39I0` | **PROVED** |
| **Lemma 3.9(ii)** | `lemma39I` | **PROVED** |
| the `⋈^At` case, with (P1)(P2)(P3) | `joinAt_case` | PROVED |
| the `⋈^∨` case | `joinOr_case` | PROVED |
| **Theorem 3.10** `Mod(D)` is a countermodel for `G` | `modR_countermodel` | **PROVED** |
| **Theorem 3.1** `⊢_FRJ(G) G ⟹ G ∉ IPL` | `soundness` | **PROVED** |

Notes on the proof.  Lemma 3.9(i) is split: `lemma39R` gives it at the
derivation's own root sequent, and its first component gives it at
p-sequents ("every world forces its own label"), which is what (P2)
consumes at worlds above the join.  In (ii), the world `σ_p` lies below
`σ`, outside `d`, so it is quantified — as the paper's own statement
already quantifies it — along with the ambient model; `RootAbove` is the
placement of a contributed model's root above `σ_p`, which is all the
`⊃∉` case needs.  The join case carries the paper's secondary induction
on `size H`, proving (P2) and (P3) simultaneously: (P2) at `A_k ⊃ B`
calls (P3) at `A_k`, and (P3) at `A_j` calls (P2) at the members of
`Σ^⊃_j ∩ Sf⁻(A_j)`; strictness of `size K < size A_j` comes from
`size_lt_of_mem_sfm`.

## §6 Completeness → `FRJ/Complete.lean` + `FRJ/Minimal.lean` — **PROVED**

| Paper | Lean | Status |
|---|---|---|
| `α ⊩* H`; `Λ*_α` | `Kripke.forceStar`, `lamStar` | done |
| `Λ*_α ⊆ Ĝ` | `lamStar_subset_gHat` | PROVED |
| Lemma 6.5, usable directions | `forces_clo_lamStar`, `mem_clo_lamStar` | PROVED |
| `h(α)` and its decrease going up | `ht`, `ht_lt` | PROVED |
| the "w.l.o.g." choice of `η` | `exists_min_eta` | PROVED |
| **Lemma 6.4**, existence half | `minMod` | **PROVED** |
| the `Ax^R` sub-case | `regPrime_ax` | PROVED |
| the `⋈^At` case | `regPrime_join` | PROVED |
| the `⋈^∨` case | `regOr_join` | PROVED |
| **Theorem 6.2(i)** `G ∉ IPL ⟹ ⊢_FRJ(G) G` | `completeness` | **PROVED** |
| soundness + completeness | `frj_iff_not_IPL` | **PROVED** |

The triple induction is the paper's, realised as the lexicographic
measure `(ht K a, t, C.size)`: (IH1) on the height of the world, (IH2)
on the sequent type with irregular before regular (`t = 0` vs `t = 1`),
(IH3) on the size of the goal.  Every recursive call decreases one
component: the `⊃` cases move to a strictly higher world (first), the
join cases drop from regular to irregular at the same world (second),
and the remaining cases shrink the goal (third).

Two simplifications, both sound because they only drop *restrictions*:

* the rank bounds (i) and (iii) of Lemma 6.4 serve minimality, which is
  out of scope, and the construction does not otherwise use them;
* PS1–PS4 are proof-search restrictions ("to reduce the proof-search
  space"), so the paper's minimal `Λ` and maximal `Θ` are not needed:
  `Λ := Λ*_α \ Σ₁` and `Θ := Λ*_α` satisfy the rules' own side
  conditions, which is all completeness requires.

### Divergence found in §6

The paper states Lemma 6.5 as `Λ_α = Cl(Λ_α) = Cl(Λ*_α)`.  Taken
literally the first equality is FALSE: `Cl` is generated by a grammar in
which `A` ranges over all formulas, so `Cl(Λ_α)` contains `Z ⊃ C` for
arbitrary `Z`, which need not lie in `Sf^L(G)` and hence not in `Λ_α`;
and the proof's step "`α ⊩ A ∧ B`, hence `A ∧ B ∈ Λ_α`" silently needs
`A ∧ B ∈ Sf^L(G)`.  Both directions the construction actually uses are
true and are proved here (`forces_clo_lamStar`, `mem_clo_lamStar`), so
nothing downstream is affected.

Also noted: in the `C = C₁ ∧ C₂` regular case the paper cites (IH2) where
the recursive call is regular-to-regular at the same world and so must
be (IH3); the measure decreases either way.

## Choice: where it came from, and how it went away

**Result.** The development is `[propext, Quot.sound]` throughout, with
`Classical.choice` in exactly one place — `frj_iff_not_IPL` — and there
for a reason that belongs to the statement, not the proof. All pins are
`#guard_msgs`-guarded in `FRJ/Audit.lean`, so a regression is a build
failure.

| | axioms |
|---|---|
| `soundness`, `completeness`, `completenessData`, `frj_iff_countermodel`, `minMod`, `minEta`, `modR_countermodel`, `lemma39R`, `lemma39I`, `lhs_clo_of_steps` | `[propext, Quot.sound]` |
| `nf_ext` | `[propext]` |
| `Kripke.decForce`, `Kripke.force_mono`, `not_IPL_of_countermodel`, `maxOn`, `eq_nil_of_forall_not_mem` | none at all |
| `frj_iff_not_IPL` | `[propext, Classical.choice, Quot.sound]` |

The last is unavoidable: `IPL G` is `∀ K, K.valid G`, and passing from
`¬ ∀ K, K.valid G` to `∃ K, ¬ K.valid G` is not constructively valid.
`frj_iff_countermodel : Provable G ↔ ∃ K, ¬ K.valid G` is the same
theorem with that step left to the caller, and is choice-free.

**Four sources, all traced rather than guessed.**

1. **Mathlib's `Finset` operations are choice-tainted at the DEFINITION
   level** — `Finset.instUnion`, `Finset.erase`, `Finset.image`,
   `Multiset.ndunion` — so any term merely *mentioning* `s ∪ t` carries
   choice however it is proved. Only `Finset.filter` is clean. The
   `List` API is axiom-free at definition level, with `List.dedup` and
   `List.erase` the two exceptions to avoid. The development moved to
   `List`.
2. **`Finite` costs choice to eliminate** (`Fintype.ofFinite`). `Kripke`
   now carries `elems`/`complete` with `decEq`/`decLe`/`decV`, which is
   also what makes `decForce` possible.
3. **Three Mathlib list lemmas**: `List.argmax_mem` and
   `List.le_of_mem_argmax` (though `List.argmax` itself is clean), and
   `List.eq_nil_iff_forall_not_mem`. Replaced by `maxOn` with its two
   specification lemmas, and by `eq_nil_of_forall_not_mem`.
4. **`tauto` and `push_neg` reason classically**, and so does
   Mathlib's `lt_or_eq_of_le` — necessarily, since deciding `a = b` in a
   partial order needs excluded middle.

   **CORRECTION (same day, by `#choice_path`).** This document first
   recorded the source as "`simp` pins `Classical.choice` where explicit
   `if_pos`/`if_neg` does not". That diagnosis was wrong. Measured:

   ```
   theorem t1 (n : Nat) : n ≤ n + 1 := by simp    -- TAINTED
   theorem t2 (n : Nat) : n ≤ n + 1 := by omega   -- clean
   theorem t3 {p : Bool} (h : p = false) :
       (if p = true then 1 else 0) = 0 := by simp  -- clean, [propext]
   ```

   and the chain for `countP_mono` as first proved runs

       cmA → cmA._f
           → IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT
           → contravariant_le_iff_contravariant_lt_and_eq
           → LE.le.lt_or_eq → lt_or_eq_of_le
           → Classical.propDecidable → Classical.choice

   So `simp` is the *route*, not the source: on a goal with no order in
   it (`t3`) it is clean, and `omega` on the very goal it taints (`t2`)
   is clean. What happened is that `simp` sent an inequality goal through
   Mathlib's ordered-algebra instances and out through `lt_or_eq_of_le`.
   Removing the `simp` calls from `countP_mono`, `countP_lt_countP` and
   `enumOf` fixed it because it removed that detour.

   **Guidance, corrected**: prefer `omega` to `simp` for arithmetic and
   order goals, and when a pin comes out dirty, *bisect* rather than
   guess — `Meta/Audit.lean`'s `#choice_path` does it in one command.

**A statement-level change was needed too, and is recorded here as a
divergence.** The irregular `⊃∈` rule

    Σ ; Θ, Λ → B
    ─────────────────  Θ ∩ Λ = ∅,  A ∈ Cl(Σ ∪ Λ)
     Σ, Λ ; Θ → A ⊃ B

requires, in Lemma 6.4, the zone `Θ₁` of a *given* derivation to be
split as `Θ ∪ Λ`. On `Finset` that split is a literal equality of the
rule's own index (`Finset.sdiff_union_of_subset`); on `List` it is not,
because `++` is neither commutative nor idempotent. Nor is there a
transport — "same members implies same derivations" is **false** here,
since `Ax^I` pins its own zone.

The fix changes the carrier, not the calculus: contexts are represented
canonically as `nf G l = (gHat G).filter (· ∈ l)`, the filter of `Ĝ`.
This is legitimate exactly because `wfR`/`wfI` prove every context of a
derivation is a subset of `Ĝ`, so `nf G` preserves membership; and every
side condition in the rule table is membership-based. Two contexts with
the same members are then literally the same list (`nf_ext`), which is
the property `++` lacks and `Finset` had. `Ax^I`, `∨` and both sides of
the irregular `⊃∈` write their computed zones canonically; canonicalising
*both* sides of `⊃∈` is what keeps Lemma 3.4(i) going through with no
extra side condition.

**Completeness is now Type-valued.** Lemma 6.4's two halves are records
carrying the derivation (`IrrWit`, `RegWit`), because extracting a
derivation from an existence proof needs `choose` or `Nonempty.some`,
both of which are choice. The same constraint forced the enumeration of
`Υ` (`enumOf`) and the minimal `η` (`minEta`) to be data: a `Prop`
cannot be eliminated into `Type`. The payoff is that

    completenessData : (K : Kripke) → ¬ K.valid G → Derivation G

is an algorithm taking a countermodel to a derivation, which is what the
campaign wanted from a refutation calculus in the first place.
