# Mechanising Propositional Lax Logic, Slime-Free

## A case study in formal metatheory: from transport hell to a complete Kripke semantics

*Draft companion paper to the `lax-logic-in-lean` development.*

### Abstract

We present a complete mechanisation, in Lean 4 over Mathlib, of the core
metatheory of Propositional Lax Logic (PLL) as developed by Fairtlough and
Mendler (*Information and Computation* 137(1), 1997): natural deduction,
conservativity over intuitionistic propositional logic, Kripke constraint
models with fallible worlds, soundness, and completeness via a canonical
model of maximally consistent theories, together with the deduction theorem,
strong extensionality, frame-correspondence results, machine-checked
underivability of the characteristic non-theorems, and an embedding of a
Hilbert-style proof checker into the natural deduction system.

The development is equally a case study in *avoiding the transport problem*
("green slime", transport hell) in dependently typed proof assistants.  An
earlier iteration of this repository was blocked by index-transport casts.
Rather than managing the casts, we redesigned the derivation system so they
cannot arise: contexts are plain lists extended only by constructor forms,
and the identity rule takes a membership *hypothesis* rather than pinning a
formula at a position.  The entire development — roughly 2,300 lines covering
syntax to completeness — contains **no cast, no `▸`-transport of data, no
heterogeneous equality, and no `sorry`**.  As a side effect, mechanisation
found three latent soundness bugs in the pre-existing formalisation, one of
which made every system in the repository inconsistent.

---

## 1. Introduction

Propositional Lax Logic extends intuitionistic propositional logic (IPL)
with a single modality `◯` ("somehow") satisfying

| axiom | scheme | reading |
|---|---|---|
| `◯R` | `M ⊃ ◯M` | unit |
| `◯M` | `◯◯M ⊃ ◯M` | multiplication |
| `◯S` | `(◯M ∧ ◯N) ⊃ ◯(M ∧ N)` | strength |

— algebraically, `◯` is a strong monad on the Heyting algebra of
propositions; proof-theoretically it is the modality of *correctness up to
constraints* used in hardware verification, and (via Moggi and Benton–Bierman–de
Paiva) the type of computations in a computational metalanguage.  `◯` is
unusual in having the flavour of both possibility and necessity: its Kripke
clause is a ∀∃ statement over two accessibility relations.

**Contributions.**  All results are mechanised in Lean 4; the table in §8
maps each theorem of Fairtlough–Mendler (henceforth F&M) to a Lean
declaration.

1. A *slime-free* natural deduction system for PLL (`PLLNDCore.lean`) in
   which weakening, exchange and contraction are admissible by a single
   renaming traversal, and no derivation ever needs an index cast.
2. Strong conservativity over IPL (F&M Thm 2.4), in two independent forms:
   a `Prop`-level translation into a standalone IPL judgment, and a
   cast-free erasure function on proof terms.
3. The deduction theorem (F&M Prop 2.2) and strong extensionality
   (F&M Thm 2.5), the latter via substitution contexts.
4. Kripke constraint models with fallible worlds (F&M Defs 3.1–3.2) and
   soundness (Thm 3.3).
5. Completeness (F&M Lemma 4.2, Lemma 4.3, Thm 4.4) via maximally
   consistent *triples* of theories, using Zorn's lemma in place of F&M's
   formula enumeration; strengthened from validity to sequent consequence:
   `Γ ⊨ φ ↔ Nonempty (LaxND Γ φ)`.
6. The three counter-models of F&M Figure 3 as finite, *decidably
   evaluable* models, giving machine-checked underivability of `¬◯⊥`,
   `◯(A∨B) ⊃ (◯A∨◯B)` and `(◯A⊃◯B) ⊃ ◯(A⊃B)` by `decide`.
7. The soundness halves of the frame correspondences of F&M Thm 4.5
   (`F = ∅` for `¬◯⊥`; mutual confluence for `◯`-distribution over `∨`).
8. Half of F&M Thm 2.3: a verified embedding of a Hilbert-style proof
   checker into the natural deduction system.
9. Three latent soundness bugs in the pre-existing formalisation, found
   *by* the mechanisation (§7).

## 2. The transport problem, and the design that dissolves it

The first iteration of this repository indexed derivations by contexts of
the form `Γ ++ φ :: Δ`:

```lean
| impIntro : LaxND (Γ ++ φ :: Δ) ψ → LaxND (Γ ++ Δ) (ifThen φ ψ)
```

This is *green slime* in McBride's sense: a function application (`++`) in
the index of a constructor's return type.  Unification cannot invert `++`,
so dependent pattern matching sticks, and every lemma that rewrites an index
— e.g. commuting an erasure function over a context — demands a transport.
The erasure function for conservativity required fifteen explicit `cast`s,
and the conservativity theorem itself was unprovable in practice because the
`isIPLProof` predicate does not compute through `cast`.

Two standard mitigations were applied and compared:

**(a) A blessed-cast API** (the `eqToHom` pattern from mathlib's category
theory): one canonical cast per indexed family plus a simp set
(`cast_rfl`, `cast_trans`, commutation, predicate-invariance), each lemma
provable by `subst; rfl` thanks to definitional proof irrelevance.  This
retroactively unblocked the old system's conservativity theorem
(`PLLNDProofPostZoom.lean`), demonstrating that the technique works — but it
manages the problem rather than removing it.

**(b) Slime removal** (`PLLNDCore.lean`): contexts are `List PLLFormula`,
rules extend them only as `φ :: Γ`, and the identity rule is

```lean
| iden {Γ φ} (h : φ ∈ Γ) : LaxND Γ φ
```

Every index in a constructor return type is now a variable or a constructor
form.  The membership hypothesis replaces positional bookkeeping, so
weakening, exchange and contraction are *admissible* by one induction:

```lean
def LaxND.rename (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ') : LaxND Γ φ → LaxND Γ' φ
```

The old positional exchange rule (`move`) becomes a one-line corollary.
Crucially, `List.map` computes definitionally on `[]` and `::`, so the
erasure translation and *both* conservativity proofs go through without a
single cast.  Option (b) is the load-bearing design decision of the
development: everything below inherits its freedom from transport.

A point of honesty about Lean's `Prop`/`Type` boundary: `φ ∈ Γ` is a `Prop`,
so it cannot be pattern-matched when *building* a derivation term (large
elimination); where the development needed that (e.g. introducing a member
of a finite disjunction), the right move was always to descend to
`Nonempty (LaxND …)` — i.e. to `Prop` — exactly where the informational
content drops.  The type theory enforces the erasure discipline the logic
suggests.

## 3. Proof theory

**Conservativity** (F&M Thm 2.4).  Route A defines the somehow-free
fragment as its own `Prop`-valued judgment `IPLND` and proves

```lean
theorem conservativity_prop : LaxND Γ φ → IPLND (Γ.map erase) (erase φ)
```

by a twelve-case induction in which every case is a bare constructor
application — the definitional computation of `map` on `::` is exactly what
slime-freedom buys.  Route B keeps proof terms: a total, cast-free
translation `LaxND.erased` together with the predicate `isIPLProof`, and

```lean
theorem conservativity : (p : LaxND Γ φ) → p.erased.isIPLProof
```

The classical statement (IPL sequents prove no new IPL theorems) follows by
`erase`-idempotence on IPL formulas.

**Deduction theorem** (F&M Prop 2.2).  In the Hilbert presentation this
needs an induction over derivations; natural deduction internalises it, and
the mechanised statement is two lines (`deduction_iff`).  F&M remark that
this property *fails* for the standard modal logics K, T, S4 — it is one of
the ways `◯` is proof-theoretically tame.

**Strong extensionality** (F&M Thm 2.5).  Syntactic contexts `C[·]` are
represented by substitution for a designated propositional constant, and

```lean
theorem strong_extensionality :
  Nonempty (LaxND [] ((iffPLL M N).ifThen (iffPLL C[M] C[N])))
```

is proved by induction on `C` through congruence lemmas for each connective;
the `◯` case is the two lax rules back to back.  The proof lives at the
level of derivability-from-sets (`⊩`, §5), where the deduction theorem and
cut make the congruence steps one-liners.

**Hilbert embedding** (half of F&M Thm 2.3).  The repository contains an
independently written Hilbert-style proof checker (`PLLProof.lean`,
`PLLAxiom.lean`).  We prove each of its twelve axioms in `LaxND`
(`axiomDeriv`) and then, by induction on checked proofs, that every formula
recorded in a valid proof is a theorem (`formulas_derivable`), hence

```lean
theorem hilbert_to_ND : p.isProofOf φ → Nonempty (LaxND [] φ)
```

The converse (ND → Hilbert) needs the deduction theorem *inside* the Hilbert
system and is future work.

## 4. Kripke constraint models and soundness

A constraint model (F&M Def 3.1) is `(W, Rₘ, Rᵢ, V, F)`: two preorders with
the single frame condition `Rₘ ⊆ Rᵢ`, a hereditary set `F` of *fallible*
worlds, and a hereditary valuation, full on `F`.  Forcing is standard
intuitionistic forcing except

- `w ⊨ ⊥  iff  w ∈ F` — fallible worlds are honest inconsistency points,
  and validate every formula (`force_of_fallible`);
- `w ⊨ ◯N  iff  ∀ v ≥ᵢ w, ∃ u, v Rₘ u ∧ u ⊨ N` — the ∀∃ clause that gives
  `◯` its dual character.

Soundness (F&M Thm 3.3) is by induction on derivations, in sequent form
`Γ ⊨ φ`.  The mechanised proof consumed the frame conditions exactly where
the paper predicts: reflexivity of `Rᵢ` in the elimination rules,
reflexivity of `Rₘ` for `◯`-introduction, transitivity of `Rₘ` for
`◯`-elimination, heredity (hence `Rₘ ⊆ Rᵢ`) in the introduction rules.

## 5. Completeness

Worlds of the canonical model are F&M's *theories*: triples `(Γ, Δ, Θ)` of
formula sets — validated, falsified, and falsified at every `Rₘ`-successor.
The third component compensates for the fact that falsity of `◯M` is not
expressible by putting a subformula anywhere; it is the distinctive feature
of the F&M proof.  A theory is **consistent** when for all finite
`Ds ⊆ Δ`, `Ts ⊆ Θ` with `Ds ++ Ts ≠ []`,

```
Γ ⊬ ⋁Ds ∨ ◯(⋁Ts).
```

The nonemptiness guard — the empty disjunction is *absent*, not `⊥` — is
essential: it makes the theory `(all formulas, ∅, ∅)` consistent, and after
maximal extension it is precisely the single fallible world the canonical
model needs (since `◯⊥` is satisfiable in PLL, `Rₘ`-successors witnessing
`⊥` must exist somewhere).  Mechanising this guard faithfully was the most
delicate part of the development; the case-split definition `disjOf` and its
intro/elim/transform lemmas encapsulate it.

Derivability from sets, `Γ ⊩ φ`, is defined with compactness built in
(some finite list from `Γ` derives `φ`), and the admissible rules F&M call
"structural reasoning" — cut, deduction, disjunction elimination, reasoning
under finite disjunctions, `◯`-functoriality, and `K ∨ ◯L ⊢ ◯(K ∨ L)` —
are provided by a small toolkit (`PLLConsequence.lean`) in which every
context manipulation is a `rename`.

**Lindenbaum.**  Where F&M enumerate formulas, we use Zorn's lemma:
consistency has finite character, so unions of chains of consistent theories
are consistent, and mathlib's `zorn_le_nonempty₀` (over a mere preorder —
antisymmetry is never needed) yields maximally consistent extensions.  All
seven properties of F&M Lemma 4.2 follow from maximality: deductive closure,
primeness, the implication and falsification decompositions, `Θ ⊆ Δ`, and
totality.  Notably, primeness is proved *by* disjunction elimination — the
repaired `orElim` rule (§7) is load-bearing here.

**Truth lemma and completeness** (F&M Lemma 4.3, Thm 4.4).  With
`Rᵢ := ⊆` on validated parts and `Rₘ := ⊆` on validated and modally
falsified parts, membership forces and falsification refutes, by induction
on the formula; the two `◯` cases perform the theory extensions of the
paper verbatim.  The endpoint is stronger than F&M's Thm 4.4 (validity):

```lean
theorem consequence_iff_derivable : Γ ⊨ φ ↔ Nonempty (LaxND Γ φ)
```

Everything in this section is `Prop`-level — sets, derivability, Zorn — so
the transport problem is not merely avoided but structurally impossible.

## 6. Executable counter-models and frame correspondences

Forcing over a finite model with decidable data is decidable
(`ConstraintModel.decForce`, by structural recursion on the formula using
`Fintype` quantifier instances).  The three counter-models of F&M Figure 3
are then two- and three-world models whose defining relations are decidable
by construction, and the underivability theorems are one `decide` away from
soundness:

```lean
theorem not_provable_not_somehow_false :
  ¬ Nonempty (LaxND [] (notPLL (somehow falsePLL)))
```

and likewise for `◯(A∨B) ⊃ (◯A∨◯B)` and `(◯A⊃◯B) ⊃ ◯(A⊃B)`.  The kernel
*evaluates* the model — quantifiers over worlds, the two frames, the
valuation — so these are counter-examples one can run, not just read.
Together with §3 this locates PLL precisely: a nontrivial extension of IPL
(no theorem of IPL becomes one by sprinkling `◯`), with a genuinely modal
`◯` (neither possibility-like distribution over `∨` nor necessity-like
distribution over `⊃` holds).

For F&M Thm 4.5 we prove the soundness halves of both frame
correspondences: on models with `F = ∅` the scheme `¬◯⊥` is valid, and on
models whose frames are *mutually confluent* the ∀∃ clause collapses to the
simple possibility clause `∃ u, w Rₘ u ∧ u ⊨ M`
(`force_somehow_iff_of_confluent`), from which distribution of `◯` over `∨`
follows.  The completeness halves require relativising the whole §5
machinery to extended proof systems and are future work.

## 7. Formalisation as debugging: three latent bugs

Mechanisation is often sold as insurance against subtle errors in new
proofs; in this project its first yield was three *existing* errors, none
found by testing or review:

1. **Every ND system in the repository was inconsistent.**  All predecessor
   systems stated disjunction elimination without its major premise —
   from `φ, Γ ⊢ χ` and `ψ, Γ ⊢ χ` conclude `Γ ⊢ χ` — which derives every
   formula (take `φ = ψ = χ`).  Nothing in Lean objects: an unsound proof
   system is a perfectly well-formed inductive type.  The bug surfaced only
   when the *elimination* was inspected for the semantic audit.  The
   repaired rule turned out to be load-bearing twice over: primeness in the
   completeness proof and the disjunction congruence in extensionality both
   need it.
2. **The Hilbert `orElim` axiom** read `(A∧B) ⊃ C` where its own comment
   says `(A∨B) ⊃ C` — still valid, but disjunction elimination was
   underivable in the Hilbert system.
3. **The proof checker's `isValid`** did not check validity recursively
   under a modus-ponens step, so stacked steps could launder unjustified
   formulas: a syntactically "valid" proof of `⊥` existed.  (Exercise: with
   `truePLL := ⊥ ⊃ ⊥` available as an axiom instance and conditionals
   checked only against *recorded* formulas, two steps suffice.)

The pattern is worth stating: **the mechanised metatheorems are what caught
the bugs**, not the definitions themselves.  Soundness-against-a-semantics
and bridge theorems between independently written systems are cheap,
high-yield sanity properties for any formalised logic.

## 8. Correspondence with Fairtlough–Mendler 1997

| F&M | statement | Lean | file |
|---|---|---|---|
| Prop 2.2 | deduction theorem | `deduction_iff` | `PLLTheorems.lean` |
| Thm 2.3 (⇐) | Hilbert → ND | `hilbert_to_ND` | `PLLHilbert.lean` |
| Thm 2.4 | strong conservativity | `conservativity_prop`, `conservativity`, `conservativity_IPL` | `PLLNDCore.lean` |
| Thm 2.5 | strong extensionality | `strong_extensionality` | `PLLTheorems.lean` |
| Def 3.1–3.2 | constraint models, forcing | `ConstraintModel`, `force` | `PLLKripke.lean` |
| (heredity) | validity hereditary; fallible worlds force all | `force_hered`, `force_of_fallible` | `PLLKripke.lean` |
| Thm 3.3 | soundness | `soundness` | `PLLKripke.lean` |
| Lemma 4.2 | maximal consistent theories | `MaxConsistent.*` | `PLLCompleteness.lean` |
| (Lindenbaum) | maximal extension | `exists_maxConsistent_extension` (via Zorn) | `PLLCompleteness.lean` |
| Lemma 4.3 | truth lemma | `truth_lemma` | `PLLCompleteness.lean` |
| Thm 4.4 | completeness (strengthened to sequents) | `completeness`, `consequence_iff_derivable` | `PLLCompleteness.lean` |
| Fig 3 | three counter-models | `not_provable_*` (by `decide`) | `PLLFrames.lean` |
| Thm 4.5 (soundness) | frame correspondences | `force_not_somehow_false_of_F_empty`, `force_somehow_iff_of_confluent`, `force_somehow_or_dist_of_confluent` | `PLLFrames.lean` |
| — | axioms `◯R`,`◯M`,`◯S`; functoriality | `somehowR/M/S`, `somehowFunctor` | `PLLTheorems.lean` |

Not yet mechanised: cut elimination (Thm 2.6) and its corollaries
(disjunction property, `◯`-reflection, subformula property, decidability,
Thm 2.8); the finite model property (Thm 4.6); the completeness halves of
Thm 4.5; the J-space translation (Thm 3.5); the bimodal classical embedding
(Thm 5.1).

## 9. Engineering lessons

1. **Remove slime; don't manage it.**  The blessed-cast API works (we built
   it, and it rescued the legacy proofs), but the slime-free redesign made
   the *new* proofs shorter than the old system's statements.  When
   constructor return indices are variables or constructor forms, `simp`,
   `induction` and definitional computation do the work that transports
   used to obstruct.
2. **Membership beats position.**  `iden : φ ∈ Γ → LaxND Γ φ` converts all
   structural bookkeeping into monotone renaming — one lemma, used
   everywhere from weakening to the Hilbert bridge.
3. **Let `Prop` absorb the classical content.**  Forcing, set-derivability,
   theories, Zorn: none of it touches proof terms, so completeness is
   transport-free by construction.  The `Prop`/`Type` elimination
   restriction actively signals where to make the switch.
4. **Prefer Zorn to enumeration in Lindenbaum arguments.**  Finite
   character of consistency is easier to mechanise than a formula
   enumeration with a three-way case split at each stage, and no
   countability instance is needed.
5. **Finite counter-models should be `decide`-able.**  A generic
   decidability instance for forcing turns every hand-drawn Kripke diagram
   into a checked underivability theorem for the cost of writing down the
   relations.
6. **Mechanise the metatheorems early.**  All three latent bugs (§7) were
   caught by soundness/bridge theorems, not by inspection of definitions.

## 10. Future work

- **Cut elimination and decidability** (F&M Thms 2.6, 2.8): a sequent
  calculus with the `◯R`/`◯L` rules, the extra principal reduction of F&M
  Figure 2, and the disjunction property and `◯`-reflection as corollaries;
  alternatively decidability via the finite model property (Thm 4.6),
  whose filtration argument should sit well on `PLLCompleteness.lean`.
- **Completeness for the extensions** of Thm 4.5, by relativising theories
  to an extended consequence relation.
- **Quantified lax logic (QLL)**: first-order extension; the slime-free
  discipline should extend with well-scoped binders (de Bruijn or locally
  nameless), and the constraint-model semantics with (co)domains per world.
- **Constraint logic programming**: `◯` as the modality of "solvable under
  constraints"; the F&M intuition of constraint contexts suggests a
  mechanised connection between PLL derivability and CLP resolution.
- **A literate Verso rendering** of the development, replacing this
  markdown draft.

### Acknowledgements

The mechanisation was carried out with Claude (Anthropic) as a proof
engineering assistant.  The development builds on Lean 4 and mathlib, and on
the second author's memories of what the 1997 proofs actually do — the
paper's PDF was consulted throughout and is quoted in the module docstrings.

### References

- M. Fairtlough, M. Mendler. *Propositional Lax Logic.* Information and
  Computation 137(1), 1997, pp. 1–33.
- R. Goldblatt. *Grothendieck topology as geometric modality.* Zeitschrift
  für mathematische Logik und Grundlagen der Mathematik 27, 1981.
- P.N. Benton, G. Bierman, V. de Paiva. *Computational types from a logical
  perspective.* JFP 8(2), 1998.
- E. Moggi. *Notions of computation and monads.* Information and
  Computation 93(1), 1991.
- C. McBride. Discussions of "green slime" in dependently typed
  programming; *Eliminating Dependent Pattern Matching* (with Goguen and
  McKinna), 2006.
- The mathlib community. `CategoryTheory.EqToHom` — the blessed-cast
  pattern in the large.
