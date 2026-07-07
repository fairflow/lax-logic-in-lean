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
| Lemma 2.1 | PLL = IPC + `(N⊃◯K) ≡ (◯N⊃◯K)` | `lemma21` | `PLLHilbert.lean` |
| Prop 2.2 | deduction theorem, Hilbert form | `HdOn.deduction` | `PLLHilbert.lean` |
| Thm 2.3 (full) | Hilbert ⟷ ND ⟷ cut-free Gentzen | `hd_iff_ND`, `cutElimination` | `PLLHilbert.lean`, `PLLSequent.lean` |
| Thm 2.6 | cut elimination | `cut_aux`, `SC.cut` | `PLLSequent.lean` |
| Lemma 2.7(i) | disjunction property | `disjunction_property` | `PLLSequent.lean` |
| Lemma 2.7(ii) | `◯`-reflection | `somehow_reflection` | `PLLSequent.lean` |
| Thm 4.6 | finite model property | `filt_force`, `finite_model_property` | `PLLFiniteModel.lean` |

Not yet mechanised: the subformula property as a statement about derivation
trees (Lemma 2.7(iii)) and decidability as a *computable* decision procedure
(Thm 2.8 — the FMP gives decidability only in principle); the completeness
halves of Thm 4.5; the J-space translation (Thm 3.5); the bimodal classical
embedding (Thm 5.1); the concrete models of §6.

## 8a. The second sweep: cut elimination, Hilbert equivalence, FMP

A second pass mechanised most of the remaining paper.

**Cut elimination** (`PLLSequent.lean`).  The sequent calculus `SCh` is
G3-style — left rules keep their principal formula via a *membership*
hypothesis, so weakening, exchange and contraction are height-preserving
admissible by the same one-lemma renaming as in natural deduction — and
carries an explicit height index.  Heights are what let a `Prop`-valued
calculus support the lexicographic induction of cut admissibility (size of
cut formula, sum of heights): no derivation-sized data, no casts.  The proof
factors the entire left-commutation into a single `leftCommute` combinator,
leaving the principal-principal reductions — including F&M's Figure 2
`laxR`/`laxL` step — as the only interesting cases.  Corollaries fall out by
last-rule analysis on cut-free proofs of `⊢ A ∨ B` and `⊢ ◯A`: the
disjunction property and `◯`-reflection, F&M Lemma 2.7(i)–(ii).

**Hilbert equivalence and a fourth bug** (`PLLHilbert.lean`).  F&M's Hilbert
system has, besides modus ponens, the regularity rule "from `M ⊃ N` infer
`◯M ⊃ ◯N`" (p. 6).  The repository's checker has no such rule — and cannot
compensate: interpreting `◯` as the constant-`⊥` operator validates `◯R`,
`◯M`, `◯S` and refutes functoriality, so the axiom set was *incomplete*
(bug #4, dual to the earlier unsoundness bugs).  The repair follows F&M
Lemma 2.1: PLL is a purely axiomatic extension of IPC by the single Kleisli
scheme, provided that scheme is read as the **bi**-implication
`(N ⊃ ◯K) ≡ (◯N ⊃ ◯K)` — the forward (bind) direction alone fails to yield
`◯R` by the same constant-`⊥` counter-interpretation.  We add `somehowBind`
as an axiom, prove the deduction theorem for any axiom set containing `K`
and `S` (F&M Prop 2.2 in Hilbert form), and obtain the full Theorem 2.3:
Hilbert consequence = natural deduction = cut-free sequent derivability,
plus Lemma 2.1 as a two-way translation through natural deduction.

**Finite model property** (`PLLFiniteModel.lean`).  F&M's filtration
identifies worlds with the same validated subformulas `T(w)` *and* the same
modally-refuted subformulas `Fₘ(w)`.  Instead of a quotient we take the
worlds of the filtered model to be the realised pairs `(T(w), Fₘ(w))`
themselves: well-definedness obligations vanish, and finiteness is a
two-line powerset argument.  The filtration lemma's `◯` cases run on
membership transfer (`◯N ∈ T(w) ⊆ T(v)`) rather than on any relation
between representatives — the trick that makes the paper's "one verifies"
go through.  Combined with soundness and the canonical model: `⊢ φ` iff `φ`
holds in every finite constraint model.

**Independent review.**  A separate fidelity audit
(`docs/formalisation-notes.md`) checked each formal statement against the
paper: all headline statements assert what they claim; the one caveat is
that `ConstraintModel.W : Type` fixes carriers to universe 0, making
soundness marginally weaker (and completeness correspondingly stronger)
than a universe-polymorphic reading — immaterial for every result here.
The audit also classifies constructivity: classicality enters only through
Zorn and excluded middle in the completeness development; soundness, the
erasure translation, cut elimination, and the Hilbert/Gentzen equivalences
are constructive.

## 8b. Proof terms, and what cut elimination does and does not give

`PLLTerms.lean` adds the missing computational layer: an intrinsically-typed
term calculus — Moggi's computational metalanguage, with `val`/`bind` for
`◯` — whose typing derivations are exactly `LaxND` derivations
(`curry_howard`).  The slime-free discipline survives one upgrade: proof
terms must compute, so variables are `Type`-valued de Bruijn witnesses
`Var Γ φ` (indices again only `φ :: Γ`) rather than `Prop`-membership;
renaming and substitution are the standard parallel traversals, and the
whole calculus remains cast-free.  Because typing is intrinsic, **subject
reduction is definitional**: the reduction relation `Step` — β for every
connective plus `let`-β and `let`-assoc — only relates terms of one sequent.

The relationship to the cut-elimination procedure of `PLLSequent.lean` is
now a statement about artefacts in the same repository, and it is exact at
the level of *rules*: cut is substitution (`Tm.cut = subst1`), each
principal case of `cut_aux` is the sequent shadow of a β-rule (the
`laxR`/`laxL` case of F&M Figure 2 *is* `bind (val s) t ⟶ t[s]`), and the
left/right commutation cases are the congruence closure.  But the two
results differ in strength, and the difference is instructive:

* cut admissibility is *weak* normalisation of one cut-reduction strategy,
  and its lexicographic metric (cut formula, derivation heights) survives
  at `Prop`-level because heights never grow along the strategy;
* β-reduction of terms duplicates subterms through substitution, so no
  height measure survives — strong normalisation genuinely needs
  reducibility (Tait), and for `let`-assoc specifically the
  Lindley–Stark ⊤⊤-lifting interpretation of `◯`.

Both normalisation theorems are set up (`Step`, `SNt`) and queued: weak
normalisation is harvestable from the cut-free calculus via normal/neutral
forms (a cut-free `SCh` derivation denotes a β-normal term with neutral
eliminations), and strong normalisation is the natural next milestone.

`PLLConstraints.lean` delivers F&M's motivating reading (§1(6)): interpret
`◯φ` as `M × ⟦φ⟧` for a combination structure `(M, op, e)` — a writer
monad — and evaluation of proof terms *is* constraint extraction.  The
two-gate circuit of the timing-analysis motivation is the worked example: a
proof of `A ⊃ ◯C` from gates `A ⊃ ◯B` and `B ⊃ ◯C` evaluates, **by
`rfl`**, to delay `d₁ + d₂` under `(ℕ, +, 0)` and to `max d₁ d₂` under the
ready-time reading `(ℕ, max, 0)` — the two halves of F&M's delay algebra
`(ℕ, 0, +, max)`.  The `◯R` term (a wire) emits `0`; the `◯M` term (join)
adds its two constraint layers.  Proofs compute constraints, kernel-checked.

## 8c. Normalisation: the substitution algebra, WN, and a certified reducer

A third pass built the normalisation layer on the proof-term calculus.

**The substitution algebra** (`PLLSubst.lean`): the σ-calculus equations —
congruence, the four composition laws (`rename_rename`, `subst_rename`,
`rename_subst`, `subst_subst`), identity, and the β-law
`(t.subst σ.lift).subst1 s = t.subst (Sub.cons s σ)` — all stated
*pointwise* (no function extensionality) and proved by structural
inductions whose binder cases are two-line variable analyses.

**Normal forms and weak normalisation** (`PLLNormal.lean`).  β-normal forms
are a mutual normal/neutral grammar with two design points: `case` and
`abort` on a neutral scrutinee are neutral (no commuting conversions), and
`bind` is *not* neutral — `bind (bind s t) u` is an assoc-redex even when
the inner `bind` is stuck — so normal `bind`-chains are exactly the
right-nested assoc-normal forms of the computational metalanguage.  `Nf` is
closed under renaming and neutral substitution, normal terms are stuck
(`not_step_of_nf`), stuck terms are normal (`nf_or_step`, progress), and —
the harvest — **every cut-free sequent proof denotes a normal proof term**
(`nf_of_SCh`): left rules become neutral substitutions, `laxL` becomes a
right-nested `bind` on a variable.  Hence every inhabited sequent has a
normal inhabitant (`normal_form_exists`): weak normalisation via cut
elimination, with the caveat stated honestly — the normal form is produced
by cut elimination, not by reducing the given term.

**Assoc termination and a certified reducer** (`PLLStrongNorm.lean`).  The
`let`-assoc fragment terminates by a weight measure
(`w(bind t u) = 2·w(t) + w(u) + 1`, renaming-invariant) — the part of
`Step` invisible to β-methods.  A computable one-step reducer `Tm.step?`
returns proof-carrying steps (`Option {t' // Step t t'}`); `step?_none`
shows a `none` answer certifies normality, so `step?` decides normality,
and the fueled normaliser `reduceFuel` is sound by construction: its result
is reduction-reachable and, when it reports normal, normal.  Full strong
normalisation — termination of the whole relation — is the one remaining
normalisation theorem, precisely scoped: Kripke-indexed Tait reducibility
(branches of `case`/`bind` live in extended contexts) with Lindley–Stark
⊤⊤-lifting to absorb `let`-assoc; with it, `reduceFuel` upgrades to a total
normaliser by well-founded recursion.

## 8d. Strong normalisation of β-reduction

`PLLReducibility.lean` proves the largest single theorem of the
development: **strong normalisation of the β-fragment** `RStep` — function,
projection, case and `let`-β with full congruence closure — for every
proof term (`beta_sn`), by Tait's reducibility method arranged for
intrinsic syntax.  The design points:

* `Red φ t` by recursion on the formula: Kripke function spaces at `⊃`
  (quantified over renamings, since `lam`-bodies inhabit extended
  contexts), elimination clauses at `∧`, *value clauses* at `∨` and `◯`
  (`t ⟶* val w → Red w`) — sound precisely because the β-fragment cannot
  restructure `bind`s;
* strong normalisation is conjoined into every clause, making CR1 free;
  CR2, CR3 and renaming-stability go by induction on the formula, with
  renaming-stability of the value clauses resting on **reflection of
  reduction under renaming** (`RStep.rename_reflect`), a
  constructor-inversion grind organised by head-splitting before step
  inversion;
* one closure lemma per construct (β-expansion for `lam`, double
  SN-inductions for `pair`/`case`/`bind`, value-invariance lemmas for
  `inl`/`inr`/`val`), then the fundamental theorem and `beta_sn` at the
  identity substitution.

`step_split` makes the reduction landscape precise: every `Step` is a
β-step or an assoc-step, and both halves are separately strongly
normalising (`beta_sn`, `assoc_sn`).  Their *interleaving* — full `SNt` —
is the one theorem left standing, and the obstruction is machine-checked:
the file exhibits a β-normal term that one assoc step equips with a fresh
`let`-β redex (the associativity law feeding the left-unit law: a `val` in
body position — the right-unit shape, not a redex — is reassociated into
scrutinee position), and an assoc-normal term whose β step creates an
assoc redex; the second reduces exactly to the first, a two-rule
ping-pong.  These four terms close both orientations of
Bachmair–Dershowitz/Geser quasi-commutation, so no generic
modular-termination theorem applies; and since assoc-created β-redexes
have unbounded scrutinees which `let`-β then duplicates, no size or count
measure survives the phase boundary either.  (A measure for the phased
strategy alone would in any case prove only that one strategy normalises —
weak normalisation, already delivered by cut elimination.)  The
value-style `◯`-interpretation used here is the empty-stack shadow of
Lindley–Stark's ⊤⊤-lifting semantics — reducibility of a computation as
orthogonality, with the SN predicate as pole, against reducible
continuation stacks — and upgrading to it is the precisely-scoped
remaining step: the principal lemma trades the value clause for an
induction on stack length inside a reduction-length measure, which is why
an inductive or length-based characterisation of SN joins the toolkit.

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

- **Strong normalisation of full `Step`** (β *and* assoc interleaved):
  upgrade the value-style `◯`-clause of `Red` to Lindley–Stark reducible
  continuation stacks (β-SN, assoc-SN, `step_split`, WN, the certified
  reducer and the σ-algebra are all done — this is the last brick).
- **A computable decision procedure** (F&M Thm 2.8): the FMP bounds the
  model search in principle; a verified decision procedure would go through
  terminating proof search in the height-indexed calculus of
  `PLLSequent.lean` (whose subformula-boundedness is manifest rule-by-rule)
  or through enumerating the finitely many filtration models.
- **Lemma 2.7(iii)** as a statement about derivation trees (a
  subformula-bounded variant of `SCh` and an embedding into it).
- **Completeness for the extensions** of Thm 4.5, by relativising theories
  to an extended consequence relation (the soundness halves are done in
  `PLLFrames.lean`).
- **The bimodal embedding** (F&M §5, Thm 5.1) — at least in semantic form,
  translating constraint models to `[S4,S4]`-models and back; and the
  concrete constraint models of §6.
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
