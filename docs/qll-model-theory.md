# QLL model theory: what is proved, and what the first-order case needs

Status 2026-09-07.  All Lean files under `LaxLogic/QLL/`; build with

```
lake build LaxLogic.QLL.Tests
```

## Proved, sorry-free

| statement | file | axioms |
| :-- | :-- | :-- |
| heredity, explosion, opening, valuation congruence | `Kripke.lean` | `[propext]` |
| soundness, `Γ ⊢q A → Γ ⊫ A` | `Prov.lean` | `[propext, Classical.choice, Quot.sound]` |
| Lindenbaum, by Zorn | `Complete.lean` | as above |
| the truth lemma, quantifier-free fragment | `Complete.lean` | as above |
| completeness, quantifier-free fragment | `Complete.lean` | as above |
| `Countable Form`, and a schedule hitting each formula infinitely often | `Countable.lean` | `[propext, Classical.choice, Quot.sound]` |
| renaming for `Prv`; the exists-fresh binders | `ProvFresh.lean` | `[propext]` |
| **saturated Lindenbaum** (`exists_saturated`) | `Saturate.lean` | as above |
| **the truth lemma, full first-order** (`truth_lemma1`) | `Complete1.lean` | as above |
| **completeness, full first-order** (`completeness1`) | `Complete1.lean` | as above |
| adequacy `Γ ⊢q A ↔ Γ ⊫ A` (`prv_iff_consequence`) | `Complete1.lean` | as above |
| erasure `Derives → Prv` (`Derives.erase`) | `Bridge.lean` | `[propext, Quot.sound]` |
| construction `PrvC → Derives` (`PrvC.toDerives`) | `Bridge.lean` | as above |
| soundness for the term calculus (`Derives.consequence`) | `Bridge.lean` | `[propext, Classical.choice, Quot.sound]` |
| **refinement is not complete** (`refinement_not_complete`) | `RefineIncomplete.lean` | as above |
| `◯∀P ⊬ ◯∃P` and `◯∃P ⊬ ◯∀P` | `CompleteTests.lean` | as above |
| the Constant Domain axiom is not derivable | `CompleteTests.lean` | as above |

`⊢q` is `Prv`: Fig. 5 with proof terms erased and the binding rules quantified
cofinitely.  `⊫` is `Consequence` over the models of `Kripke.lean`: varying
domains, fallible states, one reachability relation per modality.

## First-order completeness: the three things that had to change

**Maximality is not enough, and Zorn cannot be repaired.**  A maximal
consistent theory need not be *saturated*: an inconsistency names finitely many
falsified formulas, and `∃x A` entails no finite disjunction of its instances,
so nothing forces a witness into `val`.  Witnesses have to interleave with the
decisions, one per stage, along an enumeration of the formulas — hence
`Countable.lean`, and hence `Good` is now *consistency plus totality* (every
property the canonical model uses follows from those two), with Zorn demoted to
one implementation of `exists_good_extension`.

Henkin axioms cannot be added up front: from `∃y φ(y) ⊃ φ(c)` one derives
`∃x (∃y φ(y) ⊃ φ(x))`, which is not valid.  What is conservative is adding the
*instance* `φ(c)` at a stage where `∃y φ(y)` is already validated, and the proof
of that is the elimination rule at a parameter fresh for the theory
(`consistent_insert_witness`, on `Prv.exE_of_fresh`).

**A world must keep a reserve.**  Each stage spends a name, so a construction
spending every name leaves the limit with none fresh — and the
universal-falsity case of the truth lemma needs a fresh one, because
ω-completeness fails and no term already present will serve.  So the names are
split: even slots are spent as witnesses, odd slots survive, and a formula
mentioning a reserved name is never decided.  `Total` is therefore relative to
the reserve, and a world's *domain* is the terms avoiding it — which is exactly
why the domains increase, the point already forced by `cd_not_prv`.

**The assignment covers the names that occur.**  `Assign` asked that every
string denote an element of the domain.  That is unsatisfiable in the canonical
model — the reserved names are precisely the ones its domain omits — and it is
more than the semantics needs, since forcing depends only on the names a
formula mentions.  `Consequence` now asks for an assignment on
`ctxFv Γ ++ A.fv`.  The soundness *induction* still needs a total one (a cut
formula's names need not occur in the conclusion), so it is kept as
`ConsequenceT`; the stated soundness follows by completing the partial
assignment with `d₀` and appealing to `force_congr`.  Nothing about the
proof-theoretic side changed.

## The bridge, and the one thing it leaves open

Erasure holds for any derivation whose proof term is locally closed in its
individual indices — the hypothesis `Sound.lean` already carries, and a
necessary one, since `Derives.allE` puts no condition on the instantiated term
while `Prv.allE` rightly demands local closedness.

The converse is proved for `PrvC`, which is `Prv` with ex falso restricted to
locally closed conclusions.  The restriction is not avoidable and not
cosmetic: `Derives` records ex falso's conclusion in the proof term as
`exf A p`, so a conclusion carrying a loose de Bruijn index forces a proof term
that is not locally closed, and the abstraction steps of `∀I` and `∃E` cannot
proceed.  A formula with a loose index is not a formula, so the defect is in
`Prv.botE`.  It cannot be repaired there, because `bigOr_elim` derives an
arbitrary `K` from the empty disjunction and its callers in the completeness
proof supply formulas drawn from a theory, which are not locally closed in
general.

**Open:** `Prv Γ A → PrvC Γ A` for locally closed `Γ, A`.  This is a question
about loose indices in cut formulas — plausibly answered by instantiating every
loose index with a fixed closed term and showing `Prv` is closed under that
map — not a question about the logic.

## Refinement cannot be complete — and this is now a theorem

`RefineIncomplete.refinement_not_complete`.  The Constant Domain entailment
`∀x.(A ∨ B(x)) ⊢ A ∨ ∀x.B(x)` is refinement-valid in every model, because
refining the conclusion needs only a case split on whether some individual
takes the left disjunct — an argument Lean supplies and the object logic does
not.  It is underivable, by the two-domain Kripke countermodel `cd_not_prv`,
the same fact that forced the canonical model's domains to increase.  So the
two semantics separate on a formula, and the separation measures the strength
of the ambient logic.  A completeness result for refinement is meaningful only
against a fixed object logic from the literature, never against Lean.

## The design decisions, and what forced them

**Two reachability relations.**  `◯E` requires the same `Q` in both premises
and the conclusion, so the calculus never connects the modalities.  One
relation would validate `◯∀A ⊣⊢ ◯∃A`.  `CompleteTests.all_not_ex` and
`ex_not_all` refute both directions against explicit two-state models, so this
is settled rather than argued.

**Varying domains.**  `CompleteTests.cd_not_prv` refutes the Constant Domain
axiom in a model whose two states have different domains.  A canonical model
with constant domains would validate it, so the parameter set available at a
state must grow along the order.

**Fallible states.**  `◯⊥` is consistent — no rule derives `⊥` from it — so
the semantics needs a state reachable by `Rm` at which `⊥` holds, and such a
state forces everything.  Explosion at `∃` is what makes every local domain
non-empty, recorded as the distinguished `d₀`.

**The `∀` clause ranges over the domain of the successor.**  With the domain
taken at the current state, forcing is not hereditary.

## What the first-order case needs

The truth lemma is proved for the quantifier-free fragment.  Two of the four
quantifier cases are already unobstructed; the other two are the whole gap.

| case | needs |
| :-- | :-- |
| `∀xA ∈ val` ⟹ forces | `allE` only — but the induction must be on formula **size**, since `A{t/x}` is not a structural subformula of `∀xA` |
| `∃xA ∈ fal` ⟹ refutes | totality and `exI` only |
| `∃xA ∈ val` ⟹ forces | a witness **in the domain of that state**: the world must be `∃`-saturated |
| `∀xA ∈ fal` ⟹ refutes | a successor with a **fresh** parameter `c` and `A{c/x}` falsified there |

So worlds must carry a parameter set `P` whose complement is infinite, and be
maximal-consistent *and* `∃`-saturated relative to `P`.  Zorn does not deliver
that: a maximal consistent theory over a fixed parameter set has no fresh
parameter left, which is exactly why constant domains fail.  Saturation is an
ω-construction — decide the `n`-th formula, and when an `∃` enters `val`, add a
witness on a parameter not yet used.

### Stages

1. `Form.size`, and `size (A.openAt k t) = size A`.  Rewrite the truth lemma as
   a strong induction on size.  Adds the two unobstructed quantifier cases.
2. `Countable Form`: an injection into `ℕ`, mutual with `Tm` and `List Tm`,
   through `Nat.pair` and `Encodable String`.  Needed for the enumeration the
   ω-construction consumes.
3. A parameter supply: an injection `ℕ × ℕ → String` whose columns give, at
   every stage, infinitely many parameters not yet used.
4. The saturation lemma: from a consistent theory over a parameter set with
   infinite complement, a maximal consistent and `∃`-saturated extension over a
   larger such set.
5. Re-index the canonical model by `(P, T)`, with `Dom (P,T)` the terms over
   `P`, and discharge the remaining two truth-lemma cases.

Stage 4 is the substantial one; 1–3 are self-contained and can be done first.

## Bridges to Fig. 5, both open

`Prv` is not `Derives`.  Two statements connect them and neither is proved.

* `Derives p Γ A → Prv Γ.forms A` — erasure.  Each exists-fresh binder must be
  re-based to *every* fresh name; `Derives.renameI` supplies that pointwise
  (`Rename.lean`), but assembling it needs a recursion on the size of a
  derivation rather than on its structure.
* `Prv Γ A → ∃ p, Derives p _ A` — the direction completeness would need to
  reach Fig. 5.  It requires closing a proof term over a named variable, which
  the syntax does not have (`Pf` has `openP` but no `closeP`).

Until the first is proved, "soundness of QLL" means soundness of `Prv`.
`Sound.lean` separately proves soundness of `Derives` against the *refinement*
semantics of Figs. 3, 4 and 6, which is a different theorem about a different
semantics.
