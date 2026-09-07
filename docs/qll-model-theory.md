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
| `◯∀P ⊬ ◯∃P` and `◯∃P ⊬ ◯∀P` | `CompleteTests.lean` | as above |
| the Constant Domain axiom is not derivable | `CompleteTests.lean` | as above |

`⊢q` is `Prv`: Fig. 5 with proof terms erased and the binding rules quantified
cofinitely.  `⊫` is `Consequence` over the models of `Kripke.lean`: varying
domains, fallible states, one reachability relation per modality.

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
