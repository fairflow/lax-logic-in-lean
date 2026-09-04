# The dual of the Lax modality: ◯∃, bi-intuitionistic logic, and what the models say

> Companion to `lax-logic-interpolation-handoff.md` and
> `lax-interpolation-candidates-strategy.md`.
> Records a working session investigating whether the Lax modality has a dual, what
> that dual is, and how it connects to Rauszer's bi-intuitionistic logic.
>
> **Status markers used throughout:**
> - `[VERIFIED-COMPUTATIONALLY]` — checked by exhaustive search over small finite
>   Kripke frames (3 worlds). Not proved in general. Re-runnable; see Appendix.
> - `[LITERATURE — VERIFY]` — surfaced via web search during the session. Citations
>   may be imprecise. **Check independently before relying on them.**
> - `[CORRECTED]` — a claim made earlier in the session that turned out to be wrong.
>   Retained deliberately, because the error is informative.

---

## 0. Notation fixed in this session

| Symbol | Reading | Note |
|---|---|---|
| `◯∀` | the Lax modality (Fairtlough–Mendler `◯`) | box-then-diamond, `∀∃` |
| `◯∃` | the candidate dual ("co-lax") | backward-looking, bare `∃` |
| `≪` | co-implication (subtraction, dual of `⊃`) | see §3 on symbol choice |
| `⊃` | intuitionistic implication | |
| `≤` | the intuitionistic partial order | persistence runs along it |
| `R` | the Lax accessibility relation | a relation on worlds |

**Deliberate choice:** `◯∀` / `◯∃` rather than `□` / `◇`. The box/diamond notation
carries too much baggage from standard modal logic and would create confusion later.

---

## 1. The starting problem

The Lax modality has been suspected to have a dual for a long time, and attempts to
find one had not worked out. The question: what *is* the dual of `◯`, semantically and
proof-theoretically?

The Lax clause (in a Kripke model with intuitionistic order `≤` and lax relation `R`):

```
u ⊨ ◯∀ p    iff    ∀v ≥ u. ∃w. v R w  and  w ⊨ p
```

This is the `∀∃` / box-then-diamond composite.

### 1.1 The naive dual, and why it fails

The instinctive dual is to swap the quantifiers and reverse the relations:

```
u ⊨ dual p   iff   ∃v ≤ u. ∀w. w R v → w ⊨ p
```

`[VERIFIED-COMPUTATIONALLY]` **This collapses to vacuous truth.** On a 3-world chain
`u0 ≤ u1 ≤ u2` with `R = {u0→u1, u1→u2, u2→u2}`, this clause is **true at every world
in every valuation**, including the empty valuation. Reason: at the bottom world
nothing `R`-precedes it, so the inner `∀` is vacuously satisfied, and the outer `∃`
picks that world up. Useless as a connective.

**This is important.** If earlier attempts at the dual were hunting the *symmetric*
`∃∀` mirror, they were hunting something that does not exist. The working dual is
structurally **simpler** than the Lax modality, not mirror-image to it.

### 1.2 The persistence obstruction

The deeper reason the naive dual fails is **persistence**: in intuitionistic Kripke
models, once a formula is true at a world it is true at all later worlds. Any dual
clause that looks *backwards* risks letting truth "leak downward" against monotonicity.

An observation made during the session and worth recording, because it is correct and
sharp: *"a thing that failed always failed in the past"* is **the same constraint as
persistence**, seen from the other end. There is no independent notion of
"co-persistence" to be had on a single order. This was confirmed computationally —
entailment failures and persistence failures occur at **the same witnessing world, in
the same valuation**, never independently.

---

## 2. The candidate that works: ◯∃

```
u ⊨ ◯∃ p    iff    ∃w. w R u  and  w ⊨ p
```

A **bare existential, looking back along `R`**. One quantifier, not two.

### 2.1 Where it holds and where it breaks

`[VERIFIED-COMPUTATIONALLY]` Tested over 3-world frames:

| Frame | `R` | Result |
|---|---|---|
| chain `u0≤u1≤u2` | `R` forward along the order | both entailment and persistence hold |
| branch `u0≤u1`, `u0≤u2` | `R = {u0→u1}` | both hold |
| `a≤b`, `c` incomparable | `R = {c→a}` | **both fail**, same witness |
| `u0≤u1` | `R = {u1→u0}` (against the order) | **both fail**, same witness |

Diagnosis of the Model-4 failure: `p` holds at `u1`, `R` steps `u1→u0`, so `◯∃ p`
fires at `u0` — but `p` is false at `u0`, and `u0` is *below* `u1`. Truth leaked
downward. This is the persistence catastrophe in miniature.

### 2.2 A concrete working model

```
Worlds:   u0 ≤ u1 ≤ u2          (one intuitionistic order)
R_colax:  u0→u1, u0→u2, u1→u2   (the strict part of ≤)
R_lax:    u0→u1, u1→u2, u2→u2

valuation of p        p                  ◯∃ p          ◯∀ p
[]                    []                 []            []
[u2]                  [u2]               []            [u1,u2]
[u1,u2]               [u1,u2]            [u2]          [u0,u1,u2]
[u0,u1,u2]            [u0,u1,u2]         [u1,u2]       [u0,u1,u2]
```

`◯∃ p` lands one step **up** from where `p` starts. It reads *"p was already true
strictly below me."* Genuinely different from `p` (at `u1`, `p` holds but `◯∃ p` does
not), so it is not a collapse.

That retrospective flavour is the same one that makes Rauszer's co-implication feel
inelegant. Here it is earned from the semantics rather than bolted on.

---

## 3. Rauszer, bi-intuitionistic logic, and co-implication

`[LITERATURE — VERIFY]` Bi-intuitionistic logic (Heyting–Brouwer logic, BiInt) extends
intuitionistic logic with the **algebraic dual of implication**, called
**co-implication** (also subtraction, exclusion, difference).

**Rauszer's semantics — the key architectural fact:** she uses **one order, read in
both directions**. Implication looks *forward* along `≤`; co-implication looks
*backward* along the *same* `≤`. No second accessibility relation.

The standard clause:

```
u ⊨ A ≪ B    iff    ∃v ≤ u.  v ⊨ A  and  v ⊭ B
```

In the Kripke semantics the new connective behaves like a **backward-looking diamond
modality**. That is structurally *exactly* the `◯∃` clause of §2 — bare existential,
backwards. The architecture derived computationally in this session is the one Rauszer
already used.

**Symbol choice.** The Cambridge/RSL paper on predicate bi-intuitionistic logic uses
`≪` for co-implication. Recommended here for literature-consistency. Alternative if
ambiguity with "much less than" is a concern: `⤙`. In Lean, declare notation explicitly
either way.

### 3.1 Primary references

`[LITERATURE — VERIFY ALL]`

1. **Rauszer**, "Semi-Boolean algebras and their applications to intuitionistic logic
   with dual operations", *Fundamenta Mathematicae* 83 (1974) 219–249.
2. **Rauszer**, "Applications of Kripke models to Heyting-Brouwer logic",
   *Studia Logica* 36 (1977) 61–71.
3. **Rauszer**, "A formalization of the propositional calculus of H-B logic",
   *Studia Logica* 33 (1974) 23–34.
4. **Buisman & Goré**, "A Cut-free Sequent Calculus for Bi-Intuitionistic Logic",
   arXiv:0704.1707.
5. **Goré & Shillito**, on the wBIL/sBIL split (see §3.2).
6. **Kowalski & Ono**, Craig interpolation for *propositional* BiInt.
7. **Olkhovikov & Badia**, "Craig interpolation theorem fails in bi-intuitionistic
   predicate logic", *Review of Symbolic Logic*; arXiv:2205.00245.

### 3.2 Health warnings — Rauszer's work contains known errors

`[LITERATURE — VERIFY]` **Do not build on Rauszer uncritically.**

- Her "cut-free" sequent calculus was shown by **Uustalu** to **fail cut-elimination**.
  Buisman & Goré later supplied a correct cut-free calculus.
- **Goré & Shillito** identified a deeper conflation: two distinct consequence relations
  were run together. This splits into **weak** (`wBIL`) and **strong** (`sBIL`)
  bi-intuitionistic logic, capturing respectively the **local** and **global**
  consequence relations of the Kripke semantics. `sBIL` extends `wBIL`; `wBIL` satisfies
  the traditional deduction theorem while `sBIL` satisfies only a modified version.
  This mirrors the known local/global splitting phenomenon in modal logic.
- Rauszer's interpolation results were for **deductive interpolation** under global
  consequence — which, because the deduction theorem fails for global consequence in
  BiInt, is **not equivalent to Craig interpolation**.

### 3.3 Interpolation status in bi-intuitionistic logic

`[LITERATURE — VERIFY]` This matters directly for the main project.

- **Propositional BiInt: Craig interpolation HOLDS.** Established relatively recently
  by Kowalski & Ono, via a complex proof-theoretic argument.
- **Predicate BiInt: Craig interpolation FAILS.** The Kowalski–Ono techniques do not
  extend to the predicate case.
- **Uniform interpolation for BiInt: no result found either way.** Appears to be
  **open**. Worth confirming — if genuinely open it is itself a target.

**Moral for the Lax project: adding a dual is not interpolation-neutral.** It is a
real risk that introducing `◯∃` breaks a property that held without it. Test early.

### 3.4 Two leads worth chasing

`[LITERATURE — VERIFY]`

1. **Nested sequents.** Nested sequent systems exist for tense logics and for
   bi-intuitionistic logic which admit *syntactic* Craig interpolation proofs. Nesting
   is how the literature handles backward-looking modalities.
2. **The Iemhoff school.** Papers proving *uniform Lyndon interpolation* for
   intuitionistic modal logics work over calculi named **G3iMw** and **G4w** — the same
   naming lineage as G3iLL / G4iLL. Method is sequent-calculus-based and explicitly
   descended from Pitts. **This is the closest available template.** See e.g. "Uniform
   Lyndon interpolation for intuitionistic monotone modal logic" (arXiv:2208.04607) and
   "Uniform interpolation via nested sequents and hypersequents" (arXiv:2105.10930).

---

## 4. The adjunction — including a correction that matters

### 4.1 `[CORRECTED]` The error, and why it is instructive

During the session the requirement `◯∃ A ⊨ A` was imposed as a "counit" condition.
**This is wrong.** For an adjunction `F ⊣ G` the counit is `F(G A) → A`, not `F A → A`.
Correctly:

```
unit:    A ⊨ ◯∀ (◯∃ A)
counit:  ◯∃ (◯∀ A) ⊨ A
```

Under the *wrong* condition, an exhaustive search over all partial orders on 3 worlds
found 164 `(order, R)` pairs satisfying "entailment + persistence", and **all 164** had
`R ⊆ ≤`. That looked like a forced structural constraint. **It was an artefact of the
wrong requirement.**

**Hypothesis worth taking seriously:** if earlier attempts at the Lax dual also imposed
`◯∃ A ⊨ A`, they were imposing a condition strictly stronger than adjointness requires,
which would explain why "the dual didn't work out."

### 4.2 `[CORRECTED]` A second error: vacuous success

An "independent second order" configuration initially appeared to pass. On re-checking
it passed **vacuously** — `◯∃` never fired in that frame. Two genuinely independent
orders rescue nothing. Any implementing agent should include a **non-vacuity check**
(does the operator actually fire, and does it differ from the identity?) in every test
harness. Both checks are cheap and both caught real errors here.

### 4.3 The corrected result

`[VERIFIED-COMPUTATIONALLY]` Searching all relations `R` on the 3-chain
`u0 ≤ u1 ≤ u2` for a genuine adjunction

```
(◯∃ A ⊨ B)  ↔  (A ⊨ ◯∀ B)
```

with both operators required to preserve upward-closed sets:

- **6 relations give a genuine adjunction; 5 of these are non-trivial** (at least one
  operator differs from the identity), with unit and counit both holding.
- Examples of working `R`: `{u0→u1, u1→u1, u2→u2}`, `{u0→u1, u1→u2, u2→u2}`,
  `{u0→u2, u1→u1, u2→u2}`, `{u0→u2, u1→u2, u2→u2}`,
  `{u0→u1, u0→u2, u1→u1, u2→u2}`.
- **Pattern: `R` must be serial** — every world has an `R`-successor.
- **`◯∃ A ⊨ A` is NOT required**, confirming §4.1.

So: **the dual exists, non-trivially, as a left adjoint to the Lax modality.**

### 4.4 Structural consequence

`◯∀ ◯∃` is a **monad**; `◯∃ ◯∀` is a **comonad**. This recovers the Lax modality as the
monad arising from an adjunction — consistent with the Moggi / monadic-metalanguage
reading of Lax Logic already in play in the main project.

### 4.5 "An adjunction between adjunctions"

The observation is correct and worth keeping as an organising principle:

- `⊃` is **right adjoint to `∧`** (residuation): `A ∧ B ⊢ C  ↔  A ⊢ B ⊃ C`
- `≪` is **left adjoint to `∨`** (co-residuation): `A ⊢ B ∨ C  ↔  A ≪ B ⊢ C`
- `◯∃ ⊣ ◯∀` sits **above** both, as a modal adjunction on the propositional structure.

---

## 5. Lean statements

Skeleton only — the proofs require the project's actual `Form` and `⊢` definitions.

```lean
infixr:60 " ⊃ " => Form.imp
infixl:60 " ≪ " => Form.coimp     -- co-implication (Rauszer subtraction)
prefix:75 "◯∀"  => Form.lax
prefix:75 "◯∃"  => Form.colax

-- Residuation: ⊃ is right adjoint to ∧
theorem res_imp (A B C : Form) : (A ⋀ B ⊢ C) ↔ (A ⊢ B ⊃ C)

-- Co-residuation: ≪ is left adjoint to ∨
theorem res_coimp (A B C : Form) : (A ⊢ B ⋁ C) ↔ (A ≪ B ⊢ C)

-- Modal adjunction ◯∃ ⊣ ◯∀
theorem lax_adj (A B : Form) : (◯∃ A ⊢ B) ↔ (A ⊢ ◯∀ B)

-- Unit and counit (NOTE the composites — see §4.1)
theorem lax_unit   (A : Form) : A ⊢ ◯∀ (◯∃ A)
theorem lax_counit (A : Form) : ◯∃ (◯∀ A) ⊢ A

-- Derived: monad and comonad structure
theorem lax_monad_mult   (A : Form) : ◯∀ (◯∃ (◯∀ (◯∃ A))) ⊢ ◯∀ (◯∃ A)
theorem lax_comonad_dupl (A : Form) : ◯∃ (◯∀ A) ⊢ ◯∃ (◯∀ (◯∃ (◯∀ A)))
```

### 5.1 Semantic side, for a Lean model-theoretic development

```lean
structure LaxFrame where
  W       : Type
  le      : W → W → Prop
  R       : W → W → Prop
  le_refl  : ∀ u, le u u
  le_trans : ∀ u v w, le u v → le v w → le u w
  serial   : ∀ u, ∃ v, R u v          -- required for the adjunction (§4.3)

-- ◯∀ p at u  :  ∀ v ≥ u. ∃ w. R v w ∧ p w
def lax   (F : LaxFrame) (p : F.W → Prop) (u : F.W) : Prop :=
  ∀ v, F.le u v → ∃ w, F.R v w ∧ p w

-- ◯∃ p at u  :  ∃ w. R w u ∧ p w
def colax (F : LaxFrame) (p : F.W → Prop) (u : F.W) : Prop :=
  ∃ w, F.R w u ∧ p w
```

**Proof obligations an implementing agent should discharge first, in this order:**

1. `colax` preserves upward-closed (persistent) predicates. This is where a
   **zig-zag / commuting condition** on `R` relative to `≤` will be needed —
   the natural candidate is `R ; ≤ ⊆ R`. Determine the exact condition rather than
   assuming this one; it was *sufficient but not necessary* in the small frames tested.
2. `lax` preserves upward-closed predicates.
3. The adjunction `colax p ≤ q ↔ p ≤ lax q` as an iff, at the level of predicates.
4. Unit and counit as corollaries of 3.
5. Non-vacuity: exhibit a frame where `colax p ≠ p` and `lax p ≠ p`.

---

## 6. Proof theory: what co-implication does to the calculus

### 6.1 Multi-conclusion is forced

`≪` **cannot be stated in a single-conclusion sequent calculus.** Its rules require
multi-succedent sequents.

**This bears directly on the main project's central obstruction.** The "goal-dependent
left rule" monster — that in a single-conclusion calculus the left rules you may fire
depend on the consequent, while a uniform interpolant must be built without seeing the
consequent — is a pathology **of single conclusions**. Moving to multi-succedent
sequents may dissolve it rather than merely relocate it.

**This is the single most actionable idea in this document.**

### 6.2 The interaction problem

`[LITERATURE — VERIFY]` Completeness for BiInt is complicated by the **interaction
between implication and its dual** — explicitly compared in the literature to the
interaction between **future and past modalities in tense logic**. This is why the
working calculi are nested or labelled: structure is needed to stop the two directions
colliding.

Note the resonance: `◯∀` looks forward, `◯∃` looks backward. The Lax pair has the same
tense-logical shape, and should be expected to raise the same interaction difficulties.

### 6.3 Why polarise a bi-intuitionistic calculus

`⊃` is naturally **negative** and invertible on the right. `≪` is naturally **positive**
and invertible on the left. In a single-conclusion calculus those two invertibilities
**fight**. Polarity sorts them, and the **shifts become the licensed points of
interaction** between the assertion fragment and the refutation fragment.

`[LITERATURE — VERIFY]` This is not a novel proposal: **polarised bi-intuitionistic
logic (PBL)** exists in the literature, constructed as two fragments — positive
intuitionistic logic and its dual — extended with negations that partially internalise
the duality. Associated with the "logic for pragmatics" programme, in which formulas
express **assertions** (conjunction, implication) or **conjectures/hypotheses**
(disjunction, subtraction). Modal interpretations over **bimodal preordered frames** are
considered there.

**Payoff for the main project:** focusing buys determinism; determinism is what uniform
interpolation needs; and here polarity *also* tames the tense-like past/future
interaction. One device, two jobs. `◯∀` / `◯∃` would then be the **modal shift pair**
sitting on top of the propositional polarity structure.

---

## 7. Is bi-intuitionistic logic a calculus of disproofs?

Partly, and the boundary is precise.

`[LITERATURE — VERIFY]`

- **Pure dual fragment:** dual-intuitionistic logic (exclusion without implication) was
  shown by **Brunner & Carnielli** to be, *as a logic*, the **dual of Int**. So a
  derivation in the pure co-fragment corresponds to an **IPC refutation** under a precise
  duality — not merely in spirit.
- **Rauszer's stated aim** was a **conservative extension** of Int possessing a duality
  property analogous to classical logic's. Conservative ⇒ **no new IPC theorems**.
- **Therefore the genuinely new content lives entirely in the *mixed* fragment**, where
  `⊃` and `≪` interleave. That mixed zone is where the interaction problems of §6.2
  live, and where any new results will have to be won.

### 7.1 Relevance to complete proof search

This connects to a standing interest in calculi that **search for a proof and a
counter-model simultaneously**, syntactically, without an infinite
Lindenbaum/Zorn construction.

Bi-intuitionistic logic *does* internalise this: multi-conclusion sequents let the
right-hand side carry **refutation obligations**, so counter-model construction becomes
derivation. That is the attraction.

The honest caveat is §6.2 — the implication/co-implication interaction is precisely what
broke Rauszer's cut-elimination, and it is why the working systems need nested or
labelled structure.

**Connection to the main project's existing assets:** a terminating decision procedure
already exists (via G4C, tracking contraction). A finitary counter-model construction is
available *exactly when search terminates* — no transfinite machinery needed. So the
finite stuck search-state can serve simultaneously as: (i) the counter-model, and (ii)
the object the interpolant is read off. Same structure, two jobs.

---

## 8. Open questions

1. **Does `◯∃` break uniform interpolation for Lax Logic?** Given that Craig
   interpolation fails for *predicate* BiInt, this is a live risk. **Test early and
   cheaply**, before building on the dual.
2. **Is uniform interpolation for propositional BiInt open?** No result was found in
   either direction. If genuinely open, it is a target in its own right, and possibly an
   easier one than the Lax case.
3. **What is the exact frame condition on `R`?** Seriality is necessary in the small
   frames. The relationship to `≤` (zig-zag `R ; ≤ ⊆ R`, or something weaker) needs
   determining properly rather than by finite search.
4. **Does multi-succedent dissolve the goal-dependent left rule?** See §6.1. Highest
   value question in this document.
5. **wBIL or sBIL?** If the project ever formalises BiInt, the local/global consequence
   split (§3.2) must be resolved *first*. Rauszer's conflation of the two is the root of
   the errors in her work; repeating it would be costly.

---

## Appendix: reproducing the computational results

All results marked `[VERIFIED-COMPUTATIONALLY]` came from exhaustive search over
3-world frames in plain Python. The harness is simple enough to rebuild in an hour, and
worth rebuilding in Lean as a decision procedure over finite models:

1. Enumerate partial orders on `n` worlds (reflexive-transitive closures of subsets of
   the strict pairs, discarding those with cycles).
2. Enumerate **upward-closed** valuations (these are exactly the persistent ones).
3. Enumerate candidate relations `R`.
4. For each `(order, R)`, evaluate `◯∀` and `◯∃` on every valuation.
5. Check: adjunction as an **iff** in both directions; unit; counit; preservation of
   upward-closure; **and non-vacuity** (operator fires somewhere, and differs from the
   identity somewhere).

**Step 5's non-vacuity check is not optional.** It caught two false positives in this
session. A configuration in which the operator never fires will pass every property
vacuously and look like a success.

`n = 3` was sufficient to distinguish all the cases considered here and to refute two
plausible-looking claims. `n = 4` would give more confidence before committing to a
general proof.
