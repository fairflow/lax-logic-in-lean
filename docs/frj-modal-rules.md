# W2 — the modal rules: screens, and the rules for sign-off

*2026-08-16, branch `claude/frj-redevelopment-69005f`, on top of the
finished `FRJ/` and W1.  Supersedes `docs/frjlax-modal-rules.md`, which
was written against the archived parallel development and whose rule
figures did not respect canonical contexts.*

W2's exit criterion is: **screens recorded; rules signed off.**  The
screens are recorded and machine-checked (`FRJ/Modal.lean`, part of the
library, five axiom pins, every cell by `decide`).  The rules below are
what is being put up for sign-off; **none of them is implemented** —
`FRJ/Calculus.lean` still has the ten modality-free rules only.

---

## 1. What the semantics demands

    K,α ⊩ ◯A   iff   for every β ≥ α there is γ with Rm β γ and K,γ ⊩ A

The asymmetry with `⊃` is the whole content of the extension.  For
`A ⊃ B` the obligation at a new world is **negative** — the antecedent
fails there, so the implication holds vacuously — and that is all the
support condition (J2) has to arrange, by naming `A` as some premise's
right formula.  For `◯A` the obligation is **positive**: a modal witness
must exist, and nothing in the calculus's data supplies one.

Two lemmas, both PROVED with no axioms (`FRJ/Modal.lean`):

    circ_intro :  (∃u. Rm w u ∧ u ⊩ A)  ∧  (∀v ≥ w, v ≠ w → v ⊩ ◯A)
                  ⟹  w ⊩ ◯A

    not_force_circ :  (∀u. Rm w u → u ⊮ A)  ⟹  w ⊮ ◯A

and three more: `not_force_circ_of_no_promise` (barrenness),
`not_force_circ_of_above` (refutation descends), `circ_of_force` (the
unit).

---

## 2. The screens

All in `FRJ/Modal.lean`, on the live `Kripke`, settled by `decide`.

**Screen 1 — the witness must be SELECTIVE.**  In the two-world model
`lo < hi` with `p` only at `hi` and `Rm = ≤`,

    two ⊩_lo ◯p     and     two ⊮_lo p

so a rule must be able to build a world whose modal successor forces
something the world itself does not.

**Screen 2 — the witness is PER-WORLD.**  In the three-world model with
root below two incomparable worlds carrying `p` and `q`,

    branch ⊩_bot ◯(p ∨ q),   branch ⊮_bot ◯p,   branch ⊮_bot ◯q

so the modal data cannot be one promise fixed for the derivation: it
belongs to the world a join creates.  The same model refutes the
distribution of the modality over disjunction.

**Screen 3 — the witness cannot be an ARBITRARY CONTEXT.**  This one is a
refutation of a design rather than a model.  The tempting rule declares
"there is a world forcing `Δ`" for a context `Δ ⊆ Ĝ` of its choosing.
That is exactly the design refuted in the abandoned first attempt, whose
world predicate constrained a zone only by membership in the universe,
with no closure condition; three kernel-checked cells killed it:

    [⊥] ⊢ p        [p ∧ q] ⊢ p        [p, p ⊃ q] ⊢ q

each derivable in natural deduction yet admitted by the predicate.  So a
declared context carries a **realisability** obligation, and realisability
is not membership.  `Realisable` and one instance of the obligation are
stated in `FRJ/Modal.lean`; nothing proves it, which is the point.

---

## 3. The zones arrive with the rules

W1 established this and the build is what showed it (`FRJ/Basic.lean`, the
note on `gHat`).  The modality needs a third zone

    Ĝ = Ĝ_at ∪ Ĝ_imp ∪ Ĝ_◯,      Ĝ_◯ = Sf^L(G) ∩ {◯-formulas}

— semantically because the closure absorbs `∧` and `∨` on the left but
absorbs the modality no better than it absorbs implication, and
empirically from the 156-cell screen recorded in `docs/frj-lifting.md` §7
(32 certified failures without the modal formulas, 0 with them).

But the third zone **cannot precede the rules**: with it present, the side
condition of `⊃∉` admits a `◯`-formula into a zone, `⊃∈` shifts it into a
stable set, and the joins — which keep only the atomic and implicational
parts — silently drop it, breaking condition (†) of the join case of
Lemma 3.10.

**Therefore the following is one atomic change**, and each part of it is
unsound without the others:

1. `gHat` gains `gCirc`;
2. `Cl` gains the clause `X ::= … | ◯X` (sound by `force_circ_of_force`,
   already proved);
3. the determining part `Λ*` gains `◯A` when `α ⊩ ◯A` and `α ⊮ A`, and
   `forceStar_shape` becomes three-way;
4. the join rules gain a modal zone and its support condition;
5. the modal rules below.

Because `nf` filters against `gHat`, step 1 re-canonicalises **every**
context in the development.  That is the cost of the step, and it is why
it must be done once, with the rules, rather than in pieces.

---

## 4. The rules, for sign-off

Written with canonical conclusion contexts, per the handoff's §4.3: any
rule with a computed context in its conclusion writes it `nf G (...)`.

### 4.1 `◯∈` — regular modal introduction

        Γ ⇒ Z
    ───────────────  ◯∈      barren(d),   ◯Z ∈ Sf^R(G)
        Γ ⇒ ◯Z

`barren(d)` says the world this refutation builds declared no modal
successor.  It is an index on the regular judgment, `FRJr G b Γ C` with
`b : Bool`, not a computed property — a function on the family cannot be
defined while the family is.  Axioms and promise-free joins set it true;
the promise joins set it false; every other rule passes it through,
because no other rule builds a world.

**Obligation, PROVED**: `not_force_circ_of_no_promise`.

### 4.2 `⋈^p` — the promise join

A join carries one additional **promise premise**, a regular refutation
`Δ ⇒ D`, whose world becomes the modal successor of the new world:

    σ₁ … σₙ            Δ ⇒ D
    ─────────────────────────────────────────────────────────  ⋈^At,p
    nf G (Σ^at, Θ^at\{F}, Σ^⊃, Θ^⊃, Σ^◯, Θ^◯)  ⇒  F

with (J1), (J2), (J3) unchanged and three new conditions:

    (J5)   ◯Y ∈ Σ^◯ ∪ Θ^◯   implies   Y ∈ Cl(Δ)      — the witness
    (J6)   Σ^◯ ∪ Θ^◯ ⊆ Cl(Δ)                          — the half above
    (J7)   Γ ⊆ Cl(Δ)                                   — monotonicity

**Obligation, PROVED**: `circ_intro`.  (J5) supplies the witness at the
new world; (J6) and (J7) supply the "strictly above" half at the promise
world; at the irregular premises' worlds it comes from the closure
argument that (P2) already uses for `⊃`, needing no new lemma.  A join
with no promise has `Σ^◯ = Θ^◯ = ∅` and its world is barren.

### 4.3 `⋈^⊥` — the fallible promise, and the decision it forces

**Screens 1 and 2 do not settle the design between them.**  A fallible
world forces everything, so it witnesses every `◯`-formula at once; that
is enough for Screen 1 and not for Screen 2, which needs two worlds with
*different* witnesses.  Conversely `⋈^p` alone cannot reach every
countermodel, and the sharp instance is

    G = ◯p ⊃ p

not a theorem of PLL.  `Sf^R(G) = {G, p}` contains no `⊥`, so the only
regular axiom is the one at `p` and both axioms at `p` delete it: **no
derivable regular context of this goal contains `p`**, so no promise
premise can force `p`.  Semantically the reason is sharper: the
countermodel needs a world forcing `p`; there the modality holds by its
unit, hence so does `G`, and `⊥ ∉ Sf^R(G)` — so that world refutes
**nothing** available to the calculus, while every world of `Mod(D)` is a
p-sequent and refutes its own goal by construction.

So the witness cannot be a p-sequent.  Three ways out, and only one
survives:

| route | verdict |
|---|---|
| declare a context `Δ` and assert a world forcing it | **REFUTED** by Screen 3 — needs realisability, which is not membership; this is the FRJO failure |
| let `Mod(D)` carry worlds that are not p-sequents, labelled by a context and refuting nothing | same obligation in different clothing: such a label must be realisable |
| a **fallible** world | no realisability obligation at all: a fallible world forces everything *by construction* |

**Recommendation: fallible worlds**, i.e. `Kripke` gains a predicate `Fal`
with `⊥` forced exactly at fallible worlds, upward closed, and every atom
true there.  A join may then declare its new world's modal successor
fallible:

    σ₁ … σₙ
    ────────────────────────────────────────────────  ⋈^At,⊥
    nf G (Σ^at, Θ^at\{F}, Σ^⊃, Θ^⊃, Σ^◯, Θ^◯)  ⇒  F

with no (J5)–(J7).  Two consequences, both to be accepted knowingly:

* the witness must cover the whole cone above the new world, so the
  fallible world is a maximum of the model, modally accessible from
  everywhere; hence **no world of such a model is barren**, and `◯∈` never
  applies above it.  That is correct rather than unfortunate: a model with
  a fallible top forces every `◯`-formula everywhere, so nothing of the
  form `◯Z` can fail in it;
* **it changes the modality-free semantics**: `⊥` becomes forceable.  The
  logic is unchanged (intuitionistic logic is sound and complete for
  Kripke models with fallible worlds), and soundness is unaffected because
  every model the calculus *builds* can take `Fal = ∅` unless a rule
  declares otherwise.  But **completeness starts from an arbitrary
  countermodel**, which may now have fallible worlds, and the construction
  of Lemma 6.3 must handle them.  That is the real cost, and it is a W3/W4
  cost, not a W2 one.

### 4.4 What is deliberately not proposed

* **No modal left rule.**  The calculus has none for any connective.
* **No modal clause in the closure without the rest of §3.**  It is sound
  in isolation (`force_circ_of_force`), but adding it alone breaks the
  join condition (†).
* **No rule deriving `A ⇒ ◯A`.**  The unit makes it unsound; standing test
  cell.

---

## 5. What is asked

1. **Sign off, amend or reject** `◯∈` (§4.1) and `⋈^p` (§4.2).
2. **Decide `⋈^⊥` and fallible worlds** (§4.3).  This is the substantive
   one: it changes `Kripke`, and it puts a new obligation on the
   completeness construction.  The alternative is to accept that the
   calculus is incomplete for goals like `◯p ⊃ p` — which is a real
   option if the target is a *sound* disproof engine rather than a
   complete one, since an incomplete refutation calculus still certifies
   every refutation it finds.
3. **Confirm the atomic change of §3** — zones, closure, determining part,
   joins and rules together — since it re-canonicalises every context and
   should be done in one commit.

## 6. Status

**PROVED** (no axioms, pinned in `FRJ/Modal.lean`): the five semantic
obligations, and the three screens by `decide`.

**OPEN**: soundness and completeness for any calculus containing modal
rules.  No modal rule is part of `FRJ/Calculus.lean`.
