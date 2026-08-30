# The tag conflict, settled — and what to do about it

*2026-08-30. Branch `claude/frjv-completeness-693c52`. Companion to
`docs/gbu-circ-seams.md`. **Proposal: nothing below is implemented.***

## 1. What the conflict was

`docs/gbu-circ-seams.md` derived two rules from the `FRJ◯` rules with
matching conclusions,

    Ψ ⇒g Z             Ω ⇒g Z
    ──────── R◯        ────────── R◯ₙᵢ
    Ψ ⇒g ◯Z            Ω →g ◯Z

and `wip/gbu_circ.lean` proved their invertibility clauses (Lemma 9,
clauses 12 and 13) *under a hypothesis* `TagClean G D Z`: every database
row for `Z` carries a tag `◯∈`/`◯∉` can lift, i.e. `barren` or
`chain W` with `Covers Γ W Z`.

Meanwhile Lemmas 11 and 12 extend to the modal case only through the
FALLIBLE joins (`gbuSuccAtF`, `gbuSuccOrF`), which produce `blocked`
rows. `blocked` is not clean. Hence the conflict.

## 2. It is not bookkeeping, and `◯∈` cannot be relaxed

`◯∈` needs the root's **whole modal cone** to refute `Z` — that is what
the tag pledges (`tag_cone`) — because `◯Z` fails at a root only if no
`Rm`-successor of any world above it forces `Z`. A `blocked` row's
extracted model has a **fallible** world in that cone, and a fallible
world forces everything; so its root forces `◯W` for every `W` and
cannot refute `◯Z`. Excluding `blocked` is forced by soundness.

## 3. The clauses are false — machine-checked, by hand, in FRJ◯

No appeal to tags is needed to see it. Take

    Gtc = (◯p ⊃ p) ⊃ (◯p ⊃ p),     Ω = {◯p},     Z = p

so that `◯p ∈ Sf^L(Gtc)` (the context is critical) **and**
`◯p ∈ Sf^R(Gtc)` (the clauses' own side condition `◯Z ∈ Sf^R(G)` is
met). Then

* `evalR_tc` : `{◯p} ⇒ p` **is** refutable — straight from `gbuSuccAtF`
  with an empty implication family, i.e. `Ax^I` at goal `p` followed by
  the fallible `⋈^At`;
* `not_evalR_tc` : `{◯p} ⇒ ◯p` is **not**, because `◯p ⊢ ◯p` and a valid
  sequent is refuted by no database;
* `not_evalI_tc` : `{◯p} → ◯p` is **not** either. (This needed a sharper
  soundness lemma, `not_evalI_circ_of_valid'`, keyed to validity of `◯Z`
  rather than of `Z` — the older lemma asks for `Ω ⊨ Z`, which is false
  here. Its `◯∉` case lifts the regular premise by `◯∈`, which is legal
  because `◯∉` carries the tag condition itself.)

Hence `rcirc_not_invertible` and `rcircNI_not_invertible`, both pinning
`[propext, Quot.sound]`.

**Reading:** refuting `◯Z` at a root is *strictly stronger* than
refuting `Z`. `R◯` and `R◯ₙᵢ` with a REGULAR premise are sound but **not
invertible**, so `BSearch` cannot apply them blindly. `TagClean` is not
a hypothesis waiting to be discharged; it is false where it is needed.

## 4. Proposal

In the paper's architecture a non-invertible rule lives at a **critical**
sequent, is chosen by a database query, and comes with a **success
lemma**. So:

### (P1) `Ω ⇒g ◯Z` becomes a third critical case

Critical becomes: `Ω ⊆ Ĝ` and the goal is `D ∈ Prime`, or `C₁ ∨ C₂`, or
`◯Z`. This is not an invention — it is what `⋈^◯` is for. `joinCirc`
carries

    hZ : Z ∈ upsilon rhs

which says `Z` must be a member of the IRREGULAR premise family, exactly
as `joinOr`'s `hC` says `C₁, C₂` must be. The `∨` case and the `◯` case
have the same shape, with the single "disjunct" `Z`.

### (P2) The condition on `R◯`: its premise is the irregular judgment

    Ω →g Z
    ────────  R◯          Ω ⊆ Ĝ
    Ω ⇒g ◯Z

`R∨ₖ`'s premise is irregular for the same reason, and `⋈^◯`'s `hZ`
forces it here. **This is a change to the rule, not merely a side
condition, so it is put here for review rather than implemented.** The
alternative (P2′) below keeps the rule's form.

### (P3) Lemma 13, the `◯` success lemma

Read off `⋈^◯`, parallel to Lemma 12:

    Ω ⊆ Ĝ,  ◯Z ∈ Sf^R(G),
    (i)  ∀ A⊃B ∈ Ω,  D ▷ (Ω →g A)
    (ii) D ▷ (Ω →g Z)
    ────────────────────────────────
    D ▷ (Ω ⇒g ◯Z)

with `Υ = {A | A⊃B ∈ Ω} ∪ {Z}`. The proof should be `gbuSuccOrF`
verbatim with `joinCirc` for `joinOrF` and the family `Z :: antecedents`.

### (P2′) The alternative that keeps the rule's form: a tag-refined query

Keep `R◯`/`R◯ₙᵢ` exactly as they are and put the condition on the
DATABASE QUERY instead, adding a second evaluation relation beside `▷`:

    D ▷◯ (Ψ ⇒g Z)   iff   ∃ ⟨t, Γ ⇒ Z⟩ ∈ D  with  Ψ ⊆ Cl(Γ)
                          and  t = barren ∨ (t = chain W ∧ Covers Γ W Z)

Then Lemma 9's clauses 12 and 13 hold as stated with `▷◯` in the
premise — they are `gbuInv12`/`gbuInv13` with `TagClean` localised to
the single row — and `BSearch` queries `▷◯` at a `◯` goal. `▷◯` is
decidable exactly when `▷` is, so nothing is lost procedurally, and the
counterexample of §3 is respected: `{◯p} ⇒ p` is refutable only by a
`blocked` row, so `D ⋫◯ ({◯p} ⇒g p)` and `R◯` is not applied there
(`Ax` fires instead, `◯p` being in the context).

**Why (P2) and not (P2′), on current evidence.** Under (P2′) the success
lemma at a critical `Ω ⇒g ◯Z` still has to come from `⋈^◯`, whose query
for `Z` is the IRREGULAR `D ▷ (Ω →g Z)`; and when that query fails,
(P2′) has no rule to apply. (P2) supplies exactly that rule. So (P2′)
looks like a repair of the invertibility statement without a repair of
the search. It may still be the right choice if `⋈^◯` is not the only
route — that is the question to settle before implementing.

### (P4) The measure is unaffected

`R◯` under (P2) behaves as `R∨ₖ`: `unclosed` and `ctxSize` unchanged,
goal size drops. `R◯ₙᵢ` keeps a regular premise (its counterpart `◯∉`
has one), so it still raises `tp` and the store-carrying `Wg◯` of
`wip/gbu_measure.lean` is still required. Nothing in §§1–3 disturbs
`no_measure_stepC` or `stepU_wf`.

## 5. The one question left open

`Ω →g ◯Z` — the irregular `◯` goal — has no success lemma yet. Only two
`FRJVi` rules conclude `◯Z`: `Ax^I◯`, which fires when `Ω` is
classically saturated by its own atoms (the endpoint condition), and
`◯∉`, which is tag-conditioned and which §3 refutes as an unconditional
clause. So either

* `Ω →g ◯Z` is always discharged when it is reached — in which case
  seam 3 evaporates and `R◯ₙᵢ` is unnecessary; or
* it is not, and there is a cell that is neither `Gbu◯`-provable nor
  `FRJV`-refutable.

**The test** (to be pushed through by hand in `FRJ◯`, not searched for):
find `Ω ⊆ Ĝ`, `◯Z ∈ Sf^R(G)` with `◯Z ∉ Ω`, `Ω` NOT classically
saturated by its atoms, `Ω ⊢ ◯Z` (so the sequent is not refutable), and
`Ω` reachable as a critical context. If `Ω ⊢ ◯Z` always factors through
`Ax`, `L⊃` or `L◯` at such an `Ω`, the first horn holds.
