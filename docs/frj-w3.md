# W3 — fallible worlds, the modal rule, and what each of them buys

*2026-08-17, branch `claude/frj-redevelopment-69005f`, on top of W1 and W2.
Everything below is machine-checked in `FRJ/`; `lake build FRJ` is green,
there is no `sorry`, and every claim is pinned with `#print axioms`.*

W3's exit criterion was: **soundness extended with the `◯` cases.**  Done,
and the shape it took is not quite the shape §4 of `docs/frj-modal-rules.md`
proposed.

---

## 1. The semantics now has fallible worlds

`Kripke` gained four fields:

    Fal      : W → Prop                        the worlds at which ⊥ holds
    fal_mono : le a b → Fal a → Fal b          fallibility is inherited upwards
    fal_V    : Fal a → ∀ p, V a p              every variable holds at a fallible world
    decFal   : ∀ a, Decidable (Fal a)

and the `⊥`-clause of forcing became Fairtlough–Mendler's:

    K,α ⊩ ⊥   iff   α ∈ Fal

From `fal_mono` and `fal_V` alone, **a fallible world forces every
formula** (`Kripke.fal_force`, no axioms).  The `◯` case of that induction
is where the modal frame enters: a fallible `α` forces `◯A` because
`Rm α α`, so `α` is its own witness.

Two derived notions, because with `Fal` present the old `IPL` splits in
two:

    Infallible K  :=  ∀ w, ¬ K.Fal w
    IPL A         :=  ∀ K, K.Infallible → K.valid A     -- the paper's IPL
    PLL A         :=  ∀ K, K.valid A                    -- validity in all constraint models

`PLL A → IPL A`, and the converse fails: see §4.

## 2. Why fallible worlds are not optional

**PROVED** `valid_neg_circ_bot_of_infallible` : every infallible model
validates `¬◯⊥`.  The argument is one line — `α ⊩ ◯⊥` asks for a modal
successor forcing `⊥`, i.e. for a fallible world.

Hence `IPL (¬◯⊥)`, and hence

**PROVED** `not_provable_neg_circ_bot` : `¬ Provable (¬◯⊥)`.

That is a genuine **incompleteness**, and it holds for *every* extension of
the calculus whose extracted models are infallible, not just for the rules
written so far: soundness can only ever conclude `¬ IPL G`, and `¬◯⊥` has
`IPL`.  Since `¬◯⊥` is not valid in the logic (§4), the calculus needs
fallible worlds to reach it.  This is Matthew's argument, mechanised.

## 3. `Mod(D)` is barren, and `◯∈`

`PreModel.toKripke` used to package `Rm := ≤`, which was free while no rule
mentioned `◯`.  W3 changed it to **equality**: every extracted world is
barren, its only modal successor is itself.  The consequence, proved as
`toKripke_force_circ`, is

    Mod(D), α ⊩ ◯A   iff   Mod(D), α ⊩ A

— in every extracted model the modality is the **identity**.  Both halves
are used: left to right is the soundness of the new rule, right to left is
the unit of the modality.

The rule, now in `FRJ/Calculus.lean`:

        Γ ⇒ Z
    ─────────────  ◯∈        ◯Z ∈ Sf^R(G)
        Γ ⇒ ◯Z

with **no side condition** and, in particular, no `barren` index.  W2
proposed one; it is not needed, because barrenness is a property of the
model *construction* — it holds at every world of every `Mod(D)` — rather
than something a derivation has to track.  It would be needed the moment a
rule creates a modal successor.

**PROVED**: the `◯∈` case of Lemma 3.9(i), hence Theorem 3.10 and Theorem
3.1 (`soundness`) now cover a calculus with a modal rule.

### On committing to a barren world

The rule looks like a commitment — building a world with no modal
successors in order to refute `◯Z` — but nothing is committed in advance.
FRJ is a **forward** calculus: `◯∈` consumes a refutation of `Γ ⇒ Z` that
is already in hand, and the premise's derivation *is* the certificate that
a world forcing `Γ` and refuting `Z` exists.  Nothing is guessed.

What *is* committed in advance is the uniform choice `Rm := Eq` in
`toKripke`, and that choice has a price, stated exactly:

* it makes `◯∈` sound at every world, for free, with no bookkeeping;
* it makes `◯` the identity, so the model can never witness a modality
  non-trivially, and `◯∈` adds no refutational power beyond `◯`-erasure.

In barren models `α ⊮ ◯A` and `α ⊮ A` are equivalent, so `◯∈` is invertible
there: it is exactly right for the models the calculus builds, and it is
the ceiling of what those models can do.

## 4. The fallible route, and what it buys

The other side of the trade is `Kripke.falTop`: `K` with one fallible world
on top, **`Rm`-visible from every world**.  In it every world forces every
`◯`-formula (`falTop_force_circ`).

The correction that shapes this — Matthew's, 2026-08-17 — is that
visibility, not position, is what does the work.  A fallible world merely
sitting `≤`-above a world contributes nothing, because `Rm` is in general a
proper subrelation of `≤`.  Machine-checked as `Screen.silent`: two worlds
`w < f` with `f` fallible and `Rm` equality; the root refutes `◯⊥` and
`◯p` and *validates* `¬◯⊥`.  The sentence that claimed otherwise in
`docs/frj-modal-rules.md` §4.3 has been struck and the correction recorded
in its place.

With `triv A` the `◯`-trivialisation (`triv (◯A) = ⊤`, everything else
structural):

**PROVED** `falTop_force` : `K.falTop, α ⊩ A  ↔  K, α ⊩ triv A` at every
old world `α`.

**PROVED** `not_PLL_of_provable_triv` : an `FRJ(triv G)`-derivation of
`triv G` refutes `PLL G`.

This needed **no new rule**: the `◯`-free calculus refutes the
trivialisation, and `falTop` turns its countermodel into a countermodel for
the modal formula.  It is what W2 §4.3 called `⋈^⊥`, relocated from the
calculus to the model construction, which is where it costs nothing.

## 5. The two routes are incomparable

Both directions machine-checked, on the two formulas that separate them.

| formula | barren route (`◯∈`, `Mod(D)`) | fallible route (`triv`, `falTop`) |
|---|---|---|
| `◯p` | **refutes it** — `provable_circ_atom` | cannot: `triv(◯p) = ⊤` is valid — `not_provable_triv_circ_atom` |
| `¬◯⊥` | **cannot** — `not_provable_neg_circ_bot` | **refutes it** — `provable_triv_neg_circ_bot` |
| `◯p ⊃ p` | cannot (its erasure `p ⊃ p` is a theorem) | **refutes it** — `provable_triv_circ_imp` |

The two `provable_triv_*` results are actual `FRJ`-derivations, not
appeals to a model: `Ax^I` at `⊥` puts `⊥ ⊃ ⊥` into the irregular zone,
the join keeps it by the restriction (its antecedent `⊥` is the premise's
right formula), and `⊃∈` discharges it from the closure.

## 6. What completeness now says

`completeness`, `completenessData`, `frj_iff_countermodel` and
`frj_iff_not_IPL` gained the hypothesis that the input countermodel is
**infallible**, and `frj_iff_countermodel` now reads

    Provable G  ↔  ∃ K, K.Infallible ∧ ¬ K.valid G

which is *stronger* than before in the left-to-right direction.  The
hypothesis is not a gap in the proof: at a fallible world every formula is
forced, so `Ω_α` is empty and `Cl(Λ*_α)` cannot reach `⊥` — a fallible
countermodel carries no data the calculus can consume.  It is the exact
statement of §2's incompleteness.

## 7. Status

**PROVED, no `sorry`, axioms pinned** — `soundness` and
`frj_iff_countermodel` on `[propext, Quot.sound]`, `frj_iff_not_IPL` adding
`Classical.choice` at the one step that needs it, `Kripke.fal_force` on no
axioms at all.

**OPEN**, and unchanged by W3:

1. **The promise join `⋈^p`** (`docs/frj-modal-rules.md` §4.2) — the only
   rule that would make `◯` non-trivially true and so break the erasure
   ceiling of §3.  It needs the `barren`/`promising` index W2 described,
   because a rule that creates a modal successor destroys barrenness at the
   world it creates.
2. **The third zone `Ĝ_◯`** — still not added, for the reason recorded on
   `gHat`; it is an atomic change with the joins and would be forced by (1).
3. **Completeness for fallible countermodels** — i.e. for `PLL` rather than
   `IPL`.  Needs (1).
4. **`IPL G → PLL G` for `◯`-free `G`** (deleting the fallible worlds of a
   model preserves `◯`-free forcing at the worlds that remain).  Not needed
   by anything above; would let `frj_iff_not_IPL` be restated for `PLL`.
