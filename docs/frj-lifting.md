# FRJ(G) and what lifting it to ◯ would take

*2026-08-13.  Sources read directly: the TABLEAUX-2017 appendix
(completeness proof, Lemmas 3–5) from Fiorentini's page; the
publication list confirming the TOCL 2020 paper and — the important
find — **"A forward internal calculus for model generation in S4",
JLC 2021, by the same authors**, which is the modal instance of this
very method.  Empirical input: `wip/frj_probe.lean`
(`lean_exe frjprobe`).*

## 1. What FRJ(G) actually is

Not a rejection calculus in Łukasiewicz's sense, and not a tableau.
It is a **forward (inverse-method) saturation calculus over a finite
sequent set** whose derivations are *syntax for assembling Kripke
countermodels*.

Two sequent forms:

* **regular** `Γ ⇒ C` — "there is a countermodel rooted at a world
  forcing `Γ` and refuting `C`";
* **irregular** `Σ ; Θ → C` — the same, but with the root's content
  split: `Σ` is **stable** (holds at the root), `Θ` is **non-stable**
  (holds above it, not necessarily at it).

The completeness lemma (Lemma 4 of the appendix) makes the semantics
exact.  Writing `Λ_α` for the formulas of `SL(G)` forced at world `α`
and `Λ*_α = Λ_α ∩ L^⊃`: for a countermodel `K` of `G`, a world `α`,
and any `C` unforced at `α`, one can choose `Γ, Σ, Θ` with

    (i)   ⊢_FRJ(G)  Γ ⇒ C
    (ii)  ∃β ≥ α with Λ*_β ⊆ Γ
    (iii) ⊢_FRJ(G)  Σ ; Θ → C
    (iv)  Σ ⊆ Λ*_α ⊆ Σ ∪ Θ

so a derivation is a *recipe for the model*, and (iv) is the tie
between the syntactic zones and one world's theory.  Lemma 5 —
`Λ_α = Cl(Λ_α) = Cl(Λ*_α)` — says a world is determined by its
implicational part under the closure `Cl`; that is why FRJ can absorb
all LEFT rules into `Cl` and keep only right rules.

The engine room is the **join rules `⋈^At`, `⋈^∨`**: they take `n`
irregular premises and build a regular sequent by **creating a fresh
root below the `n` sub-models**, with

    Γ = Σ^At ∪ (Θ^At \ {C}) ∪ Σ^⊃ ∪ Θ^⊃

and side conditions (a) `Σᵢ ⊆ Σⱼ ∪ Θⱼ` for `i ≠ j`, (b) `Y⊃Z ∈ Σⱼ^⊃`
implies `Y ∈ Υ`, (c) `C ∉ Σⱼ^At`.  The two `⊃`-rules split on whether
the refuting world is the root (`⊃∈`, `A ∈ Cl(Γ)`) or strictly above it
(`⊃∉`), and `⊃∈` in the irregular case *shifts a set from the Θ-zone
to the Σ-zone* — i.e. promotes "true above" to "true here".

The induction that proves completeness is on **`h(α)`, the height of
the world** (longest path to a final world), then on sequent type, then
on `|C|`.  Termination is structural: every sequent is built from
subformulas of `G`, so there are finitely many, and forward saturation
must stop.

**Why this is the right template, in one sentence.**  My labelled
calculus diverged because backward rules (`serialC`, `counit1`)
generate fresh labels without bound; FRJ has no fresh-name generation
at all — new worlds are created by *joins over a finite sequent set*,
so termination is free.

## 2. What ◯ needs

PLL: `w ⊩ ◯A` iff `∀v ≥ᵢ w ∃u. v Rm u ∧ u ⊩ A`.  So

    refuting ◯A at α  =  ∃v ≥ᵢ α such that NO Rm-successor of v forces A.

Two quantifier facts decide the design.

**(1) The inner ∀ collapses to the Rm-MAXIMAL successors.**  Forcing is
hereditary and `Rm ⊆ Ri`, so if any `u` in the cone forces `A` then so
does every world above it; hence

    ∀u ∈ Rm-cone(v). u ⊮ A   ⟺   ∀u maximal in Rm-cone(v). u ⊮ A.

The **arity** of the ◯-refutation rule is therefore the number of
Rm-maximal successors.

**(2) The remaining ∀ is discharged by construction, not by a
premise.**  In FRJ the model is *built* by the join rules, so "these
are all the Rm-successors" is known to the rule that created them.
The universal becomes an exhaustiveness side condition on a join, not
a semantic quantifier inside a premise.

> **This corrects what I told you earlier.**  I said the ∀∃ clause
> forces a *hybrid* deduction–refutation rule, because the inner
> universal is a validity statement no antisequent premise can express.
> That is true for a BACKWARD calculus (Goranko's MIX rules, Goré–
> Postniece's `⊲/⊳`).  It is NOT true for a forward model-building
> calculus, where the model is the derivation's own product.  FRJ
> dissolves the obstacle rather than paying for it.

## 3. The arity measurement (`lean_exe frjprobe`)

Exhaustive over well-formed frames; "arity" = number of Rm-maximal
successors of a world.

| class | n=2 | n=3 |
|---|---|---|
| all well-formed | 83% unary, max arity 2 | 84% unary, max arity **3** |
| **reduced** (partial orders) | **100% unary** | 98% unary, max arity 2 |
| confluent (PCLL class) | 83% unary, max 2 | 81% unary, max **3** |
| **reduced AND confluent** | **100% unary** | **100% unary, max arity 1** |

(52,800 worlds in the last cell at n=3, all arity 1.)

**Reading.**  Confluence alone does not help.  **Reducedness is the
load-bearing condition**, and reduced + confluent gives arity exactly
1 — the ◯-refutation rule is then **unary**, the same shape as FRJ's
own `⊃`-rules, and the calculus stays inside the architecture with no
new rule format.

The reason is available in the repo already: mutual confluence gives
directedness of the `Rm`-row (`confluent_directed`), a finite directed
poset has a greatest element, and antisymmetry (= reducedness) makes it
unique.  We even have the canonical instance: `rmC_le_obInv` proves
`obInvW Δ` is the MAXIMUM `RmC`-successor.  So the unary rule's witness
is the promise world, and refuting `◯A` at `Δ` is exactly
`A ∉ obInv(Δ)`.

For full PLL the max arity grows with the frame size (2 at n=2, 3 at
n=3), so a bounded-arity rule is unlikely to exist — Goranko's `Alt_n`
phenomenon, exactly as warned.  **Corollary for sequencing: do PCLL
first.**  That is a genuine inversion — the *stronger* logic is the
easier target — and it lines up with the confluent machinery already
mechanised here.

**Your reducedness idea earns its keep here.**  It did not repair the
`⤙`/fallibility fight (nothing could: `ff` is unforceable for logical
reasons).  But it is precisely what makes the modal refutation rule
unary, and it is also what the height induction needs (see §5).

## 4. The lifted calculus, concretely

Sequent data gains two components:

    Σ ; Θ ; μ  →  C          μ = the modal zone

where `μ` records the root's `Rm`-successor content — on reduced
confluent frames, the single maximum successor's theory.  Rules:

* **`Cl` becomes PLL-closure.**  FRJ absorbs left rules into `Cl`;
  for PLL that closure must include `laxIntro`/`laxElim`.  Computable
  here: we have G4-family deciders over a finite subformula set.  This
  is the one place where the lift is *work* rather than *design*.
* **`◯∈` / `◯∉`** mirroring `⊃∈` / `⊃∉`: the refuting `v` is the root
  (premise: `A` fails at the root's modal zone, i.e. `A ∉ Cl(μ)`), or
  strictly above (premise: an irregular sequent refuting `◯A`).
* **Join rules gain a modal component**: each join declares which
  sub-models are `Rm`-successors of the new root, subject to
  `Rm ⊆ Ri`, reflexivity (the root is its own successor — so the root
  must itself refute `A`) and transitivity.  The `◯`-positive
  obligation (`◯A ∈ Σ` ⟹ every `Ri`-successor has an `Rm`-successor
  forcing `A`) becomes a side condition checked against the premises.
* **Fallibility is a zone flag.**  `⊥ ∈ Cl(Σ)` marks a fallible world;
  fallible worlds refute nothing, so they never carry a refutation
  premise, and refuting `◯A` requires no fallible `Rm`-successor.
  Pleasingly, refuting `◯⊥` is exactly the base case of that
  condition — the fallibility machinery falls out of the modal rules
  rather than being bolted on.

## 5. The four obligations, honestly graded

1. **PLL-closure `Cl` over the finite subformula set** — **SCREENED
   2026-08-13: PASSES, with the repair.  See §7.**  Still WORK (the
   closure properties (Cl1)–(Cl6) and Lemma 5's analogue must be
   PROVED, not screened), but the architecture transfers.
2. **The height induction** — needs `h(α)` to decrease along both `Ri`
   and `Rm` steps.  `Rm ⊆ Ri` gives it, PROVIDED the model is reduced
   (otherwise `Rm`-successors can be `Ri`-equivalent to the source and
   the measure stalls).  Second place reducedness is load-bearing.
3. **Join side conditions with a modal component** — decidable, but
   completeness (Lemma 4's analogue) must show every countermodel
   decomposes to satisfy them.  This is the real proof obligation.
4. **The S4 precedent must be read.**  Fiorentini–Ferrari's JLC 2021
   *forward internal calculus for model generation in S4* is the same
   method with a transitive modality — the nearest existing instance of
   exactly this lift, by the authors of the base calculus.  **Read it
   before designing anything further**; it will have solved (2) and (3)
   for `□`, and PLL's `◯` is a monad-shaped relative.

## 6. Recommendation

The lift is **plausible and much better-founded than the labelled
route** — it dissolves the ∀∃ obstacle instead of paying for it, and
its termination is structural.  Order of work:

1. Read the JLC 2021 S4 paper (obligation 4).
2. Test obligation 1 on the closed fragment: is a PLL world's theory
   `Cl` of its implicational + modal part?  A screen over the battery,
   cheap, and it is the go/no-go.
3. Target **PCLL over reduced models first**, where the ◯-rule is
   provably unary and the canonical maximum is `obInvW`.
4. Only then consider full PLL, where the unbounded arity means a rule
   schema over premise lists.

The prize is unchanged and worth it: a refutation would become a
finite syntactic object checkable by a decidable rule predicate, so
"REFUTED" becomes as cheap as "PROVED" under the machine-checked
mandate — and the countermodel is *extracted from* it rather than
substituting for it.


## 7. The `Cl` screen — RUN (2026-08-13)

`lean_exe clscreen` (`wip/cl_screen.lean`, output
`wip/cl_screen_out.txt`).  Per Matthew's instruction — a failure may
be repairable by changing the rules for `Cl`, so do not test one
statement — the screen sweeps a LATTICE of variants: three choices of
determining part `Λ*` × two closures, over 6 goals × 8 battery models
× their worlds = 156 cells each.  Only `Λ ⊆ Cl(Λ*)` can fail
(the converse is soundness), and a failure is a certificate.

| `Λ*` (determining part) | `Cl` = none | `Cl` = PLL-consequence |
|---|---|---|
| atoms + ⊥ | 129 FAIL | 92 FAIL |
| atoms + ⊥ + implications *(the literal IPC choice)* | 103 FAIL | **32 FAIL** |
| atoms + ⊥ + implications + ◯-formulas *(the repair)* | 50 FAIL | **0 FAIL** |

**Verdict: GO, with the repair — and the repair is forced.**

* The **literal IPC choice fails**: 32 certified cells where a formula
  is forced at a world but is not a PLL-consequence of that world's
  atoms and implications.  Witness: `◯(p ∧ ◯q)` at worlds 2 and 3 of
  `deep5`.  This is the expected content — `◯` is not definable from
  the propositional connectives, so a modal formula's truth is
  genuinely new data about a world, not recoverable from its
  implicational part.
* **Adding ◯-formulas to the determining part closes it completely**:
  0 failures in 156 cells.  So FRJ's Lemma 5 does have a PLL analogue,
  with `Λ*` = the non-`∧`/`∨` formulas (atoms, ⊥, implications AND
  boxes) — which is the natural reading of FRJ's own choice anyway
  (there, `∧`/`∨` are the only compositionally-recoverable
  connectives; PLL just has one more irreducible constructor).
* **Non-vacuity**: every control fails, and both dimensions do work
  (129→103→50 without closure, 92→32→0 with it).  The screen is not
  passing by accident.

**Caveats, stated.**  The battery is curated (8 models, 6 goals, 156
cells), so a pass is SUPPORT, not proof; the actual obligation is to
PROVE the Lemma 5 analogue.  And this screen tests only the *statement*
`Λ = Cl(Λ*)`; the closure properties (Cl1)–(Cl6) that FRJ's rules
consume are separate and unscreened.

**Consequence for the design.**  §4's proposal — a modal zone in the
sequent data — is not an optional extra: the screen shows modal
formulas MUST be carried as determining data.  The lifted sequent is
therefore `Σ ; Θ ; μ → C` with the boxes tracked explicitly, exactly as
designed, and obligation 1 is off the critical path.
