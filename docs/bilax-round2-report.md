# BiLax round 2 — the disproof engine, delivered

> ## ⚠ CORRECTION (2026-08-13, Matthew's challenge — READ THIS FIRST)
>
> **The title of this report is wrong and the report overstates what was
> achieved.**  What round 2 built is a countermodel constructor with a
> labelled bookkeeping layer — *not* a calculus of disproofs.  The
> decisive evidence: **neither certified refutation contains a single
> `⤙` or `◯∃`.**  Both branches (`BiLax/Pipeline.lean`) hold only
> `emb`-images, i.e. pure PLL formulas.  The co-lax modality was
> defined, screened, shown to collapse, rescued from vacuity by adding
> an entire extra relation `Rc` with three frame laws — and then plays
> NO ROLE in either refutation; `Rc` is present only to satisfy laws the
> refutations never invoke.
>
> §0's "structural finding" — that the route needs neither cut
> admissibility nor the ND↔labelled equivalence — reads, honestly, as:
> **the new logic was inessential to what was built.**  That is a
> symptom, not a result.
>
> The error: I let the Pinto–Uustalu framing ("saturated open branches
> are countermodels") substitute for the actual goal.  That literature
> is proof search WITH countermodel extraction — the standard
> model-construction approach.  The goal was the opposite direction: a
> system in which **the refutation IS the derivation**, so that finding
> one is a positive, depth-first search for a syntactic object, with the
> co-fragment carrying the content.
>
> **What the right target is** (now the live thread, see
> `docs/bilax-round3-plan.md`):
> 1. **Internalisation** — co-residuation at `C := ⊥` gives
>    `A ⊢ B ⟺ ⊢ ¬(A ⤙ B)`, hence **`A ⊬ B` iff `A ⤙ B` is
>    satisfiable**: failure of entailment becomes an existential
>    statement about ONE formula.  This is the genuine payoff of
>    co-implication, and nothing below uses it.
> 2. **A refutation (rejection) calculus** — Łukasiewicz's rejection
>    systems, and for intuitionistic logic Skura's: axioms are
>    *rejected* formulas, rules propagate rejection, and `⊬ φ` is
>    established by a POSITIVE derivation.  Complete for logics with the
>    finite model property, which PLL has.  That is the literature this
>    work should have been built from.
>
> **What survives below**: the semantics (`BiModel`, the adjunction, the
> collapse refutation) — a rejection calculus is proved complete
> *against* exactly this semantics, so the model theory is not wasted.
> **What is demoted**: everything framed here as "the disproof engine".
> The Hintikka/saturation machinery is a countermodel constructor; this
> repo already had those.  It is infrastructure, not the deliverable.
>
> The technical claims below are all still TRUE and machine-checked.
> Only their significance was misdescribed.

---


*2026-08-13.  Plan `docs/bilax-plan.md` §7; round 1 `docs/bilax-round1-report.md`.
Code: `BiLax/{Hintikka,Refute,Check,Pipeline}.lean`.  Status words precise:
PROVED = sorry-free + pinned `#print axioms`; OPEN = stated as such.*

## 0. The headline

**A failed proof search is now a certified refutation.**  [CORRECTED: this is countermodel construction, not a calculus of disproof — see the correction above.]  The round-2
pipeline is

    (untrusted search)  →  FinBranch (plain finite data)
                        →  `by decide`  (saturation certificate)
                        →  Hintikka  →  a BiModel  →  the truth lemma
                        →  ¬ Nonempty (LaxND Γ φ)          [KERNEL]

with axiom profile **`[propext, Quot.sound]`** — no choice, no
`native_decide`, no `sorry`.  This is what Matthew asked the whole
build for: refutation as a depth-first, model-size-independent,
certificate-carrying activity rather than a breadth-first battery
sweep.

**A structural finding worth stating on its own.**  The pipeline needs
NEITHER cut admissibility NOR the ND↔labelled equivalence — round 1
deferred both, and round 2 shows the refutation route does not depend
on either.  The reason: a saturated branch yields a *model*, and
soundness of `BiLaxND` (already proved) converts a model into
non-derivability directly.  Cut and the equivalence remain open
proof-theoretic questions about `BiLaxL`; they are no longer on the
critical path for the application.

## 1. Model existence (`BiLax/Hintikka.lean`)

`Hintikka` is a saturated open branch as data: worlds `Fin n`, the
relations `ri`/`rm`/`rc` and `fal` as predicates, left/right
assignments `L`/`R`, subject to the frame laws of `BiModel`, one
saturation condition per rule, and openness.

* `Hintikka.toModel` — the extracted `BiModel` (all three retrospective
  laws hold by construction).
* **`Hintikka.truth`** — the truth lemma: left formulas are forced at
  their label, right formulas refuted there.  **PROVED, and it
  DEPENDS ON NO AXIOMS AT ALL** — the strongest pin the repo has.
* `Hintikka.not_biLaxND`, `not_biConsequence` — a branch certifies
  bi-lax non-derivability, through `biLaxND_sound` alone.

This is the reusable core of completeness: completeness itself =
model existence + a saturation construction, and the construction is
where termination lives (§4).

## 2. The bridge to PLL (`BiLax/Refute.lean`)

`Hintikka.not_laxND`: a branch carrying the EMBEDDED sequent certifies
`¬ Nonempty (LaxND Γ φ)`, composing `truth`, `bforce_emb` and PLL's own
`soundness`.  Pin `[propext]`.

**Calibrations** (both PROVED, hand-built branches):

* `not_derivable_negOBot` — `⊬ ¬◯⊥`: two worlds `0 ≤ 1`, `1` fallible.
  A first attempt with reflexive `Rc` was rejected *by the counit law*
  — on this chain no world's `Rm`-cone lies below `0` — so `Rc` points
  at the top world.  The law bites; it is not decorative.
* `not_derivable_boxp_p` — `◯p ⊬ p`, the repo landmark, exercising
  atoms; no fallible world needed.

## 3. The checker and the pipeline (`BiLax/Check.lean`, `Pipeline.lean`)

`FinBranch` is the same object in fully finite presentation (`Bool`
relations, `List BiForm` assignments).  `checkB` is the conjunction of
twelve atomic decidable conditions; **`toHintikka`** turns a
`checkB = true` certificate into the real structure (PROVED, all
twelve conditions unpacked); `not_laxND_of_check` is the one-line
pinning theorem.

`BiLax/Pipeline.lean` runs both calibrations through it end to end:
the branch is written as data a searcher could emit, `checkB = true`
is discharged `by decide`, and the refutation theorems come out at
`[propext, Quot.sound]`.  **This is the repo's discover-then-pin
doctrine applied to countermodels**: the searcher may be arbitrary
and untrusted; only the certificate is checked.

## 4. What round 2 did NOT deliver, and why

* **The automated searcher** — OPEN.  The checker makes any search
  *pinnable*; writing the search itself (a saturating proof-search
  procedure with a blocking/loop-check discipline) is an engine, not a
  theorem, and it is the natural round-3 deliverable.  Its hard part
  is unchanged from the round-1 design report: `serialC` and `counit1`
  generate fresh labels unconditionally, so a naive saturation
  diverges; a demand-driven variant plus loop-checking is required,
  and its termination should be SCREENED on the catalogue's actual
  formulas before it is scoped.
* **The catalogue's 109 flags** — untouched.  They are the target the
  searcher exists for; hand-building 109 branches is not the plan.
* **The full duality bridge** (plan §7.2, the `d(Γ) ⇒ d(Δ)`
  translation) — not attempted.  The PRACTICAL form of the bridge is
  what round 2 delivered (`not_laxND`): a refutation is now a
  checkable object.  The syntactic duality theorem remains a
  separate, screenable question.
* **Cut admissibility and `BiLaxND ⊣⊢ BiLaxL`** — still OPEN, and now
  demonstrably off the critical path (§0).

## 5. Files and replay

    BiLax/Hintikka.lean   -- model existence; truth lemma (axiom-free)
    BiLax/Refute.lean     -- the PLL bridge + two hand-built calibrations
    BiLax/Check.lean      -- FinBranch, checkB (12 conditions), toHintikka
    BiLax/Pipeline.lean   -- both calibrations as data + `by decide` + pins

    lake build BiLax      -- everything above, ~1 min warm

## 6. Verdict

Round 2's mathematical content — completeness-as-model-existence, the
disproof bridge, and a kernel-checkable certificate format — is
**DONE**.  The engine that will consume it (search) is round 3, scoped
above.  The round's structural finding is that the disproof route is
independent of the two proof-theoretic obligations round 1 left open,
which removes the main risk the plan carried into round 2.
