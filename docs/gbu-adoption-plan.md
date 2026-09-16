# Adoption plan: Gbu(G), and the route to Gbu◯(G)

*Stage 1 deliverable of the `calculus-adoption` skill. Reviewable without
opening any code. **No Lean until Matthew has reviewed this.***
Written 2026-08-29, branch `claude/frj-redevelopment-69005f`.

## The requirement

> A certificate for FRJ-underivability that can be read off the FRJ
> saturated database, so that completeness of FRJ(◯) follows from a
> SYNTACTIC read-back rather than from a minimal-model construction.

Naming the capability rather than the shape matters here: the seven
routes tried so far all committed to the shape "minimal-model
construction over `Λ*`", and all seven terminated in a named hypothesis
or a frame restriction (audit, HANDOFF §2026-08-29a).

## Kind of result

Not soundness-and-completeness-against-a-semantics. This is a
**duality/read-back** result: two calculi over ONE saturated database,
with a search procedure connecting them (`reference/result-kinds.md`
triage: nearest kind is "conservativity/translation", not "semantic
completeness"). Consequence for the encoding: the database is a
first-class object, and the theorems quantify over it.

## The source — RECOVERED

* Camillo Fiorentini & Mauro Ferrari, *Duality between Unprovability and
  Provability in Forward Refutation-search for IPL*, ACM TOCL 21(3),
  Article 22, 2020.  Preprint **arXiv:1804.06689**, whose LaTeX source is
  what the existing mechanisation was transcribed from
  (`paper/frj-modal/frj-modal.tex` §2 records this, with a table of the
  journal-vs-arXiv numbering and three substantive differences).
* Recovered 2026-08-29 by following that reference: the arXiv e-print
  unpacks to `frj-corr.tex`, 228 KB — the very file
  `docs/frj-paper-skeleton.md` was generated from.
* **Parked at `LaxLogic/papers/frj-corr-arxiv-1804.06689.tex`**, which is
  git-ignored.  It is a copyrighted preprint and this repository is
  public: it must NOT be committed.  Re-fetch with
  `curl -L https://arxiv.org/e-print/1804.06689`.
* Appendix: present (§"Soundness of FRJ(G)", line 6264 of the source) —
  to be read before Stage 2, per the skill.

### Correction: the reconstruction attempted before the source arrived was WRONG

Recorded because the error is instructive.  From the statements alone I
argued that `⇒g` had to be an UNPROVABILITY judgment, because three of
Lemma 9's six clauses are unsound for provability.  The rule table
(Fig. `fig:GBU`) shows `⇒g` is ordinary provability, with `R∧` taking
BOTH premises and `L∨` taking BOTH branches, exactly as one would expect.

The actual resolution is that **`▷` is not Gbu-derivability at all**.  Its
definition (source line 3287) is a *query against the FRJ database*:

    D_G ▷ (Ψ ⇒g C)   iff  ∃ (Γ ⇒ C) ∈ D_G  with  Ψ ⊆ Cl(Γ)
    D_G ▷ (Ω →g C)   iff  ∃ (Σ ; Θ → C) ∈ D_G  with  Σ ⊆ Ω ⊆ Σ ∪ Θ

That is: **the database holds an FRJ REFUTATION covering this sequent** —
a negative fact about `τ`, not a derivation of it.  Lemma 9 then reads
correctly and cheaply: its six clauses are `Cl`-monotonicity in the left
zone plus FRJ's own right-rules, e.g. (iii) holds because `A_k ∈ Cl(Γ)`
implies `A₁∨A₂ ∈ Cl(Γ)` by `Clo.orL`/`Clo.orR`, and (iv) because
`B ∈ Cl(Γ)` implies `A ⊃ B ∈ Cl(Γ)` by `Clo.imp`.  Every one of them is
about FRJ's `Clo`, which this repo already has.

Lesson for the record: I inferred a judgment's polarity from the
soundness of lemmas that were not about that judgment.  Read the
definitions.

## The calculus, transcribed target

Two judgments — `⇒g` (full phase) and `→g` (right focus).  For every
sequent, `Lhs ⊆ Sfl(G)` and `Rhs ∈ Sfr(G)`.  In our notation:

**`⇒g`**

| rule | premises | conclusion | side condition |
|---|---|---|---|
| `Ax` | — | `A,Ψ ⇒g A` | |
| `L⊥` | — | `⊥,Ψ ⇒g C` | |
| `L∧` | `A,B,Ψ ⇒g C` | `A∧B,Ψ ⇒g C` | |
| `R∧` | `Ψ ⇒g A` and `Ψ ⇒g B` | `Ψ ⇒g A∧B` | |
| `L∨` | `A,Ψ ⇒g C` and `B,Ψ ⇒g C` | `A∨B,Ψ ⇒g C` | |
| `R∨ₖ` | `Ψ →g Cₖ` | `Ψ ⇒g C₁∨C₂` | |
| `L⊃` | `A⊃B,Ψ →g A` and `B,Ψ ⇒g C` | `A⊃B,Ψ ⇒g C` | |
| `R⊃ᵢ` | `Ψ ⇒g B` | `Ψ ⇒g A⊃B` | `A ∈ Cl(Ψ)` |
| `R⊃ₙᵢ` | `A,Ψ ⇒g B` | `Ψ ⇒g A⊃B` | `A ∉ Cl(Ψ)` |

**`→g`** (no left rules at all — that is what "focused" means here)

| rule | premises | conclusion | side condition |
|---|---|---|---|
| `Ax` | — | `A,Ψ →g A` | |
| `R∧` | `Ψ →g A` and `Ψ →g B` | `Ψ →g A∧B` | |
| `R∨ₖ` | `Ψ →g Cₖ` | `Ψ →g C₁∨C₂` | |
| `R⊃ᵢ` | `Ψ →g B` | `Ψ →g A⊃B` | `A ∈ Cl(Ψ)` |
| `R⊃ₙᵢ` | `A,Ψ ⇒g B` | `Ψ →g A⊃B` | `A ∉ Cl(Ψ)` |

**Why it is backtracking-free, which is the whole point.**  The two
non-invertible rules are `R∨ₖ` and `L⊃`.  `Search` does not guess: it
queries the database and takes a branch the database does NOT refute —
`choose any Cₖ with D_G ⋫ (Ω →g Cₖ)`, `choose any A⊃B ∈ Ω with
D_G ⋫ (Ω →g A)` (source lines 3396, 3416).  The FRJ refutation database
is the oracle that removes the choice.  **That** is the duality's
mechanism, and it is concrete.

## The harness — proving the results before the rules exist

This is Matthew's instruction (2026-08-29) and it is the core of the
plan: *do not implement rules; derive them from the obligations the
proofs cannot discharge.*

Encode Gbu not as an inductive family but as a **parameter**:

    structure GbuOps (G : Form) where
      Seq   : Type                      -- the two sequent forms
      Der   : Seq → Prop                -- ⊢_Gbu(G)
      Eval  : DB G → Seq → Prop         -- D_G ▷ τ
      wg    : Seq → Nat × Nat × Nat     -- the measure
      …one FIELD per property the proofs consume, nothing else

Then state and prove §5's theorems **generically over `GbuOps`**. Every
field the proof reaches for is a demand on the rules; every field it does
NOT reach for is not part of the specification. The output of the stage
is the minimal `GbuOps` that supports Theorems 6–10 — which is the
*specification of Gbu*, derived rather than guessed.

Two properties make this honest rather than circular:

1. **Calibrate on IPC, where the answer is checkable.** FRJ's IPC side is
   fully mechanised here (`FRJ/Minimal.lean`'s `completeness` is the
   paper's §6 for `◯`-free goals; `FRJ/Search/` is `FSearch` with
   subsumption). So a reconstructed `GbuOps` can be tested: does the
   derived specification admit an instance, and does the instance agree
   with FRJ on the corpus? If the harness produces a specification no
   calculus can satisfy, that shows up here and not after the `◯` work.
2. **A vacuous instance must be impossible.** `GbuOps` with `Der := fun _
   => True` satisfies anything, so the plan requires a NEGATIVE gate:
   an explicit `GbuOps`-instance that is refuted by the corpus, watched
   failing, before any positive claim (`METHOD.md`'s standing rule —
   never ship a gate you have not watched fail).

Only then, Stage B: add the `◯` cases to the same harness. The `◯`-rules
of Gbu◯(G) are read off the obligations that the IPC-calibrated proofs
cannot discharge for `◯`-goals — and the prediction from
`docs/frj-ljfo-duality.md` §3 is that the obligation will be *the dual of
FRJV's tag*, which is where every previous route died.

## Scope

**In scope**, by label: `lemma:GBUsound` (7), `theo:GBUsound` (6),
`lemma:wggbu` (8), `theo:gbufin` (7), `lemma:gbuInv` (9),
`lemma:gbuiOr` (10), `lemma:gbuSuccAt` (11), `lemma:gbuSuccOr` (12),
`theo:search` (8), `theo:GBU-FRJ` (9), Theorem 10.

**Out of scope**, explicitly: re-deriving FRJ's §1–§4 (already
mechanised); `BSearch` as a *runnable* procedure (Stage 4, later); the
`◯` case (Stage B, gated on IPC calibration); any change to FRJV's rules
— the V5 licence rule stands.

## Repo results consumable read-only

`FRJ/Basic.lean` (`sfL`/`sfR`, `gAt`, `gImp`, `Clo`, `isPrime`),
`FRJ/Calculus.lean` + `CalculusV.lean` (the FRJ/FRJV families),
`FRJ/Sound.lean` + `SoundV.lean`, `FRJ/Search/Core.lean` (`Ops`, the
saturation loop, subsumption), `FRJ/Minimal.lean` (§6 for `◯`-free).

## Stage status

* **Stage 2 (transcription) — DONE.**  `wip/gbu.lean`: 16 constructors
  across `GbuR`/`GbuI`, each citing its source line; `#slime` reports 0
  of 16 slimed.
* **Stage 3 (the paper's results) — soundness and termination DONE.**
  Lemma 7 (`seqValid_of_GbuR`/`_GbuI`), Theorem 6
  (`pll_of_provableGbu`, `ipl_of_provableGbu`), Lemma 8 (`wg_step`),
  Theorem 7's usable content (`step_wf`).  Sorry-free; soundness pins
  `[propext]`, the weight and termination results `[propext,
  Quot.sound]`.
* **§4 and Lemma 9 — DONE** (`wip/gbu_db.lean`).  Subsumption `⊑`
  (source 2664), (DB1) and (DB2) (source 2827/2830), and the evaluation
  relation `▷` (source 3287) transcribed; all NINE clauses of Lemma 9
  proved (the earlier `pdftotext` extract truncated at six).  Sorry-free;
  the three pure-`Clo` clauses pin `[propext]`, the six that apply an
  `FRJ` rule `[propext, Quot.sound]`.
* **Lemmas 10–12, Theorems 8–10 — DONE** (2026-08-29).  `gbuInv10`,
  `gbuSuccAt`, `gbuSuccOr` in `wip/gbu_db.lean`; `search` (Theorem 8),
  `gbu_frj_duality` (Theorem 9), `provableV_of_not_pll` and
  `provableGbu_of_pll` (Theorem 10) in `wip/gbu_search.lean`.  All pin
  `[propext, Quot.sound]` — choice-free, the two `Decidable` arguments
  being the paper's own database queries.  **Stage 3 is therefore
  complete over IPC.**
* **Stage 4 (the runnable procedure) — OPEN.**  What is missing is the
  FINITE saturated database of §4 with a decidable `▷`.
  `saturated_fderivable` shows saturation is not the obstruction (the
  set of all derivable sequents is saturated); finiteness and
  decidability are.
* **Stage B (the `◯` extension) — SPECIFIED, not implemented.**  The
  three obligations, the rules they force, and the measure failure are
  in `docs/gbu-circ-seams.md`.  D8 below records how they are named in
  the Lean.

## Divergence log

| # | Divergence from the paper | Where | Why |
|---|---|---|---|
| D1 | `R∨ₖ` split into `rorR1`/`rorR2` (and the focused twins) | `wip/gbu.lean` | house style; `FRJ/CalculusV.lean` already splits `∧R` |
| D2 | the blanket `Lhs ⊆ Sf^L(G)`, `Rhs ∈ Sf^R(G)` is not a field on every constructor | `wip/gbu.lean` | a condition on the sequent LANGUAGE, not a rule side condition; soundness never uses it.  It IS load-bearing for Lemma 8, so it is carried explicitly on the two `R⊃ₙᵢ` steps |
| D3 | left zones are `List Form` with a `CtxEq` field on each conclusion naming a member | `wip/gbu.lean` | keeps the paper's set reading of `A,Ψ`; house style |
| D4 | soundness proved semantically against `Kripke`, not by the paper's translation into `GJ` | `wip/gbu.lean` | same statement, stronger conclusion: no infallibility needed, so `PLL`-validity, of which the paper's `IPL` reading is a corollary |
| D5 | Theorem 7's `O(|τ|²)` height bound replaced by well-foundedness of the step relation | `wip/gbu.lean` | well-foundedness is what backward search needs; the asymptotic constant is not used downstream |
| D7 | the well-formedness invariant `Ψ ⊆ Sf^L(G)`, `C ∈ Sf^R(G)` is carried as an explicit hypothesis of `SearchOk` | `wip/gbu_search.lean` | the paper leaves it inside "a `Gbu(G)`-sequent"; it is what makes `unclosed_lt` apply and what Lemmas 9–12's FRJ side conditions need |
| D8 | `◯`-freeness of `G` is a hypothesis (`hcircL`, `hcircR`) of Theorem 8 | `wip/gbu_search.lean` | our `Form` has a `◯` constructor because the same datatype carries the modal development; §5 is about IPC.  The hypotheses are consumed at exactly three points, which is the obligation list for `Gbu◯` (`docs/gbu-circ-seams.md`) |
| D6 | derivability taken in the REPAIRED family `FRJVr`/`FRJVi`, tag existentially quantified | `wip/gbu_db.lean` | the paper's `FRJ(G)` is the IPC calculus and carries no tag; `FRJV` is what this campaign is about, and Lemma 9's proofs use only rules the two families share |

## Open questions for review

1. The blocker is cleared, so Stage 2 (transcription of Fig. `fig:GBU`,
   14 rules across two judgments) can start on Matthew's word.
2. Does the harness still earn its place now that the IPC rules are in
   hand?  My reading: yes, but its role moves.  For IPC it is no longer
   needed — transcribe the rules and prove the results.  For **Gbu◯** it
   is exactly right, because the `◯`-rules genuinely do not exist, and
   the shape of the obligation is now predictable: the `◯` clause of the
   EVALUATION RELATION `▷`, since that is where FRJV's rows carry their
   tags.  So: transcribe IPC, prove §5, and run the harness only at the
   `◯` step.
3. Order check: the skill forbids starting an extension's Stage 5 before
   the base's Stage 3.  So Gbu◯ waits until Gbu(G)'s §5 results are
   proved for IPC.
