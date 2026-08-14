# The DISPROOF investigation — dedicated handover

*Created 2026-08-13.  This file is the standing handover for ONE
thread: building a calculus in which non-provability is established by
a POSITIVE derivation.  It is deliberately separate from `HANDOFF.md`
(repo-wide), `docs/next-session.md` (whatever is live), and the UI
handovers.  Append dated sections; do not rewrite.*

**Scope rule.** If a question is about uniform interpolation, it does
not belong here.  The UI campaign is PARKED by Matthew's decision
(2026-08-13): no UI work until the disproof side has more machinery
and results.

---

## 1. The goal, stated so it can fail

A refutation should be a **finite syntactic object, built forwards by
rules, checkable by a decidable rule-application predicate** — not a
countermodel found by search and not a failed proof search re-read.
Then "REFUTED" is as cheap as "PROVED" under the machine-checked
mandate, and the 109 open flags of the closed-fragment catalogue
become attackable.

Success criterion, concrete: **derive a sample of the catalogue's 57
pinned crank-7 separations as `Reject` derivations** (calibration),
then settle flags the battery could not (discovery).

## 2. Where the thread stands (2026-08-13)

### Live: `Reject/` — the forward, model-generating calculus

Template: Fiorentini–Ferrari, FRJ(G) (TABLEAUX 2017 appendix read at
source; TOCL 2020) and their JLC 31(3) 2021 S4 model-generation
calculus (**paywalled — abstract only; obtaining it is a task**).  The
principle: *rules ARE model constructors; each rule's soundness is a
forcing lemma about the construction*.

PROVED, and **all four core lemmas are AXIOM-FREE**:

| name | role |
|---|---|
| `addRoot` | the constructor: a new root BELOW a model |
| `addRoot_force_some` | forcing unchanged above the new root — why this is the safe direction |
| `boxRefuteHere` (◯∈) | refute `◯A` at the root: root and its `Rm`-cone refute `A` |
| `boxRefuteAbove` (◯∉) | refute `◯A` via a world above with no `Rm`-successor forcing `A` |
| `boxHolds` | the ◯-POSITIVE rule (carry `◯A` in the root's context) |
| `solo`, `solo_force_somehow` | base case; `◯` is the identity at a single world |
| `not_laxND_of_root` | read the conclusion off the root → certified PLL underivability |

`Reject/Demo.lean`: `⊬ ¬◯⊥` and `⊬ ◯p` as CONSTRUCTION TERMS.

### The two screens that licensed this (both green, both re-runnable)

* **arity** (`lean_exe frjprobe`): the ◯-rule's arity = number of
  `Rm`-MAXIMAL successors.  **reduced + confluent ⟹ 100% unary**
  (52,800 worlds at n=3).  Reducedness is the load-bearing condition;
  confluence alone does nothing.  Full PLL's arity grows with frame
  size (Goranko's `Alt_n`), so **PCLL is the easier target** — a
  genuine inversion.
* **`Cl` transfer** (`lean_exe clscreen`): FRJ absorbs left rules into
  a closure `Cl`, valid because a world is `Cl` of its determining
  part.  The literal IPC choice (atoms + implications) **FAILS for
  PLL**, 32 certificates, witness `◯(p ∧ ◯q)` at `deep5` w=2,3.
  Adding ◯-formulas closes it: **0 failures in 156 cells**.  So the
  modal zone in the sequent is FORCED, not a design flourish.

### Retained but NOT active: `BiLax/`

* `not_laxND_iff_coimp_sat` — **`φ ⊬ ψ ⟺ (emb φ ⤙ emb ψ) satisfiable`**,
  machine-checked both directions.  Its role: the SPECIFICATION a
  `Reject` derivation meets (the model a derivation builds witnesses
  exactly that ∃, by reflexivity of `Ri`).  Nothing in the FRJ route
  consumes it.
* `⤙` needs NO new frame conditions (persistence uses only
  `Ri`-transitivity).  All of `Rc`/`square_c`/`counit_c`/`serial_c`
  exists for `◯∃` alone.
* **`◯∃` is currently UNUSED machinery.**  It collapses to the
  identity over the natural class (`colax_collapse_of_rm`, proved),
  needed a whole extra relation to be non-trivial, and appears in
  neither certified refutation.  Not refuted as a concept; not needed
  for disproof.
* Rounds 1–2's Hintikka/checker machinery is a COUNTERMODEL
  CONSTRUCTOR.  Both round reports carry corrections saying so.

### Killed, with certificates

* Skura-style rejection systems: **wrong template** (non-analytic;
  `r_mp` hides an IPC proof and `r_sb` a substitution guess — model
  search inside a side condition).
* Candidate ◯-rejection rules R3 (`⊣φ / ⊣(◯φ⊃φ)`) and R4
  (`⊣φ / ⊣¬¬◯φ`): certified Ł-soundness violations (`lean_exe
  rejscreen`).  R1, R2, R5 survive but show no PCLL-discrimination
  witness — the Kreisel–Putnam danger sign, still open.
* `addTop` (adjoining a fallible top to satisfy `serial_c`):
  **UNSOUND** — makes `◯φ` true everywhere.  Corpse kept in
  `BiLax/Internal.lean`.

## 2b. The adversarial pass — DONE (2026-08-13), and it changed T1

`Reject/Audit.lean`, all pinned, three of five answers good and two
that constrain the join rule.

| question | verdict |
|---|---|
| Are `boxRefuteHere`'s premises vacuous or over-strong? | **Neither** — `boxRefuteHere_exact` proves they are EXACTLY "no `Rm`-successor of the root forces `A`" |
| Is `S = ∅` legal, and does it break anything? | Legal (`emptyS`); the rule stays sound, as an instance of the above.  Documented, not a defect |
| Does `addRoot` preserve REDUCEDNESS? | **YES** (`addRoot_reduced`) |
| Does `addRoot` preserve CONFLUENCE? | **NO** — `addRoot_not_confluent`, machine-checked counterexample |
| Do the rules COMPOSE to a real result? | **YES** — `boxp_not_p`: the repo landmark `◯p ⊬ p` by construction |

**The finding that constrains T1.**  The counterexample is two
incomparable worlds with identity relations (confluent and reduced);
adding a root whose modal cone is one of them destroys confluence —
`Rm root (some true)` and `Ri root (some false)` have no common
completion.  This matters because the **unary-arity licence for the
◯-rule holds on reduced AND confluent frames** (docs/frj-lifting.md
§3).  A calculus whose constructor leaves the confluent class loses
that licence.  So T1 must choose, EXPLICITLY:

* **(a)** carry a confluence side condition on the join (stay in the
  class where the ◯-rule is unary — the PCLL-first route); or
* **(b)** accept non-confluent constructions and give the ◯-rule its
  general list-of-premises form (Goranko's `Alt_n` shape, heavier to
  mechanise).

Recommendation: **(a)**, consistent with "PCLL is the easier target".
Either way the choice must be made and recorded, not drifted into.

**Also fixed**: `boxHolds` was INCOMPLETE — it could witness `◯A` at
the root only through a PROPER `Rm`-successor, missing the reflexive
case where the root itself forces `A`.  `boxHoldsRoot` supplies it.
Lesson for T1: check the reflexive/degenerate case of every new rule.

## 3. The task queue, in Matthew's agreed order

### T1 — the JOIN rule  ⟵ START HERE
Generalise `addRoot` to several premise models: disjoint union + fresh
root, with the join declaring which components are `Rm`-successors
(subject to `Rm ⊆ Ri`, reflexivity, transitivity, and the
◯-positive obligation as a side condition).  Without it the calculus
builds only linear models, which is why the demos are the corpus's two
smallest facts.  **Model: Opus 5. Effort: high.**  Reason: design plus
fiddly dependent-type plumbing (a `Sigma`/sum world type), and the
soundness lemmas must be got right first time or the whole tower
leans.

### T2 — COMPLETENESS
The FRJ Lemma 4 analogue: from any countermodel, extract a derivation,
by induction on world HEIGHT (then sequent type, then `|C|`).  Needs
reducedness for the measure to decrease — the second place
reducedness is load-bearing.  **Model: Opus 5. Effort: max.**  Reason:
this is the hardest mathematics in the thread and the point where it
either becomes a calculus or stays a certificate format.  Do not
delegate; do not interleave.

### T3 — the SEARCHER
Forward saturation over the finite sequent set (goal-parametrised, so
termination is structural — this is exactly what the labelled route
lacked).  Compiled `lean_exe`, streaming one line per cell, per repo
doctrine.  **Model: Sonnet 5 for the engine after Opus 5 fixes the
saturation strategy. Effort: medium–high.**  Reason: once the rules
are frozen this is engineering, and Sonnet is the better
cost/throughput point for grind.

### T4 — the 109 FLAGS
Calibrate on the 57 pinned separations, then attack the flags.
**Model: Sonnet 5 (runs, triage), Opus 5 for interpreting residue.
Effort: medium.**  Mechanical once T3 lands.

### T0 (parallel, cheap, do anytime)
Obtain the JLC 2021 S4 paper — institutional access, interlibrary, or
email the authors.  It will very likely have solved T1's side
conditions and T2's induction for `□`.  **Model: Haiku 4.5 or a
research subagent. Effort: low.**

### Standing before every proof is scoped
Adversarial pass on `Reject`'s current rules — in particular whether
`boxRefuteHere`'s side condition is doing real work or is vacuously
satisfiable on the constructions we can build.  **Model: Opus 5.
Effort: high.**  Four hours old, no adversarial pass yet.

## 4. The systematic method Matthew asked for

Not ad-hoc screens per question, but a standing pipeline.  Four
stages, each with the repo's existing tooling named:

1. **CANDIDATE GENERATION — `tools/FrontierSampler`.**  Stop
   hand-picking rule shapes and corpus cells.  Generate candidates
   stratified by the residue shape of the previous round (repo
   CLAUDE.md's standing rule).  Applies to: candidate ◯-rules, join
   side conditions, and the formulas a searcher is calibrated on.
   The `rejscreen` corpus was hand-built and was UNDER-POWERED because
   of it (the instantiation defect, §"corrections" below) — exactly
   what the sampler exists to prevent.
2. **EXTENSIONAL ATTACK — the four directions of repo CLAUDE.md.**
   Corpus replay first (the G4iLL blocker, the catalogue's merge
   sites, the φ★/φ♦ ladder), then boundary cells, then frontier
   extension, then branch coverage.  Three-valued verdicts; `fail`
   only on a certificate; `flag` never dropped.
3. **EFFICIENT COMPUTATION — compiled harnesses, never `#eval`.**
   `lean_exe`, one appended line per cell, gated by CONSTRUCTED value
   size, every skip reported.  The four harnesses this thread already
   has (`frjprobe`, `clscreen`, `rejscreen`, `s0screens`) are the
   pattern; a fifth for join side conditions is T1's companion.
4. **VERIFICATION — discover-then-pin.**  Search untrusted, certify by
   kernel.  `BiLax/Check.lean`'s `FinBranch → by decide → Hintikka`
   is the worked example; `Reject` needs its analogue so searcher
   output becomes a construction term automatically.

**The route from proof theory to computation and back**, stated as the
standing shape: a rule is DESIGNED from the semantics (a forcing
lemma), SCREENED by a compiled harness before any proof is scoped,
IMPLEMENTED with its soundness lemma, and CONSUMED by a searcher whose
output is re-certified by the kernel.  Every arrow in that cycle
exists in the tree already; T1–T4 walk it once more.

## 5. Corrections made in this investigation (keep, do not repeat)

* Rounds 1–2 were presented as a disproof engine; they are a
  countermodel constructor.  Corrected at the head of both reports.
* "The ∀∃ clause forces a hybrid deduction–refutation rule" — TRUE for
  a backward calculus, FALSE for a forward one.  The model is the
  derivation's own product, so "all `Rm`-successors" is a
  construction-time side condition.
* "On the closed fragment PCLL ≈ PLL" — FALSE; this repo's own
  kernel-pinned merges witness `PLL ⊊ PCLL` there.  The merges are
  SPARSE (4 of 680 cells).  The screen's empty discrimination column
  was an INSTANTIATION defect.
* The Brunner–Carnielli reference is REAL (*J. Applied Logic* 3
  (2005) 161–184) but the duality is **provability ⟷ refutability**,
  so non-provability stays existential on both sides — the wrong
  category by Matthew's own ∀∃/∃∀ criterion.

## 6. Replay

    lake build Reject          # the calculus + demos
    lake build BiLax           # internalisation, retained machinery
    lake exe frjprobe          # ◯-rule arity by frame class
    lake exe clscreen          # the Cl transfer screen
    lake exe rejscreen         # Kreisel-Putnam screen for ◯-rules

Docs: `docs/frj-lifting.md` (the design + both screens),
`docs/bilax-b-report.md` (literature + corrections),
`docs/bilax-plan.md`, `docs/bilax-round{1,2}-report.md` (corrected),
`docs/pcll-closed-fragment-catalogue.md` (the acceptance corpus).

---

## 2026-08-14 (late) — the normalisation pipeline repaired; the RN dictionary's true status

Standing item adopted at Matthew's direction: **whenever equations are
banked, re-run the loop** (`rwscreen`, then `rnextend`, then promote
anything that closes, then re-pin the axioms). Full record:
`docs/rn-dictionary-status.md`. Summary for whoever takes T1:

**Two defects found and fixed.**

1. `Rewrite/Catalogue.lean` had harvested all 323 cell theorems of
   `wip/rnDict.lean` by name, but that file proves only 236 — 87 are
   `sorry`, and **four are REFUTED** (`cAnd_8_10`, `cImp_9_4`,
   `cImp_12_4`, `cImp_14_4`: the stated collapse to `q0` is FALSE).
   So `rndSet` and `fullSet` carried `sorryAx`, and four rules
   rewrote a formula to one *not* interderivable with it. `RwRule.ok`
   is exactly what makes `norm_interd` unconditional, so a `sorry`ed
   `ok` voids that guarantee silently. Fixed: 236 proved cells only,
   with `#print axioms rndSet`/`fullSet` now `#guard_msgs`-pinned as a
   standing guard against a repeat.
2. The canonicaliser was fighting its own rules: `canon` sorts ∧/∨
   arguments, the harvested rules were stated in the dictionary's
   argument order, so canonicalising a goal moved it out of reach.
   A control against the cells the table *provably* closes read
   **47/237**. Fixed with `canonRule`/`canonSet` (rules through the
   same canonicaliser — sound for free) and `simpIter` (alternate
   `norm` and `canon` to a fixpoint). Control now **237/237**.

**Use `Rewrite.simplifyWith Rewrite.fullSetC fuel φ`** — not
`simplify`, not `fullSet`, not `norm`. Measured gain over the previous
figures: flat cells rewritten 68% → **89%**, crank cut 21% → **34%**,
distinct forms 96 → **28**; nested corpus 167 → **25** distinct forms
(floor 15) with crank down 40%.

**Can the method extend the RN(◯,{}) analysis? No, and the negative is
informative.** `lean_exe rnextend` tests whether the simpset closes any
of the 87 unproved dictionary cells — a syntactic match of normal
forms would be a certificate, needing no search. **0 of 87**, with the
control at 237/237 in the same run, the fifteen representatives still
pairwise distinct (15/15), and the four refuted cells correctly *not*
matched. Rewriting is congruence closure over banked equations, and
the open cells are by construction outside it: recombination cannot
settle them. Only a new proof search or a ≥5-world confluent
countermodel can.

**What this hands T1.** The 83 open cells are a concrete target list
(⊃ 43, ∨ 28, ∧ 14, ◯ 2 — the implication table is where the dictionary
is weakest, which is exactly where a refutation calculus should bite),
machine-readable as `RnExtend.openCells` in `wip/rn_extend.lean`. If
the join rule makes branching countermodels constructible, these are
the first cells to aim it at. Also inherited: the *pattern* for a
trustworthy null result — control plus adversarial check in the same
run — which T1's screens should follow.

---

## 2026-08-14 (night) — WHAT `Reject/` ACTUALLY IS: a correction to this document's own framing

*Written by the `ljf-pll` session at Matthew's request, after he
observed that he had understood the rejection calculus to be built via
LJF◯ and that `Reject/` appears not to be that. He is right. The
framing corrected here is MINE — it entered in `docs/frj-lifting.md`
and was passed to the T1 agent in `docs/t1-join-rule-prompt.md`, which
built faithfully on it.*

*Read from the code on `claude/t1-lax-logic-refutation-37c0bf`
(`Reject/{Build,Join,Complete,Height,Bisim,Audit,Demo}.lean`, 2,022
lines, all sorry-free), not from the reports.*

### What `Reject/` is

Three functions on Kripke models, and theorems about them.

* `solo V₀ fal hfull : ConstraintModel` — a one-world model.
* `addRoot (M : ConstraintModel) (D : RootData M) : ConstraintModel` —
  a new world strictly below `M`, choosing which worlds become the
  root's proper `Rₘ`-successors (`D.S`) and which atoms hold there
  (`D.At`).
* `join Mods D = addRoot (union Mods) D` — the same below a disjoint
  union. That is T1 in full: `union`, and `join` defined from it.

The three things this document has been calling "the ◯ rules" —
`boxRefuteHere`, `boxRefuteAbove`, `boxHolds` — are **theorems about
forcing at the new root**, not rules of inference. And the step that
reaches PLL is

    theorem not_laxND_of_root (hΓ : ∀ χ ∈ Γ, N.force w χ) (hψ : ¬ N.force w ψ) :
        ¬ Nonempty (LaxND Γ ψ) := by
      rintro ⟨p⟩; exact hψ (soundness p N w hΓ)

— PLL's own Kripke soundness, applied. So the certificate `Reject/`
produces is a **countermodel**, the same kind of object the battery
produces. What is new is that it arrives with a construction history.

### What `Reject/` is not

* **Not LJF◯-based.** Import closure: `PLLKripke`, `PLLFrames`,
  `PLLConfluentComplete`, `PLLCountermodelEmit`, `PLLSemUI`,
  `Mathlib.Data.Set.Card`. `grep "LJF" Reject/*.lean` is empty.
* **No sequents.** The string "sequent" occurs 0 times in the code
  (twice in a doc comment). There is no `Γ ⇒ C` and no irregular
  `Σ ; Θ → C`.
* **No derivations.** The only inductives in the directory are `Built`
  — a PREDICATE ON MODELS — and `Lift`, a relation used to build the
  disjoint union. There is no type of refutations, no judgment, no
  rule per connective, and nothing indexed by a sequent. No object in
  `Reject/` is *about* a particular entailment until
  `not_laxND_of_root` is applied at the very end.
* **Nothing to search — SUPERSEDED WITHIN THE HOUR, see the amendment
  below.** In `Build.lean`/`Join.lean`/`Complete.lean` the abstract
  constructions are not searchable data: `RootData` carries

      S  : M.W → Prop
      At : String → Prop

  and `Built.join` quantifies over `{ι : Type}` with no finiteness, so
  a `Built` model is not a finite syntactic object and constructions
  cannot be enumerated. `Reject/Cert.lean` (commit `c70ac4e`, landed
  while this section was being written) supplies the effective layer
  separately, over `FinCM`.

### What IS proved, read as mathematics rather than as a calculus

**`gen_of_reduced`** — every world of a finite reduced constraint
model is bisimilar to the root of a `Built` model; hence
**`built_countermodel_of_reduced`**, and with `not_laxND_of_built`
(pin `[propext]`) a two-way statement on that class.

So T2 is a **normal-form theorem for countermodels**: every finite
reduced countermodel is bisimilar to a well-founded tree with fallible
worlds only at the leaves. The height induction (`Reject/Height.lean`)
and the bisimulation transfer lemma (`Reject/Bisim.lean`) are the real
content, both sorry-free and pinned. This is worth keeping and is not
affected by anything above.

### Two checkable inaccuracies in the T2 documentation

1. `Reject/Complete.lean`'s header says `Built` "unfolded, that is the
   finite `Rᵢ`-TREES". `Built.join` takes `{ι : Type}` with no
   finiteness constraint, so branching may be infinite; the inductive
   gives well-founded DEPTH only. The theorems are unaffected —
   `gen_of_reduced` assumes `Finite N.W` separately — but the
   characterisation as written is wrong.
2. "calculus" throughout, and "the class the calculus generates".
   There is no calculus in the proof-theoretic sense. **This wording
   is mine, inherited by the T1 agent from the handoff prompt**, and
   should be corrected at its source rather than charged to that
   session.

### How the framing went wrong

After BiLax was refuted, Matthew asked for FRJ(G) to be read and its
◯ rules implemented on the model of the Fiorentini–Ferrari JLC 2021
S4 paper. `docs/frj-lifting.md` argued that a FORWARD architecture
dissolves the ∀∃ obstacle, because "all `Rₘ`-successors" becomes a
construction-time side condition when the model is the derivation's
own product. That argument is sound as far as it goes.

What was then built was the model-construction layer and its forcing
lemmas — and called a calculus. The layer that makes FRJ(G) a calculus
was skipped: FRJ(G) saturates a finite set of SEQUENTS, regular
`Γ ⇒ C` and irregular `Σ ; Θ → C`, and EXTRACTS the model from the
saturated set. `Reject/` has the extraction and no sequents.

### What would close the gap

1. A sequent syntax — FRJ's regular/irregular pair, or LJF◯ sequents
   if the calculus↔PLL bridge ever lands (it does not exist today; see
   the status table in `docs/rho-order.md`).
2. Derivations as an inductive type over that syntax, one rule per
   connective, so a derivation is a finite object about a named
   sequent.
3. ~~`RootData` made effective~~ — **DONE by T3**, by a different and
   better route than the one proposed here: rather than making the
   abstract `RootData` finite, `Reject/Cert.lean` works over the
   repo's concrete finite model type `FinCM` and decides class
   membership structurally (`BuiltB` = rooted ∧ reduced ∧ tree ∧
   fallible-leaves), with `certifies M w Γ C : Bool` and
   `not_laxND_of_certifies` pinned `[propext, Quot.sound]`.
4. An extraction map from saturated derivations to `Built` models.

Step 4 is where the present work is retained rather than discarded:
T1 and T2 become the ADEQUACY proof for the calculus once a calculus
exists — soundness of extraction, and completeness of the model class
it targets. The semantic half is done; the syntactic half has not been
started.

### Standing correction for anyone writing here next

Do not describe `Reject/` as a calculus, as a rejection calculus, or
as LJF◯-based. Describe it as what it is: **constructors for
countermodels, with a normal-form theorem (T2) saying the constructed
class is expressively complete for finite reduced countermodels.** The
open obligation (R) — every underivable sequent HAS a finite reduced
countermodel — sits underneath T2 and is separate from everything
above.

### AMENDMENT, same night — T3 closes the effectivity point

The section above was read off `Reject/{Build,Join,Complete}.lean` at
commit `a57bfc5`. Commit `c70ac4e` (`Reject/Cert.lean`, 107 lines,
sorry-free) landed immediately afterwards and changes one of the four
items. Corrected status:

* **Certificates ARE now finite decidable data.** `BuiltB : FinCM →
  Bool` and `certifies : FinCM → Nat → List PLLFormula → PLLFormula →
  Bool`, with `not_laxND_of_certifies` and `not_laxND_of_check_any`
  pinned `[propext, Quot.sound]`. So "nothing to search" is no longer
  true of the thread as a whole; it remains true of the abstract
  `Built`/`RootData` layer, which is not what the searcher ranges
  over.
* **A forward saturating search exists and produces results.**
  `lake exe t3search`, sharing premises by the 4-tuple
  (`root`, `univ`, `some`, `box`) read off `join_force_box_iff`: 140
  separations from two saturations with 88 stored states, including
  `◯(p∨q) ⊃ (◯p∨◯q)` correctly refuted in PLL. That is a genuine
  forward method, and it is closer to FRJ(G) than the earlier layer
  was.

**What does NOT change.** There are still no sequents, no derivation
type, and no rule per connective. `BuiltB` is a structural predicate
on a finite model — rooted, antisymmetric, chain predecessors,
fallible leaves — so what it certifies is that a model lies in a
canonical class, not that it was derived. The T3 note says "`BuiltB`
is what makes a certificate a DERIVATION rather than a found
countermodel"; that is the one claim in it worth contesting. A
derivation records WHICH rule applied at WHICH sequent, and that is
what supports the proof-theoretic payoffs — subformula property, cut,
interpolation. A model plus a decidable class check carries none of
it. The right description is **canonical-form countermodels found by
forward saturation**, which is a real and useful thing, and is what
the searcher's 140 separations demonstrate.

So of the four gap items: 3 is done, 1 and 2 are open, 4 is
conditional on 1 and 2.

*Note on merging: this section was appended on `ljf-pll` while
`claude/t1-lax-logic-refutation-37c0bf` was appending its own dated
sections to the same file. Expect a conflict here and interleave by
date rather than taking one side.*
