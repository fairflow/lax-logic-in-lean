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

---

*The sections below were written concurrently on `claude/t1-lax-logic-refutation-37c0bf` (T1/T2/T3, the (R) proof and the LJF◯ bridge) and merged here 2026-08-14 night; the sections above are the `ljf-pll` line. Same night, two hands.*

## 2026-08-14 — T1 DONE: the JOIN rule, and the confluence decision

`Reject/Join.lean` (build: `lake build Reject`; screen: `lake exe
joinscreen`, source `wip/join_screen.lean`, output
`wip/join_screen_out.txt`).  The calculus is no longer restricted to
chains.

### The construction, and why it factors

    join Mods D  =  addRoot (union Mods) D

`union` (the disjoint union of the premise models, world type
`Σ i, (Mods i).W`) is the only new constructor; the fresh root is the
existing `addRoot`.  That factorisation is the design decision that
made T1 cheap: every lemma of `Reject/Build.lean` —
`addRoot_force_some`, both ◯-refutation rules, `boxHolds`/
`boxHoldsRoot`, `addRoot_reduced`, `not_laxND_of_root` — applies to a
join unchanged, and the dependent-type plumbing is confined to one
inductive family (`Lift`) whose single constructor says the union
relates only worlds of the same component.  `rcases` on it recovers
the component with no transport, which is why every core lemma below
is axiom-free.

### PROVED, with pins (all transcribed verbatim, `#guard_msgs`-pinned in the file)

| result | statement | pin |
|---|---|---|
| `union_force` | forcing inside a component is unchanged by the other components | *no axioms* |
| `join_force_comp` | the preservation lemma for the join (the analogue of `addRoot_force_some`) | *no axioms* |
| `join_force_box_iff` | **the ◯ rule at a join, exactly**: root ⊩ ◯A ⟺ (root ⊩ A ∨ some cone world forces A) ∧ every component world has an `Rm`-successor forcing A | *no axioms* |
| `joinBoxRefuteHere` / `joinBoxRefuteAbove` / `joinBoxHolds` | ◯∈, ◯∉, ◯-positive, componentwise | *no axioms* |
| `join_refute_box_iff` | **the two refutation rules are jointly EXACT** — the root refutes ◯A iff ◯∈'s premises hold or ◯∉'s do | `[propext, Classical.choice, Quot.sound]` |
| `addRoot_confluent_iff` | confluence of `addRoot`, exactly: `MutuallyConfluent M ∧ ∀ s t, S s → ∃u. s Rᵢ u ∧ t Rₘ u` | *no axioms* |
| `union_confluent_iff` | the union is confluent iff every premise is | *no axioms* |
| `join_confluent_iff` | the side condition, exactly | `[propext]` |
| `join_confluent_of_cone_empty` | confluent premises + empty cone ⟹ confluent join | `[propext]` |
| `join_cone_empty_of_confluent_branching` | a confluent BRANCHING join has an empty modal cone | `[propext]` |
| `join_empty_box_iff` | 0 premises: `◯` is the identity at the root | `[propext]` |
| `join_unit_box_iff` | 1 premise: the modal rule degenerates to `addRoot`'s | `[propext]` |
| `Iso.force` | **forcing transfer**: isomorphic constraint models force the same formulas at corresponding worlds | *no axioms* |
| `join_unit_force` | 1 premise: the join agrees with `addRoot` **POINTWISE** — every world, every formula | *no axioms* |
| `not_derivU_of_root` | a confluent root certifies **PCLL** underivability | `[propext]` |
| `rho6_needs_branching` | every world refuting `¬¬◯⊥ ∨ ¬◯⊥` has two `Ri`-INCOMPARABLE successors | `[propext, Classical.choice, Quot.sound]` |
| `not_derivable_rho6` | **`⊬ ¬¬◯⊥ ∨ ¬◯⊥`** (catalogue class ρ6 = t 5 = q7, crank 4) | `[propext, Quot.sound]` |
| `not_derivU_rho6` | **`⊬_PCLL ¬¬◯⊥ ∨ ¬◯⊥`** — same derivation, read in PCLL | `[propext, Quot.sound]` |

`MJ_confluent` `[propext]` and `MJ_root_branches`
`[propext, Classical.choice, Quot.sound]` are pinned too.  22 pins in
all; the build fails if any drifts.

### THE CONFLUENCE DECISION: **(a)**, and why

**Taken: (a) — the join carries a confluence side condition.**  Not
drifted into; the alternative was screened and priced.

The condition is exact, not a sufficient guess:

    MutuallyConfluent (join Mods D)
      ⟺ (∀ i, MutuallyConfluent (Mods i)) ∧ ConeDominates Mods D

where `ConeDominates` is `∀ s t, D.S s → ∃u. s Rᵢ u ∧ t Rₘ u`.  The
audit's `addRoot_not_confluent` is exactly the instance where the
second conjunct fails, so the counterexample is now explained rather
than merely recorded.

**What it costs, stated as a theorem, not a hope.**
`join_cone_empty_of_confluent_branching`: when the join genuinely
branches — two distinct components, one carrying a cone world, the
other inhabited — confluence forces the root's modal cone to be
EMPTY.  In the union, `s Rᵢ u` keeps `u` in `s`'s component and
`t Rₘ u` keeps it in `t`'s, so no common completion exists across
components.

**Why that is a design and not a restriction.**  On a confluent frame
`w ⊩ ◯A ⟺ ∃u. w Rₘ u ∧ u ⊩ A` (`force_somehow_iff_of_confluent`,
already in the tree).  A branching root's only `Rm`-successor is
itself, so it witnesses `◯A` through itself: **the ◯-rule at a
branching root is unary, with the root as its own witness** — which is
precisely the arity licence docs/frj-lifting.md §3 measured (reduced +
confluent ⟹ 100% unary, 52,800 worlds at n=3) and which option (b)
would have thrown away.

**And it pays.**  Because the constructions stay confluent, a
refutation certifies underivability in **PCLL** as well as PLL
(`not_derivU_of_root`, on the tree's `ConfluentU.derivU_sound`).  PCLL
is the logic the acceptance corpus is stated in
(docs/pcll-closed-fragment-catalogue.md), so option (a) makes the
calculus speak the corpus's own language.  Option (b) would have
bought unrestricted cones at the price of a list-arity ◯-rule
(Goranko's `Alt_n` shape) and PLL-only conclusions.  The general rules
are nonetheless proved here unconditionally — `join_force_box_iff` and
the three rules carry no confluence hypothesis — so (b) remains
available without redoing any of this work; only the side condition
would be dropped.

### What the screens found

`lean_exe joinscreen`: 16 cells × 24 formulas, seven sections, each
with a control that must fail in the same run.  **All seven green**
(`VERDICT A=true B=true C=true D=true E=true F=true G=true`).

* **A** constructor laws: 16/16 well-formed.  Control A′: an
  `Rm`-cone that is not `Rm`-upward closed, and a root atom absent
  from a component, are both REJECTED — the two `RootData` laws do
  real work.
* **B** preservation: 984 (component-world × formula) cells, 0
  mismatches.  Control B′: of 2 well-formed cross-linked joins (an
  `Ri` link between two components) 1 BREAKS preservation, certificate
  `comp 0 world 0 formula ¬◯⊥` — the check has teeth.
* **C** the exact ◯ rule: 360 cells, 0 mismatches.  Control C′: the
  INCOMPLETE rule (the `boxHolds` defect the audit found — no
  reflexive disjunct) is exposed on 8/15 cells, witness `◯⊤`.  The
  degenerate case is therefore covered by test as well as by proof.
* **D** confluence: the characterisation agrees with `confl` on 16/16
  cells; the branching corollary holds on 4/4 branching cells with a
  non-empty cone.  Both are now theorems.
* **E** degeneracy: 5/5 single-component cells agree POINTWISE with an
  independently-written `addRoot`.  Now also PROVED — see the
  addendum below.
* **F** soundness, adversarially: 7 sequents certified derivable by
  the searcher IN THE SAME RUN — including the G4iLL blocker
  `◯((◯p⊃r)⊃◯p), ◯p⊃r ⇒ r` — and no cell's root witnesses any of them
  as refuted.  Control F′: 7/16 cells refute `¬◯⊥∨◯⊥`, 3/16 refute
  `(p⊃q)∨(q⊃p)`, so the pipeline fires.
* **G** which targets NEED branching (added after the screen corrected
  the first choice of target — see below).  Exhaustive chain battery:
  2,378 closed chains ≤ 5 worlds, 5,510 p,q-chains ≤ 4 worlds.
  Needs-branching in the corpus: `¬¬◯⊥∨¬◯⊥` (ρ6), `¬¬◯⊥∨◯¬◯⊥` (ρ9),
  `g1` (ρ11), `r1` (ρ12), and the control `(p⊃q)∨(q⊃p)`.  Positive
  control (Gödel–Dummett must need branching) and negative control
  (`◯p`, `¬◯⊥∨◯⊥` must be chain-refutable) both pass.

**A correction the screen forced.**  The first choice of worked
target, `¬◯⊥ ∨ ◯⊥` (ρ4), does NOT need branching: a single
`addRoot` over the two-world chain refutes it at the root (the root
refutes `◯⊥` through its own trivial modal cone, while a world above
forces it — heredity runs upward only).  Section G was written to
choose the target on evidence instead, and `rho6_needs_branching` then
upgrades that evidence to a theorem: any world refuting ρ6, in any
constraint model, has two `Ri`-incomparable successors.  So the worked
composition provably cannot be built by `addRoot` alone.

### Normalisation (§H), reported as measured

On this corpus the certified pipeline
`Rewrite.simplifyWith Rewrite.fullSetC 12` rewrites **1/24 cells (4%)**,
24 → 23 distinct forms, crank 72 → 70 (**2%**) — far below the 89% /
34% of `rwscreen`'s flat corpus.  The reason is the corpus, not the
normaliser: these are the catalogue's own canonical representatives,
which are already in normal form.  The CONTROL in the same run
confirms it — on a scrambled corpus (`⊤∧(φ∨φ)`, `◯◯φ`) the pipeline
rewrites **48/48 (100%)**, 48 → 32 distinct forms, crank 243 → 169
(**30%**).  Per `docs/rn-dictionary-status.md`, a low rate reported
without that control would not have been trustworthy.

### The banking loop

**No new certified `Interd` was established by T1** — the results are
forcing lemmas and underivabilities, not interderivabilities — so
there is nothing to bank and `rwscreen`/`rnextend` were not re-run.
Recording the negative explicitly so the standing item is not silently
skipped.

### What T2 (completeness) inherits

* The constructor is now **complete for branching**: any finite family
  of premise models can be joined, and `join_force_comp` says the
  premise refutations survive the join verbatim.  The Lemma 4 analogue
  can therefore decompose a countermodel into components without
  re-proving anything about forcing.
* **The rules are EXACT, not merely sound.**  `join_force_box_iff` and
  `join_refute_box_iff` are iffs, so the completeness direction does
  not need new modal lemmas — it needs only to produce the premises,
  which are stated entirely inside the components.
* **The class is fixed**: reduced (`addRoot_reduced`) and, under the
  side condition, confluent (`join_confluent_iff`).  Both of the
  places docs/frj-lifting.md §5 says reducedness is load-bearing — the
  unary arity and the height induction — are therefore available.
* **The height measure is safe under the join**: the root is strictly
  below every component world and components are mutually
  `Ri`-incomparable (`Lift.fst_eq`), so `h(root) = 1 + max h(premise)`.
  This is the measure T2's induction needs; it has not been mechanised
  yet and is the first thing T2 should write.
* **A calibration target exists**: `not_derivU_rho6` is the first
  catalogue class settled by construction rather than by search.  The
  57 pinned crank-7 separations are the rest of the calibration set,
  and §G's list (ρ6, ρ9, ρ11, ρ12) says which of them need the join.
* **A forcing-transfer lemma is available** (`Iso.force`, added the
  same day — see the addendum): isomorphic constraint models force the
  same formulas at corresponding worlds, axiom-free and stated with an
  explicit two-sided inverse, so nothing classical enters.  T2 will
  want it as soon as it renames or quotients models.

### Addendum (same day) — the unary degeneracy is PROVED, not screened

The one item left open above is closed.  Three new results, all
`#guard_msgs`-pinned and all **axiom-free**:

* **`Iso.force`** — the general forcing-transfer lemma.  `Iso C D` is a
  bijection of worlds that reflects and preserves both relations,
  fallibility and the valuation; stated with an explicit two-sided
  inverse rather than a surjectivity hypothesis, so no choice is
  needed.  The two quantifier clauses (`⊃`, `◯`) are where the
  inverse does the work: a successor on the target side is pulled back
  before the induction hypothesis applies.
* **`unitIso`** — a unary join IS an `addRoot`, via the map that
  forgets the (unique) component index (`Option.map Sigma.snd`).  Every
  field is `Iff.rfl` except the two relation clauses, where `Lift`'s
  single constructor is introduced and eliminated.
* **`join_unit_force`** — `(join (fun _ : Unit => M) D).force x φ ↔
  (addRoot M (unitRootData D)).force (x.map Sigma.snd) φ`, for EVERY
  world and EVERY formula, with `join_unit_root_force` the root
  instance a derivation reads.

So `joinscreen` §E's 5/5 pointwise agreement is now a theorem, and the
boundary cell the doctrine demands of a generalisation — the new
constructor must reduce to the old one when its extra freedom is
unused — is discharged by proof.  25 pins in the file.

**T2 is unblocked**: nothing in the join is now screened-only.

---

## 2026-08-14 (evening) — T2 DONE: COMPLETENESS, and what it costs to run

`Reject/Height.lean`, `Reject/Bisim.lean`, `Reject/Complete.lean`.
Screen: `lake exe t2screen` (`wip/t2_screen.lean`, output
`wip/t2_screen_out.txt`), seven sections, all green.

### The theorem

**`gen_of_reduced`** — every world of a finite REDUCED constraint
model is bisimilar to the root of a model the calculus BUILDS. Hence

**`built_countermodel_of_reduced`** — a sequent with a finite reduced
countermodel has a countermodel that is a *construction*: a `Built`
model whose root forces the hypotheses and refutes the conclusion.

With `not_laxND_of_root` (T1) the two directions meet: on that class,
underivability and constructibility coincide.

| result | pin |
|---|---|
| `height_lt_of_ri`, `height_lt_of_rm`, `height_induction` | `[propext, Classical.choice, Quot.sound]` |
| `upSet_ssubset` | `[propext, Quot.sound]` |
| `union_reduced`, `join_reduced`, `join_comp_incomparable` | *no axioms* |
| `exists_cover_below` | `[propext, Classical.choice, Quot.sound]` |
| `Bisim.force` | `[propext, Classical.choice, Quot.sound]` |
| `genSolo` | *no axioms* |
| `genJoin`, `gen_of_reduced`, `built_countermodel_of_reduced`, `built_iff_of_reduced` | `[propext, Classical.choice, Quot.sound]` |
| `not_laxND_of_built` | `[propext]` |

51 pins across `Reject/`; the build fails if any drifts.

### Three design decisions, each forced by something measured

**1. The measure is UP-SET CARDINALITY, not longest path.**
`height N x = |{z | x Rᵢ z ∧ x ≠ z}|`. FRJ uses the longest ascending
path; the two differ in value and agree in everything the induction
uses — a strict `Rᵢ`-step strictly decreases both. Cardinality is a
proper-subset argument, so no well-founded recursion is needed to
*define* it, only to consume it.

**2. Reducedness is load-bearing, and now measured.** §A′ of the
screen: the decrease holds on all **2,588** reduced models of the
≤3-world battery and FAILS on all **1,826** non-reduced ones, smallest
certificate the two-world `Rᵢ`-cycle `{n := 2, ri := [(0,1),(1,0)]}`.
This is the second place `docs/frj-lifting.md` §5 predicted it would
bite; the first was the unary arity of the ◯-rule.

**3. Bisimulation, not isomorphism — and REUSED, not reinvented.**
The built tree duplicates worlds the countermodel shares between
branches, so the two are never isomorphic. Matthew's catch: the notion
already exists in this tree as `SemUI.ABisim`
(`LaxLogic/PLLSemUI.lean`), built for the *semantic route to uniform
interpolation*, with `force_iff_of_bisim` already proved. Its zig-zag
is already the one `◯` forces. `Reject/Bisim.lean` is therefore a thin
adapter — `Bisim M N := ABisim (fun _ => True) M N` — and nothing is
duplicated. The parked UI machinery has now paid for itself twice.

### What `Built` actually is

`solo` and `join` generate exactly the finite `Rᵢ`-TREES, with
**fallible worlds only at leaves**: `join` sets its new root's `F` to
`False` unconditionally, so fallibility can enter only through `solo`.
That is why `solo` is not redundant, and it is the constructor-level
form of "fallibility is a zone flag" (`frj-lifting.md` §4).

The claim was screened before it was proved (§D): over the ≤3-world,
two-atom battery — 30,424 well-formed frames, 1,430 of them trees —
every corpus formula refuted anywhere is refuted **at the root of a
tree**, 0 gaps in 22 cells, with a non-vacuity control (6 formulas
refuted at no tree root).

### Matthew's objection about PCLL, and its answer

*"Tree models cannot be confluent but some models ARE confluent and
they genuinely force other things — so trees may suffice for PLL but
not for PCLL."*

The objection is right in form and dissolves in substance, and the
reason is worth recording because it corrects how
`join_cone_empty_of_confluent_branching` should be read.

That theorem constrains **IMMEDIATE** branching only. A confluent tree
may branch freely *above* a node with a non-trivial modal cone.
Certificate (§F, 4 worlds, hand-built because the ≤3-world battery is
too small to contain the shape):

    deepCone : W = {0,1,2,3},  Ri = 0 < 1 < {2,3},  Rm = {(0,1)},
               p at 1,2,3
    well-formed ∧ confluent ∧ a tree;  cone(0) = {1} NON-empty;
    0 ⊩ ◯p and 0 ⊮ p;  2,3 incomparable above 0.

And the constraint at immediate branching is not something the
calculus imposes — it is what confluence *itself* forbids: in the
union, `s Rᵢ u` keeps `u` in `s`'s component and `t Rₘ u` keeps it in
`t`'s, so distinct components have no common completion. Any confluent
tree has an empty cone at an immediately-branching node, built by this
calculus or not.

Measured consequence (§F): **0 completeness gaps for confluent trees
either**, in 22 cells over 25,171 confluent models against 739
confluent trees. So decision (a) is not paying for the PCLL reading
with completeness, on the evidence available.

### THE COST OF RUNNING IT — and the repair, applied

The goal asked how to extract the most efficient checkable procedure.
Measured, §G:

| | proof indexed by ALL greater worlds | indexed by COVERS |
|---|---|---|
| chain, n = 5 | 16 | 5 |
| chain, n = 8 | 128 | 8 |
| chain, n = 10 | **512** | **10** |

`|T(w)| = 1 + Σ_{v > w} |T(v)|` is `2^(n-1)` on a chain: every world is
re-expanded once per path that reaches it. **The proof now indexes by
COVERS** (`Succ w := {v // Covers N w v}`), which is still exhaustive
by `exists_cover_below` — every world above `w` lies above some cover
— and gives `n` on a chain. That repair is *in the mechanised proof*,
not a note about it; `Gen` gained the `onto` invariant (every world
above `w` is reached) to support it.

**What remains exponential, and the plan.** Even by covers, the tree is
the set of PATHS through the poset, so a poset with many maximal
chains still blows up. Trees forbid sharing by construction, and that
is the real ceiling. Two ways out, in the order they should be tried:

1. **Extract the DERIVATION, not the MODEL.** FRJ's own object is a
   DAG over a finite sequent set (subformulas of the goal), which is
   exponentially smaller than the model it denotes, and *checking* a
   derivation is polynomial in its own size. This is exactly T3's
   design, and it is the reason T3 is forward saturation over sequents
   rather than model construction. T2 says the model exists; T3 should
   never build it.
2. **Admit sharing into `Built`.** A `share` constructor (a join whose
   components may overlap above a cut) would collapse paths to a DAG,
   at the cost of re-proving the modal rules for overlapping
   components — and, note, of leaving the tree class, so
   `join_cone_empty_of_confluent_branching` would need restating.
   Only worth it if (1) proves insufficient.

Checking is already cheap either way: `Built` is decidable on `FinCM`
data (is it a tree with fallible leaves), and `forceB` is polynomial in
`|M|·|φ|`. The expensive half is FINDING, which is T3's problem, and
(1) is the answer to it.

### The ONE remaining gap, named precisely

`built_countermodel_of_reduced` needs a **finite reduced** countermodel.
That is exactly the hypothesis FRJ's Lemma 4 carries too, and it is
what the handoff's T2 entry specified ("from any countermodel … needs
reducedness for the measure to decrease"). What is NOT yet proved is
the hook-up:

> **(R)** every underivable sequent has a finite REDUCED countermodel.

Status: **OPEN**, with evidence and with a certificate saying why the
obvious routes fail.

* Evidence for (R): §C of the screen — the reduced battery refutes
  everything the full battery refutes, 0 gaps in 22 cells.
* The repo's own finite-model construction does **not** supply it. The
  filtration (`PLLFiniteModel.lean`) has worlds `(T, Fm)` with
  `Ri q q' := T ⊆ T'`, so two worlds with the same theory and
  different modal parts are `Rᵢ`-equivalent and distinct — not
  reduced.
* Quotienting cannot fix it. `Rᵢ`-equivalent worlds *do* force the
  same formulas (their up-sets are equal — one line from
  `force_hered` both ways), but they need not be BISIMILAR, and the
  quotient by bisimilarity need not be antisymmetric. §E is the
  certificate: a 3-world model with `0 ≈ᵢ 1`, `Rₘ`-cones `{0,2}` vs
  `{1}`, where `0 ⊮ ◯p` while `2 ⊩ ◯p`. No finite tree is bisimilar to
  it.
* Nor does the *emitter*. `PLLFinComp.emitter_completeness` DOES give
  a machine-checked finite countermodel for every underivable sequent
  — `¬ Nonempty (LaxND Γ C) → ∃ M w, FinCM.checkB M w Γ C = true` —
  so the finiteness half of (R) is already proved in the tree. But its
  worlds are `FTheory` triples `(val, fal, mfal)` with
  `ri := val ⊆ val'` and `rm := val ⊆ val' ∧ mfal ⊆ mfal'`
  (`canonCMof`), so two worlds with the same `val` and different
  `mfal` are `Rᵢ`-equivalent and distinct. Not reduced, for exactly
  the reason the filtration is not.

**A concrete, cheap route for (R), to be SCREENED before it is
scoped.** Refine the emitted model's `Rᵢ` lexicographically:

    Ri' q q' := q.val ⊆ q'.val ∧ (q.val = q'.val → q.mfal ⊆ q'.mfal)

This is reflexive and transitive, ANTISYMMETRIC on `FTheory` pairs
(equal `val` and equal `mfal`), contains `Rm` (which already demands
both inclusions) and is contained in `Ri`. So the frame conditions and
reducedness are free; the only obligation is that the verified checker
still passes with the smaller `Rᵢ`. Shrinking `Rᵢ` makes `⊃` and `◯`
EASIER to force, so only the reflecting direction is at risk, and the
risk is confined to pairs with equal `val` and `⊆`-incomparable
`mfal`. That is decidable, so it is a screen — run `checkB` with the
refined `ri` over the closed-fragment corpus and over the p-carrying
cells, with a control that the unrefined model still passes in the
same run. If it survives, (R) is a short proof; if it fails, the
certificate names the shape that defeats it, and the fallback is a
Hintikka/canonical TREE over the subformula closure — the same object
T3 searches for, which is a reason to do T3 next and take (R) as its
by-product.

### What T3 inherits

* A completeness theorem to be complete *for*: exhausting the space of
  `Built` models is now meaningful, because `gen_of_reduced` says the
  space is not missing anything (on reduced finite countermodels).
* The measured reason to search **sequents, not models**: §G.
* `exists_cover_below` and the `onto` invariant, which say a searcher
  need only branch on COVERS.
* The open item (R), which T3's saturation is the natural way to close.

---

## 2026-08-14 (late) — the (R) SCREEN: run, and it found a route

`lake exe rscreen` (`wip/r_screen.lean`, output `wip/r_screen_out.txt`).
Per doctrine the screen sweeps a LATTICE of refinements, not the one
statement the previous section proposed — and the one proposed
(refine `Rᵢ` lexicographically by `mfal`) is **V1**, which turns out to
be sound but insufficient on its own.

Battery: 4,414 well-formed frames on ≤3 worlds with one atom, of which
**1,826 are NON-reduced** — the cells the question is about. Each
variant is judged on three decidable things: (a) is the refined frame
still well-formed, (b) is it REDUCED, (c) is FORCING PRESERVED at every
world for all 16 closure formulas.

| variant | (a) wf | (b) reduced | (c) forcing |
|---|---|---|---|
| **V1** `Fm`-inclusion *(the proposed route)* | 1826/1826 | **60/1826** | 1826/1826 |
| **V2** cone-inclusion | 818/1826 | 1444/1826 | 1766/1826 |
| **V3** index order *(control)* | 940/1826 | 1826/1826 | 1796/1826 |
| **V4** `Fm` + index | 955/1826 | 1826/1826 | 1826/1826 |
| **V5** `Fm` + `Rm` + index | 1806/1826 | 1444/1826 | 1826/1826 |
| **V6** `Fm` + `Rm`-RANK + index | 1444/1826 | 1826/1826 | 1826/1826 |

**V6 restricted to the `Rₘ`-ACYCLIC models: 1444/1444 on all three.**

Read in order, this is a worked instance of "each round's residue
defines the next stratum":

* **V1** — the section-above proposal — preserves forcing everywhere
  and stays well-formed everywhere, but only reduces 60 of 1,826:
  worlds with EQUAL `Fm` stay `Rᵢ`-equivalent. Sound, insufficient.
* **V3** is the control: antisymmetry bought by an arbitrary linear
  order costs both well-formedness and forcing. So the modal data is
  doing real work in V1/V4/V6, not the ordering as such.
* **V4** (V1 + index tie-break) gets reducedness AND forcing, but
  breaks `Rm ⊆ Ri`: `Rm w v` with `Fm(w) = Fm(v)` and `w > v` as
  indices loses the pair.
* **V5** lets `Rₘ` win the tie — and breaks `Rᵢ`-TRANSITIVITY on 20
  cells, because "Rₘ wins, else index" can CYCLE. Certificate: a
  3-element `Rᵢ`-class with `Rm 2 0`, giving `0 < 1 < 2 < 0`.
* **V6** replaces the tie-break by a LINEAR EXTENSION of `Rₘ` — the
  rank `|{v | v Rₘ w}|`, which strictly increases along a proper
  `Rₘ`-step on an acyclic model. Total on each equal-`Fm` group, hence
  transitive; extends `Rₘ`, hence `Rm ⊆ Ri` survives; antisymmetric,
  hence reduced. All three clauses pass, on every acyclic cell.

**The route for (R), in two steps, both provable:**

1. **Quotient by `Rₘ`-equivalence.** `Rₘ`-equivalent worlds have equal
   `Rᵢ`-up-sets and equal `Rₘ`-cones, so the equivalence IS a
   bisimulation — `Bisim.force` transfers forcing, and the quotient is
   `Rₘ`-acyclic. (This is the step V6 needs and the reason its failures
   on the full battery are exactly the 382 `Rₘ`-cyclic cells.)
2. **Refine `Rᵢ` by V6.** `Fm`-inclusion, then `Rₘ`-rank, then index.

The remaining obligation is (c) for step 2 — that shrinking `Rᵢ` this
way cannot make a `⊃` or `◯` become true. The `⊃` case is easy
(`Rᵢ`-equivalent worlds force the same formulas, so a dropped witness
is replaced by the world itself). The `◯` case is the content, and the
`Fm` ordering is exactly what makes it work: the world with the LARGER
`Rₘ`-cone has the SMALLER `Fm`, so V1 keeps the arrow from big-cone to
small-cone, which is the direction that keeps ◯-witnesses reachable.

**Caveat, stated.** ≤3 worlds with one atom. The configuration that
would break (c) needs a witness world whose `Fm` is incomparable to the
source's, and the screen shows none exists at this size — support, not
proof. `rscreen` is re-runnable at a larger battery when one is
affordable.

---

## 2026-08-14 (night) — T3: the CERTIFICATE FORMAT and the SEARCHER

`Reject/Cert.lean`; searcher `lake exe t3search` (`wip/t3_search.lean`,
output `wip/t3_search_out.txt`).

### What is now PROVED

`certifies M w Γ C : Bool` — well-formed frame, in the BUILT class,
root forces `Γ`, root refutes `C` — with

| result | statement | pin |
|---|---|---|
| `not_laxND_of_certifies` | a `Bool` decides underivability | `[propext, Quot.sound]` |
| `not_laxND_of_check_any` | the check is sound at ANY world, not only the root | `[propext, Quot.sound]` |

so the thread's goal sentence is discharged on the checking side: a
refutation is now **a finite syntactic object whose validity is a
decidable predicate**. `BuiltB` decides membership of the class
`solo`/`join` generate — rooted, `Rᵢ`-antisymmetric, predecessors a
chain, fallible worlds only at leaves — which is the tree
characterisation T2 established.

The split is deliberate and worth keeping straight: **soundness does
not need `BuiltB`.** `checkB` alone certifies underivability for any
finite model (`FinCM.not_provable_of_check`, already in the tree).
`BuiltB` is what makes a certificate a DERIVATION rather than a found
countermodel, and it is what a searcher should range over — because
T2 says completeness lives in that class and nowhere smaller.

`not_laxND_of_check_any` is the mining lemma, and it needed no new
proof: `not_laxND_of_root` was never stated only for roots. **Every
world of every stored model settles an underivability.**

### The searcher: saturation with SHARING

T2 §G said the extracted MODEL is exponential, so the search must
share. What a join consumes from a premise `c`, over the closure `cl`,
is exactly four sets (read off `join_force_box_iff`):

    root(c)  forced at c's root          (the ⊃/∧/∨ clauses)
    univ(c)  forced at EVERY world       (⊃ quantifies over the cone)
    some(c)  forced at SOME world        (what a modal cone realises)
    box(c)   A with every world having an Rₘ-successor forcing A
                                          (the ◯-positive obligation)

Two premises with the same 4-tuple are interchangeable, so the store is
keyed by it and duplicates are discarded. **That is the DAG the tree
cannot express**, and it is why the store stays tiny while the models
it denotes do not.

### Measured, on two covering goals

Matthew's point — wrap several representatives in one covering goal —
is the operating principle, and the two runs demonstrate its content:
**coverage = closure.**

| | closure | atoms | states stored | witness worlds | calibration | adversarial | harvest |
|---|---|---|---|---|---|---|---|
| **Goal 1** 13 catalogue reps | 26 | — | **20** | 127 | 5/5 | 6/6 clean | **93/156** |
| **Goal 2** 9 p,q formulas | 21 | p,q | **68** | 220 | 5/5 | 6/6 clean | **47/72** |

**140 separations from two saturations**, 88 stored nodes in total.
Goal 1 settles ρ4, ρ6, ρ11 (= g1) and ρ12 (= r1) as construction
certificates; Goal 2 settles `◯p`, `◯p ⊃ p`, `(p⊃q)∨(q⊃p)`, `p ∨ ¬p`
and — the useful one — `◯(p∨q) ⊃ (◯p∨◯q)`, the PCLL distribution
axiom, correctly refuted **in PLL**.

The first run of Goal 1 FLAGGED `⊬ (p⊃q)∨(q⊃p)`, which is the
principle biting rather than a defect: a variable-free covering goal
has no atoms in its closure, so no seed carries `p`. Goal 2 is the same
method with a closure that reaches them, and it settles the cell at
node 32. Choose the goal to cover the targets, or the harvest cannot
reach them.

The adversarial check is the one that matters for trust: six sequents
certified derivable — including the G4iLL blocker
`◯((◯p⊃r)⊃◯p), ◯p⊃r ⇒ r` — and **no** stored model certifies any of
them, at any world, in either run.

### Scope, stated rather than assumed

* **Cone choices are restricted to WHOLE components.** Whole components
  are `Rₘ`-upward closed, so every choice the searcher makes is legal
  and every hit is kernel-checkable. But cones selecting PART of a
  component are not explored, so the searcher is **sound, not known
  complete**. A `FLAG` therefore means "not settled at this budget or
  in this cone-fragment", never "underivable".
* **The sequent-level calculus is not built.** What exists is
  saturation over CONSTRUCTIONS keyed by their join-relevant state —
  which is the sharing that matters — not FRJ's `Σ ; Θ ; μ → C`
  sequents with the `Cl` closure. That remains the route to a rule set
  with a completeness theorem of its own, and `Cl` is still the one
  piece graded WORK in `frj-lifting.md` §5 (screened, not proved).
* **Search completeness rests on (R).** `gen_of_reduced` says the built
  class is complete for finite REDUCED countermodels; (R) is still
  open, with the two-step route mapped in the previous section.

### What T4 inherits

A working discovery loop: pick a covering goal, saturate, harvest at
every world. The calibration and adversarial blocks are already in
`t3search` and should be re-run with the 57 pinned crank-7 separations
substituted for the ad-hoc `known` list — that is the calibration the
handoff asked for, and it is now a one-line change rather than a
project.

---

## 2026-08-14 (night) — (R) is PROVED. T2 is now UNCONDITIONAL.

`Reject/Reduce.lean`. The open item is closed, by the route the screen
found, and with it the last hypothesis comes off completeness:

```
theorem not_laxND_iff_built {Γ ψ} :
    ¬ Nonempty (LaxND Γ ψ) ↔
      ∃ (M : ConstraintModel) (r : M.W),
        Built M ∧ (∀ χ ∈ Γ, M.force r χ) ∧ ¬ M.force r ψ
```

**On PLL, underivability and constructibility coincide.** `←` is T1
(`not_laxND_of_root`); `→` is T2 composed with (R).

| result | pin |
|---|---|
| `Fm_mono`, `force_iff_of_ri_equiv` | *no axioms* |
| `qBisim` | `[propext]` |
| `qModel_rm_antisymm` | `[propext, Quot.sound]` |
| `eq_of_rm_of_rrank_eq`, `refineM_reduced`, `exists_refined_witness`, `refineM_force` | `[propext, Classical.choice, Quot.sound]` |
| `exists_reduced_countermodel` — **(R)** | `[propext, Classical.choice, Quot.sound]` |
| `built_countermodel`, `not_laxND_iff_built` | `[propext, Classical.choice, Quot.sound]` |

64 pins across `Reject/`.

### The two steps

**Step 1 — quotient by `Rₘ`-equivalence** (`qModel`, `qBisim`).
`Rₘ`-equivalent worlds are `Rᵢ`-equivalent (`Rm ⊆ Ri`), hence force the
same formulas, and have the same `Rₘ`-cone. So the collapse is a
bisimulation and forcing is untouched. It removes exactly the
`Rₘ`-cycles that no refinement of `Rᵢ` could survive — an `Rᵢ`
containing a cyclic `Rₘ` cannot be antisymmetric.

**Step 2 — refine `Rᵢ`** (`refineM`). Keep `x Rᵢ y` unless `x ≈ᵢ y`, in
which case keep it only when `rle x y`: `Fm`-inclusion, then
`Rₘ`-RANK, then an arbitrary injective key. `Rm ⊆ Ri` survives because
rank is a strict linear extension of `Rₘ` on an acyclic model
(`eq_of_rm_of_rrank_eq`), which is precisely what step 1 supplies.

### The one non-obvious step, and how it goes

Shrinking `Rᵢ` cannot make `◯A` become TRUE. `exists_refined_witness`:

> if `x`'s own cone realises `A` (`A ∉ Fm x`) but some `Rᵢ`-successor
> `y` refutes `A` throughout its cone (`A ∈ Fm y`), then some world the
> refinement KEEPS above `x` does too.

Take `m` of maximal `Rₘ`-rank in `{v ≥ᵢ x | A ∈ Fm v}` — a set that is
`Rₘ`-closed, since `Fm` only grows along `Rₘ` (`Fm_mono`). Maximal rank
plus `eq_of_rm_of_rrank_eq` makes `m` its own only `Rₘ`-successor, so
`Fm m` is exactly what `m` refutes. Then either `m ≉ᵢ x`, and the arrow
survives vacuously; or `m ≈ᵢ x`, and then `Fm x ⊆ Fm m` (everything in
`Fm x` is refuted at `x`, hence at `m`) while `A ∈ Fm m \ Fm x` — so
`Fm x ⊊ Fm m` and `rle x m` holds. Either way the witness is kept.

The `⊃` case is the easy dual: a dropped witness is `Rᵢ`-equivalent to
the source, so the source replaces it.

### What this changes

* `docs/rn-dictionary-status.md`'s 83 open cells and the catalogue's
  109 flags are now attackable by CONSTRUCTION with no side condition:
  a failure to build is not "the builder was not clever enough" but
  evidence, because the class is complete.
* T3's searcher is now complete **for the space it explores** — the
  remaining gap is its restriction to whole-component cones, which is a
  searcher scope choice and is stated in `wip/t3_search.lean`, not a
  gap in the calculus.
* The `rscreen` caveat stands as a caveat about the SCREEN only: the
  proof is not restricted to ≤3 worlds or one atom. The screen chose the
  refinement; the proof establishes it in general.

---

## 2026-08-14 (night) — the LJF◯ ↔ PLL BRIDGE

`LaxLogic/LJFOBridge.lean`. The arrow that did not exist anywhere in
the repo — confirmed by pickaxe over every ref
(`git log --all -S "LaxND" -- 'LaxLogic/LJFO*'` returns nothing) — now
exists in one direction outright and is reduced to one named statement
in the other.

### PROVED: soundness, LJF◯ ⟹ PLL

Erase polarity (`↓`/`↑` vanish, `circ` becomes `◯`) and read the
judgment flag as the modality:

    Γ ⊢tru P   ↦   ⌊Γ⌋ ⊢ ⌊P⌋
    Γ ⊢lax P   ↦   ⌊Γ⌋ ⊢ ◯⌊P⌋

which turns `LJFOCore`'s own gloss — "the lax goal is definable" — into
a theorem. One mutual recursion over the four judgments, mirroring the
`wk` family. The three modal rules land exactly where they should:

| LJF◯ rule | PLL rule |
|---|---|
| `laxOf` (truth-to-lax coercion) | `laxIntro` — it IS `φ ⊢ ◯φ` |
| `circL` (left focus on a box, lax only) | `laxElim` |
| `circR` | identity at `tru`, `laxIntro` at `lax` (`◯φ ⊢ ◯◯φ`) |

Everything else is structural, and every structural move is
`LaxND.rename`, which subsumes weakening, exchange and contraction —
so **no cut and no admissibility lemma is used anywhere**.

| result | pin |
|---|---|
| `Stab.sound`, `Inv.sound`, `sound_tru`, `sound_lax`, `laxND_of_ljfo`, `not_ljfo_of_not_laxND` | `[propext, Quot.sound]` |
| `erase_polarise`, `eraseCtx_polarise` | `[propext]` |
| `bridge_iff` | `[propext, Quot.sound]` |

**No `Classical.choice`** — the bridge matches the LJFO development's
own axiom profile, which was a design constraint of that campaign
(zero imports, nothing else carries the proof).

### PROVED: completeness too — focalization for PLL

`LJFComplete.lean`'s `posOf`/`negOf` DISCARD the modality
(`.somehow φ ↦ posOf φ`), because that development targets IPC through
`PLLND.erase`. So the bridge needed its own ◯-PRESERVING polarisation,
`posOfO`/`negOfO`, with `erase_polarise` proving the round trip is the
identity on PLL formulas. With it:

```
theorem bridge_iff (Γ φ) :
    Nonempty (LaxND Γ φ) ↔ Nonempty (Inv (Γ.map negOfO) [] .tru (negOfO φ))
```

**Both halves are proved.** `←` is `Inv.sound` composed with the round
trip. `→` is `FocalizationPLL`, via `focalizeSCO` — the port of
`LJFComplete.focalizeSC` to the ◯-preserving polarisation, composed
with the repo's cut elimination `PLLND.ND_to_SC`.

The port was bounded, and the reason is worth recording: **every helper
`focalizeSC` needs already exists in `LJFOCore` with the flag
threaded** — `unStable`, `invertPos`, `invBranches`, `extract`,
`simHyp`, `upMerge`, `stabOr1/2`, `nBotElim`. Only four
bridge-specific helpers had to be ported (`stabOfInvO`, `branchLFocO`,
`branchInO`, `shiftInO`), and they got SIMPLER: with `◯` kept,
`posOfO (◯φ) = ↓(circ …)` is a shift, so the `somehow` case joins the
`∧`/`⊃` cases instead of recursing.

The genuinely new content is the two modal cases, trivial in
`LJFComplete` only because `negOf` erases `◯` there:

| `SCh` rule | LJF◯ construction |
|---|---|
| `laxR` | `circR` over `laxOf` — prove the body TRULY, then coerce |
| `laxL` | `circR` over `lfoc`/`circL` — focus the box, body into the queue via `shiftInO` |

`laxL` also needed `circInv`: `circR` is the only rule that concludes
`circ` from an EMPTY inversion queue (the `Ω`-processing rules all need
a non-empty one), so inverting it is a single pattern match.

**This closes `docs/ljfo-fidelity.md` §5's open item.**

### What this settles about the repo's status

* An LJF◯ **proof** transfers to PLL: `laxND_of_ljfo`.
* An LJF◯ **failure** transfers to PLL, and conversely: `bridge_iff`.
  So LJF◯'s uniform-interpolation machinery is now connected to PLL,
  which was the point of the campaign.
* `not_ljfo_of_not_laxND` runs the other way and is immediately usable:
  a PLL countermodel — including any `Reject` certificate — shows the
  corresponding LJF◯ sequent has NO derivation. So the disproof thread
  can now settle LJF◯ questions, which is a use of `Reject/` nobody
  had planned for.

---

## 2026-08-15 (early) — THE LINK: LJF◯ and Reject joined into the two-sided engine

*The `ljf-pll` session, at Matthew's direction ("the extra machinery in
LJF◯ is lying unused. Use it now please and link it somehow to Reject/
and effectively and test it"). Full report: `docs/two-sided-engine.md`.
The T1 branch is merged into `ljf-pll` (merge `8a2d1a8`), so both
machines now live on one line.*

The link is the observation that the two campaigns built the two
halves of one decision procedure, each ending in a Bool:

* `TwoSidedLink.searchProves f Γ φ` — LJF◯ backward search on the
  bridge's polarisation. Sound (`laxND_of_searchProves`) AND complete
  (`searchProves_complete`), both `[propext, Quot.sound]`, choice-free
  — completeness is `FocalizationPLL` + `search_complete` with the
  `Nonempty` eliminated into a propositional goal.
* `Reject.certifies M w Γ φ` — a Built-tree countermodel. Sound
  (`not_laxND_of_certifies`); complete in principle
  (`not_laxND_iff_built`) but not yet effectively.
* `two_sided_disjoint` — the sides can never both fire, at kernel
  level.

Measured on the 462 ρ-order cells against the old machinery recomputed
in the same binary (`lean_exe twosided`): agreement with zero
conflicts; the proof side settles **all 158** derivable cells by fuel
40 at unmeasurable cost against the G4c oracle's 9.8 s; the Built
subbattery (570 of 10,534 frames — 5.4%) retains 248 of 302
refutations, the missing 54 being exactly the cells whose bisimilar
tree needs more than 5 worlds; a streaming 6-world tree generator
chases those. Kernel exemplars in `wip/two_sided_pins.lean`: the
kernel re-runs the focused search inside `decide` in ~1 s, no
`native_decide`.

**What this supersedes and what it does not.** For PLL sequent
questions on the closed corpus, the engine replaces both the blind
battery and the G4c oracle. It does NOT yet carry a feasible
exhaustion bound (an LJF◯ `false` at fuel 64 is evidence, not a
certificate — the pigeonhole layer over the finite subformula universe
is the missing theorem), and the refutation side still SEARCHES the
Built class rather than computing certificates from
`not_laxND_iff_built` (blocked on the constructivisation already
specced with the T1 session). Those two effectivity theorems are the
whole remaining gap between "engine" and "decision procedure".

---

## 2026-08-15 (morning) — /goal: FRJ◯, the refutation calculus, derived

*Matthew's /goal: derive the refutation calculus — judgment,
completeness, extraction — on the basis of FRJ extended to ◯; continue
to an efficient refutation procedure; test on the corpus. He also
resolved the source of the week's confusion: FRJ(G) is the refutation
calculus; LJF◯ was the (interpolation-born) proof calculus. Reject's
role: the model-checking side.*

**The derivation of the rules.** LJF◯'s `succs` enumerates rule
instances; derivable = some instance with all premises derivable. The
refutation calculus is the DUAL, one rule per instance shape (= per
connective and phase): refuted = every instance has a refuted premise.
Refutation AXIOMS fall out mechanically as the no-instance cases —
right focus on `fls`; left focus on `◯Q` at `tru` (the lax-only
condition working for disproof); `init` with the atom absent; `⊃/∧`
right at `lax` (the flag discipline). Loops are broken by a HISTORY:
`cyc` discharges a stable sequent already on the branch — the
coinductive step read inductively, sound in the extracted model where
the recurrence is the same world revisited. Contexts grow inside the
finite subformula universe and the history blocks revisits, so search
terminates with NO fuel — canonical-sequent counting in place of
`decideFuel`-style bound arithmetic.

**Built (`FRJO/Core.lean`, new lib):** `RT` (derivations: per
instance, the index of the failing premise; finite syntax), `wf` (the
decidable rule-application predicate), `find` (the untrusted searcher,
history-terminating), `worldsOf` + `Unravel.assemble` (extraction:
worlds = the stable contexts the DERIVATION visits), and

    FRJO.refute? : List PLLFormula → PLLFormula → Option (RT × FinCM × Nat)

— search, self-check `wf`, extract, gate by `FinCM.checkB`; a hit is
consumable by `not_provable_of_check`, i.e. kernel-checkable today.

**Status ledger (rigid):** per-instance soundness PROVED-by-gate
(every emitted refutation carries a verified certificate); the
once-and-for-all `SoundnessFRJO` and the completeness `CompletenessFRJO`
(item 2, the pigeonhole/loop-check theorem) are STATED as named
propositions and OPEN. Corpus test running at write-up
(`lean_exe frjoscreen`: the 302 battery-refuted cells + the 2 flags).

### 2026-08-16 — the depth wall, measured to destruction

The compiled `searchProves` on the flag cell `ρ12 ⊢ ρ15` at fuel 64
was left running and killed after **~24 hours wall clock** without
returning (fuels ≤ 52 answer `false` in ~0 ms). Together with FRJ◯'s
refutation search finding NO derivation for either flag cell in ~0 ms
— on a corpus where it found one for every genuinely refutable cell —
the two flags now carry converging evidence of DERIVABILITY with a
proof of depth > 52, out of naive reach from both sides. They stay
OPEN. The practical moral is the pigeonhole bound again, from the
other direction: without it, deep fuel is not a usable instrument, and
the refutation calculus's completeness theorem (`CompletenessFRJO`)
is what would let FRJ◯'s "no derivation" settle them instead.

### 2026-08-16 — CompletenessFRJO: substrate proved, three lemmas out

`wip/ljfo_completeness.lean` (commit `8177d6b`): PROVED and pinned —
`isEmpty_holds_iff_search` (underivability = search failure at every
fuel, choice-free), `exists_allFail` (the finite-list pigeonhole
through `search_mono`: a cofinally-failing instance has an
everywhere-failing premise — S3's premise selector), and
`completeness_of_construction` (the goal reduces to S3). OPEN: S1
`okS_succs` (invariant preservation; every case closes on paper with
single-step `UClosed` fields; one `sorry`, membership bookkeeping — a
blunt-automation pass got the `stab`/`rfocus` cases through and stalled
on `lfoc`, reverted to keep the record clean), S2 `PigeonholeBound`
(Finset counting), S3 `ConstructionFRJO` (strong induction on
bound−|history|, premises by `exists_allFail`, revisits by `cyc`).
NEXT SESSION: S1 by hand (case shapes now known), then S2, then S3.
