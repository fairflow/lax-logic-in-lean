# BiLax: a bi-lax extension of PLL, and a principled calculus of disproof

*Plan written 2026-08-13, before any development.  Companion to
`docs/lax-dual-colax-biint-handoff.md` (the survey; cited below as
[H§n]).  Status discipline as everywhere in this repo: PROVED /
REFUTED / OPEN, with screens before proof builds (repo CLAUDE.md,
TESTING FOR COUNTEREXAMPLES).*

## 1. Why build this

**The disproof asymmetry.**  Every non-trivial inequivalence on
RN(◯,{}) — and now on its PCLL quotient — has been certified by
*countermodel*: an unprovable sequent has (by completeness) a
falsifying model, and we hunt for it breadth-first over finite
batteries.  The closed-fragment catalogue's 109 surviving flags are
exactly the cells where this method ran out: vector-identical on every
mutually confluent model with ≤ 5 worlds, so settling them needs
either a ≥ 6-world countermodel (the battery grows exponentially) or a
deeper positive search.  A **calculus of disproof** — where a
refutation is itself a *derivation* — is model-size-independent and
depth-first: precisely what those 109 cells need, and what every
future separation campaign needs.

**The mechanism.**  Bi-intuitionistic logic internalises refutation:
multi-succedent sequents carry refutation obligations on the right,
and the pure co-fragment is, by Brunner–Carnielli, dual to Int — a
co-derivation *is* an IPC refutation under a precise duality [H§7].
The lax analogue: extend PLL by Rauszer's co-implication ⤙ and the
co-lax modality ◯∃ (the left adjoint of ◯∀, certified to exist
non-trivially [H§4.3]), and aim at the theorem "co-derivations =
PLL-refutations" for the lax pair.

**The duality dividend.**  ◯∀◯∃ a monad, ◯∃◯∀ a comonad, `⊃ ⊣ ∧` and
`∨ ⊣ ⤙` as residuations with the modal adjunction sitting above them
[H§4.4–4.5]: one organising principle for material now scattered
across ad-hoc arguments.  And the standing suspicion [H§6.1] that
multi-succedent sequents dissolve the goal-dependent-left-rule
pathology that has dogged every uniform-interpolation attempt here.

**Acceptance corpus, fixed now:** the certified catalogue
(`docs/pcll-closed-fragment-catalogue.md`).  Success at each round is
measured against it: (i) re-derive known separations as
co-derivations; (ii) settle flags the battery could not.

## 2. Notation (settled by scratch test, 2026-08-13)

Tested against this repo's actual import surface (Lean 4.31 +
mathlib): **`⟶` (U+27F6) is unusable** — mathlib's `Quiver.Hom`
claims it globally and the elaborator resolves to it even against a
scoped competitor.  The following set parses cleanly, scoped in the
`BiLax` namespace, with associativity and precedence verified:

| symbol | codepoint | reading | Lean declaration |
|---|---|---|---|
| ⇾ | U+21FE rightwards open-headed arrow | implication (forward) | `scoped infixr:56 " ⇾ "` |
| ⇽ | U+21FD leftwards open-headed arrow | implication, arguments flipped | `scoped infixr:55 " ⇽ "` |
| ⤙ | U+2919 leftwards arrow-tail | co-implication (Rauszer's glyph): `A ⤙ B` = "A excluding B" | `scoped infixl:55 " ⤙ "` |
| ⤚ | U+291A rightwards arrow-tail | co-implication, arguments flipped | `scoped infixl:56 " ⤚ "` |
| ⤛ ⤜ | U+291B/C double arrow-tails | bolder variants, held in reserve | tested, parse fine |
| ◯∀ | (compound token) | the lax modality | `scoped prefix:75` |
| ◯∃ | (compound token) | the co-lax modality | `scoped prefix:75` |

Notes.  (i) The arrow-tails answer the ">-- and --<" request with
single codepoints: ⤚ *is* the ">--" shape, ⤙ the "--<", mirror-images
as ← / → are.  (ii) ⇾/⇽ give implication its directional pair with
the same mirror discipline, visually distinct from Lean's function
arrow → at every size.  (iii) If ⤙ renders too light against ⇾ in
practice, the doubles ⤛/⤜ are the drop-in bolder pair — decide after
seeing real proof states, not now.  (iv) ◯∀/◯∃ follow the handoff's
deliberate box/diamond avoidance [H§0].  (v) For prose and displays:
the single-glyph biconditional you asked about is ↔ (U+2194) or the
long ⟷ (U+27F7) — "∀∃ ⟷ ∃∀" typesets as one arrow.

## 3. Where it lives

New top-level directory **`BiLax/`** in the package (sibling of
`LaxLogic/`), its own `lean_lib` (the `wipshared` pattern already
proves two libs coexist), modules registered explicitly:

    BiLax/Syntax.lean      -- BiForm, notation, embedding of PLLFormula
    BiLax/Frames.lean      -- BiModel, forcing, persistence, the frame laws
    BiLax/Hilbert.lean     -- BiLaxND (the Hilbert/ND system, local consequence)
    BiLax/Sequent.lean     -- BiLaxSC (Rauszer-adapted, multi-succedent, WITH cut)
    BiLax/Soundness.lean   -- both calculi sound over BiModel; pins
    BiLax/Screens.lean     -- the finite-model harness (a lean_exe)

Nothing in `LaxLogic/` is touched; `PLLFormula` and `ConstraintModel`
are imported, never modified.  `BiForm` is a fresh inductive with an
embedding `emb : PLLFormula → BiForm`; all conservativity statements
run through `emb`.

## 4. Semantics: the design space, screened before anything is proved

The intended model class extends the repo's `ConstraintModel`
(Ri, Rm, F, V with heredity and `full_F`), because the acceptance
corpus's separations USE fallible worlds — a bi-lax semantics that
drops F cannot certify them.  Three design cells must be settled by
the round-0 screens, not by fiat:

**(a) The co-lax persistence condition.**  `◯∃ p at u := ∃w, Rm w u ∧
p w` [H§2] is hereditary along Ri only under a zig-zag law; the
sufficient candidate is `Rm ; Ri ⊆ Rm` (w Rm u → u Ri v → w Rm v),
known sufficient-not-necessary at n = 3 [H§5.1(1)].  Screen: over all
frames n ≤ 4, compute the exact boundary between "colax preserves
upsets" and not; adopt the weakest clean law that also keeps the
adjunction (below).  Note this is a NEW frame class: the repo's
constraint models do not satisfy it in general, so every lifting
statement ("this PLL countermodel is a BiLax countermodel") gets a
side condition — a screened lemma, not an assumption.

**(b) Co-implication at fallible worlds — a landmine found while
planning.**  Rauszer's clause `u ⊨ A ⤙ B iff ∃v ≤ᵢ u, v ⊨ A ∧ v ⊭ B`
breaks the PLL invariant that fallible worlds force everything
(`force_of_fallible`): at fallible u whose only ≤ᵢ-predecessors are
fallible, no v refutes B, so u ⊮ A ⤙ B.  Three candidate repairs, to
be screened for (persistence ∧ conservativity-over-emb ∧ co-residuation
∧ non-vacuity):

  1. patch the clause: `u ∈ F ∨ ∃v ≤ᵢ u, v ⊨ A ∧ v ⊭ B`;
  2. keep Rauszer's clause and *give up* fallible-forces-everything
     for BiForm (it survives on the emb-image — check that this is
     enough for every downstream use);
  3. restrict round 1 to F = ∅ models and add fallibility in round 2
     (REJECTED unless 1 and 2 both fail: it forfeits the acceptance
     corpus).

**(c) Seriality.**  The adjunction needed serial Rm at n = 3 [H§4.3].
The repo's models are reflexive-Rm (hence serial) — likely free, but
screen whether the F-machinery interacts.

**Round-0 harness.**  A compiled `lean_exe` (the repo's oracle
pattern) replacing the handoff's Python appendix: enumerate orders and
relations to n = 4, upward-closed valuations, evaluate ◯∀/◯∃/⊃/⤙ per
candidate clause, check adjunction-as-iff, unit, counit, persistence,
co-residuation `(A ⊢ B ∨ C) ↔ (A ⤙ B ⊢ C)`, and ALWAYS the
non-vacuity checks — the handoff caught two false positives exactly
there [H§4.2], and this repo's screens caught two statement defects
the same way last session.  One appended line per cell; fail only on
certificate; flags re-run at raised n.

## 5. The consequence relation: decided now, not discovered later

**Local consequence, wBIL-style.**  The single worst error in the
literature is Rauszer running local and global consequence together
[H§3.2]; Goré–Shillito's split makes wBIL (local; classical deduction
theorem) vs sBIL (global; modified deduction theorem).  Everything in
this repo is local (forcing at a world; `Consequence` in
PLLKripke.lean), so: **BiLax = the local consequence relation**, the
deduction theorem is expected in its traditional form, and every
statement that smells global (rules with side conditions on ALL
worlds) gets flagged at review.  sBIL-flavoured questions are
explicitly out of scope until a dedicated round.

## 6. Round 1 — the first calculi, and what gets reported

### 6.1 The Hilbert/ND system `BiLaxND`

PLL's `LaxND` (all rules, via emb) extended by:

    (⤙-residuation)   from  A ⊢ B ∨ C   infer  A ⤙ B ⊢ C     and conversely
    (◯∃-mono)         from  A ⊢ B       infer  ◯∃A ⊢ ◯∃B
    (adjunction)      from  ◯∃A ⊢ B     infer  A ⊢ ◯∀B        and conversely

with unit `A ⊢ ◯∀◯∃A` and counit `◯∃◯∀A ⊢ A` DERIVED from the
adjunction rules (not postulated — the handoff's §4.1 corrected-counit
lesson is baked into the rule choice: nothing of the shape ◯∃A ⊢ A
appears anywhere).  Exact axiomatisation of the ⤙-fragment to be
transcribed from Rauszer 1974/1977 with the [LITERATURE — VERIFY]
flags of the handoff discharged against the papers at transcription
time, not trusted from memory — hers or mine.

### 6.2 The sequent calculus `BiLaxSC` (Rauszer-adapted, WITH cut)

Multi-succedent sequents Γ ⇒ Δ (finite multisets).  Base: the
multi-succedent intuitionistic calculus with the standard asymmetric
pair —

    (⇾R)   Γ, A ⇒ B        ⊢   Γ ⇒ A ⇾ B, Δ      (succedent collapses: the intuitionistic restriction)
    (⤙L)   A ⇒ B, Δ        ⊢   Γ, A ⤙ B ⇒ Δ      (antecedent collapses: the dual restriction)
    (⇾L)   Γ ⇒ A, Δ   and   Γ, B ⇒ Δ   ⊢   Γ, A ⇾ B ⇒ Δ
    (⤙R)   Γ ⇒ A, Δ   and   Γ, B ⇒ Δ   ⊢   Γ ⇒ A ⤙ B, Δ

— plus the modal rules: PLL's ◯∀-rules lifted to multi-succedent
(design cell: `laxL`'s ◯-restricted succedent must be re-stated for
Δ ≠ singleton; candidate: succedent entirely ◯∀-formulas), and for ◯∃
round 1 takes the *adjoint presentation*: ◯∃-monotonicity, unit and
counit as rules/initial sequents.  **Cut is a rule of the system and
stays.**  This is deliberate and stated loudly: Rauszer's own
cut-elimination claim is FALSE (Uustalu) [H§3.2]; round 1 makes no
structural claims at all.  The calculus exists in round 1 to be (i)
sound, (ii) equivalent to `BiLaxND`, (iii) the vehicle on which the
refutation reading is prototyped.  The cut-free repair is round 3's
job, from Buisman–Goré or the polarised route [H§6.3] — chosen then,
with the round-1 experience in hand.

### 6.3 Round-1 reports (the deliverables)

1. **Soundness, machine-checked and pinned**: `BiLaxND` and `BiLaxSC`
   sound over the screened BiModel class; `#print axioms` transcribed.
   Includes the semantic theorems: persistence of every connective,
   the adjunction-as-iff, unit, counit, co-residuation, and the
   non-vacuity witnesses (a frame where ◯∃p ≠ p and ◯∀p ≠ p) [H§5.1].
2. **Equivalence** `BiLaxND ⊣⊢ BiLaxSC-with-cut` (both directions).
3. **Conservativity screens** (not theorems yet): on the battery, does
   `BiLaxND ⊢ emb φ` iff `LaxND ⊢ φ`?  Expected yes (Rauszer's stated
   aim was conservativity over Int [H§7]); a failure is a certified
   redirect, caught for the price of a screen.
4. **The completeness DESIGN report** (a document, not a build):
   canonical model for local BiLax — expected shape: worlds are pairs
   (prime theory, prime co-theory) with the tense-like interaction of
   [H§6.2] handled Buisman–Goré-style; where F goes; what breaks if
   the ⤙-clause repair chose (b)(1) vs (b)(2); an estimate.  Building
   it is round 2, scoped by this report.
5. **The interpolation-risk screen** [H§8.1]: cheap early test of
   whether ◯∃ breaks uniform interpolation phenomena we care about —
   run the φ★/φ♦ escalation ladder and the UI-room refuters through
   emb and check the co-fragment does not manufacture interpolants
   that shouldn't exist (or destroy ones that do).  Adding a dual is
   not interpolation-neutral; test before leaning on it.

## 7. Round 2 — completeness and the disproof bridge

1. **Completeness build** per the round-1 design report (local
   consequence; the finite-model-property variant if the canonical
   route hardens — the repo's G4-style terminating search + stuck-state
   countermodel reading [H§7.1] is the fallback and may even be
   preferable: same structure, two jobs).
2. **The disproof duality — the crown.**  Candidate statement (to be
   screened at small n before any proof is scoped, per doctrine):
   with `d(·)` the dualising translation (∧↔∨, ⊃↔⤙-with-flip,
   ◯∀↔◯∃, ⊥↔⊤):

       BiLax ⊢ Γ ⇒ Δ    ⟷    BiLax ⊢ d(Δ) ⇒ d(Γ)

   and its working corollary: a certified refutation of `φ ⊢ ψ` (φ, ψ
   in the emb-image) IS a derivation in the co-fragment — the
   Brunner–Carnielli phenomenon [H§7], lax edition.
3. **The RN(◯,{}) application** — the point of the whole build: a
   co-derivation searcher (`BiLax/Search.lean`, certificate-carrying,
   discover-then-pin like PLLSearch, NEVER a decidability theorem) run
   against the catalogue: first re-derive a sample of the 57 pinned
   crank-7 separations as co-derivations (calibration), then attack
   the 109 flags (discovery).  Every settled flag is a new catalogue
   entry or a new merge; either is progress the battery could not buy.

## 8. Round 3 — structural proof theory (scoped, not committed)

Cut-free repair (Buisman–Goré adaptation, or the polarised PBL route
where ⇾ is negative/right-invertible, ⤙ positive/left-invertible, and
the shifts license the interaction [H§6.3]); then the multi-succedent
attack on the goal-dependent left rule [H§6.1] — flagged in the
handoff as its single most actionable idea, and kept OUT of rounds
0–2 so the disproof payoff does not wait on it.

## 9. Danger ledger (standing, from [H] + this plan)

* Rauszer's cut-elim is false; her interpolation results are
  deductive-interpolation-under-global — neither is inherited.
* wBIL/sBIL conflation: decided (local), reviewed at every statement.
* The ∃∀ mirror-dual collapses to vacuity; the true dual is the bare
  backward existential [H§1.1] — no symmetric-mirror statements.
* `◯∃A ⊢ A` is NOT the counit and must appear nowhere [H§4.1].
* Vacuous success: every screen carries the non-vacuity check.
* Fallibility × ⤙ (the §4(b) landmine): settled by screen, round 0.
* Interpolation non-neutrality: screened round 1, before dependence.
* `⟶` belongs to mathlib's Quiver: never use it (tested).

## 10. Effort and sequencing

Round 0 (screens + skeleton): one session.  Round 1 (both calculi +
soundness + equivalence + the two reports): one to two sessions.
Round 2 (completeness + bridge + searcher): two to three sessions,
gated on the round-1 completeness report.  Round 3: unscoped until
round 2 lands.  (House rule: these estimates historically run ~4×
pessimistic on mechanical parts and optimistic on research parts; the
research parts here are the §4 screens' outcome, the completeness
build, and the duality bridge.)

**Sign-off point:** this plan.  On approval, round 0 starts with the
`BiLax/` skeleton and the screening harness; no theory file is written
before the §4 cells are screened.
