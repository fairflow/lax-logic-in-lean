# BiLax round 1 — soundness report, screens, and the completeness design

*2026-08-13.  Plan: `docs/bilax-plan.md`.  Survey: `docs/lax-dual-colax-biint-handoff.md`
(cited [H§n]).  Code: `BiLax/` (own `lean_lib`), screens `lean_exe bilaxscreen`.
Status words used precisely: PROVED (sorry-free + pinned `#print axioms`),
REFUTED (certificate), OPEN.*

## 0. The headline finding: the first design was REFUTED by its own screens

Reading `◯∃` back along `Rm` — the handoff's §2 clause, taken literally over the
repo's constraint models — makes the co-lax modality **the identity**:

> `Rm` is reflexive, so `A ⊢ ◯∃A`; `Rm ⊆ Ri` and persistence give `◯∃A ⊢ A`.

The round-0 screen reported `nonId = 0` across **all 44,160 well-formed 3-world
frames**: the operator never differed from the identity anywhere.  This is exactly
the vacuity trap the handoff warned about ([H§4.2], where it caught two false
positives) — and it would have made the entire bi-lax extension a notational
variant of PLL.

It is now a THEOREM, `colax_collapse_of_rm` (BiLax/Frames.lean), kept in the
development as the reason the design is what it is.

**The repair**, and it is the handoff's own: its working model took the co-lax
relation to be the *strict* part of `≤` — irreflexive.  So `BiModel` carries a
**separate co-lax relation `Rc`**, not required reflexive, with three laws.  A
second screen finding: the `square` law over `Rm` that the first design carried is
**free** (0 failures — take the witness `v` itself, by `refl_m`), so it was dropped.

## 1. The model class (`BiLax/Frames.lean`)

`BiModel` extends the repo's `ConstraintModel` (`Ri`, `Rm`, `F`, `V`, heredity,
`full_F`) with `Rc` and:

| law | statement | buys |
|---|---|---|
| `square_c` | `Rc w u → Ri u v → ∃w', Ri w w' ∧ Rc w' v` | persistence of `◯∃` |
| `counit_c` | `Rc w u → ∃v, Ri w v ∧ ∀y, Rm v y → Ri y u` | the counit `◯∃◯∀A ⊢ A` |
| `serial_c` | `∀v, ∃u, Rm v u ∧ Rc v u` | the unit `A ⊢ ◯∀◯∃A` |

`serial_c` is the exact compatible form of the handoff's seriality finding
[H§4.3].  Each law was derived analytically (the largest-upset-avoiding-`u`
argument) and then screened for necessity, not assumed.

**Forcing.**  Forward clauses are PLL's; `A ⤙ B` at `w` iff some `Ri`-predecessor
forces `A` and refutes `B`; `◯∃A` at `w` iff some `Rc`-predecessor forces `A`.

**PROVED and pinned** (all `[propext, Classical.choice, Quot.sound]` or cleaner):

* `bforce_hered` — every connective persistent (retrospective ones via
  transitivity and `square_c`);
* `bforce_emb` — the embedding agrees with PLL forcing, connective by connective;
* `bforce_of_fallible_forward` — fallible worlds force every FORWARD formula;
* `bforce_ff` — `ff = ⊤ ⤙ ⊤` is forced NOWHERE;
* `bforce_unit`, `bforce_counit`, `bforce_adjunction` (the modal adjunction as an
  iff on a model), `bforce_coresiduation` (`⤙` left adjoint to `∨`);
* `colax_collapse_of_rm` — the refutation above.

### The fallibility question, settled

`bforce_ff` is the sharp form of the answer to "can frame conditions repair the
fallibility/subtraction fight?": **no** — `ff` is unforceable for logical, not
geometric, reasons, so no reducedness or order condition can rescue exfalso for
it.  What holds instead is `bforce_of_fallible_forward`, and the bi-language
thereby separates PLL's **local falsum** `⊥` (= fallibility, the machinery the
variable-elimination strategy needs) from the **absolute falsum** `ff`.  Exfalso
is fragment-relative in both calculi accordingly, and the countermodel-search
application is untouched: its end-sequents live in the embedded fragment.

## 2. The two calculi

### `BiLaxND` (`BiLax/Hilbert.lean`) — the reference system

PLL's `LaxND` rules over `BiForm`, with `falsoElim` carrying `IsForward`, plus
theorem-level retrospective rules (`coimpDisj`, `coimpMin`/`coimpMax`,
`colaxMono`, `adjL`/`adjR`).  Retrospective rules are theorem-level because a
context forced at `w` need not be forced at a predecessor — the same
future/past asymmetry as fragment-relative exfalso, now on the proof-theoretic
side.  **Unit and counit are derived** (`biLax_unit`, `biLax_counit`, both from
`adjL`/`adjR` on the identity): nothing of the shape `◯∃A ⊢ A` appears anywhere
in the system, per [H§4.1]'s corrected-counit lesson.

### `BiLaxL` (`BiLax/Labelled.lean`) — the labelled calculus, CUT-FREE BY DESIGN

Per Matthew's directive (no defective start point), the sequent system is
labelled from the start, Negri-style, template Pinto–Uustalu
`[LITERATURE — VERIFY]`.  Rauszer's calculus is not used.  28 rules over sequents
carrying a label graph:

* relational atoms `ri`, `rm`, **`rc`**, `fal`, and the auxiliary `cw` (the inner
  ∀ of `counit_c`, split geometrically into `counit1`/`counit2`);
* labelled formulas in two sorts: `fm A` ("A here") and `dm A` ("some
  `Rm`-successor forces A" — the inner ∃ of the `◯∀` clause, split into
  `dmL`/`dmR`);
* **every frame law is a geometric rule** (`riRefl`, `riTrans`, `rmRefl`,
  `rmTrans`, `subMi`, `falHered`, `squareR`, `serialC`, `counit1`, `counit2`) —
  so **fallibility is first-class syntax** (`fal` atoms, `falForward` as
  fragment-relative exfalso), which is exactly the "amend the calculus to take
  fallibility" requirement;
* logical rules: `impL`/`impR` (forward along `Ri`), `coimpL`/`coimpR` (backward
  along `Ri`), `laxL`/`laxR` via `dm`, `colaxL`/`colaxR` backward along `Rc`.

**PROVED and pinned**: `biLaxL_sound` (all 28 rules, over the `LSeq.Valid`
semantics with substitutions `ρ : Label → W`, fresh-label updates handled by
`Function.update` and pointwise freshness lemmas) and
`biLaxL_sound_consequence` (labelled derivations certify local consequence of
an ordinary sequent).  **No cut rule exists in the system**, so cut-freeness is
not a theorem to prove but a property of the presentation; what remains is
CUT ADMISSIBILITY (§4 below).

## 3. The screens (`BiLax/Screens.lean`, `lake exe bilaxscreen`)

Exhaustive over well-formed frames, all with non-vacuity counters.  Latest run
(after the `Rc` repair):

| n | well-formed | `square_c` fails | `counit_c` fails | `serial_c` fails |
|---|---|---|---|---|
| 1 | 16 | 0 | 0 | 8 |
| 2 | 6,144 | 1,728 | 2,688 | 4,128 |

| screen | n=1 | n=2 |
|---|---|---|
| S-P persistence of `◯∃` given `square_c` | 32 pass, 0 fail | 12,992 pass, 0 fail |
| S-P on `square_c`-FAILING frames | — | 2,304 pass, **2,112 FAIL** |
| S-C counit | 16 pass, 0 fail | 2,464 pass, 0 fail |
| S-U unit | 16 pass, 0 fail | 2,464 pass, 0 fail |
| S-A adjunction (iff, all upset pairs) | 16 pass, 0 fail | 2,464 pass, 0 fail |
| S-R co-residuation (all upset pairs) | 16 pass, 0 fail | 2,464 pass, 0 fail |
| S-F `ff` forced nowhere | 16 pass, 0 fail | 2,464 pass, 0 fail |
| non-vacuity `nonId` (`◯∃ ≠ id`) | 8 | 4,224 (S-P), 96 (law-satisfying) |

Readings: the 2,112 persistence failures on `square_c`-failing frames witness the
law's **necessity** (it is exact, not merely sufficient); the three non-zero
"fails" columns show the laws are **not free** (so `BiModel` is a proper
subclass of the repo's models — every lifting statement must carry them); and
`nonId > 0` is the non-vacuity check that the first design failed.

## 4. What is NOT done, stated plainly

* **Cut admissibility for `BiLaxL`** — OPEN.  The plan's §6.2(ii) obligation.
  Negri's standard argument should transcribe; until it is machine-checked, no
  claim about cut is made.
* **`BiLaxND ⊣⊢ BiLaxL`** — OPEN, and coupled to the above (the ND→labelled
  direction routes through cut).  Both systems are independently sound, which is
  what round 1 needed; the equivalence is round 2's opening item.
* **Conservativity over PLL** — screens NOT run: they need a BiLax prover, and
  the labelled calculus is the natural search vehicle (round 2).  What IS proved
  is the semantic half, `emb_sound`: every `LaxND` derivation is a bi-lax
  consequence of the embedded sequent.
* **The interpolation-risk screen** [H§8.1] — deferred to round 2 for the same
  reason (it needs search).
* **Completeness** — round 2; design below.

## 5. The completeness design report (round 2's scope)

**Route: saturation-with-countermodel-extraction, not a canonical model.**  The
labelled calculus was chosen precisely so that a failed proof search *is* a
countermodel: a saturated open branch gives the label graph (worlds and
relations `Ri`, `Rm`, `Rc`, `F` read off the atoms) and the valuation (atoms in
`fm` position on the left), and completeness is the statement that a saturated
open branch satisfies every left formula and refutes every right one.  This is
the payoff Matthew asked for — depth-first refutation instead of breadth-first
battery search — and it needs no Lindenbaum/Zorn machinery.

Obligations, in dependency order:

1. **Saturation conditions** — one per rule, phrased on a set of labelled
   formulas + atoms; the geometric rules give closure conditions on the graph
   (reflexivity, transitivity, `Rm ⊆ Ri`, `F`-heredity, `square_c`, `serial_c`,
   `counit_c` — the last two GENERATE fresh labels, so saturation is infinitary
   in general and the termination question is item 4).
2. **The extraction lemma** — a saturated open branch defines a `BiModel`
   (all three laws hold by construction from the closure conditions) and the
   truth lemma: `fm A` on the left ⟹ forced; on the right ⟹ refuted.  The
   `dm` sort needs its own two clauses.  Expected difficulty: the `⤙` and `◯∃`
   cases, where the witness is a PREDECESSOR — the branch must have generated it
   (that is what `coimpL`/`colaxL` do) and no later rule may destroy it
   (monotonicity of the branch).
3. **Completeness** = contraposition of 2 with soundness.
4. **Termination / decidability** — the serious risk.  `serialC` and `counit1`
   generate fresh labels unconditionally, so naive saturation diverges; the
   standard fix is to fire them only when demanded (a *lazy* or *demand-driven*
   presentation) plus a loop-check/blocking condition on repeated label types.
   This is where the Pinto–Uustalu system's own termination analysis must be
   read and adapted `[LITERATURE — VERIFY]`, and it is the gate on the
   RN(◯,{}) application: a non-terminating search is not a countermodel finder.
5. **The disproof bridge** (plan §7.2) and the co-derivation searcher (§7.3)
   follow, aimed at the catalogue's 109 flags.

**Estimate**: item 1–3 one focused session if the truth lemma's retrospective
cases behave; item 4 is genuinely open-ended and should be screened (does the
demand-driven variant terminate on the catalogue's actual formulas?) before it
is scoped.

## 6. Round-1 verdict

Round 1's deliverables 1 (soundness of both calculi, pinned), the semantic
theorem package, and the screens are **DONE**; deliverables 2–3 and 5 are
explicitly deferred with reasons; deliverable 4 (this design report) is
delivered.  The round produced one certified refutation of its own first design,
which is the outcome the screens-before-proofs discipline exists to buy.
