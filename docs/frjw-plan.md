# FRJW — the calculus, and the campaign

**Status:** W1–W4 landed — see the divergence log. The completeness
route changed on 2026-08-31; the old W5/W6 are stood down, see the last
section.
**Branch:** `frjw-dev`. **Predecessor:** FRJV (`FRJ/CalculusV.lean`).

Terminology: an object of `FRJWr` / `FRJWi` is a **disproof** (regular /
irregular). "Proof" is reserved for the provability calculi — Gbu◯,
LaxND, G4c, SC.

---

## 1. What FRJW is

FRJW is FRJV with one rule added and one deleted.

**Added — `Lift` (working name `(R^bar)`).** A regular disproof becomes
an irregular one over any retained `Ĝ`-context inside the closure of its
own context:

        Γ ⇒ C          Θ ⊆ Ĝ,   Θ ⊆ Cl(Γ)
    ─────────────────────────────────────────  (Lift)
                   ∅ ; Θ → C

As a constructor:

```lean
| lift {t : Tag} {Γ Θ : List Form} {C : Form}
    (d : FRJWr G t Γ C)
    (hΘ : ∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) :
    FRJWi G [] Θ C
```

**Deleted — `⊃∉` (`impNotIn`).** It is `Lift` composed with `⊃∈`:
from `d : Γ ⇒ B` and `Clo Γ A`, `⊃∈` gives `Γ ⇒ A ⊃ B` with no side
condition, and `Lift` gives `∅ ; Θ → A ⊃ B`. `⊃∉`'s extra condition
`¬ Cl(Θ) ∋ A` is not needed.

**Kept — `◯∉` (`circNotIn`).** Not redundant: its premise is a regular
disproof of `Z`, not of `◯Z`, so it climbs the modality and `Lift` does
not. Every other FRJV rule is unchanged.

---

## 2. Why `Lift` is the right addition

Three facts, all machine-checked, `[propext, Quot.sound]`.

**(a) The irregular duality has a hole.** For every `G`, `Z`, `Σ`, `Θ`,
FRJV has no irregular disproof of `◯(◯Z ⊃ Z)`
(`FRJ.V.WCounter.no_irregular_circ_imp_self`): only `◯∉` and `Ax^I◯`
conclude a `◯` goal; `◯∉` needs a cleanly tagged regular disproof of
`◯Z ⊃ Z`, forbidden by `not_clean_imp_self`, and `Ax^I◯` needs
`classForce ats (◯Z ⊃ Z) = false`, impossible because `◯` is transparent
to `classForce` and the body is `¬x ∨ x`.

**(b) Gbu◯ cannot fill it, and must not.** `∅ →g ◯(◯p ⊃ p)` is not
derivable (`FRJ.Gbu.not_gbuIC_Gcc`) — `soundIC` gives the irregular
judgment the same reading as the regular one, `∀w. w ⊩ Ψ → w ⊩ C`, and
`◯(◯p ⊃ p)` is refuted by the model `GccWitness` extracts.

**(c) A regular disproof exists but cannot be used.** `provableV_Gcc`
disproves `◯(◯p ⊃ p)` by the barren `⋈^◯` join. It is unusable where an
irregular disproof is required, because the two judgments assert
different things:

* a *regular* disproof is existential — `modR d` builds one model and
  `lemma39R` says `C` fails at its root;
* an *irregular* disproof is a schema — by `lemma39I`, `C` fails at ANY
  infallible world `w` of ANY premodel with `lbl w ⊆ Cl(Σ ++ Θ)`, the
  disproof's regular components grafted above `w`, and `w ⊩ Σ ∩ sfm C`.

The joins `⋈^At`, `⋈^∨`, `⋈^◯` build a FRESH root and need their premise
formulas to fail *there* — at a world the join built. Only the schema
reading gives that, which is why join premises are irregular.

`Lift` is exactly the bridge from (c) to the schema, and it is sound
because forcing is monotone: the component's root sits above `w` and
refutes `C`, so `w` refutes `C`.

---

## 3. What is already checked

| fact | name | file |
|---|---|---|
| `Lift`'s `lemma39I` clause | `not_force_of_rootAbove` | `wip/rbar.lean` |
| no irregular FRJV disproof of `◯(◯Z ⊃ Z)` | `no_irregular_circ_imp_self` | `wip/gbu_weakening.lean` |
| `∅ →g ◯(◯p ⊃ p)` not Gbu◯-provable | `not_gbuIC_Gcc` | `wip/gbu_search_circ.lean` |
| regular FRJV disproof of `◯(◯p ⊃ p)` | `provableV_Gcc` | `wip/gbu_search_circ.lean` |
| its extracted countermodel, dumped | `dumpModel` / `countermodel_Gcc` | `wip/gbu_search_circ.lean` |

`not_force_of_rootAbove` was negative-tested: the same one-line proof does NOT
typecheck for a tagless `◯∉`, so the gate discriminates.

---

## 4. The task in hand

**Before the first build**, in a fresh Claude worktree, clone the Lake cache
from the repository root — it is an APFS clone, so it is instant, and without
it the first build recompiles the whole development:

```
cp -Rc <repo-root>/.lake .lake
```

The repo root is `lax-logic-in-lean`, not `LaxLogic/`. Push with
`scripts/campaign-push.sh frjw-dev`; never push the local `claude/…`
worktree branch name.

Then, in order. Each stage ends when its deliverable is pushed.

**W1 — transcribe.** `FRJ/CalculusW.lean`: copy `FRJVr`/`FRJVi`, add
`lift`, delete `impNotIn`. `#slime` must report 0; `#rules` must show one
constructor per rule.

**W2 — conservativity.** Every FRJV disproof is an FRJW disproof:

    FRJVr G t Γ C → FRJWr G t Γ C        FRJVi G Σ Θ C → FRJWi G Σ Θ C

The only non-trivial case is `impNotIn`, reconstructed as `lift (impIn d hA _) hTh`.
Do this BEFORE soundness — it is what licenses reusing the FRJV corpus.

**W3 — soundness.** Port `lemma39R` / `lemma39I` with `RegIdx (lift d) := Unit`,
`preI (lift d) _ := preR d`. The new `lemma39I` case is `not_force_of_rootAbove`,
already proved. **The real obligation is not this case but the joins':**
each join must still discharge

    RootAbove P hP w (preI (prem j) i) …

for components now supplied by `lift`. `lift`'s `hΘ` is verbatim `⊃∉`'s
`hTh`, so the interface is unchanged — but that is an argument, not a
proof, and W3 is where it gets checked.

**W4 — the duality gap closes.** Show `∅ ; ∅ → ◯(◯p ⊃ p)` is an FRJW
disproof (`lift GccWitness.2 (by simp)`), i.e. the (a)/(b) mismatch is
gone. This is the test that the whole exercise was for.

**W5 — the two invertibility clauses.** Both should now be immediate:

    (∨-inv)  D ▷ (Ω ⇒g C₁) ∧ D ▷ (Ω ⇒g C₂)  ⟹  D ▷ (Ω ⇒g C₁ ∨ C₂)
    (★)      D ▷ (Ω ⇒g Z)  ⟹  D ▷ (Ω ⇒g ◯Z)      (Ω ⊆ Ĝ_at ∪ Ĝ_imp, Υ dead)

`(∨-inv)` by `⋈^∨` on two `lift` premises; `(★)` by `lift` then
`gbuSuccCirc`. That these two fall out is the coherence check on the
design: they were the search's two unmet needs, and neither was part of
the motivation for `Lift`.

**W6 — completeness.** Rebuild the Gbu◯ search over FRJW. Not before W5.

---

## 5. Screen before you build

Per `METHOD.md`, statements get an extensional attack before a proof is
scoped. For FRJW the two live risks are:

1. **Termination of search, not soundness.** `Lift` makes `EvalI` at
   least as strong as `EvalR` over `Ĝ`-contexts, so the `∨` and `◯`
   branches take the join route far more often. Re-check the `Wg`
   measure against the new traffic before W6.
2. **`RootAbove` at the joins** (W3). Build the smallest join over a
   `lift` premise by hand and watch it typecheck, before porting all
   eight join constructors.

Then the standard four directions, in order: corpus replay (the ρ-sweep
harness `lake exe frjvrun sweep`, ported), boundary cells (`⊥`, empty
contexts, `Θ = ∅`, `Γ = ∅`), frontier extension, branch coverage.

---

## 6. Not in scope

`searchO` and its two supplies `BigAnte` / `CleanReg` are RETIRED, not
inherited: `residues_unsatisfiable` shows the pair is contradictory at
`◯(◯p ⊃ p)`, so the theorem is vacuous for any modal `G`. Do not attempt
to discharge either. The FRJW search of W6 is built fresh, on the
invariant `¬ D ▷ (Ω ⇒g C)` that W5's two clauses make propagable.

---

## Fidelity / divergence log

FRJW is a NEW calculus: fresh proofs of everything, soundness included;
no FRJV theorem migrates by renaming or aliasing; FRJV files stay
byte-for-byte untouched.  A later merge back into FRJV would produce a
third name (FRJ◯).  This log records divergence from **FRJV** (the
predecessor); divergence from the paper is FRJV's own log
(`docs/refat-plan.md`, V1–V5), which carries over unchanged.

| # | Divergence from FRJV | Where | Why |
|---|---|---|---|
| W1 | `lift` added to the irregular family: `Γ ⇒ C` with `Θ ⊆ Ĝ`, `Θ ⊆ Cl(Γ)` yields `∅ ; Θ → C` | CalculusW | ours; the irregular duality hole at `◯(◯Z ⊃ Z)` (§2) |
| W2 | `⊃∉` (`impNotIn`) deleted; reconstructed as `lift (impIn d hA hgoal) hTh` — its extra condition `¬ Cl(Θ) ∋ A` is dropped, not reconstructed | CalculusW | redundant given `lift` (§1) |
| W3 | `DisprovableW` replaces the `ProvableV`-pattern name for `∃ t Γ, Nonempty (FRJWr G t Γ G)` | CalculusW | terminology: an FRJW object is a DISPROOF; `ProvableV G` read the wrong way round |
| W4 | everything else transcribed verbatim — machine-diffed: the `#rules` tables of the two families are identical modulo the V→W rename outside the `⊃∉`/`lift` swap (2026-08-31) | CalculusW | fidelity gate |
| W5 | `FRJ.W.RuleName` replaces `impNotIn` by `lift` (the shared `FRJ.RuleName` stays untouched); `lift` takes `⊃∉`'s slot everywhere in the step/occurrence/extraction/soundness layers: exception list of Lemma 3.4(i), `RegIdx = Unit`, `preI = preR d`; the `lemma39I` case is `(R^bar)`'s clause from `wip/rbar.lean`, using none of `lift`'s side conditions | StepW, ExtractW, SoundW | the W3 port (2026-08-31) |

Stage-W1 gates in `FRJ/CalculusW.lean`: `#slime` pinned by
`#guard_msgs` at 0 computed indices for both families (13 + 8
constructors); the pin was watched to fail on an injected mismatch
before shipping.  `#rules` output inspected and diffed as above.

---

## Route change (2026-08-31, Matthew): completeness via LJF◯ focalisation

**Decision.**  The completeness of `Gbu◯(G)` is NOT to be pursued
through the FRJ database/search route (the old W5/W6).  That route has
repeatedly failed at the same focalization-shaped obligations
(`searchO`/`BigAnte`/`CleanReg` retired by `residues_unsatisfiable`;
several failed FRJV-completeness campaigns before that).  Instead:
**go via LJF◯ focalisation**, which is already PROVED —

    bridge_iff : Nonempty (LaxND Γ φ)
                   ↔ Nonempty (Inv (Γ.map negOfO) [] .tru (negOfO φ))

`LJF/OBridge.lean`, ON `frjw-dev` ALREADY (the calculus map's "unmerged
branch t1" note was stale; corrected), pins `[propext, Quot.sound]`, no
choice.  `LaxND ↔ SC` and cut elimination are also mechanised
(`SC_to_ND`, `ND_to_SC`, `cutElimination`, `LaxLogic/PLLSequent.lean`).

**Target statement** (syntactic end to end; `ofPLL` is the mechanised
`PLLFormula ≃ Form` of `FRJ/Bridge.lean`):

    gbuC_complete :  Nonempty (LaxND [] φ)  →  ProvableGbuC (ofPLL φ)

by composing `bridge_iff (→)` with a NEW structural translation `T`
from the four LJF◯ judgments into the two Gbu◯ ones.  Because LJF◯
derivations are already focused, `T` is a recursion, not a
focalization proof — the one focalization proof in the repository is
reused, not re-done.

**Judgment map, first draft (F1 settles it):**

| LJF◯ | Gbu◯ |
|---|---|
| `Inv Γ Ω j N` (inversion) | left-invertible spine: `landL`/`lorL`/`lbot`/`lcirc`(+`I`) |
| `Stab Γ .tru P` | `GbuRC` (re-entry point) |
| `RFocus Γ j P` (right focus) | `GbuIC` |
| `LFoc Γ N j P` (left focus) | nested `limpL` / `limpLI` spine |
| flag `.lax`, `circR`/`laxOf`/`circL` | `rcirc`/`rcircI`/`lcirc`/`lcircI` |

**Risk register — screen these BEFORE building `T` (counterexample
first, per METHOD.md):**

* **R1 — antecedent hyper-focus.**  `LFoc.impL`'s first premise is a
  full `Stab Γ .tru Q` (may itself left-focus); Gbu◯'s `limpL` demands
  the antecedent IRREGULAR (`GbuIC`, no left rules off the `◯`-goal
  fragment).  Chained modus ponens is handled in Gbu◯ by ORDERING the
  `limpL`s, so `T` at this case needs either a reordering/permutation
  lemma or a proof that `focalizeSCO`'s output is already orderly.  If
  neither holds at some cell, hunt a kernel-checked
  Gbu◯-underivability witness there — that outcome means Gbu◯ needs a
  rule amendment, which goes to Matthew as a displayed rule first.
* **R2 — `limpLI`'s size condition** `A.hasCirc = false ∨ |A| < |◯C|`
  at the lax flag: a focused derivation may demand an irregular
  left-implication step with a large modal antecedent.  Same discipline:
  drive the case, extract the candidate cell on failure, countermodel
  before any rule change.
* **R3 — plumbing.**  (i) `Sf^L/Sf^R` threading: Gbu◯'s modal
  constructors carry membership conditions; supply an LJF◯ subformula
  invariant (`LJF/OUniverse.lean`) or thread hypotheses through `T`.
  (ii) `Clo` at `rimpI`/`rimpNI`: LJF◯'s `impR` always extends the
  context, `rimpI` never does — `T` needs a `Clo`-absorption
  (weakening-like) admissibility for `GbuRC`/`GbuIC`.

**Stages (replacing the completeness role of W5/W6):**

* **F1 — judgment map + statements.**  The displayed statement of `T`
  for each judgment, with side-condition threading; put to Matthew
  before building.
* **F2 — screen R1–R3** as above; each screen failure is a RESULT
  (candidate incompleteness cell for Gbu◯), not a blocker.
* **F3 — build `T`**, mutual recursion, pins.
* **F4 — compose** `gbuC_complete`; corollary with `soundRC`: Gbu◯ is
  complete in itself, and the ◯L/◯R admissibility questions of
  `wip/gbu_ndrules.lean` dissolve (they become corollaries).

**Stood down, not deleted:** the database route (old W5/W6).  FRJW
W1–W4 are banked and untouched — FRJW remains the disproof/countermodel
side (`soundnessW`).  Whether to rebuild the FRJW search (decision
procedure) after F4 is a separate decision for Matthew.  The `Eval*`
lemmas over FRJV and `wip/gbu_db.lean` stay as they are; nothing new is
built on them.

### F-stage record (2026-08-31, evening)

**F4 PROVED, kernel-checked, choice-free.**  In
`wip/gbu_ljfo.lean` (support: `wip/gbu_ljfo_support.lean`, transport:
`wip/gbu_ljfo_transport.lean`):

    gbuC_complete : Nonempty (LaxND [] φ) → ProvableGbuC (ofPLL φ)
    -- #guard_msgs-pinned: [propext, Quot.sound]

Composition: `bridge_iff` (LJF◯ focalisation, `LJF/OBridge.lean`) →
`tInv` (the F3 translation) → `nf_negOfO` goal rewrite.

**F3 architecture as built** (two designs died in F2 screens; the
surviving one):

* CPS-hoisting: `GbuIC` is not monotone (`gbuIC_not_monotone`) and has
  no modus ponens (`gbuIC_no_mp`) — both kernel-checked screens in
  `wip/gbu_ljfo_support.lean` — so every irregular delivery is produced
  at the exact consumption context and moved only by `≐`-transport.
* MODE-GENERIC traversal (`Kit`): one mutual recursion serves the
  regular target (`regKit`: `limpL/lorL/landL/lbot`) and, below any
  `◯`-opening, the irregular `◯`-goal target (`irrKit`:
  `limpLI/lorLI/landLI/lbotI`).  A `.lax` left-focus spine builds
  entirely inside the irregular judgment (`combSpineLaxI`); `lcircI` is
  its `circL` context bridge — the regular judgment has no bridge at a
  non-`◯` goal, which forces the mode switch.
* The licenced `|◯C|` adaptation of `GbuIC.limpLI` (`A ∈ Sf^R G`
  replacing the size bound; cell and licence comment at the rule in
  `wip/gbu_circ.lean`) is consumed at exactly one place:
  `irrKit.impOpen`.
* `R∧ᵢ`'s two same-context premises: `combPair` retries to a
  `≐`-stable context, fuel-founded on the count of universe formulas
  (`U ⊇ Sf^L G`) missing from the context (`satMeasure_lt`).
* The unsound corner (right focus, lax, on `↓↑P`) is excluded by the
  `noDUP`/`noDUN` invariant; `negOfO` images satisfy it
  (`noDUN_negOfO`).
* Termination: a shallow derivation weight `wS/wRF/wLF/wI` (auto
  `sizeOf` reduces badly), lexicographic `(2·w, fuel)` with `2·w+1`
  offsets for the regulariser and the pair.

The ◯L/◯R admissibility questions of `wip/gbu_ndrules.lean` are now
corollaries, as predicted.  Old W5/W6 database route remains stood
down.

**Sequent form** (same evening, Matthew's request): via the deduction
theorem for `LaxND` (`dedAll`, iterated `⊃`-introduction) and a
curried-to-`∧` conversion (`curryToAnd`, using only `iden`, `⊃I/⊃E`,
`∧E`, `rename`):

    gbuC_sequent_complete :
      Nonempty (LaxND Γ φ) → ProvableGbuC (ofPLL (bigAnd Γ ⊃ φ))

`#guard_msgs`-pinned [propext, Quot.sound] (a first draft's `tauto`
pulled Classical.choice; replaced by a constructive membership term).

### FRJW completeness thread (opened 2026-08-31, late evening)

The target is the constructive dichotomy (no declaration exists — OPEN):

    decideGbuW : ∀ G, ProvableGbuC G ⊕ DisprovableW G

which yields FRJW completeness (via `pll_of_provableGbuC`) and the
exhaustiveness half of the Gbu◯/FRJW duality.  Done so far:

* **Exclusion half BANKED** (`wip/gbu_frjw_exclusion.lean`, both
  directions, [propext, Quot.sound]): a Gbu◯ proof and an FRJW
  disproof of the same goal cannot coexist.
* **W-engine built and registered**: `FRJ/Search/OpsW.lean` (`wOps`),
  register entry `Engines.frjwRefute`, TOOLS.md row.  Smoke: closes
  the Gcc gap computationally (irregular row via `Lift` where the
  V-engine provably has none), ◯-free agreement with `vOps`, no false
  hits on valid cells.

Next, in order (statement-first, per METHOD.md):
1. Cell-level dichotomy statement drafted from Theorem 8/9's
   `SearchOk`/`EvalR`/`EvalI` shapes over a W-database; the old
   supplies `BigAnte`/`CleanReg` are FRJV-specific and REFUTED — the
   W-analogues must be drafted fresh (`Lift` is expected to be what
   discharges the old `BigAnte`-shaped demands).
2. Extensional attack BEFORE any proof build: corpus + boundary +
   Gcc family + frontier strata through the W-engine, with the pinned
   `ProvableGbuC ⇔ PLL` equivalence (via the G4c decider) as
   ground-truth oracle — every cell now has a definite expected side.
   Needs a `frjvrun` subcommand (or sibling exe) for compiled runs.
3. Only then scope `decideGbuW`, templating Theorem 8/9's recursion
   with the saturation measure (`satMeasure_lt` pattern).

Frame-conditioned FRJV completeness routes (endpoints, cone-grounded):
judged not worth significant effort (Matthew, 2026-08-31); at most a
cheap reconnaissance whether `Lift` discharges their condition sites.

**2026-09-01**: cell-level statement drafted, revised (tag EXPLICIT in
the regular database sequent — Matthew's call, and the tagless draft
was defective: the ◯-manufacture needs tag-aware (DB2); the `regC`
stratum dissolves into the derived pledged query `WEvalRP`), and
LANDED as `wip/gbu_frjw_dichotomy.lean` (defs only; `searchW` /
`gbu_frjw_dichotomy` / `decideGbuW` remain OPEN, no declarations).
Screening runner `lake exe wscreen` (`tools/WScreen.lean`): 18/18 PASS
including Gcr, Gcc, and the big-antecedent cell; no flags, no alarms.
NEXT DECISION PENDING (Matthew): Prop-∃ vs Type/Σ packaging of the
statement layer before the proof build is scoped.

### searchW proof architecture (2026-09-01, from the searchO survey)

The W-database lemma stack is COMPLETE and green
(`wip/gbu_frjw_db.lean`, `wip/gbu_frjw_circdb.lean`): Lemmas 9(i–xiv),
11, 12, 13/14, with `gbuInv9` Lift-based (stronger), `gbuInv12/13` on
the pledged query `WEvalRP` (no `TagClean` supply), `gbuInvLift` (the
general regular→irregular transfer), and `gbuInv14` extended by the
`lift` case.

The searchO transcription is mechanical EXCEPT at one seam, the
irregular `◯`-critical cell, where V punted to `BigAnte` (false) and
`cirr`/`CleanReg` (false).  The W-resolution, from the survey:

* All `◯`-row manufacture now goes through `refutedCleanly_circ`
  (barren `⋈^◯`) + `Lift`/`◯∉` — no pledged query is NEEDED by any
  caller, so the clean mode stays dead.
* The `Υ`-loop (antecedent queries) has a MEASURE problem only in the
  irregular mode (no mode to drop).  Resolution: run the `Υ`-loop in
  the REGULAR mode before every reg→irr entry (mode-drop pays for the
  antecedent recursions), and THREAD the `Υ`-facts through the
  irregular invariant at the `Ĝ`-ancestor:

      WIrrInvU G D Ω C := ¬ WEvalI D Ω C ∧
        ∃ Ω₀ ⊆ Ĝ, cover ∧ ¬ WEvalI D Ω₀ C ∧
          (∀ A B, imp A B ∈ Ω₀ → WEvalI D Ω₀ A)      -- hups, NEW

  Goal-steps keep `Ω₀` verbatim; left-openings ride the ancestor; the
  `◯`-critical manufacture happens AT `Ω₀` with `hups(Ω₀)` in hand.
* PUBLIC STATEMENT DELTA (for Matthew): the reg clause of `WSearchOk`
  and the root dichotomy are UNTOUCHED; the irr clause's invariant
  must carry the `hups` conjunct (a hypothesis-strengthening).  The
  proof will be built against the aux spec; the public irr clause is
  then stated at the strengthened invariant.

### The chase-revisit residual: full mechanism map (2026-09-01)

`searchW` (`wip/gbu_frjw_search.lean`, uncommitted) compiles with ONE
`sorry`.  The built design replaced the `hups` threading above (which
is hereby superseded): the `Υ`-loop runs IN the irregular mode with a
visited-set `V` of chased antecedents, measure

    wgW G reg Ψ C V = (unclosed G Ψ, |Sf^R(G) ∖ V|, tpC reg C, seqSize Ψ C)

The one open branch is the chase-REVISIT corner, with hypotheses:
critical cell `Ψ ⊆ Ĝ_at ∪ Ĝ_imp`, goal `◯Z ∈ sfR G`, and

    heZ  : WEvalI D Ψ Z                 (a Z-row covers Ψ)
    hne  : ¬ WEvalI D Ψ (◯Z)            (no ◯Z-row)
    hnocm: no classical countermodel     (axIC unavailable)
    hallQ: every A = ante(Y), Y ∈ imp(Ψ): refuted ∨ (hasCirc ∧
           ¬|A| < |◯Z| ∧ A ∈ V);  some such A unrefuted (stuck)
    hnrp : ¬ WEvalRP D Ψ Z              (no pledged regular Z-row)

Constructor sweep (kernel fact): irregular `◯`-rhs rows come ONLY from
`lift`/`◯∉` (both blocked by `hnrp`), `axIC` (blocked by `hnocm`), and
`⋈^◯` + `lift`.  So the ⋈^◯-join is the unique remaining manufacture.

**The Gx provenance, decoded.**  The engine's row for the constructed
cell `Gx = ((◯r⊃b) ∧ ¬¬r) ⊃ ◯r` at `Ψ = {◯r⊃b, ¬¬r}` is the join over
the family `{axI r, impInI(axI ⊥) : ¬r}` with BOTH implications
retained by the `KeptChain`: `◯r⊃b` because `RefAt` descends `◯r → r ∈
Υ` (the circ-clause, cone = true), `¬¬r` because `¬r ∈ Υ` (its
refutation is in the family).  A `Ψ`-implication is covered by the
join in exactly one of THREE ways:

  (i)  its antecedent is refuted: the antecedent's row joins the
       family, `.ups` keeps the implication;
  (ii) its antecedent is `RefAt`-reachable over `Υ` (circ/and/imp
       descent bottoming in `Υ` or `Clo`);
  (iii) its CONSEQUENT is `Clo`-available in the join context
       (`Clo`'s imp-clause; the `b`-mechanism in the Gx row).

**The corner sweep** (`wip/cornersweep.lean`, output `wip/cornersweep_out.txt`, V-free
overapproximation, 15 adversarial formulas, every critical sub-cell,
engine + G4c oracle): exactly TWO corner-shaped cells in the whole
corpus, both the licence cell `Ψ = {p, ◯p⊃r} , ◯r` (in Glic and Glw),
stuck antecedent `◯p`, with (i),(ii),(iii) ALL false — and the stuck
antecedent ORACLE-DERIVABLE at `Ψ` (`p ⊢ ◯p`), i.e. resolved by the
chase at first visit.  ZERO cells with a stuck antecedent
underivable-and-unrefuted: no counterexample to the dichotomy.
Licence-shaped cells are derivation-side; the corner is reachable only
as a REVISIT (stuck antecedent already in `V`), which no corpus
formula realises.

**Open kernels for closing the sorry** (V carries no invariant, so
revisit-unreachability is at present unprovable):

  K1  The V-invariant `∀ A ∈ V, RefAt true [C] Ψ A` (goal-path
      reachability) is preserved by every step of the search EXCEPT
      descent into a disjunct when BOTH disjuncts are unrefuted
      (RefAt's or-clause needs both sides).
  K2  Rebasing the invariant's `Clo Ψ` side conditions onto the join
      context needs a kept-chain ordering; mutually-referencing stuck
      implications are not obviously orderable.
  K3  `hJ2` (Σ-zone implications need `Υ`-antecedents) blocks families
      with Σ-dirty rows.  For PRIME `Z` the single-row family is
      Σ-empty (`st_nil_of_prime`: only `axI`/`lift` produce prime
      rhs), which covers every corner the sweep found.  The general
      fix would relax `hJ2` to `RefAt`-descent — a CALCULUS change,
      requiring sign-off and a re-proof of `soundnessW`'s join case.

Decision pending (Matthew): (a) build the V-invariant motive with
K1/K2 as stated risks; (b) propose the `hJ2` relaxation first (kills
K3 and most of K2); (c) both.
