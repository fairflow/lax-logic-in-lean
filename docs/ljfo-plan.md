# LJF◯: uniform interpolation for PLL — the campaign plan

*2026-08-09 evening. Matthew's directive: go for UI for the whole of PLL on
the existing work (simp round 1 base), round D postponed. This document is
the campaign opener: the calculus extension is settled, the interpolant
clause set is drafted as candidates, and the paper-level minimality
obligations that must be run before mechanising are listed. Claim
discipline: UI for PLL is OPEN (Iemhoff's proof rests on G4iLL, refuted
in-repo); this campaign is an attempt at the first proof.*

## 1. What changes in the calculus (settled)

The design is `PLLFocused.lean`'s, already exercised by the blocker
derivation (`wip/ljf-lax-blocker.lean`, commit d9041f3):

* Syntax: `Neg` gains `circ : Pos → Neg`. Nothing else.
* A flag `JD ::= tru | lax` on all four judgments: `Stab Γ j P`,
  `RFocus Γ j P`, `LFoc Γ N j P`, `Inv Γ Ω j N`.
* Rules: `circL` is the **only rule that reads the flag** (left focus on
  `circ Q` releases `Q` into inversion, at `lax` only); `circR` *sets* its
  premise to `lax` from either flag (goal inversion of `circ Q`);
  `impR`/`andR` are `tru`-only (at `lax` they would assert the converse of
  K, REFUTED in-repo); `impL` proves its argument at `tru`; every other
  rule threads `j` untouched.
* Contexts stay persistent (`lfoc` selects by membership) — this is what
  dissolves the G4iLL contraction failure, machine-checked at the blocker.

**The lax goal is definable**: `Γ ⊢lax P` iff `Γ ⊢tru ↓◯P`-wise (circR is
invertible). Consequence, load-bearing for the whole design: **`interp`
needs no flag parameter.** The interpolant of a lax-goal sequent is the
interpolant at the `◯`-goal; only the derivation-traversal functions (the
`T*`/`U*` families) carry `j` as an index.

## 2. The interpolant extension (candidates — not yet run through (ii))

### Weights

`w(circ Q) = wPos Q + 1`. Justification (termination of the box fire):
opening consumes `3^(wQ+1)` from the station and adds `↑Q` to `todo` at
cost `2·3^wQ`, and `2·3^w < 3^(w+1)` — the same shape as `dec_fire`.
The `◯`-implication `↓◯Q′ ⊃ N` gets `w = wPos Q′ + 1 + 1 + wNeg N + 1`
by the existing `imp`/`down` bookkeeping, no new constant.

### New parked shapes

`ParkedN` gains two constructors: boxes `circ Q`, and `◯`-implications
`.imp (.down (.circ Q′)) N` — the `L◯→` territory where G4iLL broke.
Neither is left-invertible, so both park; the aggregate phase gains their
dispatch rows.

### ∃p aggregate (goal `none`), new conjuncts

For each parked member at `(X, rest) ∈ splits done`:

* **Box opening** (`X = circ Q`):  `circ (↓ E_p(↑Q :: rest))` — the
  strongest lax consequence: everything the opened station yields, boxed.
  The box is consumed and its content added; a second opening of the same
  box adds nothing (its products are already present) — the saturation
  argument owed in §3.
* **`◯`-implication fire** (`X = ↓◯Q′ ⊃ N`), the Dyckhoff-analogue pair,
  following the corrected G4s clauses (`PLLG4UI.lean`'s two lax firing
  clauses, R◯→″/L◯→″):
  `(↓ A_p([residual] , rest ⇒ ◯Q′) ⊃ E_p(N :: rest)) ∧ E_p(residual station)`
  — the same guarded-pair shape as the existing Dyckhoff conjunct, with
  the antecedent demand now at a `◯`-goal. Expect the E-res third
  component to be forced again, as it was for the intuitionistic Dyckhoff
  clause.

### ∀p aggregate, new goal shape `circ Q`

The `◯`-goal station is the *lax* station — strictly more attacks than a
`tru` station, because `circL` is enabled:

* the direct row: `interp p [] done (some (.up Q))` (prove `Q` truly;
  laxness for free; same station, smaller goal — no guard, like the
  `∧`-goal rows);
* for each parked box `circ R`: the opening attack, **E-guarded**:
  `↓E_p(↑R :: rest) ⊃ A_p(↑R :: rest ⇒ circ Q)` — goal kept, station
  opened. The naked row is WRONG: see §3-results below, where the
  (ii)-induction forces the guard;
* the existing fire and Dyckhoff attack rows, unchanged;
* the `◯`-implication fire attacks, mirroring the E-side pair.

And ∀p at `tru` goal shapes: unchanged rows — boxes contribute **no**
attack at a `tru` goal (circL is flag-gated). This asymmetry *is* the
modal content of the interpolant.

## 3. Paper obligations before mechanising (the candidates method)

The method's rule, learned on the IPC campaign: run the (ii)-minimality
induction on paper per candidate clause and let failures dictate guards —
three definition changes were forced that way last time. To run before
writing `interp`'s new arms:

1. **Box clause, E-side**: minimality at a saturated station with a box —
   does every lax use of the station factor through
   `circ (↓E(↑Q :: rest))`? The circL case of the induction; where the
   E-guard analogue may be forced.
2. **◯-implication pair, both sides**: replay the Dyckhoff-dispatch
   analysis (`dykAnt`) with the antecedent at a `◯`-goal. The residual
   station argument (`dykCommute`'s analogue) must be re-derived in the
   flagged calculus — expect `circRel`-style shift-release lemmas.
3. **Saturation**: extend `findFire`/`Saturated` to the two new
   dispatches; check `findFire_none_spec` still characterises the
   saturated station (boxes unopened at `tru` stations are *properly*
   parked — they only matter at lax stations).
4. **The blocker as test #1**: replay `wip/ljf-lax-blocker.lean`'s term in
   the extended zero-import calculus verbatim.
5. **Converse-K must fail**: `⊬ (↓(Q ⊃ ↑?) …)` — the `impR`-at-`lax`
   restriction is what blocks it; a `decide`-style or hand check that the
   extended rules do NOT derive it (the restriction was found by soundness
   failing once already; keep it as a standing negative test).

## 3-results. First pass of the paper obligations (2026-08-09, late)

Run per the method: the (ii)-minimality induction on paper, per candidate
clause, before mechanising. Three findings and one conjecture.

**(a) The E-side box conjunct needs no guard.** At a saturated station
with `circ Q` parked at `(circ Q, rest) ∈ splits done`, a lax use of the
box (`circL`) is dispatched through the conjunct `◯(↓E(↑Q :: rest))`:
left-focus the interpolant's conjunct, `circL` it (the goal flag at the
use site is lax, matching the conjunct's own openability), `downL` puts
`E(↑Q :: rest)` in context, and the continuation crosses to the opened
station through the minimality recursion at strictly smaller measure —
`3^{wQ} + sum3 rest < 3^{wQ+1} + sum3 rest`, which is why
`w(circ Q) = wPos Q + 1`. Residual uses of the consumed box in the
continuation are cleaned by a `boxClean` analogue of `fireClean`: a later
`circL` on the same box re-derives its content from the opened station's
own products (`posRestore` territory). Single-premise clause, no
branching, no guard forced.

**(b) The A-side box-opening row MUST be guarded — first modal guard,
forced on paper.** With the naked row `A(↑R :: rest ⇒ ◯Q)`, the
(ii)-induction fails at the assembly step: the recursion at the opened
station yields the row from `E(↑R :: rest)` beside Δ, but the aggregate
is proved at `tru` from `E(done)`, and `E(done) ⊢tru E(↑R :: rest)` is
FALSE — only `◯E(↑R :: rest)` holds (that is the box conjunct itself).
Guarding repairs both directions at once:

    row_R  =  ↓E(↑R :: rest) ⊃ A(↑R :: rest ⇒ ◯Q)

*Soundness*: beside the station, at the lax goal open `circ R`; `eSound`
at the opened station supplies the guard; the implication yields the
opened-station `∀p`, which closes `◯Q` there. *Minimality*: `impR` (at
`tru` — the flag restriction is satisfied because rows are formulas
proved truly), assume the guard, and the recursion's conclusion is
exactly the body. This is the same failure-and-repair shape as the two
intuitionistic E-guards; the discipline extends to the modal rows
verbatim.

**(c) `findFire` and `Saturated` are unchanged.** Boxes and
`◯`-implications never fire during station reduction — like the Dyckhoff
implications they are parked shapes with *aggregate* rows, so saturation
is still exactly `findFire = none`, and `findFire_none_spec` is
untouched. The whole change to the station discipline is two new
`ParkedN` constructors.

**(d) Conjecture (the dykAnt-analogue, still to run).** The
`◯`-implication pair's antecedent demand `↓A(rest ⇒ ◯Q′) ⊃ …` should
need NO witness-box clause family: Iemhoff's `L◯→″` witness variants
existed because her `∀p` at a `◯`-succedent could not itself open boxes;
here the `◯`-goal aggregate *contains* the (guarded) opening rows, so the
witness variability is absorbed inside `A(⇒ ◯Q′)`. If this survives the
dykAnt-analogue paper pass, the modal clause set is strictly simpler than
the G4s-corrected one. This is the next obligation to run, together with
the flagged `dykCommute` (the argument `s : Stab … tru (↓circ Q′)`
analysed through `circR` into its lax phase).

Statement hygiene noted for stage 3: the saturated-case statements
(`SatE2`/`SatA2`) generalise over the flag `j` — the interpolant is
flag-free, the traversals are flag-indexed.

**(e) The dykAnt-analogue pass (2026-08-09, run to completion).** The
parked `◯`-implication is `X = ↓◯Q′ ⊃ N` at `(X, rest) ∈ splits done`; a
use of it is `impL s k` with `s : ⊢tru ↓◯Q′` over the station and `k` the
continuation through `N`. Four results:

1. **The antecedent demand sits at `rest` — `X` consumed, nothing
   retained, no residual.** The analysis of `s` (the flagged
   `negOfDownStab`, then `circR` is the only goal-inversion for a
   `◯`-goal) releases a *lax* derivation `d′` of `↑Q′` over the station.
   The traversal mining `d′` for `A(rest ⇒ ◯Q′)` meets uses of `X`
   itself — the case that killed both of Iemhoff's options (consume:
   incomplete; retain: non-terminating). Here it dissolves: an inner use
   of `X` carries its own argument `s₂ : ⊢tru ↓◯Q′`, a *structural
   subterm*, and the traversal restarts on `s₂`, discarding the inner
   continuation — we are mining for the `∀p`-formula, not replaying the
   derivation, and `s₂` already proves the very goal being analysed.
   Structural descent on the argument replaces `dykCommute`'s residual
   trick, and is simpler: no commute, no manufactured uses. Working name
   for the traversal case: the **modal descent**.
2. **Witness-box absorption CONFIRMED at design level.** G4s's `L◯→″`
   witness-variant clauses (fire against a witness box `◯X` with demand
   `A(X::Γ ⇒ ◯A)`) are the composition of our `◯`-implication row with
   the *guarded opening rows inside* `A(rest ⇒ ◯Q′)`: when `d′` opens a
   box during the lax phase, the mined formula's own opening row carries
   it. One clause, box-variability internal to the recursion.
3. **The E-side pair carries the E-res component**, by the same forcing
   as the intuitionistic Dyckhoff conjunct (same-station minimality
   climbs in a measure-carrying proof):

       (↓A(rest ⇒ ◯Q′) ⊃ E(N :: rest)) ∧ E(rest)

   and the A-side attack row is the unguarded pair
   `A(rest ⇒ ◯Q′) ∧ A(N :: rest ⇒ G)`, mirroring `atkDyk`; the weight
   `w(X) = wQ′ + wN + 3` dominates both components' recursions with the
   same slack shapes as `dec_dyk1/2` (checked arithmetically:
   `3^{wQ′+1}` and `2·3^{wN}` both sit under `3^{wQ′+wN+3}`).
4. **Blocker consistency check.** In the blocker, `χ = ↓(↓◯p ⊃ ↑r) ⊃ ◯p`
   is an *intuitionistic* Dyckhoff shape whose `N` happens to be a box,
   and `h = ↓◯p ⊃ ↑r` is the modal shape; the sequent flows through the
   guarded box-opening row composed with the existing Dyckhoff row — the
   double use of `h` is the first use dispatched at the outer station and
   the second inside the antecedent mining, met by modal descent. No
   retention anywhere. The known-hard sequent is covered by clause
   composition, on paper.

**(f) Stage-1 port check: `PLLFocused` lacks the truth-to-lax coercion.**
With `impR`/`andR` at `tru` only and no coercion rule, `⊢ ◯(↓(⊤⊃⊤))` is
underivable in `PLLFocused` as written: `circR` forces the lax phase,
where no rule can prove an implication — the calculus misses `◯φ` for
provable implicational `φ`, i.e. it is incomplete for PLL (its
completeness was only ever the stated `Focalization` hypothesis, so
nothing proved is affected; the blocker never crosses this gap). The
repair is Pfenning–Davies `laxIntro` in focused form:

    laxOf : Stab Γ tru P → Stab Γ lax P

at the *stable* judgment only — the phase where judgment transitions
belong. Consequences checked: the identity `idPos` at a lax index routes
through `laxOf` at its stable node (this is how the defect was found);
the `∀p` direct row ("prove `Q` truly") is exactly `laxOf`'s soundness,
which the clause design had already assumed; converse-K stays refuted
(`laxOf` demands the whole positive truly — `Q ⊢ ◯N` supplies only a lax
body). Bookkeeping: two flag-reading rules now, `circL` (content) and
`laxOf` (administrative coercion); the traversals gain one benign `Stab`
case, recursing at the `tru` index.

**Paper obligations status**: (1)–(3) and (e) run; forced changes
incorporated (one modal E-guard, one E-res component); obligations left
to mechanisation: the E-res forcing verification, the `boxClean`
construction, and the standing tests (blocker replay, converse-K
failure). Stage 1 begins.

## 4. Porting plan (Rules 1–2 compliant)

New branch `ljf-pll` from `ljf-simp-1`. The extension is built as
**`LaxLogic/LJFO.lean`**, a staged transformation of `LJF.lean` (zero
imports preserved — the Q1 auditability property is worth keeping):

* **Stage 1**: syntax + judgments + weights + `ParkedN` + `interp` with
  the new clauses + termination + `interp_pfree`. Compiles alone.
* **Stage 2**: the toolkit + `eSound`/`aSound` with the flag threaded
  (`fireASound` and `interpFire_eq` port unchanged in shape; the fire
  equation stays goal-generic — now over the larger goal type).
* **Stage 3**: the mega-mutual with lax cases; the farm macros are the
  single edit point for new termination entries (the C2 dividend).
* `LJF.lean` stays green beside it throughout; when LJF◯ lands, `LJF.lean`
  moves to `Archive/` per Rule 1 (it remains the IPC control experiment —
  the bridge `LJFComplete.lean` then needs retargeting or archiving with
  it; decision deferred).
* Final bridge: `Deriv ↔ LJF◯` on all of PLL (the focalization agent's
  `SCh`-simulation route extends: `SCh`'s lax rules translate to
  `circR`/`circL` — the persistent-context treatment is exactly what the
  blocker exercise validated).

## 5. Reuse inventory from the existing work

Ideas that port unchanged: the weighted single-Nat measure (+ lax costs),
parkedness, the E-guard discipline, the fire/park station discipline,
`interpFire_eq`'s statement shape, the equation-outside-the-mutual rule,
the farm macros, the whole termination lore. Lemmas expected to port with
flag decoration only: `Sub`/weakening, `routeStab`, `simStab`/`simHyp`,
`invBranches`/`extract`, `idPos`/`idNeg`, `upMerge`, `relStab`,
`negOfDownStab`. Lemmas needing genuine rework: `dykCommute` (flagged
version + the `◯`-implication analogue), `findFire` (two new dispatch
kinds), the saturated-case entry analysis (`TInv`-family gains circL
cases at lax indices).

## Stage-3 threading scheme (fixed 2026-08-10, mid-port)

* `eMinF`/`SatE2`/the T-family: **j-generic** — `∀ {j}, Inv … j ψ → Inv (E :: Δ) [] j ψ`; every arm gains one slot before the derivation.
* `aMinF`/`SatA2`/the U-family: derivation at `j`, conclusion at `tru`
  against the **jGoal-translated** target:
  `Inv (E :: Δ) [] .tru (interp … (some (jGoal j G)))` with
  `jGoal tru G = G`, `jGoal lax (↑P) = ◯P` (lax sequents are interpolated
  at the ◯-goal; lax imp/and-goal derivations are constructor-free).
* New mutual members: `cimpAntC` — the modal-descent miner, deriving
  `A(rest ⇒ ◯Q′)` from the ◯-implication's tru argument by structural
  descent on inner self-arguments (no residual, no commute); `boxClean` —
  the fireClean analogue for a consumed box (later `circL`-uses re-derive
  the content from the opened station's products).
* New T/U cases: `laxOf` (recurse at tru, administrative), `circR`
  (recurse at lax), `circL`-dispatch on parked boxes (through the box
  conjunct at lax + station-crossing recursion), ◯-implication dispatch
  (through the modal pair; argument mined by `cimpAntC`; E-res projected
  as in the intuitionistic case).
* Farms: `ljf_dec_e`/`ljf_dec_a` already carry the modal descent entries.

## Forced change #2 (2026-08-10, caught at mechanisation): the direct row is a FAMILY

The paper pass enumerated the *stable* dispatch at the ◯-goal but not the
right-focus spine. A lax `RFocus` can reach genuinely lax stable nodes
(`or1 → … → rel → inversion → stable → circL`), and `◯` does not
distribute over `∨` in PLL, so the single direct row
`A(done ⇒ ↑Q)` cannot cover them. The repair, by the body's shape — the
**lax goal-inversion rows** replacing the direct row in the ◯-goal
aggregate for goal `◯Q`:

* `Q = atom/fls`: the old direct row `A(done ⇒ ↑Q)` (laxness only via
  `laxOf` there);
* `Q = or P₁ P₂`: three rows — `A(done ⇒ ◯P₁)`, `A(done ⇒ ◯P₂)`, and
  `A(done ⇒ ↑(P₁∨P₂))`;
* `Q = down M`: `A(done ⇒ jGoal lax M)` (for `M` an implication there is
  no row: lax implications are underivable).

Correspondingly `URF`/`UStab` at the lax index dispatch right-focus
constructors through this family; the station rows are unchanged. This
is the modal round's second forced definition change, and the first
caught by the machine rather than the paper pass.

## Resume point (2026-08-10 ~09:30, mid E2/A2 port; goal: all four UI statements)

Done: eMinF/TInv/TStab/TRF/TLF/TpElim/TpLF/TpInv/aMinF/UEntry threaded
(E-side j-generic, Tp-family walks tru emitting at j); UStab redesigned
(jGoal-uniform oracles + cmem + j-conditioned bmem); interp's ◯-goal
clause = 7 concrete shape clauses with the lax goal-inversion prefix
family (forced change #2); aSound's ◯-goal clause = 7 matching clauses
(or-shape by decidable-equality dispatch; shifted bodies via circROf);
interpFire_eq moved before Part 4 with 7 concrete ◯-cases; soundness
heartbeats 12M. `lake build LaxLogic.LJFO 2>&1 | grep -E "^error:"` drives.

Remaining, in dependency order:
1. Seven ◯-shape equation lemmas (mirror interpA_atom_eq) for the
   U-rewrites.
2. interp_pfree's ◯-goal blocks (7 farm-style variants; prefix arities 1
   and 3 + the station cases as in the existing blocks).
3. URF: {j}, target jGoal; lax arms route: init → direct row (tru-init
   body under nOrAllIntro head); or1/or2 → the ◯Pᵢ rows; rel → the
   down-shape rows (circROf compositions).
4. UStab arms: pass cmem/bmem through; lax lfoc-dispatch: boxes via bmem
   rfl + the guarded-row construction; ◯-imps via cmem + cimpAntC;
   laxOf-case recurses at tru (same L).
5. ULF/UInvG/UpElim/UpLF/UpInvG: bump + circL/circR cases (UInvG's circR
   → recurse at lax with the same aggregate).
6. dykAntC: thread; NEW cimpAntC — the modal-descent miner: derive
   A(rest ⇒ ◯Q′) from s : ⊢tru ↓◯Q′ mined via flagged negOfDownStab →
   circROf → the lax phase traversal; self-uses of X descend structurally
   on their (smaller) arguments — measure (station-μ, szS s).
7. boxClean (fireClean-analogue: later circL-uses of the consumed box
   re-derive content from the opened station's products via posRestore).
8. eMinF/aMinF [] clauses: TInv/UEntry calls carry j; box/cimp dispatch
   cases in TStab/TLF (E-side): box → the box conjunct + station-crossing
   eMinF at [↑Q]++rest with boxClean; cimp → modal pair projection +
   cimpAntC + eMinF at [N]++rest.
9. Farms: ljf_dec_e/a already carry modal entries; add per-error.
10. satE2/satA2/dykAnt assembly + pins; blocker still standing test.

## Forced change #3 (2026-08-10, caught during the U-family port): the ◯-goal aggregate must be box-wrapped

**The defect.** With the ◯-goal aggregate a bare disjunction `nOrAll rows`,
`SatA2` is FALSE. Counterexample: `done = []`, `Δ = [◯q]` (p-free, kept),
`G = ↑q` at `lax`. The sequent `◯q ⊢lax ↑q` is derivable (`circL` on the
kept box), but the conclusion demands `⊤, ◯q ⊢tru A([] ⇒ ◯q)` where
`A([] ⇒ ◯q) ≈ ↑q` — and `◯q ⊬tru q`. A lax use of a KEPT hypothesis (the
traversal's keep branch) cannot be rebuilt inside a tru derivation of a
bare disjunction.

**The repair.** Wrap every ◯-goal aggregate in the modality:

    interp p [] done (some (.circ P)) = ◯(↓(nOrAll rows))

with the row families exactly as in forced change #2. Then the ∀p value is
tru-derivable by `circR`, and its inversion (`circR; stable; rfoc; rel`)
re-enters the LAX judgment, inside which the traversal's keep branch
rebuilds kept-hypothesis focuses natively (`circL` legal). In the
counterexample: `◯q ⊢tru ◯(↓↑q)` by `circR` then `circL` — derivable.

**Scheme.** The wrapper lives at the jGoal boundary only; interp's
recursive calls (the rows) are untouched, so the termination measure and
the whole descent kit are unchanged. The inner U-family
(`UStab`/`URF`/`ULF`/`UInvG`) targets the UNWRAPPED disjunction at the
flag `j` (`Inv (E::K) [] j (nOrAll L)`); row emissions built at tru lift by
`laxOf` at the stable judgment (`upOfTru`); `UEntry` alone crosses the
wrapper (`circR; stable; rfoc; rel` prefix at lax). Soundness side:
`aSound`'s ◯-clauses gain a `circL`-open prefix on the interpolant
hypothesis; the E-row guards track automatically (stated via `interp`).

**Method note.** Third instance of the definition-revision loop at
mechanised granularity: the statement (`SatA2`) was refutable by a 2-line
countermodel BEFORE any proof attempt could fail opaquely — the flag
discipline made the defect a TYPE error, not a stuck goal.

## Process adoption (2026-08-10, from the reviewer's note `ljfo-cost-review.md`)

Adopted at the conditional-E2/A2 clean compile (`70740d3`):

1. **Single-build loop** — every build now `tee`s to a log; secondary
   greps read the log at zero compile cost.
2. **Part 4/5 split** — `LaxLogic/LJFOCore.lean` (Parts 1–4, the blocker
   standing test, and the five axiom pins; zero imports) is frozen and
   cached; `LaxLogic/LJFO.lean` (Parts 5–8) imports only the core. One
   cross-module repair was needed: `interpA_atom_eq`'s closing `simp`
   relied on same-module matcher reuse; it now ends `simp only …; rfl`.
3. **Deferred: `laxRows` (reviewer §5).** The recommendation predates the
   U-family port: UStab/URF/ULF/UInvG are now already written against the
   seven inlined shape clauses and compile. Naming the row family remains
   the right simplification-round refactor, but its "strictly cheaper
   now" premise no longer holds; deferred to the simp round.
4. **Next: the evaluator bank (reviewer §4), then `CimpAnt` in
   `wip/ljfo_dev.lean` against the frozen core (reviewer §3).**

Status at this point: satE2/satA2 are GREEN **conditional on `CimpAnt`**
(the isolated modal-descent miner, DykAnt-style). The deep self-use
analysis (this session) shows the miner needs either (a) a dedicated
subterm-measured traversal family, or (b) a further forced change to the
E-row antecedent — the evaluator bank should adjudicate (b) cheaply
before (a) is built.

## Evaluator bank verdicts (2026-08-10 evening, `wip/ljfo_eval.lean`)

Built on `prove?Bounded`/`refute?` (the certificate engines, per the
standing search-tooling rule — the decidability fuel is infeasible).
Three-valued cells: fail/flag only ever reported on certificates.

* **Calibration PASSED (live-fire):** the forced-change-#3 cell
  (`done = []`, `Δ = [◯q]`, goal `◯q` at lax) is CERTIFIED-FAIL against
  the pre-wrapper value and PASSES against the wrapped one.
* **E2/A2 minimality sweeps: zero failures, zero flags** over the
  degenerate bank (empty stations, p-carrying boxes, ∨-bodies, ⊥,
  p-guarded rows, boxed kept hypotheses).
* **The CimpAnt cells: zero failures, zero flags** — including p-carrying
  `Q′`, boxes in `rest`, kept-side grounding.  The E-row antecedent
  `A(rest ⇒ ◯Q′)` is minimality-adequate on the bank; no forced change
  #4 is indicated.  Option (b) (guard at the full station) also passes —
  no discriminating cell found.

## The miner: the measure wall, precisely (for Matthew)

The statement `CimpAnt` is supported by the bank; the remaining question
is purely proof-architecture.  Ten-odd designs were pushed to their
failure points this session; the wall, in one sentence: **the mining must
restart on χ-fire arguments inside material it obtained by rebuilding
(peel/simulation/weakening), so no structural measure survives; and no
station/goal-weight measure orders the restart, because a χ-use can occur
at an arbitrarily small local goal.**  Deep χ-uses under branch-local
releases are semantically real (their arguments use the branch locals),
so top-level descent alone cannot reach them.

Two costed discharge routes:

1. **Height bound by pigeonhole for LJF◯** — the exact ingredient
   `PLLG4Dec` provides for G4c ("what lets the Pitts interpolants be
   defined by plain fuel recursion").  Scope: a decider-scale finite-space
   development for the focused calculus.  Big, but on well-trodden
   in-repo ground.
2. **A χ-aware antecedent aggregate** (retention-lite in the formula) —
   needs a termination-compatible formulation; the naive one is circular.
   This is a definition-design decision of the kind Matthew governs.

Station-fuel (strong induction on `sum3 done`, tying the `cAnt` knot per
station) handles all OTHER cimps' dispatches during the mining; it is the
same-χ deep uses that need (1) or (2).

## Route (3) — the χ-threaded family with the max-measure (designed 2026-08-10 late; the first fully-closing termination story)

Thread an optional active-χ datum `χdat : Option Pos` (carrying `Q′`)
through the T/U-family, with the THREE changes:

1. **hm gains the χ-class** (`Z ∈ done ∨ Z ∈ K ∨ Z = χ` when active), and
   the two stable dispatchers gain a χ-arm;
2. **every member's measure becomes**
   `(2·sum3 todo + sum3 station + 3 ^ max (goal-w) (χ-w) + c, sizeOf d)`
   — inactive mode: `max` collapses to the goal weight, the existing
   arithmetic untouched;
3. **`cimpAnt` joins the mutual** with measure second component
   `sizeOf s + 2`.

Why it closes, where every previous design failed: within a fixed
station the family walks RAW SUBTERMS only (all rebuilds are on outputs
or feed strictly smaller stations — this is why the family's own measure
works).  So at a χ-use node `.lfoc h (.impL s₂ lf₂)` the re-entry
`cimpAnt … s₂` has: first components EQUAL (both `max`-dominated by the
χ-weight), second `sizeOf s₂ + 2 < sizeOf node` (node ≥ s₂ + lf₂ + 2).
The entry `cimpAnt → UEntry (.stable s)` drops on `sizeOf s + 1 <
sizeOf s + 2`.  Cross-station exits drop on the first component as
always.  Deep χ-uses under branch locals are handled AT their nodes by
the walk (the locals are already in the walk's bookkeeping), which is
what the top-level-descent designs could never reach.

Cost: one extra argument everywhere, the max-form re-run of the
decreasing farm, χdat-threading through the crossing helpers, and the
row/guard adjustments — with the E-guard and the A-row's antecedent
component uniformised to `A(rest ⇒ ↑↓◯Q′)` (tru-mode at the residual
station; termination station-financed on both sides, checked above).
The evaluator bank should re-run on the adjusted rows first.

Estimated as the cheapest of the three routes and the one that keeps the
descent argument of §3(e) intact.  Routes: (1) height bound (decider
scale), (2) χ-aware antecedent formula (design risk), (3) this.

## Route (3) part 1 LANDED (2026-08-11 ~00:40): the uniformised antecedent, whole development green

The row surgery is complete and machine-checked end to end:

* `interp`: all 12 antecedent sites (the E-guard and the 11 A-attack
  rows) now carry `A(rest ⇒ ↑↓◯Q′)` — truth-mode at the residual
  station; termination station-financed (dec_cimp1 kit bumped one
  exponent).
* `eSound`'s modal pair SIMPLIFIED: the E1/A1 interlock is now a direct
  `aSound` call at the ↑↓-goal (no `circR` dance); `atkCimp` fires by
  `unStable` on the antecedent value.
* The tail (equations, ConjMems, oracles, dispatch arms, `CimpAnt`)
  tracked in ONE pass — the `cAnt`-parameterisation absorbed the target
  change automatically. Both modules green; all pins pass.
* Evaluator: zero certified failures; the calibration defect still
  reproduces; the route-(3) cells (minimality AND the soundness spot)
  green. The pre-surgery `cimpCell`/`cimpCellB` sweeps are now STALE
  (they test formulas no longer in the rows) and only flag on budget.

## The one remaining hole in route (3) part 2, precisely

The χ-threaded family closes every cycle EXCEPT: in mining mode the walk
can enter a LAX phase (through a ◯-goal emission), where `UStab`'s
laxOf-down arms REBUILD (`negOfDownStab`) — breaking the raw-subterm
size invariant that the descent's second component rides.  Candidate
patch: a ghost measure `szF` = the largest χ-fire-argument size in a
derivation, with monotonicity lemmas through every rebuilder (`wk`,
`relStab`, `negOfDownStab`, `simInv`; fire arguments are preserved
verbatim by all of them), and the lex `(station, szF, …)`.  Needs its own
session: the `szF`-monotonicity family is ~20 mechanical lemmas plus the
measure rewrite.

## Route (3) FINAL form (2026-08-11 ~02:00): the bounded family — no measure rewrite, no χ-threading

The discharge architecture that survives every failure mode found tonight:

1. **Guard at the FULL station**: the E/A cimp-row antecedent becomes
   `A(done ⇒ ↑↓◯Q′)` (the (b)-form; its cells were CERTIFIED GREEN on the
   bank tonight as `cimpCellB`).  Requires the `f(none)` reweighting of
   `interp`'s termination (`none`-mode weighted `sum3 todo + sum3 done`,
   arithmetic verified this session) so the same-station reference is
   financed.  With the guard at `done`, the miner is ONE LINE — 
   `UEntry done … (.up (.down (.circ Q′))) (.stable s)` — and every χ-use
   at every depth dispatches NATIVELY (χ ∈ done); no 3-way map exists
   anywhere.
2. **The knot, termination-visibly**: `CimpAntLt n := ∀ …, sizeOf s < n → …`;
   the mutual's `cAnt` parameter becomes `CimpAntLt n` with `(n, hn)`
   threaded as PASSENGER arguments (no measure changes — the family's own
   WF is untouched); each member's `hn` bounds its derivation argument,
   propagated by `sizeOf`-constructor arithmetic at each recursive call;
   crossings restart with a FRESH `n′ := sizeOf (rebuilt) + 1` (rebuilds
   harmless — this is what kills the szF/#5 machinery).  Dispatch sites
   supply `sizeOf s_d < n` from `hn` by subterm arithmetic.
3. **`cimpAnt : ∀ n, CimpAntLt n`** by plain strong induction on `n`
   OUTSIDE the mutual, passing itself at smaller `n`.
4. `satE2`/`satA2` unconditional with entry `n := sizeOf d + 1`.

Steps: (1) interp reweight + guard change + farm repair [the risk item];
(2) `(n, hn)` threading [~60 mechanical sites]; (3) the wrapper; (4)
assembly + pins.  Each step banked green or reverted — the branch is
never left red.

## TERMINUS of the discharge search (2026-08-11 02:15) — two sharp obstructions, and the §3(e) suspicion

**(I) The (b)-guard is termination-INFEASIBLE.** Any `f(none)` heavy
enough to finance the same-station reference `A(done ⇒ ↑↓◯Q′)` inside
`E(done)` (needs `f ≳ 3^(wQ′+2)`, station-dependent) is unpayable at the
box-row's crossing `some@done → none@[↑R]+rest`: the box's weight is
spent exactly (`2·3^wR` vs `3^(wR+1)`), leaving no margin for a
station-sized `f` over `rest` against an arbitrarily small goal weight.
Checked for `f = sum3 todo + sum3 done`, `f = sum3 done`, and the
cimp-only variant with adjusted todo-coefficients — the box-row breaks
all of them.  So the guard stays at `rest`, as landed.

**(II) With the guard at `rest`, every mining architecture fails at the
same point: χ-uses inside CROSSED-station material.**  A use of the
consumed ◯-implication inside a fire/box-crossing's continuation sits at
a station that does not contain χ and cannot retain it (p-fulness), at an
arbitrary local goal; the full-aggregate descent trick types only at the
mining station's own walk.  Exhausted tonight: top-level descent,
scan-strengthen, 3-way maps with max-measures, szF ghost measures, the
bounded `(n, hn)` family, station-fuel knots — each closes every cycle
EXCEPT this one.

**The suspicion this pins on the paper design:** §3(e)'s claim that
Iemhoff's witness-box family is "absorbed" by the guarded opening rows
covered the ANTECEDENT's box-openings — but crossed-station χ-reuse is
precisely the configuration her `L◯→″` witness variants existed for.
The absorption claim may be wrong for the E-row, and the row may need a
witness-style component after all — a definitional decision on the
theorem itself.

**Standing equipment for whatever is decided:** the calibrated evaluator
(seconds per cell, certified verdicts) and the conditional-green
development (any row change re-checks E1/A1/E2/A2 mechanically through
the `cAnt` parameterisation, as tonight's surgery proved in one pass).

## RESOLUTION of the terminus (2026-08-11 01:30) — the corrected calculus already answers this, at a known price

`docs/commentary.md` §4 (the three retention revisions) holds the actual
corrected rule:

    Γ, ◯χ, ◯φ→ψ, χ ⇒ ◯φ    Γ, ◯χ, ψ ⇒ Δ
    ------------------------------------- L◯→″
            Γ, ◯χ, ◯φ→ψ ⇒ Δ

The antecedent premise RETAINS the modal implication itself (and the
witness box, opened) — precisely what dissolves both of tonight's
obstructions at once: with χ retained in the antecedent station, every
χ-use at every depth and in every crossing is a NATIVE station-member
dispatch (no χ-class, no descent, no miner at all — `CimpAnt` becomes a
plain `UEntry` call).  The gap review's ①/② pattern (one occurrence of
the modal implication used outside AND inside a box-opening) is exactly
the (β)-configuration that defeated every consumed-χ architecture.

**The price, stated exactly:** retention breaks the additive `sum3`
measure — the corrected calculus terminates on the **DM (multiset)
order**, and transposing the E/A-row retention to `interp` means
re-founding `interp`'s termination, the descent kit, and the family
measures on that order.  §3(e)'s absorption claim is hereby REFUTED at
mechanised granularity: the witness/retention discipline is not
absorbable into the guarded opening rows on the additive measure.

**The decision (Matthew's):**
  (A) re-found on the DM-order and take the retention rows — the
      literature-faithful route; multi-session, but the corrected
      calculus's own termination argument is the template, in-repo;
  (B) the pigeonhole height-bound / fuel route (decider-scale for LJF◯);
  (C) an exemption: E2/A2 stand as machine-checked conditional on the
      isolated `CimpAnt`, pending (A) or (B).
The evaluator bank and the `cAnt`-parameterised development re-check any
choice mechanically.

## CORRECTION to the resolution, from the repo's own roadmap (2026-08-11 01:40)

`docs/commentary.md` §"what remains" states it outright: the corrected
calculus is **not Dershowitz–Manna decreasing at `L◯→″`/`R◯→″`'s first
premises** — there is NO DM template to transpose; option (A) as
previously stated is infeasible-as-stated.  The repo's own plan (item 1)
for exactly this is the **history/loop-check over finite subformula-
closed set-contexts** (weak termination + complete strategy), with a
Bílková-style order as fallback; and item 2 predicted that the UI
interpolant recursion "needs care exactly where the duplication lives".

Tonight's terminus is that prediction reached at mechanised granularity —
with the notable result that the focused route absorbed everything else:
the whole minimality induction is machine-checked except the SINGLE point
where the duplication lives (`CimpAnt`).  The real options:

  (A′) a Bílková-style order for the antecedent recursion (research);
  (B)  the finite-space/history discipline for LJF◯ — the roadmap's own
       item 1, acknowledged there as "a genuinely separate piece of
       work", which the pigeonhole/fuel machinery of `PLLG4Dec` already
       demonstrates for G4c;
  (C)  E2/A2 stand as machine-checked conditional on the isolated
       `CimpAnt` until (A′) or (B) lands.

The dependency structure is now exactly the roadmap's: item 1 (the
termination discipline) precedes the last step of item 2 (UI).  The
campaign advanced item 2 to within one typed obligation of completion.

## Route (B) begun (2026-08-11 01:35): layer 1 GREEN

`LaxLogic/LJFOHeight.lean` — the height-indexed four-judgment calculus
(`StabH`/`RFocusH`/`LFocH`/`InvH`), monotone in the bound, equivalent to
the unindexed judgments (`toH`/`ofH`).  The `G4sh`-analogue for LJF◯;
purely additive over the frozen core; compiled green first build.

Next layers, in order:
2. the set-context (Finset) forms + transfer (membership-based rules
   make this direct), and the Ω-component finiteness discipline;
3. the sequent-space bound + duplicate-collapse (pigeonhole), giving the
   computable height bound H₀ — `PLLG4Dec.height_bound` is the template;
4. the retention rows + fuel-founded `interp` (the definitional step —
   THE point to confirm direction with Matthew before executing);
5. `CimpAnt` discharged natively over the retention rows; satE2/satA2
   unconditional; pins.

## Route (B) layer 2a GREEN (2026-08-11 01:35)

`LaxLogic/LJFOUniverse.lean` — the mutual subformula closures
(`uPosP`/`uNegP`/`uPosN`/`uNegN`), self-membership, the fourteen one-step
closure facts, context universes (`uCtxP`/`uCtxN`), and the `UClosed`
invariant structure.  List-based, zero imports beyond the core,
sorry-free (a first draft of the closure-transitivity theorem was CUT
rather than committed with sorries — it is layer 2b's first obligation).

Layer 2b next: closure transitivity (`UClosed (uCtxP Γ) (uCtxN Γ)`, by
the mutual subformulas-of-subformulas induction) + the rule-stability
lemmas (each rule's premises stay in a `UClosed` universe).  Both
direction-neutral.  The direction-committing step remains layer 4.

## Route (B) layer 2b GREEN (2026-08-11 01:45)

The eightfold closure-transitivity mutual (`uPP`/`uNP`/`uPN`/`uNN`/
`uPPn`/`uNPn`/`uPNn`/`uNNn`) and the invariant theorem `uClosed_ctx :
UClosed (uCtxP Γ) (uCtxN Γ)` — sorry-free.  Next (2c): the
rule-stability lemmas over the H-judgments (every rule's premises stay
within a `UClosed` universe), then layer 3 (space bound + collapse).

## Route (B) layer 3a GREEN (2026-08-11 02:45)

`LaxLogic/LJFOSearch.lean` — the four-judgment sequent type `LSeq`
(DecidableEq), the backward rule-instance enumerator `succs` (all four
judgment kinds, the lax-only gates explicit), and the uniform
derivability target `LSeq.holds`.  Definitions only, first-build green.
Direction note: (B) is the commentary's OWN primary plan ("the planned
route … history/loop-check over the finite space"), which is why the
build proceeds without waiting — (A′)/model-completion remain the
documented fallbacks.

Next slices, template-mode: `succs_sound` (constructor replay per
instance; use the if-chain idiom — Or-elimination into Type is blocked),
then `succs_complete` (each constructor's premises appear), then the
fueled search with a visited set, its round-trip, and the height bound.

## Route (B) layer 3b GREEN (2026-08-11 ~03:00)

`succs_sound` — every enumerated instance replays its rule (uniform over
the four judgments), with the enumerator refactored into NAMED instance
families (`laxInsts`/`circInsts`/`goalInsts`/`stableInsts`/`omegaInsts`)
after inline matches kept capturing hypotheses into motives.  Idiom
lessons banked in passing: `++` is left-associative in the membership
chains; decidable-if conditions must be atomic applications, not inline
matches, when Type-valued elimination follows.

Next: `succs_complete` (each constructor's premise list is enumerated),
then the fueled visited-set search and the round-trip.

## Route (B) layer 3d GREEN (2026-08-11 ~02:55)

The fueled backward search (`search`), computable witness extraction
(`anyWitness`), **`search_sound`** (a successful search rebuilds a kernel
derivation, at every fuel), and `search_mono`.  With 3b/3c this
completes the sound half of the decider round-trip.

Remaining for the height bound: the completeness half — search at
pigeonhole fuel finds every derivable sequent — which needs the
sequent-space cardinality over the `UClosed` universe (layers 2a/2b
supply the invariant) and the duplicate-collapse argument.  That is the
one genuinely hard piece of the decider; then layer 4 (retention rows +
fuel-founded `interp`) discharges `CimpAnt`.

## Route (B) layer 3e GREEN (2026-08-11 ~03:10): THE DECIDER ROUND-TRIP

`search_complete` closes the round-trip: **derivable ⟺ searchable**, at
existential fuel (fuel = derivation height), with `search_sound`
rebuilding kernel derivations.  The pigeonhole/computable bound is NOT
needed for this form — it is only needed if layer 4's fuel-founded
`interp` requires a sequent-computable fuel (stabilisation); the
existential form may suffice for the miner, which transforms GIVEN
derivations whose heights are available through `toH`.

The completeness proof caught two genuine defects in the height layer
(the `init` and `flsL` leaves were indexed at bare `n`, defeating fuel-0
search) — fixed at source, all layers re-verified.

Standing (B)-inventory, all sorry-free over the frozen core:
heights + equivalence; universes + transitivity + `uClosed_ctx`;
`LSeq`/`succs` in named families; `succs_sound`/`succs_complete` (+ the
H-form); the fueled search; `search_sound`/`search_mono`/
`search_complete_h`/`search_complete`.

Next: layer 4 — the retention rows + fuel-founded `interp` (the
definitional step), now with the fuel discipline standing ready.

## Review round, 2026-08-11 morning (Matthew-directed): the frontier attack + simp round 1

Full review: `docs/ljfo-review-2026-08-11.md`.  Attack outcome, one
line: zero certified failures of `CimpAnt` anywhere decidable
(corpus/crossed-χ/boundary/no-row/GZ strata); every escalated flag
resolved YES, the last two at KERNEL level via `LJFOSearch.search`
(fuel 32: `E(φ★) ⊢ ¬¬◯⊥`, closing the cross-route check against the
semantically proved `∃p.φ★ = ¬¬◯⊥`; fuel 48: the `[◯p→r, ◯(↓◯p)]`
cell, with `⊢ A` outright).  The focused kernel search out-screens the
G4c certificate prover by orders of magnitude on interp values and is
now the escalation engine of record; the `bchi` horizon stations are
its named next stratum.

**Simp round 1 (support modules) log:**
* `LJFOSearch.lean`: `memSingle` (14 singleton-membership chains),
  `premsH0/H1/H2` (19 premise lambdas in the height-indexed
  completeness).  Statements untouched.
* `LJFOUniverse.lean`: the eightfold transitivity mutual was ASSESSED
  and left alone — the imp constructor's Pos/Neg asymmetry blocks the
  duality collapse; the file is already clean.  Recorded so round 2
  does not re-derive this.
* `LJFO.lean`: the survey found its round-1 candidates (the laxOf-arm
  prefixes, the ConjMems rows) all sit INSIDE the seven-shape regions
  that round 2's `laxRows` collapse rewrites wholesale — deduplicating
  them now would edit the same lines twice.  Round-1 scope closed at
  the support modules; the LJFO.lean dedup merges into round 2.

**Round 2 design pin (before starting):** the row family is named in
the TAIL, not the core — `LJFOCore.lean` stays frozen.  The seam
already exists: `interpCircShape` (LJFO.lean:1325) packages the
shape-generic box-wrapped equation as a Σ'.  Round 2 = (1) a top-level
`laxRows p done Q : List Neg` with seven shape equations proved
through that seam; (2) the four layers' seven-clause groups
(U-rewrites, pfree blocks, dispatch arms) collapsed to single
`laxRows` clauses discharged by `cases Q`; (3) the merged round-1
LJFO.lean dedup (laxOf-arm prefixes, ConjMems rows) done inside the
same rewrite.  Baseline to beat: 1773 s tail re-elaboration; every
batch lands green or is reverted.

## The core extracted (2026-08-11 ~08:45, Matthew's question): W, its equivalence route, and a GZ-candidate cell

**W (the common core of the three blockers):** over the finite
(station, ◯-goal) space of the input's universe, the monotone fuel
iteration of the retention equations (`interpF`; A from ⊥, E from ⊤)
stabilises up to interderivability at finite fuel.  Each route blocker
= W + a specific computable bound (room / 2d / structural measure) —
all three are UI-sufficient (with their banked machinery) and none is
a consequence of UI.  **Upgrade: modulo layer 4's fuel-soundness and
fuel-minimality (cofinality — every sufficient p-free θ sits below
A_{height of θ's derivation}, provable with the native retention
miner), W ⟺ UI for LJF◯ per cell**: a cofinal ascending chain has a
greatest element iff it is eventually constant.  So W is not merely
the common factor; with cofinality it is EQUIVALENT to UI (modulo
focalization for PLL proper).

**Empirics (wip/ljfo_stab.lean, certified):** monotonicity direction
holds everywhere tested; `[◯p→r]` stabilises at f₀=2 (both engines),
`[◯q→r]` at f₀=3.  **The GZ-candidate cell: ({◯p→r, ◯q} ⇒ ◯p)** —
certified two-periodic strict ascent A₁⊊A₂⟛A₃⊊A₄⟛A₅⊊A₆ with A₂, A₄
certified INSIDE the sufficient set (A_f, S ⊢ ◯p); A₆'s sufficiency
unsettled at 200k budget.  Chains grow ~2× per level syntactically
(never syntactically stable — a simplifier is a layer-4 engineering
need).

**The fork, both prongs now concrete:** (i) REFUTATION prong — extract
the closed family θ_k from A₂/A₄/A₆ on the candidate cell, prove
strict ascent for all k by a parametric countermodel family
(branchdia/paramfork machinery), and cofinality ⟹ ∀p inexpressible at
this cell ⟹ **UI for PLL is FALSE**.  (ii) PROOF prong — layer 4
(fuel soundness + cofinal minimality) formalises W ⟺ UI; then proving
stabilisation per cell (pigeonhole over the finite sequent space
bounds derivation heights, hence the needed fuel) gives UI.  The same
two lemmas (fuel-soundness, cofinality) are the first step of BOTH
prongs — layer 4 is the next move regardless of the answer's sign.

### Correction to "the core extracted" (2026-08-11 afternoon, Matthew's objection — he is right)

"Each blocker is exactly W with my bound" is NOT literally true and is
withdrawn.  The scopes differ: `cascade_boxgoal_pos` (U) and the
semantic `mforth`/`mback` (V) close routes to UI for the ONE-VARIABLE
fragment as those campaigns fought it; `CimpAnt` (and W) concern full
PLL.  What survives precisely: U, V, W each are UI-sufficient FOR
THEIR SCOPE together with their route's proved machinery; none is a
consequence of UI; the ◯-crossing-reuse shape is common but the
statements are not interchangeable, and no disjunction
ψ = U ∨ V ∨ W ⊣⊢ PLL.UI is claimed — as literally stated ψ ⊣⊢ PLL.UI
is almost certainly FALSE in the ⟸ direction (UI does not imply any
of the three construction-specific statements) and the ⟹ direction
fails at scope for U and V.  The machine-checkable surrogate on offer
is layer 4's per-cell equivalence: fuel-soundness + cofinal
minimality make (chain stabilises at the cell) ⟺ (the cell's uniform
interpolant exists), for LJF◯, cell by cell — the two lemmas are the
fresh session's first target either way.

Matthew's alternative preparation routes, recorded: (1) prove
`CimpAnt` restricted to the 1-pv fragment (matching U/V's scope; note
the candidate cell needs q, r, so it vanishes at 1 pv — the fragment
may genuinely be easier); (2) PCLL (◯ distributes over ∨): the
distribution law collapses forced change #2's row family toward the
single direct row and shrinks the fixpoint system; the engines
already support PCLL refutation natively (`Config.accept :=
RNC.confB`); run the paper pass over the clauses first; (3) both
combined; (4) unify U/V/W formally inside a bi-lax-intuitionistic
frame (`docs/lax-dual-colax-biint-handoff.md`: ◯∃ ⊣ ◯∀, and §6.1's
point that multi-succedent may dissolve the goal-dependent left rule)
— separate thread, real mathematics, health warnings in that file.

## The measure-interface stratum (pinned 2026-08-11, Matthew's suggestion, assessed and adopted post-layer-4)

Origin: Matthew proposed a Girard-candidates move for the complexity
measure — prove against an abstract μ satisfying a named descent
interface, realise concretely later, with a parallel existence/
consistency ledger.  Assessment (2026-08-11 afternoon reply):

* NOT for termination, and no `partial def` anywhere: a Lean partial
  def is kernel-opaque (no equations, nothing provable — the mandate
  dies); and the abstract-μ interface for termination either contains
  the retention re-entry inequality (unrealisable by any additive
  measure — the route-(B) terminus) or weakens to "μ exists over the
  finite space", which IS the fuel/pigeonhole formulation.  Fuel is
  the initial object of the measure category: every concrete μ
  factors through a fuel bound, and a computable stabilisation bound
  f₀(S, Q) IS the realised measure.  The existence ledger already has
  a name: W.
* ADOPTED as the post-layer-4 bounds-and-unification layer:
  1. `Measure := {μ // the descent interface}` (the interface = the
     dec_* farm's inequalities, stated abstractly);
  2. every inhabitant realises a terminating `interp_μ` agreeing with
     `interpF` at fuel `μ(S,Q)` (WF recursion on hypothesised μ via
     `termination_by`/`decreasing_by` from the interface — supported,
     no partiality);
  3. inhabitation ⟺ W-with-computable-bounds;
  4. the room-style (G4c tower) and height-style finances become
     INSTANCES — exact bounds as theorem-shaped comparisons, and the
     only stateable frame found so far for route (4)'s formal
     implications among U/V/W (morphisms between interface instances
     over the three judgment spaces).
* Speculative lead, flagged as such: "derivable at some fuel" is a
  constraint-indexed judgment in F&M's own reading of ◯ ("φ under
  some constraint"); the Curry-problem constraint-completeness
  machinery (Thms 5/6, partly mechanised) is the natural host for the
  measure-existence statement as a constraint family — the method
  self-applied.

Sequencing: layer 4 first (fuel-soundness + cofinal minimality); this
stratum after, feeding the paper's bounds section and route (4).

## The candidate cell RESOLVED (refutation prong, 2026-08-11 15:04; integrated and independently re-verified by the coordinator)

**({◯p→r, ◯q} ⇒ ◯p) is NOT a Ghilardi–Zawadowski witness: the chain
stops climbing at f = 6.**  The extracted closed family, with
π := (q∧r) ⊃ ◯⊥, ρ := ◯π, σ := q ∧ (◯⊥ ⊃ r), crank
F(X) := ◯((X ∧ ρ) ∨ (σ ⊃ ◯⊥)):
θ₁ = ◯⊥, θ₂ = ◯(◯⊥ ∨ (q ⊃ ◯⊥)), θ_{k+1} = F(θ_k).  Certified:
θ₁ ⊊ θ₂ ⊊ θ₃ (checkB countermodels M₁, M₂ — M₂ also refutes the raw
A₆ ⊢ A₅); then **θ₄ ⟛ θ₃ and ∀n. θ_{n+4} ⊢ θ_{n+3}, kernel-proved,
axioms [propext, Quot.sound]** (`wip/ljfo_theta_pinned.lean`,
`_certs`, `_axioms`; rebuilt green in the main worktree).  The
collapse mechanism: F's X-FREE disjunct σ ⊃ ◯⊥ re-derives the whole
body from the third rung — the retention crank has a fixpoint and
cannot generate unbounded content at this cell.  On the simplified
forms the chain itself is proved to plateau (pnf(A₆) ⟛ pnf(A₇);
pnf(A₈) ⊢ pnf(A₆)).

OPEN, named: (1) the raw bridge for f ≥ 6 — the clean fix is the
NORMALISER-SOUNDNESS lemma (LaxND derivability of the pnf rewrite,
both directions; unit laws + idempotence + absorption + ◯∧-fusion +
◯⊥ ⊢ ◯C + unit + join; a few hundred routine lines) — now a named
layer-4 adjunct, upgrading every pnf-level result to raw wholesale;
(2) faithfulness θ_k ⟛ A_{2k} for k ≥ 4 (blocked by the bridge);
(3) W at this cell follows from (1)+(2) — currently proved for the
family, de-risked for the chain.  **The next GZ stratum is specified
by the failure analysis: stations whose crank has NO X-free
disjunct** — the σ ⊃ ◯⊥ escape must be structurally impossible.

## The candidate cell CLOSED from the proof side too (proof prong, 2026-08-11 14:58; convergent with the refutation prong)

**The cell's ∀p pre-interpolant exists and is identified:**

    θmax := ((◯⊥ ⊃ r) ∧ ◯q) ⊃ ◯⊥        (p-free, 13 nodes)

— which is exactly `E₃ ⊃ ◯⊥` where `E₃ ⟛ (◯⊥⊃r) ∧ ◯q` is the ∃p
value at fuel 3, i.e. the station's own ⊥-INSTANCE.  Certified:
θmax ∈ Suff (sufficiency), A₂/A₄/A₆ ⊢ θmax, and **A₆ ⟛ A₇ ⟛ A₈ ⟛
θmax all PROVED both directions ON THE RAW VALUES** via the certified
decomposition (θmax is ◯-fixed, so ∨/∧/◯-elimination splits the
2036-node sequents into engine-sized leaves; `θmax ⊢ A₇` needed 8M
nodes).  This CLOSES the refutation prong's raw-bridge gap from f = 6
up, and closes A₆/A₈ soundness.  The 5→6 countermodel dissection: the
last climb adds the station's head implication in its ⊥-instance as a
guard — bounded content; every chain value sits at ◯-class-depth ≤ 2
(nothing escapes upward).  So at this cell: the chain stabilises at
f = 6, the limit is θmax, and W holds.

**The maximality mechanism, general and important:** substituting
p := ⊥ in any derivation of `θ, S ⊢ ◯p` yields `θ ⊢ ⊥-instance` — the
⊥-instance of a cell is ALWAYS a p-free upper bound of Suff, and it is
the maximum whenever it is itself sufficient (here: because ◯⊥ ⊢ ◯p
re-derives the goal).  OPEN to make this a certificate: the
substitution-admissibility lemma `Deriv Γ C → Deriv (Γ[p:=χ])
(C[p:=χ])` (routine induction; also generally valuable — it turns
instance-bounding into a certified screening tool for every cell).
OPEN also: the decomposition trees as single pinned Lean terms.

**The next GZ stratum, now doubly filtered** (both agents converge):
a station whose crank has NO X-free disjunct (refutation prong) AND
whose goal is NOT settled by ◯⊥ (proof prong: otherwise the
⊥-instance closes the cell).  Layer-4 requirements enriched:
stabilisation testing must be LOGICAL, never syntactic (the chain is
logically stationary from f = 6 while syntax doubles); the
normaliser-soundness lemma and the substitution lemma are the two
named adjuncts.

Probe: `wip/ljfo_ub.lean` (exe `ubrun`), integrated from the agent
worktree; prong-1 artefacts already integrated and kernel-verified.

## Simp round 2 (2026-08-12): the `laxRows` collapse — both batches, done

**Batch 1** (commit 9cff0c7): `LaxLogic/LJFORows.lean` created ON TOP of
the tail — `circStationRows`/`laxPrefix`/`laxRows` named and the unified
equation `interp_circ_laxRows` proved by `cases Q` from the seven
`interpA_circ*_eq` lemmas.  Additive; nothing in the tail edited.

**Batch 2** (this commit): the dependency reversed, the consumers
collapsed, and round 1's deferred `LJFO.lean` dedup folded in.

### Restructure

`LJFORows.lean` now imports only the frozen `LaxLogic.LJFOCore`, and
`LaxLogic.LJFO` imports IT.  Moved down, because each needs nothing beyond
`interp`:

* `Saturated` — the tail's only definition that the station equations use;
* `rowMem` / `rowMemR`, the two row-membership combinators.  Every
  membership side condition in the traversals has the shape
  `f ⟨(X,rest),hsp⟩ ∈ (splits done).attach.map f`, optionally behind a
  goal-inversion prefix, and every one of the 55 call sites re-proved it
  inline as a three-line
  `List.mem_append_right _ (List.mem_map_of_mem (List.mem_attach _ ⟨_,_⟩))`;
* `eConjRows` — the `∃p` station map — with `interpE_eq` and the five
  `*ConjMem` projections restated over it.  Those five repeated the whole
  19-line map in their STATEMENT; each is now one `rowMem`.  (This is
  round 1's deferred "ConjMems row families" item.)

### The unified equation absorbs its own shape analysis

`interp`'s goal dispatch matches on the positive UNDER the `◯`
(`| .circ (.atom q) => …`, `| .circ .fls => …`, …), so `rw [interp]`
cannot fire at an abstract `Q` — that is *why* seven lemmas existed.
Round 2 keeps the case split and stops restating the lemma around it:

    theorem interp_circ_laxRows (hsat : Saturated done) (Q : Pos) :
        interp p [] done (some (◯Q)) = ◯(↓(nOrAll (laxRows p done Q))) := by
      match Q with
      | .atom _ | .fls | .or _ _ | .down (.up _) | .down (.circ _)
      | .down (.and _ _) | .down (.imp _ _) =>
        conv => lhs; rw [interp]
        split
        all_goals rename_i heq
        · rw [hsat] at heq; cases heq
        · rfl

180 lines — the seven lemmas plus the `interpCircShape` Σ'-seam, which
turned out to have NO call sites — become 14.  Both are preserved in
`Archive/ljfo-simp-round2-superseded.lean`.

### Consumer collapse: what folded, and what legitimately stayed per-shape

* **`UEntry` — folded, 7 → 1.**  The seven ◯-goal arms differed only in
  which `interpA_circ*_eq` they named; they are now the single
  shape-generic clause `| _, _, hm, hm2, hK, .up P₀, .lax, .stable s`,
  whose four row memberships are the named `laxRows_qimpMem` /
  `_dykMem` / `_cimpMem` / `_boxMem`.  With the four `tru` arms
  deduplicated alongside: 178 → 36 lines.
* **`UStab` — prefix folded, bodies stayed.**  The seven `.laxOf` arms all
  opened with the same five-line
  `nOrAll_inj (Pos.down.inj (Neg.circ.inj (…)))` identification of the row
  list; that is now one `laxRows_of_eq`.  Their bodies stay per-shape and
  should: each emits a *different* prefix entry (`.or` emits the third of
  three) and continues into a different `∃p`-side traversal (`.atom` splits
  on `atomMem`, `.down (.up P')` re-enters `UEntry` through `negOfDownStab`
  under a `laxOf`, `.down (.circ P')` without it).  111 → 52 lines.
* **`URF` — equation folded, arms stayed.**  The five lax arms now name the
  unified equation; the arms themselves stay per-shape by the design pin's
  own criterion — `or1`/`or2` select prefix rows 1 and 2, and
  `.down (.up P')` / `.down (.circ P')` dispatch to different `UEntry`
  calls while `.down (.and _ _)` / `.down (.imp _ _)` are `nomatch`.
* **`UInvG` — nothing to migrate.**  Its arms (`.stable`, `.orL`, `.flsL`,
  `.downL`, `.atomL`) are already flag-generic; the row lists reach it
  only as the parameter `L`.  Recorded so round 3 does not re-survey it.
* **`ULF`, `UpElim`, `UpLF`, `UpInvG` — no membership blobs at all**; they
  thread `qmem`/`dmem`/`cmem`/`bmem` through unchanged.

### Discipline

Zero statement changes.  `satE2`, `satA2`, `CimpAnt`, `eSound`, `aSound`
keep their exact statements; all seven `#guard_msgs` axiom pins (five in
`LJFOCore.lean`, two in `LJFO.lean`) are untouched and re-verified, and
`wip.ljfo_theta_axioms` still builds clean with its five θ-family pins at
`[propext, Quot.sound]`.  `interpE_eq` and the five `*ConjMem` keep their
names and types up to the naming of the map.  `LJFOCore.lean` was not
touched.

### Metrics

| | before (797f301) | after |
|---|---|---|
| `LaxLogic/LJFO.lean` | 2726 | 2202 |
| `LaxLogic/LJFORows.lean` | 81 | 264 |
| built total | 2807 | 2466 (**−341, −12.1 %**) |
| `Archive/…round2-superseded.lean` | — | 224 (not built) |
| tail elaboration (`lean`, solo, core cached) | 1126 s | 1163 s (**+3.3 %**) |
| `LJFO.olean` (+`LJFORows.olean`) | 344.8 MB | 333.8 MB (−3.2 %) |

**The compile-time target was NOT met, and the round-1 style of estimate
that predicted it is withdrawn.**  The design pin set "1773 s tail
re-elaboration" as the baseline to beat; the honest like-for-like pair
(both runs `lean` on the tail alone, `LJFOCore` cached, nothing else on
the machine) is 1126 s → 1163 s — flat to within a few percent, if
anything marginally worse.  Two intermediate figures seen during this
session must NOT be quoted as a speedup: the 1740 s derived from the
baseline `lake` run's olean timestamps was contaminated by a concurrent
elaboration for 12 of its 29 minutes, and the post-change
`lake build LaxLogic.LJFO` of 1393 s is not comparable to it for the same
reason.

Why flat, in retrospect: the seven `rfl`s that closed the seven per-shape
equations still happen — they are now the seven branches of
`interp_circ_laxRows`'s `match Q`, because `interp`'s goal dispatch
genuinely needs the shape.  Round 2 removed the *restatement* of those
seven aggregates, not the *defeq checks* on them; and the collapsed
`UEntry` clause pays back a little by unfolding `laxRows`/`laxPrefix`/
`circStationRows` where the old clauses had the list spelled out.  The
deliverable is therefore source size and a single point of truth for each
station map — 55 inline membership blobs and five verbatim copies of the
19-line `∃p` map are gone — not wall-clock.

**Round 3 (NOT this session): farms / profiling / fidelity table.**  The
timing question above is precisely its remit: this session has one sample
per configuration, which bounds the answer at "flat" but does not
attribute the cost.  Profile before assuming any structural change here
buys elaboration time.

## Simp round 2 — retrospective (2026-08-12)

Continuing the method ledger (the numbering runs on from the review
round's item 8).  Round 2 is the first simplification round in this
development whose headline goal was *missed*, so the lessons are worth
more than the diff.

**9. Source duplication and elaboration cost are independent here — the
round's central finding, and it refutes the premise it was scoped on.**
The design pin named "1773 s tail re-elaboration" as the baseline to
beat, on the reasoning that seven restatements of one aggregate must cost
seven times.  They do not.  What the elaborator pays for is *defeq checks
on `interp` values*, and collapsing seven statements into one lemma with
seven branches leaves the number and the size of those checks exactly
where they were: 1126 s → 1163 s.  The rule for round 3 and after: in
this development, to buy elaboration time you must reduce the NUMBER of
defeq checks or the SIZE of the terms they run on.  Reducing the number
of *lines that mention* those terms buys readability and nothing else.
Never again scope a simplification round on a compile-time promise
without a profile first.

**10. The frozen core admits a middle module for free, and that is where
iteration is cheap.**  `LJFOCore.lean` has ZERO imports, and every
station equation needs nothing beyond `interp`.  So a module between the
core and the tail costs nothing structurally — and anything living there
type-checks in **0.4 s** against the cached core, against **19 minutes**
for the same content inside the tail.  Round 2's whole design
(`eConjRows`, `laxRows`, the membership combinators, the unified
equation) was developed and debugged in that 0.4 s loop and entered the
tail already correct; the one tail failure was in tail-only code.  Rule:
anything provable from the frozen core goes in `LJFORows.lean`, not
because the tail cannot hold it, but because the tail cannot afford to
iterate on it.  Layer 4's `interpF` row families are the next candidates.

**11. Time elaboration with bare `lean`, solo, like-for-like — mtimes are
not a measurement.**  The first figure this session reported was a 33 %
speedup.  It was wrong twice over: the "baseline" was derived from olean
timestamps inside a `lake` run that had a second elaboration on the
machine for 12 of its 29 minutes, and it was compared against a bare
`lean` number that excludes the 333 MB olean write and lake's overhead.
The correct protocol, used for the figures now in the log: `lean <file>`
on the tail alone, core cached, nothing else running, both sides, same
mode.  A `lake` number is a *build* measurement and is only comparable to
another `lake` number taken the same way.

**12. Where the sevenfold-ness is essential, and where it was
incidental — the map, for reuse.**  ESSENTIAL: `interp`'s ∀p goal
dispatch matches on the positive UNDER the `◯` (`| .circ (.atom q) =>`,
`| .circ .fls =>`, …), so no tactic can cross that wrapper at an abstract
`Q`; the shape analysis is irreducible and now sits in exactly one place,
`interp_circ_laxRows`'s `match Q`.  Also essential: any arm that SELECTS
a row (`URF`'s `or1`/`or2` take prefix entries 1 and 2) or DISPATCHES on
the shape (`.down (.up P')` vs `.down (.circ P')` enter `UEntry`
differently; `.down (.and _ _)`/`.down (.imp _ _)` are `nomatch`).
INCIDENTAL, and now gone: restating the aggregate once per shape;
re-proving row membership at each call site; opening each lax arm with
its own `nOrAll_inj` chain.  This map transfers directly to layer 4 —
`interpF` mirrors `interp` clause for clause with the (b)-guard at all
twelve modal sites, so it will grow the same essential seven and the same
incidental duplication unless the row families are named from the start.

**13. The deliverable that compounds is the single point of truth, not
the line count.**  Before: the 19-line `∃p` station map appeared verbatim
six times (`interpE_eq` plus five `*ConjMem`), the ◯-goal station map
seven times, and the membership argument at 55 call sites.  Changing one
row shape — which forced changes #2 and #3 each did — meant editing every
copy consistently, and a divergence between copies would have shown up
only as a mysterious defeq failure hundreds of lines away.  After: one
edit site each.  That is the answer to the standing point that stacked
layers are a HUMAN cost (item 8) even where the machine is indifferent —
which, as item 9 says, it turned out to be.

**14. One failed build, one cause: a rewritten lambda's binder list.**
`(fun _ hsp => laxRows_boxMem hsp)` against
`j = .lax → ∀ {R rest}, mem → …` bound `hsp` to the implicit `R`, not to
the membership: Lean auto-binds leading implicits when the lambda's FIRST
binder faces them, but once an explicit binder has been consumed the next
named binder takes the implicit.  The original wrote `fun _ {R rest} hsp`
and was right to.  Cost: one 22-minute cycle.  Rule: when replacing a
lambda in an argument position, keep the original binder list verbatim
and change only the body.

**15. Estimation bias, now recorded in both directions.**  The banked
calibration is that my refactor COST estimates run ~4× pessimistic.
Round 2 adds the opposite error on the other axis: the BENEFIT estimate
was optimistic — a predicted large compile-time cut, delivered flat.
Treat both as the same failure to measure before promising.

**16. What round 3 should ask first.**  Not "what else can be
deduplicated" — item 9 says that spends effort on the wrong axis.  Ask
where the 1163 s actually goes.  The three candidates worth profiling,
in order of suspected cost: the mega-mutual's well-founded packing and
its `decreasing_by` farm; the `rfl` defeq checks that close the aggregate
equations (each runs on `interp` values thousands of nodes wide); and
`interp`'s own equation-lemma generation.  Only after that does the
fidelity table have a cost model to sit on.

## Simp round 3 (2026-08-12): profiling, the farm, the tru-side map, the fidelity table

Matthew's steer before starting: compile time matters ("times are getting
long") but is worth about **10 % of the effort**, the rest on completing the
rounds.  Logged against that budget.

### 17. Where the 1163 s goes — all three of item 16's candidates are wrong

`lean -Dprofiler=true` on the tail, core cached:

| phase | time | share |
|---|---|---|
| **`simp`** | **811 s** | **68 %** |
| kernel type checking | 230 s | 19 % |
| process pre-definitions (WF packing) | 115 s | 10 % |
| elaboration | ~15 s | 1 % |
| linting | 4 s | <1 % |

Item 16 guessed the WF packing, the aggregate `rfl` checks and `interp`'s
equation-lemma generation.  The WF packing is 10 %, the `rfl` checks sit
inside elaboration and type checking, and equation-lemma generation does not
register.  **It is `simp`, and it is inside `decreasing_by`**: both farms
open with `all_goals simp_wf` and `all_goals try simp only [sum3,
sum3_append, goalW, wNeg, wPos]`, run over every decreasing goal the
eighteen-function mega-mutual generates, before a `first |` chain of 68
(`ljf_dec_e`) and 62 (`ljf_dec_a`) alternatives.

### 18. The farm: one dead alternative, found and removed; no duplicates exist

Two corrections to what the round assumed on opening.

* **The farms are not tail-only.**  `LaxLogic/LJF.lean`, the IPC control,
  invokes them seventeen times.  Any trim must keep that file green, so the
  probe target is `lake build LaxLogic.LJFO LaxLogic.LJF`.
* **There are no duplicate alternatives to delete.**  A first analysis
  reported 51; that was a parser running past the end of `ljf_dec_e` into
  `ljf_dec_a` and comparing the two macros' lists against each other.  Within
  true boundaries (2280–2399 and 2402–2545) both farms have zero
  byte-identical repeats.  The safe mechanical trim does not exist.

What does exist: `(simp_arith; done)` at **position 21 of 68 and 21 of 62**
is **DEAD in both farms** — deleted, and `LaxLogic.LJFO` and `LaxLogic.LJF`
both build green.  Every goal not closed by the first twenty alternatives
used to pay a full `simp_arith` before the remaining forty-odd were tried.
Recorded in both macro docstrings so it is not re-added blindly.

**Its timing effect was NOT isolated, and no speedup is claimed.**  The probe
build (core + LJF + LJFO, parallel, 30:59) is not comparable to the
LJFO-alone figure (26:03), and isolating it costs two more ~20-minute runs —
outside the budget.  What remains of the 811 s is `simp_wf` and the
unconditional `simp only`, both load-bearing.

**The method, for whoever continues.**  Delete-and-build is a decisive
one-bit test for a farm alternative at ~30 min a bit.  Do it in BATCHES:
delete a suspected-dead block, and bisect only if the build goes red.  At one
alternative per probe the remaining ~125 entries are unaffordable.

### 19. The tru-side station map — line-neutral, and that is the honest result

The map was spelled out verbatim in four `interpA_*` equations, exactly the
duplication `laxRows` removed on the lax side.  It is now `truStationRows`,
and all nine aggregate equations live in `LJFORows.lean` over the three named
maps.  A structural fact fell out worth keeping: `circStationRows` is
`truStationRows` **plus the single lax-only `circL` row**, so the entire modal
content of the aggregate is one row.

Numbers: **2466 → 2461 built lines, tail build 23:13 → 26:03.**  Line-neutral
and slightly slower — the 44 duplicated lines are offset by the named
definition and its pointer comments, and naming a map adds a delta-unfolding
step to many defeq checks.  This is item 9 again, now with a second data
point: in this development these refactors buy structure, not size and not
speed.  Keep them for the single point of truth, and stop predicting
otherwise.

### 20. The fidelity table

`docs/ljfo-fidelity.md`: per clause of `interp`, the move, the LJF◯ rule it
answers, whether soundness and minimality run on raw rules or a named toolkit
lemma, and whether Pitts/Dyckhoff make the corresponding move.  §4 is the four
forced departures; §5 the PROVED/conditional/OPEN ledger.  The correspondence
column is expository and says so.

Two claims corrected while writing it, both against the source, both of a kind
worth watching for: **`dykAnt` is not unconditional** (it is `dykAntC cAnt …`
inside the cAnt-parameterised mutual — `DykAnt` is not open, but it is
discharged *relative to* `CimpAnt`), and **`LJF.lean` is not a Liang–Miller
port** (its header records that it is built from its own rules so the
technique is what is under test).  The table also flags that
`docs/calculus-map.md` still has no LJF◯ entry.

### 21. Process note

A docstring-only edit to `LJFOCore.lean` costs a full 31-minute core + LJF +
LJFO rebuild.  Bundle comment edits with the build that tests them; this round
spent one rebuild on a comment.

### 22. The focused profile: there is no hot spot, and a fifth of the build is the audit

Matthew, 2026-08-12: *"we can't do 125 × 30 minute probes, and I find them of
questionable use, but that may be because they are not sufficiently
focussed."*  Both halves are right.  Delete-and-build answers one bit per
30 minutes and was the wrong instrument; the right one is
`-Dtrace.profiler=true`, which nests by tactic invocation and marks each
`first` alternative ✅/❌ with its own time.  `-Dprofiler=true` only reports
per-COMMAND aggregates, which for a single mega-mutual is one number ("simp
811 s") with no way to see which simp.  One traced run answers what 125
probes would have.

**Finding 1 — there is no hot spot.**  At a 250 ms threshold, *three* tactic
nodes in the entire file exceed it.  The farm's cost is thousands of
individually-cheap calls, not a slow tactic.  So trimming alternatives can
only ever shave a fraction, however many are dead: the probes were indeed of
questionable use, and not because they were badly run.

**Finding 2 — two nodes dominate.**

| node | traced time | what it is |
|---|---|---|
| `Elab.def.processPreDef` | 1114 s, **one** node | the mega-mutual's WF pre-definition processing — every `decreasing_by` run lives inside this |
| `#print axioms LJFO.satE2` | 223 s (`Kernel` 219 s under `Elab.async`) | the AXIOM PIN, not the proof |

The 223 s matches the 230 s that `-Dprofiler=true` reported as "type
checking" almost exactly, so it is not a tracing artifact: **about a fifth of
the tail's build is the kernel checking `satE2` when `collectAxioms` forces
it at the pin.**  That is the price of the machine-checked mandate on a term
this size, it is not optional, and it should be counted as audit cost rather
than proof cost when the build time is discussed.

**Finding 3 — the lever, and it is not the farm.**  What makes each of the
thousands of calls cost anything is the *goals*: eighteen mutually recursive
functions, each contributing decreasing goals over a lexicographic measure
containing `3 ^ wNeg G` on large terms.  Fewer functions in the mutual, or a
cheaper measure, would move the needle.  Deleting `first` alternatives will
not.  **Recommendation: stop trimming the farm.**  `(simp_arith; done)` was
worth removing because it was dead, but it was never going to be the answer.

**Note for anyone re-running this**: with tracing on, the two `#guard_msgs`
pins FAIL and `lean` exits 1 — trace output is appended to the message the
docstring is compared against (`+ trace: [Elab.command] …`). The axiom lines
themselves are correct. This is an artifact of tracing, not a broken tree;
the untracked build at the same commit is green.

### 23. Correction to item 22: the satE2 pin is proof cost, not audit cost

Item 22 said "about a fifth of the tail's build is the kernel checking
`satE2` when `collectAxioms` forces it at the pin", and called it audit cost.
The audit-cost half of that is **WRONG and is withdrawn**; the arithmetic is
right, the attribution is not.

Tested by moving all seven pins into `LaxLogic/LJFOAudit.lean`, which nothing
imports (2026-08-13, Matthew's direction on separate grounds):

| step | time |
|---|---|
| `LaxLogic.LJFOCore`, five pins removed | 3:19.80 |
| `LaxLogic.LJFO`, two pins removed | **27:49.78** (was 26:03 *with* them) |
| `LaxLogic.LJFOAudit` — all seven pins | **1.8 s** |

No saving.  The kernel check of `satE2` happens when `LJFO.olean` is written;
`#print axioms` merely AWAITED that asynchronous task, so the profiler
attributed the wait to the pin.  It is the price of having `satE2` at all.

Two lessons, both instances of ones already in this ledger:

* **Item 11 again** — a profiler attributes time to the node that *waits*
  for asynchronous work, not to the node that *causes* it.  Under async
  elaboration, "command X took N s" means "X did not return for N s".
* **Item 9/15 again** — I predicted a saving and measured its absence, for
  the third round running.  The rule earned here: with async elaboration,
  never treat a profiler attribution as a cost that can be *moved* until the
  move has been measured.

What the move is still worth, on Matthew's ground and not on speed: the pins
are a periodic check rather than a per-edit one, since by design this
development uses no `sorry` outside `wip/` without his authorisation.  And
the same measurement makes that cheap — **the full audit costs 1.8 s**, so
`lake build LaxLogic.LJFOAudit` before any commit that changes a proof is
free.  What it costs is that a `sorryAx` regression is no longer caught by
the default build.
