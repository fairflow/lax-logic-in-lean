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
