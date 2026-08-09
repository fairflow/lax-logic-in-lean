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
  laxness for free);
* for each parked box `circ R`: the opening attack
  `interp p [↑R] rest (some (circ Q))` — goal kept, station opened
  (no guard: opening is free given the box);
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
