# Route (B) read-through — simplification, shortening, presentation
Started 2026-09-05 19:35 BST at frjw-dev 2cc7826 (WP1c and WP2 in flight).
Scope: LJF/OFuel*.lean (13 modules, ~10 200 lines), wip/ui_routeB_*.lean.
Method: read, do not prove.  Notes per module, then cross-cutting themes.

## Sizes (lines)
OFuel 311 · OFuelSound 1642 · OFuelMin 755 · OFuelHeight 1182 · OFuelP 610 ·
OFuelPSound 1937 · OFuelPMin 650 · OFuelPCof 390 · OFuelPFamKit 278 ·
OFuelPFam 1958 · OFuelPCofinal 124 · statements 182 · blueprint 175.
Two parallel chains: interpF (OFuel/OFuelSound/OFuelMin ≈ 2 700) and interpP
(OFuelP…OFuelPCofinal ≈ 5 950); OFuelHeight serves both.

## Per-module notes

### LJF/OFuelP.lean (610) — the definition `interpP`
Read in full.
* STRUCTURE: fuel-0 defaults (⊤ in ∃p mode, ⊥ in ∀p mode); processing phase
  (13 clauses, all "park" or "split"); aggregate phase = findFire, then
  ∃p read-off (one match over the 8 parked shapes) or ∀p by goal shape.
* THE BIG DUPLICATION: the ∀p mode has ELEVEN goal-shape blocks
  (↑q, ↑⊥, ↑(P₁∨P₂), ↑↓M, ◯q, ◯⊥, ◯(P₁∨P₂), ◯↓↑P′, ◯↓◯P′, … plus ⊃ and ∧
  goals) and each block repeats verbatim the same six "context attack"
  arms (q-implication, Dyckhoff, ◯-implication, three parked shapes) and,
  for ◯ goals, a seventh arm (a parked box opened).  Only the HEAD rows
  differ per goal shape (direct attempts: sub-goals, the boxed opening).
  ~300 of the 610 lines are this repetition.  The comment says "inlined
  per goal shape so each aggregate case is self-contained"; the cost is
  paid three more times downstream (OFuelPSound's eleven ∀p cases,
  OFuelPMin's row lemmas, OFuelPFam Part 3's row-block record — the
  "second copy of the row spec" that hid two of WP1a's fourteen sites).
* PROPOSED FACTORING (no termination cost): recursion is structural on
  the fuel, so the smaller-fuel function `interpP p f` is a VALUE that a
  non-recursive helper can take:
      attackRows (rec : List Neg → List Neg → Option Neg → Neg)
                 (done : List Neg) (G : Neg) : List Neg     -- the 6 (+1) arms, ONCE
      headRows  (rec) (done) : Neg → List Neg               -- per goal shape
      ∀p aggregate at G := nOrAll (headRows … G ++ attackRows … G)   (boxed for ◯ goals)
  and the same for the ∃p read-off (`existsRows`).  Then: one row-membership
  lemma per ARM (not per arm × goal shape), one soundness lemma per arm,
  the family's row-block record disappears (it IS attackRows), and the
  ∀p attack row of the record becomes a definitional unfolding.
  Estimated effect: OFuelP −250 lines; OFuelPSound −600 (eleven cases → one
  parametric case); OFuelPMin −150; OFuelPFam Part 3 −200.
* SMALLER: `pGuard p a nTop (…)` / `pGuard p a nBot (…)` idiom fine.
  `| _ => nTop` / `| _, _ => nBot` "unreachable shapes" arms rely on
  ParkedCtxP; a `match` on a `ParkedNP`-refined subtype would make the
  unreachable arms vanish and the soundness cases exhaustive by
  construction (optional; costs a dependent match).
* PRESENTATION: the header narrates the campaign ((a)(b)(c), dates,
  "purely additive", "generated from OFuel.lean").  For a reader, lead
  with the SPECIFICATION: "interpP p f todo done g is the fuel-f
  approximant of ∃p (g = none) / ∀p at goal G (g = some G) of the station
  (todo, done)", a TABLE of the row shapes (parked shape → ∃p row, ∀p
  attack row), then the invariants (ParkedCtxP, Saturated), then code.
  Move the history to the record.
* SANITY SECTION: the three `decide` agreements with interpF at fuels 0–8
  and the three ≠ controls are good and cheap (60 s); keep.  They are the
  only remaining USE of interpF in the P-chain (see cross-cutting).
* PINS at the end are `[propext, Classical.choice, Quot.sound]` for two
  trivial lemmas (`ParkedNP.of_parkedN`, `ParkedCtxP.cons`) — the choice
  there is from `List.mem` decidability via `rcases`/classical? worth a
  look: these should be choice-free; a `Decidable` leak in a lemma used
  everywhere is a pin-widening source downstream.

### LJF/OFuelPSound.lean (1937) — soundness at every fuel
* TEN declarations; `aSoundP` alone is 1529 LINES (one definition), `eSoundP`
  222.  `aSoundP` mirrors interpP's ∀p mode case by case: eleven goal-shape
  blocks × the same seven attack arms, each arm's soundness re-derived in
  place (WP1a's report: "the eleven ∀p rows … are plain `atkPark`" — i.e.
  eleven copies of ONE lemma application).  With `attackRows` factored in
  the definition, this becomes: one lemma `attackRows_sound` (per arm, 7
  cases) + one lemma `headRows_sound` (per goal shape, the genuinely
  different part) + a 30-line `aSoundP`.  Estimate: 1529 → ~350.
* `atkPark` (35 lines) is already that generic lemma; the eleven blocks
  just call it eleven times with the same shape of argument.
* GOOD: `ESoundP'`/`ASoundP'` "statements witnessed" section (statement
  as a `Type`, proof as its inhabitant) is the right presentation — the
  reader sees the theorem before the 1500-line proof.  Move it to the TOP
  of the module (statement first, proof after), and put the pins beside it.
* The Dyckhoff exercising cell + `interpP_dykStation_row` (by `rfl`) is a
  good negative control; keep, 30 lines.

### LJF/OFuelPMin.lean (650) — rows at fuel, processing-phase minimality
* Three separate "station maps" (`eConjRowsP`, `truStationRowsP`,
  `circStationRowsP` + `laxPrefixP`/`laxRowsP`) each followed by one
  membership lemma PER PARKED SHAPE (8 + 7 lemmas), plus seven
  `interpPA_*_eq` equations (one per goal shape).  All of this is the
  definition's own structure restated so proofs can `rw` with it.  With
  `attackRows`/`headRows` in the definition, the station maps ARE the
  helpers, the membership lemmas become one lemma each (`mem_attackRows`,
  `mem_headRows`), and the seven `interpPA_*_eq` become one unfolding.
  Estimate: 650 → ~300.
* `eMinPP`/`aMinPP` (85/129) — the processing-phase minimality — fine;
  they are the real content of the module.
* `SatE2P`/`SatA2P` are DEFINED here (Part 5) but the reader looks for
  them in OFuelPCof/OFuelPCofinal.  Put the statements in one place: a
  small `OFuelPStatements.lean` (or the top of OFuelPCofinal) holding
  ESoundP', ASoundP', SatE2P, SatA2P, ECofinalP, ACofinalP, TInvP, UEntryP,
  ParkAntP — every route-(B) statement on one page, each with the pin of
  its inhabitant.  Today they are spread over five modules.

### LJF/OFuelPCof.lean (390) — entry points, reductions, dispatch, UpFrom kit
* The header (75 lines) is a campaign narrative: the measure table, "What
  is OPEN" (now FALSE: the family is proved), the refutation of the
  height order for interpF.  Headers age badly; keep only what is
  timeless here ("this module states the two entry points and proves
  the reductions and the dispatch lemma") and point to the record for
  history.  Same disease in OFuelP, OFuelPFam, OFuelPCofinal headers.
* `UpFrom` kit (`map₂`, `map₃`, `UpFrom2.map₂`, `toUpFrom2`, later
  `mk1`/`mk2`/`map` in the family): exists because "interpP has no
  chain-monotonicity lemma".  ONE lemma — chain monotonicity,
      E_{f+1} ⊢ E_f     and     E_f, A_f ⊢ A_{f+1}  (A modulo E)
  — would let every traversal return a derivation at ONE fuel and delete
  the upward-closed machinery from the family (thresholds by `max`,
  re-reads at the common threshold, `mk2`'s "two fuel units").  But
  monotonicity itself needs to compose derivations inside row shapes,
  i.e. CUT for `Inv` — the same `CutInv` that N3's backward direction
  needs.  See cross-cutting: one admissibility lemma is the key to
  several simplifications.
* The five `*FireE` instances of `parkFireE` (50 lines) are again per
  parked shape what one lemma over `attackRows` would be.

### LJF/OFuelPFamKit.lean (278) + LJF/OFuelPFam.lean (1958) — the family
Read: Parts 2, 3 (assemblers, RowKit), `TStabQ` in full, `UStabQ`'s arms,
the p-eliminator group's header, Parts 5–8 headers.
* THE TWENTY PARKED ARMS ARE ONE ARM.  In `TStabQ` the five parked-
  implication cases (◯-imp, Dyckhoff, ∨-imp, ↓↑-imp, ↓∧-imp) are
  textually identical 9-line blocks differing ONLY in the name of the
  `*FireE` instance; the same five-fold block recurs in `TpElimQ`,
  `UStabQ` (with `*FireA` and `kit.{d,c,o,s,a}mem`) and `UpElimQ`.
  `parkFireE`/`parkFireA` are already generic; `parkAntP_of_satA2P` and
  `hgt_antDispatch` are already generic in the antecedent positive `Q`.
  What keeps the five apart is only that the DEFINITION distinguishes
  them (five constructors of `ParkedNP`, five ∃p read-off arms, five
  `*ConjMemP` lemmas, five `RowKit` fields, five `*FireE`/`*FireA`
  instances).  See cross-cutting theme 1.
* THE DYCKHOFF RESIDUAL CONJUNCT IS DEAD for cofinality: the ∃p row of
  `↓(Q′ ⊃ N′) ⊃ N` carries a second conjunct `E(↓N′ ⊃ N :: rest)`
  ("the E-res component") that NO clause of the family or the kit uses
  (grep: 0 hits in OFuelPFam/OFuelPFamKit; the Part 3 docstring says
  "the residual ignored").  It survives only as a soundness obligation
  (`resSim`, 5 mentions in OFuelPSound) and in `dykConjMemP`'s statement.
  Dropping it makes the Dyckhoff row IDENTICAL to the generic parked row
  `(↓A(done ⇒ ↑Q) ⊃ E(N :: rest)) ∧ E(rest)` — the last asymmetry
  between the five shapes.  (Check before dropping: is the residual used
  by the E-side MINIMALITY of the processing phase, `eMinPP`?  grep says
  OFuelPMin mentions it only in the row statement.  A one-cell negative
  control — a station whose consequence needs the residual — should be
  attempted first; if none exists, drop.)
* `RowKit` (86 lines, 8 fields) is the "second copy of the row spec"
  (WP1a's finding).  With `attackRows` in the definition its fields are
  `hV` + ONE membership fact `∀ X rest, (X, rest) ∈ splits done →
  attackRow X rest ∈ L f`, i.e. `mem_attackRows` — the structure becomes
  two fields or disappears.
* The p-eliminator group (`TpElimQ`, `TpLFQ`, `TpInvQ`, `UpElimQ`,
  `UpLFQ`, `UpInvGQ`; 6 of 17, ~430 lines) exists because a fire on the
  ELIMINATED atom `p` continues under a different invariant (the spliced
  `lfP`, whose height is why their measure is `hgt + hgtL lfP`).  Not a
  cheap merge; leave, but give the group a 10-line explanation at its
  head in these terms (today the reader reconstructs it from §4.17).
* NAMING: `T*`/`U*` (∃p/∀p traversals, from `LJF/O.lean`), suffix `Q`
  (the fuel-carrying version), `eMinQ`/`aMinQ`, `RF`/`LF`/`Inv`/`Stab`/
  `Elim` — a GLOSSARY TABLE (judgement form × side → name → what it
  returns) at the top of OFuelPFam would save every reader an hour.
* STALE PROSE: the Part 5 header still says "the antecedent guards are
  the two parameters, so no clause calls the ∀p side" — false since WP1b
  (the guard is native, the SCC is whole, one mutual of 17).  Part 4's
  "WITHDRAWN" section is history that belongs in the record, not in the
  module.  Same for the module header's measure narrative.
* KIT: `ljf_dec_h`/`ljf_dec_p`/`hgt_*` macros are the right idea (one
  tactic per edge class); `wip/hgt_probe.lean` as a 3.7 s bench is
  exactly the working method to keep.  After WP1c (budgets) most of the
  Part 4b height machinery moves out of the recursion into ordinary
  lemmas; re-check what is still needed then.
* `UpFrom`/`UpFrom2` plumbing (`mk1`, `mk2`, `map`, `map₂`, thresholds by
  `max`, "two fuel units" at ◯ clauses) is ~15% of every definition.  It
  goes away with chain monotonicity, which needs `CutInv` (theme 4).

### LJF/OFuelPCofinal.lean (124) — the read-off
* Good: statements and inhabitants together, pins beside them.  Two
  things to move IN here (or into a statements module): `SatE2P`/`SatA2P`
  (now in OFuelPMin Part 5) and `ESoundP'`/`ASoundP'` (OFuelPSound), so
  that every route-(B) theorem statement is on one page.
* `ECofinalP`/`ACofinalP` carry a single fuel `Σ f`; the `UpFrom` forms
  `SatE2P`/`SatA2P` are the ones N3 uses.  Say so in the docstrings, or
  state ECofinalP in the UpFrom form and derive `Σ f` (then "N0d's
  upward-closed forms" stop being a separate drafted node).

### LJF/OFuelHeight.lean (1182) — the height table
* Parts 1–6 (~440 lines): size functions and the transformers' bounds —
  live, used by Part 10.  Parts 7–9 (~400 lines): the REFUTATIONS of the
  height-first order for interpF (`invImpOr`/`invStrip`/`invCurry` rise,
  `negOfDownStab`/`dykCommute` unbounded, max-height fails) and the
  verdict/design sections.  Those are evidence for a decision already
  taken (parking) and recorded in the clause table §4.13; they are not
  used by the P chain.  Keep them building (they are kernel-checked
  refutations) but move them to `LJF/OFuelHeightEvidence.lean` off the
  P chain's import path, so the live table is Parts 1–6 + 10 (~780).
* Part 10 is the interface the family uses; after WP1c the family will
  consume its lemmas as ordinary bound proofs.  Its 10.8 "what Part 10
  does NOT establish" is exactly the two facts WP1b had to add
  (`hgt + hgtL lfP` for the p-eliminators; the cast); fold them in.

### The interpF chain: OFuel (311), OFuelSound (1642), OFuelMin (755)
* `interpF` and `interpP` differ in 145 of ~360 clause lines: the three
  reshaping clauses vs parking, the Dyckhoff guard, and the three extra
  parked-shape rows (which are the ONLY reason interpP's ∃p read-off and
  eleven ∀p blocks are longer).  Everything else is byte-identical.
* OFuelSound (`aSoundF` 1312 lines, `eSoundF` 220) and OFuelMin
  (`eMinFF`/`aMinFF`, the row lemmas, `CimpAntF`, the termination note)
  are SHADOWED one-for-one by OFuelPSound/OFuelPMin/OFuelPCof; the F
  chain's cofinality was never completed (stopped at the founding).
* Supersession check (skill `constraint-supersession-check`), interpF chain
  → interpP chain:
  | constraint | source | interpF chain | interpP chain | verdict |
  | soundness at every fuel (N0a) | blueprint N0a | eSoundF/aSoundF | eSoundP/aSoundP, same pins | DISCHARGED |
  | rows, processing minimality, reductions (N0b) | blueprint N0b | OFuelMin | OFuelPMin/OFuelPCof | DISCHARGED |
  | the retention obligation as an instance of ∀p-cofinality | OFuelMin Part 6 | cimpAntF_of_satA2F | parkAntP_of_satA2P (all shapes) | DISCHARGED |
  | reference definition for the kernel agreement checks | OFuelP sanity § | interpF itself | — | keep OFuel.lean (311) |
  | the founding refutation record (§4.11) | clause table | OFuelMin termination note | recorded in §4.11/§4.13 prose | LAPSED as code, kept as record |
  | transport to PLL via the processed station (N6 "depends on N0b") | blueprint N6 | eMinFF | eMinPP | DISCHARGED once N6 is stated over interpP (WP2) |
  Re-opened: none.  → archive OFuelSound + OFuelMin (2 400 lines) to an
  `Archive`/`Reject`-style location off the default targets once the
  blueprint's N0a/N0b/N6 point at the P chain; keep OFuel.lean for the
  agreement theorem.

### wip/ui_routeB_statements.lean (182), wip/ui_routeB_blueprint.lean (175)
* Statements file: after WP1b it is mostly a re-export of OFuelPCofinal
  plus the interpF forms `ECofinalF`/`ACofinalF` and prose.  Fold: keep
  only what is NOT in production (the F forms, which are superseded, see
  above) — likely delete after the supersession is recorded.
* Blueprint file: N1–N6 drafted over interpF with `sorry` bodies (by
  direction).  WP2 restates N1–N3 over interpP in `wip/ui_routeB_n3.lean`;
  when it lands, retarget N4–N6 to interpP and retire the interpF
  drafts, so that there is ONE statement of each node.

## Cross-cutting themes (ordered by value ÷ cost)

**1. Five parked shapes → one.**  The parked implications are exactly
`Q ⊃ N` with `Q` a compound positive (`Q₁ ∨ Q₂` or `↓M`, any `M`); the
atom case fires and `⊥ ⊃ N` is dropped.  `interpP` treats all five the
same way (park; ∃p row `(↓A(done ⇒ ↑Q) ⊃ E(N :: rest)) ∧ E(rest)`; ∀p
attack row `A(done ⇒ ↑Q) ∧ A(N :: rest ⇒ goal)`), except the dead
Dyckhoff residual.  Make the definition say so: `ParkedNP` with FOUR
constructors (`atom`, `qimp`, `box`, `pimp : CompoundPos Q → ParkedNP (Q ⊃ N)`),
one ∃p arm, one attack arm, one `*ConjMemP`, one `*FireE`/`*FireA`, one
`RowKit` membership field, one family arm in each of the four
arm-bearing definitions (20 → 4).  Every proof that is now written five
times is written once.  Estimated removal: ~1 500 lines across
OFuelP/OFuelPSound/OFuelPMin/OFuelPCof/OFuelPFam, and the class of
"forgot one of the five" defects (WP1a's fourteen sites) disappears.
Precondition: the Dyckhoff residual conjunct is dropped (negative-control
hunt first) or kept as a uniform extra conjunct `E(rest')` for all shapes.

**2. Factor the ∀p mode: `attackRows`/`headRows`.**  Structural recursion
on the fuel lets a non-recursive helper take `interpP p f` as a value, so
the eleven goal-shape blocks become `headRows G ++ attackRows done G`
(boxed for ◯ goals).  With theme 1 the attack list is a `map` over
`splits done` with a 3-way match (q-implication, compound-antecedent,
box).  Collapses `aSoundP` (1529 lines → ~350), the seven `interpPA_*_eq`
equations, the fifteen membership lemmas, and `RowKit`.

**3. One page of statements; headers without history.**  A module
`LJF/OFuelPStatements.lean` (or the top of OFuelPCofinal) holding, as
displayed `Type`s: `ESoundP'`, `ASoundP'`, `SatE2P`, `SatA2P`, `ECofinalP`,
`ACofinalP`, `TInvP`, `UEntryP`, `ParkAntP`, and later N1–N6 — each
with the pin of its inhabitant.  Module headers state what the module
defines and proves; dates, "WITHDRAWN", "what is OPEN", measure
narratives and refutation stories go to `docs/ui-ljfo-clause-table.md`,
which already has them.  (Four headers are already wrong about the
current state.)  A glossary table for the family's names.

**4. Cut for `Inv` — one lemma, several simplifications.**
    CutInv : Inv Γ [] tru N → Inv (N :: Δ) [] j ψ → Inv (Γ ++ Δ) [] j ψ
LJF◯ has no cut lemma; completeness is only for `negOfO`-polarised
contexts.  Routes: (a) cut admissibility for the focused calculus
directly (Liang–Miller style, with ◯ — the unfocused SC in this repo has
cut elimination already); (b) polarisation invariance
`Inv Γ [] j N ↔ Inv (Γ.map (negOfO ∘ eraseNeg)) [] j (negOfO (eraseNeg N))`
+ `Inv.sound` + `FocalizationPLL`.  Pays for: N3 backward (WP2 states it
as the obligation); chain monotonicity `E_{f+1} ⊢ E_f`, `E_f, A_f ⊢ A_{f+1}`,
which deletes the `UpFrom` plumbing from the family and lets cofinality
be stated at one fuel; and probably several ad-hoc transformers
(`unStable`, `fireClean`, `boxClean`, `simHyp`) become instances of cut +
weakening.  This is the one NEW theorem in this list; everything else is
refactoring.

**5. Archive the interpF chain** (table above): OFuelSound + OFuelMin
off the default targets; OFuel.lean stays for the agreement theorem;
blueprint N0a/N0b/N6 re-pointed to the P chain.  −2 400 lines of live
maintenance.  OFuelHeight Parts 7–9 likewise to an evidence module.

**6. Build time** — WP1c (explicit budgets) in flight; with themes 1–2
the family itself shrinks by roughly half, which compounds.

**7. Pins to look at**: `ParkedNP.of_parkedN`, `ParkedCtxP.cons` at
`[propext, Classical.choice, Quot.sound]` for trivial lemmas — likely a
`Decidable`/`rcases` leak; worth making choice-free since they sit under
everything (a widening source once WP1c removes the recursion's choice).

## Suggested order
1. WP1c lands (budgets) → verify.                          [in flight]
2. Theme 1 + 2 as ONE refactor of the definition, soundness re-proved
   first (the WP1a pattern: definition, `eSoundP`/`aSoundP` at the same
   pins, `dykStation` control, then rows, then family arms).  Statements
   unchanged, so WP2's N3 is unaffected.                     [1–2 runs]
3. Theme 3 (statements page, headers, glossary).            [hours, no Lean risk]
4. Theme 5 (archive F chain, evidence module) with the supersession
   table in the commit.                                     [hours]
5. Theme 4 (`CutInv`) as its own work package, refute-first: state,
   screen on the corpus, then build via (b) or (a).         [days]
6. Theme 7 (pins).                                          [minutes]

Not proposed: merging the p-eliminator group; changing the judgement-
form-per-definition structure of the family (it mirrors the calculus,
which is the right shape for a reader who knows LJF).
