# WP12c — cofinality for the pair-recording recursion `interpR`

Route (B), node **N4**, the last open obligation of the route.  Started
15:35 BST, 2026-09-06 (this run 16:18–17:20).

Every claim below is **PROVED** (a named Lean declaration, sorry-free, pin
measured with `#axioms_within_pin` and asserted with `#axioms_within`),
**REFUTED** (kernel-checked countermodel), **OPEN** (a typed obligation, no
term built) or **DESIGN** (a statement written down, not through a refutation
stage).

**Headline.**  The induction is NOT closed.  What this run delivers is seven
sorry-free modules and one statement-level result: the escape statements
handed over by §4.32 **cannot support the induction as written**, for a
reason that is exact and localised, and the repair that does support it
replaces formula-level escapes by **derivation-level** ones.  `SatE2R` /
`SatA2R` — hence `PLL_UI` through `pll_ui_R` — are now reduced to two typed
obligations of that shape, named verbatim in §6.

Modules, all leaves under `wip/`, `LJF/` untouched:

| module | contents | build |
|---|---|---|
| `wip/ui_routeB_r_seenmono.lean` | record monotonicity of `interpR` | 31 s |
| `wip/ui_routeB_r_esc2.lean` | the escapes restated station-free; the four structural steps | 10 s |
| `wip/ui_routeB_r_escd.lean` | the derivation-level design; `SatE2R`/`SatA2R` reduced to it | 31 s |
| `wip/ui_routeB_r_proc.lean` | the processing phase of the family, at every record | 23 s |
| `wip/ui_routeB_r_procd.lean` | the same block carrying derivation-level escapes | 15 s |
| `wip/ui_routeB_r_guard.lean` | both ends of the escape mechanism: the cut site and the recording-site loop | 36 s |
| `wip/ui_routeB_r_rows.lean` | the row layer for `interpR` at a saturated station | 10 s |

---

## 1 · Record monotonicity — PROVED

`wip/ui_routeB_r_seenmono.lean`.  `wip/ui_routeB_r_mono.lean` reads the
polarity table along the FUEL; this reads it along the RECORD.  With

    SeenLe s s'  :=  ∀ Q done, seenMemR s Q done = true → seenMemR s' Q done = true

    interpR_seenMonoE : SeenLe seen seen' →
        Inv [interpR p f todo done none seen] [] .tru (interpR p f todo done none seen')
    interpR_seenMonoA : SeenLe seen seen' →
        Inv [interpR p f todo done (some G) seen'] [] .tru (interpR p f todo done (some G) seen)

at every state, every fuel and every so-related pair of records; plus the two
instances the record's one growth step uses, `interpR_seenStepE` /
`interpR_seenStepA` at `seen` versus `(Qa, done) :: seen`.  Pins
`[propext, Classical.choice, Quot.sound]`, the choice from `impMono`'s cut.

The proof is `wip/ui_routeB_r_mono.lean`'s operator lemma over `stepR`, the
sixteen processing clauses discharged against an abstract approximant.  The
one new case carries the content: at a parked implication the loop test may
fire against `seen'` and not against `seen`, and then the `∃p` row is `⊤` on
the right (so entailed) and the `∀p` row is `⊥` on the left (so entailing).

Gate watched failing: `interpR_seenMonoE` pinned at `[propext, Quot.sound]`
errors with

    'LJFO.interpR_seenMonoE' depends on Classical.choice, which the bound does not allow.
      declared: [propext, Quot.sound]

---

## 2 · Why §4.32's escape statements cannot support the induction

§4.32 (`wip/ui_routeB_r_esc.lean`) indexes the escapes by the CURRENT
station:

    escRowsR p f done seen = [ A^R(done ⇒ ↑Q | seen) | (Q,T) ∈ seen, sameSet T done ]
    escConjR p e done seen = [ ↓A^R(done ⇒ ↑Qa | (Qa,done)::seen) ⊃ E^R([N],rest | seen)
                             | (Qa ⊃ N, rest) ∈ splits done, seenMemR seen Qa done ]

Both lists therefore CHANGE along every station-changing edge, and no clause
of the induction can move them.

* **`∀p`.**  The station-attack clause reads its continuation at the residue
  state `([N], rest)`, which saturates to some `done''`; its escapes are
  those of the pairs set-equal to `done''`.  A recorded pair `(Q,T)` with
  `sameSet T done''` and NOT `sameSet T done` produces a disjunct there that
  is not a permitted disjunct of the conclusion at `done`, and the two
  `interpR` values sit at different, unrelated stations, so nothing converts
  one into the other.
* **`∃p`.**  Dually the conjuncts are HYPOTHESES: applying the induction
  hypothesis at the residue state requires SUPPLYING the residue's cut
  conjuncts, and `E^R(done | seen)` together with the conjuncts at `done`
  does not supply them.

This is a statement fault, not a proof fault.  §4.32's statements are not
refuted — no countermodel is claimed — they are **unsuitable**: the step at
which they must move has no clause.

---

## 3 · The station-free restatement, and its four steps — PROVED

`wip/ui_routeB_r_esc2.lean`.  Index the escapes by the RECORD alone; each
recorded pair carries its escape at its OWN station, under the record it had.
The record is a list built by consing, so "the record it had" is the tail:

    escConjS p e []        = []
    escConjS p e (QT :: s) = interpR p e [] T none s                :: escConjS p e s
    escRowsS p f []        = []
    escRowsS p f (QT :: s) = interpR p f [] T (some ↑Q) (QT :: s)   :: escRowsS p f s

    escHyp  p e done seen  = nAndAll (interpR p e [] done none seen :: escConjS p e seen)
    escGoal p f done g seen = nOrAll (interpR p f [] done (some g) seen :: escRowsS p f seen)

Neither list takes a station argument, so both are LITERALLY unchanged along
every edge but the guard call.  The `∃p` conjunct of a pair is its station's
`∃p` approximant under the record BEFORE it was recorded — the record under
which the row the loop check later cuts is still present.  The `∀p` escape is
its guard sequent's `∀p` approximant under the record as EXTENDED by it —
literally the guard conjunct of `parkRowAR` at the recording site.

The statements over them are `SatE2RS` / `SatA2RS` (typed obligations, OPEN).
PROVED: the specialisation (`satE2R_of_escapesS`, `satA2R_of_escapesS`,
`pll_ui_R_escS`) and the four steps at which the record changes.

    escHyp_record   : Inv [escHyp p e done seen] [] .tru
                          (escHyp p e done ((Qa, done) :: seen))
    escGoal_absorb  : Inv [escGoal p f done (↑Qa) ((Qa, done) :: seen)] [] .tru
                          (nOrAll (interpR p f [] done (some ↑Qa) ((Qa, done) :: seen)
                                    :: escRowsS p f seen))
    escHyp_recorded : Inv [escHyp p e done (t ++ (Q,T) :: s)] [] .tru (escHyp p e T s)
    escGoal_escape  : Inv [escGoal p f T (↑Q) ((Q,T) :: s)] [] .tru
                          (nOrAll (escRowsS p f (t ++ (Q,T) :: s)))

The first two are the guard call: the `∃p` hypothesis at the extended record
is supplied by the one in hand (its new head is the head we hold, its old
head weakens by §1), and the escape the extension adds IS the guard conjunct,
so the extended conclusion collapses to "the guard conjunct, or an escape
already permitted here".  The last two are a cut site: the statement at the
recorded station and record has its hypothesis among our conjuncts and its
conclusion among our escapes.

Gate watched failing: `escGoal_absorb` at `[propext]` errors with "depends on
`Quot.sound`, which the bound does not allow".

---

## 4 · Where the FORMULA-level design still bottoms out — the ∃p side

The restatement repairs propagation.  What it does not repair is one step
INSIDE the `∃p` traversal, and that step decides the design.

At a station attack on a parked `Qa ⊃ N ∈ done` whose row is NOT cut, the
`∃p` traversal must discharge the row's guard

    A^R(done ⇒ ↑Qa | (Qa, done) :: seen)

and only the `∀p` statement at the extended record supplies it.  Carrying
formula-level escapes, that statement returns a DISJUNCTION,

    A^R(done ⇒ ↑Qa | (Qa,done)::seen)  ∨  ⋁_k A^R(T_k ⇒ ↑Q_k | u_k) ,

and in escape branch `k` the `∃p` traversal holds a `∀p` formula about an
ANCESTOR station `T_k` and must still prove its own goal `ψ`.  What the
branch yields is, through the conjunct `E^R(T_k | s_k)` and that station's
own row, the `∃p` approximant at the ancestor's fire state
`([N_k], rest_k)`; to use it one needs a derivation of `ψ` THERE, and the
only route to one is to transport the current derivation, which is a cut, so
its height is not controlled and the family's measure — `(normalised
derivation height, station weight, sizeOf)`, `LJF/OFuelPFamKit.lean` Part 4b
— cannot pay for the step.  §4.20's table decides this: the step needs a
height-strict edge and has only a weight-strict one.

The two obvious variants are worse, not better:

* putting the escapes into the `∃p` CONCLUSION blocks the traversal, which
  replays the goal's own introductions (`impR`, `andR`, `circR`) and cannot
  do so under a disjunction;
* putting them into the `∃p` HYPOTHESIS needs a conjunct that implies the
  goal, and the goal is not fixed along the traversal (`TStabQ` is called
  from `ULFQ` at a kept implication's antecedent, with a different goal and
  the same record).

So: **`SatE2RS` and `SatA2RS` are not refuted, but no proof of them by the
family's induction exists that this run could find, and the obstruction is
exactly the step above.**

---

## 5 · The design that does support the induction: derivation-level escapes

`wip/ui_routeB_r_escd.lean`.  Make the escape a DERIVATION rather than a
formula.  Two facts about `interpR` make it work.

**(1) The record extension is confined to the guard call — PROVED.**

    parkRowER_record : parkRowER id prev done Qa N rest res seen =
      nAnd (if seenMemR seen Qa done then nTop
            else .imp (.down (prev [] done (some ↑Qa) ((Qa, done) :: seen)))
                      (prev [N] rest none seen))
           (prev res rest none seen)
    parkRowAR_record : parkRowAR id prev done Qa N rest goal seen =
      (if seenMemR seen Qa done then nBot
       else nAnd (prev [] done (some ↑Qa) ((Qa, done) :: seen))
                 (prev [N] rest (some goal) seen))

Both are `rfl`, pinned axiom-free.  In both rows `(Qa, done) :: seen` occurs
in the guard sub-call ALONE — the fire continuation and the residual are read
at `seen` — and every other clause of `stepR` passes its record through
unchanged.  Consequently a state whose record contains `(Qa, done)` lies
inside that guard's sub-traversal, and the derivation it carries is a proper
sub-derivation of the guard derivation `s_d` used there.  This is
`docs/ui-ljfo-clause-table.md` §4.28's observation, now a fact about the
definition rather than about a picture of it.

**(2) The set-equality of the stations is absorbed by weakening — PROVED.**
The loop check fires when the recorded station `T` is SET-EQUAL to the
current one, not equal to it, so the escape must carry a derivation at `T`
where the traversal holds one at `done`.  The two sequents differ only in the
multiplicity and order of hypotheses:

    sameSet_subs : sameSet T S = true → Sub T S ∧ Sub S T
    wkSameSet    : sameSet T S = true → Inv (T ++ Γ) Ω j C → Inv (S ++ Γ) Ω j C

**(3) So an escape can carry a strictly smaller guard derivation.**  When the
loop check fires for a recorded pair, the traversal holds the antecedent
sub-derivation of the current derivation: by (2) a derivation of the SAME
guard sequent, of height strictly below the one in use at the recording
site.  Returned as an escape it is caught at that
site, which RESTARTS its guard call with it; an escape for an older pair is
passed further up, and at the top level (`seen = []`) there is nothing to
pass.

The restart is well-founded on the guard derivation's height.  Stripped of
everything else that is

    escapeLoop : (h : D → Nat) → ((d : D) → Sum R {d' : D // h d' < h d}) → D → R

PROVED, axiom-free.  And in the family's own types, over the `∀p` entry as a
typed obligation (`wip/ui_routeB_r_guard.lean`):

    UEntryRD p := ∀ done, Saturated done → ParkedCtxP done →
                  ∀ {Γ' K}, (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
                  ∀ G seen b {j} (d : Inv Γ' [] j G), BookBound seen b (hgtI d) →
                  Sum (UpFrom2 (fun e f => Inv (interpR p e [] done none seen :: K) [] .tru
                         (interpR p f [] done (some (jGoal j G)) seen)))
                      (EscD K seen b)                                          -- OPEN

    guardLoop : UEntryRD p → ∀ done, Saturated done → ParkedCtxP done →
                ∀ {K}, PFreeCtx p K → ∀ Qa seen b {Γ'},
                (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' →
                ∀ (s : Inv Γ' [] .tru (↑Qa)), BookBound seen b (hgtI s) →
                Sum (UpFrom2 (fun e f =>
                       Inv (interpR p e [] done none ((Qa, done) :: seen) :: K) [] .tru
                           (interpR p f [] done (some ↑Qa) ((Qa, done) :: seen))))
                    (EscD K seen b)                              PROVED, [propext]

    satA2RD_of_uentryRD : UEntryRD p → SatA2RD p                 PROVED, [propext]

`guardLoop`'s value is exactly the guard conjunct of `parkRowER` /
`parkRowAR`, the `∀p` approximant at the EXTENDED record; its recursion books
`hgtI s` as the head of the height book at each attempt, so an escape for the
pair just recorded is required to beat the height in hand, and the loop is a
well-founded recursion on `hgtI s`.  An escape for an older pair is passed up
unchanged.  Gate watched failing: `guardLoop` at `[]` errors on `propext`.

The other end — what a CUT site produces — is PROVED in the same module:

    escOfCut : ∀ seen b Qa done h, seenMemR seen Qa done = true →
               BookBound seen b h →
               ∀ (gd0 : Inv (done ++ K) [] .tru (↑Qa)), hgtI gd0 < h →
               EscD K seen b                            PROVED, [propext, Quot.sound]

It walks the record to the pair the loop test fired on, moves the derivation
from the current station to the recorded one by `wkSameSet` (`hgt_wk`: the
height is unchanged), and discharges the strict bound from the book
invariant.  Its input is exactly what a cut site holds: the antecedent
sub-derivation of the derivation in hand, `hgtI gd0 < hgtI d`.  Gate watched
failing: `escOfCut` at `[propext]` errors on `Quot.sound`.

So both ends of the escape mechanism are machine-checked — what a cut site
produces and what a recording site does with it.  What is left is the
traversal that carries them between the two.  The escape type and its emptiness at the empty record:

    HeightBook : SeenR → Type          -- one height per recorded pair
    EscD (K : List Neg) : (seen : SeenR) → HeightBook seen → Type
      | here  (gd : Inv (T ++ K) [] .tru (↑Q)) (hlt : hgtI gd < n) : EscD K ((Q,T) :: s) (n, bs)
      | there : EscD K s bs → EscD K (e :: s) (n, bs)
    escD_nil_empty : EscD K [] PUnit.unit → False            PROVED, axiom-free

**The book invariant, and a statement fault caught in this run.**  A first
draft of the two obligations quantified over the height book with no relation
to the derivation.  That draft is UNPROVABLE: at a cut site the traversal
must return an escape, and the escape must beat a booked height that the
statement leaves arbitrary — 0, for instance.  The obligations therefore
carry

    BookBound : ∀ (seen : SeenR), HeightBook seen → Nat → Prop
      | [],     _, _ => True
      | _ :: s, b, h => h ≤ b.1 ∧ BookBound s b.2 h
    bookBound_nil  : BookBound [] b h                        PROVED, axiom-free
    bookBound_mono : h ≤ h' → BookBound seen b h' → BookBound seen b h
                                                             PROVED, axiom-free

as a hypothesis at `hgtI d`: the derivation a state carries is no higher than
any height booked in the record.  It holds at the top (`seen = []`, the book
empty), it is re-established at a recording site (the head is booked as the
guard derivation's own height, and the older entries survive because the
guard derivation is a sub-derivation), and it descends with the derivation —
`bb_park`, `bb_orBranch`, `bb_andHyp`, `bb_impFls`, `bb_fire` in
`wip/ui_routeB_r_procd.lean`, each `LJF/OFuelHeight.lean` Part 10's height
lemma for that edge.  With it a cut site can build its escape: the antecedent
sub-derivation has `hgtI s_d < hgtI d ≤ n_k`.

Both sides of the mutual return `Sum (ordinary conclusion) (EscD …)`, and NO
escape formulas appear anywhere: the statements are `SatE2R` / `SatA2R` at an
arbitrary record with an `EscD` alternative.  On the `∃p` side the escape
branch of §4 disappears — the traversal simply passes the escape up.

Gate watched failing: `satE2R_of_escD` at `[]` errors with "depends on
`propext`, which the bound does not allow".

---

## 6 · The residual, verbatim

`wip/ui_routeB_r_escd.lean`.  Both are OPEN: no term of either type is built.

```lean
def SatE2RD (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR) (b : HeightBook seen),
    Saturated done → ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j ψ), BookBound seen b (hgtI d) →
      Sum (UpFrom (fun e => Inv (interpR p e [] done none seen :: Δ) [] j ψ))
          (EscD Δ seen b)

def SatA2RD (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg) (seen : SeenR) (b : HeightBook seen),
    Saturated done → ParkedCtxP done → PFreeCtx p Δ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j G), BookBound seen b (hgtI d) →
      Sum (UpFrom2 (fun e f => Inv (interpR p e [] done none seen :: Δ) [] .tru
             (interpR p f [] done (some (jGoal j G)) seen)))
          (EscD Δ seen b)
```

and what they buy, PROVED:

    satE2R_of_escD : SatE2RD p → SatE2R p                                  [propext]
    satA2R_of_escD : SatA2RD p → SatA2R p                                  [propext]
    pll_ui_R_escD  : (∀ p, SatE2P p) → (∀ p, SatA2P p) →
                     (∀ p, SatE2RD p) → (∀ p, SatA2RD p) → PLL_UI
                                        [propext, Classical.choice, Quot.sound]

`SatE2P` / `SatA2P` are not open: they are inhabited by `LJFO.satE2P` /
`satA2P` (`LJF/OFuelPCofinal.lean`), carried as variables here only because
these leaves must not import the 237 MB family module.

The statements `SatE2RS` / `SatA2RS` of §3 remain OPEN as well, and §4 says
why they should not be attempted.

---

## 7 · The first block of the family — PROVED

`wip/ui_routeB_r_proc.lean`.  `LJF/OFuelPMin.lean` Part 5's `eMinPP` /
`aMinPP` transposed to `interpR` with the record carried.  The processing
phase is record-blind (§5(1)), so the transfer holds at every record with the
record a spectator:

    SatE2Rg p := ∀ done Δ ψ seen, Saturated done → ParkedCtxP done →
                 PFreeCtx p Δ → PFreeN p ψ → ∀ {j}, Inv (done ++ Δ) [] j ψ →
                 UpFrom (fun e => Inv (interpR p e [] done none seen :: Δ) [] j ψ)
    SatA2Rg p := ∀ done Δ G seen, Saturated done → ParkedCtxP done → PFreeCtx p Δ →
                 ∀ {j}, Inv (done ++ Δ) [] j G →
                 UpFrom2 (fun e f => Inv (interpR p e [] done none seen :: Δ) [] .tru
                                         (interpR p f [] done (some (jGoal j G)) seen))

    eMinPRg : SatE2Rg p → ∀ todo done Δ ψ seen, ParkedCtxP done → PFreeCtx p Δ →
              PFreeN p ψ → ∀ {j}, Inv ((todo ++ done) ++ Δ) [] j ψ →
              UpFrom (fun e => Inv (interpR p e todo done none seen :: Δ) [] j ψ)
    aMinPRg : SatA2Rg p → ∀ todo done Δ G seen, ParkedCtxP done → PFreeCtx p Δ →
              ∀ {j}, Inv ((todo ++ done) ++ Δ) [] j G →
              UpFrom2 (fun e f => Inv (interpR p e todo done none seen :: Δ) [] .tru
                                      (interpR p f todo done (some (jGoal j G)) seen))

with `satE2R_of_g : SatE2Rg p → SatE2R p` and `satA2R_of_g` at `seen = []`,
`interpRFire_eq` (the fire step, one equation for every mode and record), the
two `∨`-inversion equations, and `seqSum`, the sequencing that a `Sum`-valued
(derivation-level-escape) version of these clauses needs at the one clause
with several branches.

`wip/ui_routeB_r_rows.lean` is the next block, `LJF/OFuelPMin.lean`
Parts 2–4 for the pair recursion: the aggregate at fuel `f+1` as an equation
for each of the nine goal shapes (`interpRE_eq`, `interpRA_imp_eq`,
`interpRA_and_eq`, `interpRA_atomT_eq`, `interpRA_atomF_eq`,
`interpRA_fls_eq`, `interpRA_or_eq`, `interpRA_down_eq`,
`interpRA_circ_eq`, all `[propext]`), one membership lemma per row
(`eRow_*Mem`, `aRow_*Mem`, all `[propext, Quot.sound]`) and the four
equations a dispatch clause splits on — the two rows with the loop test open
and the two with it fired (`parkRowER_open`, `parkRowER_cut`,
`parkRowAR_open`, `parkRowAR_cut`, all axiom-free).  `parkRowAR_cut` is why
the `∀p` side must escape: the row is `⊥`.  Gate watched failing:
`interpRE_eq` at `[]` errors on `propext`.

Two transcription differences from `interpP` were forced and are worth
recording for whoever writes the saturated phase:

* `stepR`'s station maps and its `∨`-inversion map over their lists PLAIN
  where `interpP`'s are `.attach` maps.  So every row membership is
  `List.mem_map_of_mem` and needs no `rowMem`; and in the `∨`-inversion
  clause `memMapWitness` returns the branch alone, so the `maxOver` bound is
  read back through `List.mem_attach`;
* `decreasing_by ljf_dec_e` is ambiguous in a leaf that sees both
  `LJF/OCore.lean`'s macro and `LJF/Base.lean`'s, so the alternatives are
  spelled out as in `stabP` (`wip/ui_routeB_wp4.lean`).

Gate watched failing: `eMinPRg` at `[propext, Quot.sound]` errors with
"depends on `Classical.choice`, which the bound does not allow".

`wip/ui_routeB_r_procd.lean` is the same block over the `Sum`-valued
statements of §6, i.e. the block as the final family will contain it:

    eMinPRD : SatE2RD p → ∀ todo done Δ ψ seen b, ParkedCtxP done → PFreeCtx p Δ →
              PFreeN p ψ → ∀ {j}, Inv ((todo ++ done) ++ Δ) [] j ψ →
              Sum (UpFrom (fun e => Inv (interpR p e todo done none seen :: Δ) [] j ψ))
                  (EscD Δ seen b)
    aMinPRD : SatA2RD p → … the two-fuel form

Every clause is the one above with the escape passed straight through — the
processing phase never touches the record, so an escape arising below is an
escape here, at the same record, height book and `p`-free context.  The only
clause needing plumbing is the inversion of a disjunctive hypothesis, which
has one sub-result per branch of `invertPos` and must sequence them:
`seqSumG` (all succeed, or one escapes).  Gate watched failing: `aMinPRD` at
`[propext, Quot.sound]` errors on `Classical.choice`.

---

## 8 · Status

| claim | status |
|---|---|
| record monotonicity of `interpR` (`interpR_seenMonoE/A`, `interpR_seenStepE/A`) | **PROVED** |
| §4.32's escape statements support the induction | **NO** — §2, statement-level; not refuted, unsuitable |
| the station-free restatement `escConjS`/`escRowsS`, `escHyp`/`escGoal` | DESIGN |
| its four structural steps (`escHyp_record`, `escGoal_absorb`, `escHyp_recorded`, `escGoal_escape`) | **PROVED** |
| `satE2R_of_escapesS`, `satA2R_of_escapesS`, `pll_ui_R_escS` | **PROVED** |
| `SatE2RS p`, `SatA2RS p` | OPEN, and §4 says not to attempt them |
| the record extension is confined to the guard call (`parkRowER_record`, `parkRowAR_record`) | **PROVED**, axiom-free |
| set-equal stations weaken into one another (`sameSet_subs`, `wkSameSet`) | **PROVED** |
| the recording-site restart is well-founded (`escapeLoop`) | **PROVED**, axiom-free |
| the recording-site loop in the family's types (`guardLoop`, over `UEntryRD`) | **PROVED**, `[propext]` |
| the escape a cut site creates (`escOfCut`) | **PROVED** |
| `EscD` empty at the empty record (`escD_nil_empty`) | **PROVED**, axiom-free |
| the obligations WITHOUT the book invariant | unprovable — caught and repaired in this run |
| the book invariant and its descent (`BookBound`, `bookBound_mono`, `bb_*`) | **PROVED** |
| `satE2R_of_escD`, `satA2R_of_escD`, `pll_ui_R_escD` | **PROVED** |
| the processing phase at every record (`eMinPRg`, `aMinPRg`) | **PROVED** |
| the same block carrying derivation-level escapes (`eMinPRD`, `aMinPRD`, `seqSumG`) | **PROVED** |
| the row layer at a saturated station (nine aggregate equations, fifteen row memberships, the four dispatch equations) | **PROVED** |
| **`SatE2RD p`, `SatA2RD p`** | **OPEN** |
| N4 for PLL | **OPEN**, over `SatE2RD` + `SatA2RD` alone |

Before this run N4 rested on `SatE2R` + `SatA2R` (§4.31), with the intended
route through the escape statements of §4.32.  After it, N4 rests on the two
derivation-level obligations above, the escape statements of §4.32 are known
to be the wrong shape and why, the processing phase of the family is built,
and the two lemmas any version of the saturated phase needs — record
monotonicity and the confinement of the record extension — are theorems.

### 8.1 The founding the next package needs

`guardLoop` is stated over the `∀p` entry as a PARAMETER, but in the family
that entry is the `∀p` traversal itself, so the loop belongs INSIDE the
mutual — as `ParkAntP` did before the height re-founding of §4.17.  The
measure carries it: `LJF/OFuelPFam.lean` is founded on
`μ = (normalised derivation height, station weight, sizeOf)`, and

* the loop's restart calls the entry with `gd`, where `hgtI gd < hgtI s` is
  the escape's own bound, so the first component drops strictly;
* the loop's first call is at `s`, the antecedent sub-derivation, whose
  height is below the dispatching derivation's, so the loop's calls all sit
  below the clause that opened it.

So the same three-component measure founds the family with the loop in it,
and no new component is needed.  The two facts to supply per clause are the
ones the family's `decreasing_by` already proves; what is new is that they
must ALSO be exported as `≤`, to descend the book invariant (`bb_*`, §5).

**A note against re-deriving.**  The ∃p side cannot be closed alone over the
`∀p` entry as a parameter and then composed: the `∀p` side calls the `∃p`
side (`UStabQ` → `TStabQ`, `UEntryQ` → `aMinQ`), so a `∃p` development
conditional on `UEntryRD` leaves a fixpoint, not a reduction — the same shape
`ParkAntP` had.  The two halves must be one mutual, which is why this run did
not build half of it.

**What is NOT delivered:** the saturated phase, i.e. the mutual family for
`interpR`, ◯-free or otherwise (the processing phase of §7 is built, both
escape-free and `Sum`-valued, and the row layer it reads with it).  It was not attempted: the analysis above
took the first two hours of the run, and re-authoring
`LJF/OFuelPFam.lean`'s seventeen-definition mutual with `Sum`-valued returns
and a recording-site loop inside the same strongly connected component is a
work package of that module's scale, not of the hours that remained.  The
next package should start from §5 and §7, and should build the ◯-free
instance first (rule 8) against `ipc_ui_routeB` (`wip/ui_routeB_wp4.lean`).
