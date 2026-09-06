# WP12d — the saturated phase for `interpR`: the residual REFUTED, repaired, and where the induction still has no clause

Route (B), node **N4**, the last open obligation of the route.  Started
17:51 BST, 2026-09-06, on the WP12c tip `51caaf9`.

Every claim below is **PROVED** (a named Lean declaration, sorry-free, pin
measured with `#axioms_within_pin` and asserted with `#axioms_within`),
**REFUTED** (kernel-checked countermodel), **OPEN** (a typed obligation, no
term built) or **DESIGN** (a statement written down).

---

## Headline

The work package asked for the mutual cofinality family for `interpR`,
◯-free first, over the two obligations WP12c handed over.  It was not built,
and it should not be: **the `∃p` obligation is FALSE.**

    satE2RD_refuted : SatE2RD "p" → False        PROVED, [propext, Quot.sound]

so the pair `(SatE2RD, SatA2RD)` that `pll_ui_R_escD` reduces `PLL_UI` to is
not inhabitable.  That reduction stands as a theorem and is now known to be
vacuous.  Three further things are delivered: a **repaired** pair of
obligations that the counter-instance cannot touch, with the whole mechanism
re-proved over it; a **one-world semantics for `LJF◯`** with soundness for
all four judgments, which is what made the refutation possible and is a
general refutation oracle for `Inv`; and the **localisation of the remaining
difficulty**, which the repair does not touch — the escape has no step across
the `p`-free binders that the inversion phase creates, and a designed cell
exhibits the configuration as a kernel-checked derivation.

Modules, all leaves under `wip/`, `LJF/` untouched:

| module | contents | build |
|---|---|---|
| `wip/ui_routeB_r_bind.lean` | the binder crossings that ARE available, and the room arithmetic | 12.6 s |
| `wip/ui_routeB_r_bindcell.lean` | the designed cell: the crossing is reached and the step does not apply | 14.4 s |
| `wip/ui_routeB_r_refute.lean` | one-world semantics for `LJF◯`; `SatE2RD` REFUTED | 14.5 s |
| `wip/ui_routeB_r_escw.lean` | the repaired residual, the mechanism re-proved over it | 14.3 s |
| `wip/ui_routeB_r_grow.lean` | the station-growth repair REFUTED | 14.3 s |

No 25-minute build was paid for: the family it would have compiled is not
worth compiling until the statement question below is settled.

---

## 1 · `SatE2RD` is REFUTED

`wip/ui_routeB_r_refute.lean`.  The obligation is

```lean
def SatE2RD (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR) (b : HeightBook seen),
    Saturated done → ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j ψ), BookBound seen b (hgtI d) →
      Sum (UpFrom (fun e => Inv (interpR p e [] done none seen :: Δ) [] j ψ))
          (EscD Δ seen b)
```

and the fault is that the record `seen` and the `p`-free context `Δ` are
quantified INDEPENDENTLY, with a bare NUMBER booked per recorded pair.  They
are not independent in the family: a record entry is created at a recording
site, which has a `Δ` of its own, and the escape's payload is a derivation at
that entry's station OVER THAT `Δ`.  Nothing in the statement says the
recorded pair was ever recordable.

**The counter-instance.**

    p     := "p"
    Qa    := ↓↑a                 M₀ := ↑a,  so Qa = ↓M₀
    X     := Qa ⊃ ↑n             a parked `simp` implication, antecedent compound
    done  := [X, ↑p]             saturated, `p`-carrying
    Δ     := []
    ψ     := Qa ⊃ ↑n             `p`-free
    seen  := [(Qa, done)]        station set-equal to `done`, so the loop test fires
    b     := (hgtI refD, ())     the tightest book the invariant allows

`refD : Inv (done ++ []) [] .tru ψ` exists (assume `↓↑a`, fire `X`, get `↑n`)
and `BookBound seen b (hgtI refD)` holds.  Both branches then fail.

* **The value branch.**  At this record `interpR`'s ∃p row for `X` is `⊤`
  (`parkRowER_cut`) and the row for `↑p` is `⊤` because its atom IS `p`.  The
  whole row list is computed by `rfl`:

      BindCell.cellRows :
        eRowsR id "p" prev done seen
          = [nAnd nTop (prev [] [↑p] none seen), nTop]

  so the ∃p interpolant is built from `nTop` alone AT EVERY FUEL
  (`Refute.ev_interpR_done`), and the one-world model with `a` true, `n`
  false satisfies it and refutes `ψ` (`Refute.valueFails`).
* **The escape branch.**  `EscD [] seen b` asks for a derivation of
  `done ++ [] ⊢ ↑Qa`, i.e. of `↑↓↑a`; the one-world model with `a` false
  satisfies `done` and refutes it (`Refute.escapeFails`).  `EscD.there`
  reaches the empty record, where `escD_nil_empty` applies.

**PROVED**

    Refute.satE2RD_refuted : SatE2RD "p" → False        [propext, Quot.sound]

**What is NOT refuted.**  `interpR` itself; `SatE2R` / `SatA2R` (`seen = []`,
where the escape branch is empty and the interpolant keeps its fire rows);
uniform interpolation for PLL.  The instance is a STATEMENT fault of the
generalisation to an arbitrary record, exactly the class of §5's earlier
finding that the obligations WITHOUT the book invariant were unprovable.

---

## 2 · The tool: a one-world semantics for `LJF◯` — PROVED

`wip/ui_routeB_r_refute.lean` Part 1.  Nothing in `LJF/` had a semantics.
A single-point Kripke model evaluates every formula classically, with the
lax modality read as the identity nucleus:

    evP v (.atom a) = v a      evP v .fls = false
    evP v (P ∨ Q)   = evP v P || evP v Q
    evP v (↓M)      = evN v M
    evN v (↑P)      = evP v P            evN v (◯P)     = evP v P
    evN v (Q ⊃ N)   = !(evP v Q) || evN v N
    evN v (M ∧ N)   = evN v M && evN v N

Soundness for all four judgments, by one mutual induction:

    sndI : Inv Γ Ω j C → CtxT v Γ → OmT v Ω → evN v C = true
    sndS : Stab Γ j P  → CtxT v Γ → evP v P = true
    sndR : RFocus Γ j P → CtxT v Γ → evP v P = true
    sndL : LFoc Γ N j P → CtxT v Γ → evN v N = true → evP v P = true
                                                       [propext, Quot.sound]

hence the oracle

    no_inv_of_model : CtxT v Γ → evN v C = false → Inv Γ [] j C → False

Exhibit a valuation satisfying the hypotheses and refuting the goal, and no
derivation exists.  It is complete for nothing, but it is cheap, kernel-
checked and needs no search, and it settled both branches above.

---

## 3 · The repair — PROVED, and the residual RESTATED

`wip/ui_routeB_r_escw.lean`.  Book what a recording site actually holds — its
guard DERIVATION — instead of that derivation's height:

    GuardBook Δ []            = PUnit
    GuardBook Δ ((Q,T) :: s)  = Inv (T ++ Δ) [] .tru (↑Q) × GuardBook Δ s

    EscW Δ seen bk
      | here (gd : Inv (T ++ Δ) [] .tru (↑Q)) (hlt : hgtI gd < hgtI g)
      | there : EscW Δ s bs → EscW Δ ((Q,T) :: s) (g, bs)

    GuardBound Δ [] bk h            = True
    GuardBound Δ ((_,_)::s) bk h    = h ≤ hgtI bk.1 ∧ GuardBound Δ s bk.2 h

An escape now beats the booked DERIVATION, and the book's mere existence says
the pair was recordable at this `Δ`.  The counter-instance of §1 is excluded
outright:

    refute_blocked : GuardBook [] BindCell.seen → False   [propext, Quot.sound]

— at `Δ = []` there is no derivation of `done ⊢ ↑Qa` at all, so the repaired
statement has nothing to say there.

**The restated residual (OPEN, no term of either type is built):**

```lean
def SatE2RW (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR) (bk : GuardBook Δ seen),
    Saturated done → ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j ψ), GuardBound Δ seen bk (hgtI d) →
      Sum (UpFrom (fun e => Inv (interpR p e [] done none seen :: Δ) [] j ψ))
          (EscW Δ seen bk)

def SatA2RW (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg) (seen : SeenR) (bk : GuardBook Δ seen),
    Saturated done → ParkedCtxP done → PFreeCtx p Δ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j G), GuardBound Δ seen bk (hgtI d) →
      Sum (UpFrom2 (fun e f => Inv (interpR p e [] done none seen :: Δ) [] .tru
             (interpR p f [] done (some (jGoal j G)) seen)))
          (EscW Δ seen bk)
```

and what they buy, PROVED:

    escW_nil_empty        : EscW Δ [] PUnit.unit → False              []
    guardBound_nil, guardBound_mono                                    []
    satE2R_of_escW        : SatE2RW p → SatE2R p                [propext]
    satA2R_of_escW        : SatA2RW p → SatA2R p                [propext]
    pll_ui_R_escW         : (∀ p, SatE2P p) → (∀ p, SatA2P p) →
                            (∀ p, SatE2RW p) → (∀ p, SatA2RW p) → PLL_UI
                                  [propext, Classical.choice, Quot.sound]

Both ends of the mechanism survive the change unchanged in content:

    escWOfCut             : what a cut site produces      [propext, Quot.sound]
    UEntryRW (OPEN), satA2RW_of_uentryRW, guardLoopW               [propext]

`guardLoopW`'s restart is now literally "book the smaller derivation", which
is what the loop was always doing; the numeric book was a lossy encoding of
it.

**Why the repair is not refutable the way `SatE2RD` was.**  The two branches
cannot both fail.  For the value branch to fail the derivation `d` must use a
row the record has cut — the cut rows are the ONLY thing the record removes
from the interpolant — i.e. must left-focus the recorded implication; and that
costs at least three units more than the guard derivation it contains:

    hgt_fireCost : hgtS (Stab.lfoc h (.impL s lf)) = hgtS s + hgtL lf
    hgtL_ge      : 3 ≤ hgtL lf
    hgt_fire_above_guard :
        hgtI (Inv.stable s) + 3 ≤ hgtI (Inv.stable (Stab.lfoc h (.impL s lf)))
    hgtI_up_ge   : 3 ≤ hgtI d   for d : Inv Γ [] j (↑P)
                                          all PROVED, [propext, Quot.sound]

For the escape branch to be empty the booked `g` must be MINIMAL for the
guard sequent; then `hgtI d ≥ hgtI g + 3 > hgtI g` and `GuardBound` fails, so
the instance is not an instance.  Conversely, if `g` is far enough from
minimal for `GuardBound` to hold, a shorter derivation of the guard sequent
exists and IS an escape.  This is an argument about instances, not a proof of
`SatE2RW`; what is proved is the arithmetic it turns on.

---

## 4 · Where the induction still has no clause — the `p`-free binders

The repair fixes the STATEMENT.  It does not fix the INDUCTION, and the
remaining difficulty is separate, localised, and exhibited by a cell.

### 4.1 The step

`K`, the `p`-free context the traversal runs at, is NOT constant along the
saturated phase.  Four clauses of the `interpP` family extend it —
`TInvQ`/`TpInvQ` and `UInvGQ`/`UpInvGQ` at `Inv.downL` and `Inv.atomL`
(`LJF/OFuelPFam.lean` Parts 5 and 6) — because the derivation binds a new
`p`-free hypothesis there.  A recording site sits ABOVE such a clause and a
cut site can sit BELOW it, so the escape must cross, and the family needs

    EscD (M₀ :: K) seen b → EscD K seen b

whose payload is a DERIVATION.  That is a context STRENGTHENING, not a
weakening: it is not available for nothing.

### 4.2 The crossings that ARE available — PROVED

`wip/ui_routeB_r_bind.lean`.  Available exactly when the bound hypothesis is
one that a single left focus on a member of `K` re-supplies:

    bindBackI      : ↑↓M₀ ∈ Γ → Inv (M₀ :: Γ) [] j (↑P) → Inv Γ [] j (↑P)
                     — `stable · lfoc · rel · downL`, four rules, no cut   []
    hgt_bindBackI  : hgtI (bindBackI h x) = hgtI x + 4                     []
    EscC K c       : the escape with `c` units of height still to spend
    escC_crossDown : ↑↓M₀ ∈ K → EscC (M₀::K) (c+4) seen b → EscC K c seen b
    escC_crossAtom : ↑a ∈ K → EscC (↑a::K) c seen b → EscC K c seen b
    escC_crossMem  : M₀ ∈ K → EscC (M₀::K) c seen b → EscC K c seen b
    hgt_keptSpan   : hgtS (Stab.lfoc h (.rel (.downL x))) = hgtI x + 4     []
    bb_keptSpan    : the book invariant crosses the span with NO slack
    escOfCutC      : `escOfCut` in cost form

The accounting closes exactly: the four constructors `bindBackI` rebuilds are
the four the traversal consumed to reach the binder (`hgt_keptSpan`), so an
escape created below with `c + 4` units of room is created under a book bound
that already grants them.

### 4.3 The two binders that are NOT crossed

**(i) A disjunctive kept hypothesis.**  `UInvGQ` at `Inv.orL` splits
`Ω = ↓M₀ ∨ PB :: Ω'` before the `downL`.  Re-supplying `M₀` from
`↑(↓M₀ ∨ PB) ∈ K` needs `Inv Γ [↓M₀ ∨ PB] .tru (↑P)`, i.e. `Inv.orL` applied
to BOTH branches, and the escape carries one.  Room is not the difficulty —
`hgt_orSpanL : hgtI (Inv.orL (Inv.downL x) e) = hgtI x + hgtI e + 2` grants
more than the 4 a crossing costs — the DISCHARGE is.

**(ii) The goal antecedent.**  `TInvQ` proves a `p`-free implication goal by
`Inv.impR`, which puts the antecedent into `Ω`; the following `downL` binds
it into `K`.  That hypothesis is the antecedent of the goal being PROVED, so
nothing above holds it; and

    hgt_goalSpan : hgtI (Inv.impR (Inv.downL x)) = hgtI x + 2              []

grants 2 units where `bindBackI` costs 4.  Two independent reasons.

A third case, not separately named: when a kept hypothesis is reached through
a left-focus CHAIN (`LFoc.impL`, `LFoc.and1/2`) before the `LFoc.rel`, the
formula `↑↓M₀` is a subformula of a `K`-member and not a member itself, so
`escC_crossDown`'s premise again fails; replaying the chain would need the
chain's own antecedent derivations, which the escape does not carry.

The residual is one typed obligation (OPEN, no term built):

```lean
def EscBindOpenR (p : String) : Type :=
  ∀ (K : List Neg) (M₀ : Neg) (c : Nat) (seen : SeenR) (b : HeightBook seen),
    PFreeN p M₀ → PFreeCtx p K →
      EscC (M₀ :: K) (c + 4) seen b → EscC K c seen b
```

`escC_crossDown` is this type with the extra premise `↑↓M₀ ∈ K`, and is
PROVED.

### 4.4 The designed cell — PROVED

`wip/ui_routeB_r_bindcell.lean`.  One cell (CLAUDE.md rule 9), not a sweep:
a single kernel-checked derivation exhibiting the configuration, so the claim
rests on a term.

    Qa   := ↓↑a                    M₀ := ↑a,  Qa = ↓M₀
    X    := Qa ⊃ ↑n                the parked implication
    done := [X, ↑p]                saturated, `p`-carrying
    HK   := ↓(Qa ⊃ ↑n) ⊃ ↑Qa       a kept implication
    K    := [HK]                   `p`-free
    seen := [(Qa, done)]

`Qa` is provable at `done ++ K` only through `HK`, and `HK`'s antecedent is
the implication `Qa ⊃ ↑n`, whose proof BINDS `M₀` (`Inv.impR` then
`Inv.downL`) and then attacks `X` AGAIN at the same station.  The goal is
`↑n` throughout and `X` is the only source of `n`, so the cut site cannot
avoid firing `X`.

| declaration | content |
|---|---|
| `cellDeriv` | the configuration is realisable |
| `cellSaturated`, `cellParked`, `cellPFreeK` | the side conditions |
| `cellCut : seenMemR seen Qa done = true` | the loop test fires below the binder |
| `cellRows` | the whole ∃p row list there: `X`'s fire is gone |
| `cellRowE`, `cellRowA` | `⊤` and `⊥` by `parkRowER_cut` / `parkRowAR_cut` |
| `cellHeight : hgtI cellEscapePayload + 4 < hgtI (Inv.stable sGuard)` | the escape is well-formed WHERE IT IS CREATED |
| `cellCrossFails : ↑↓M₀ ∉ K ∧ M₀ ∉ K` | both crossing premises are FALSE here |
| `cellGoalSpan : hgtI dGoal = hgtI xCut + 2` | 2 units granted, 4 needed |

No countermodel is claimed for the cell: it does not show that no derivation
of `done ++ K ⊢ ↑Qa` exists.  It shows that the step the family needs is
REACHED and that the step it has does not apply.

---

## 5 · Status

| claim | status |
|---|---|
| `SatE2RD p` (WP12c's ∃p residual) | **REFUTED** (`satE2RD_refuted`) |
| `SatA2RD p` (WP12c's ∀p residual) | OPEN; not refuted in this run, and no longer load-bearing |
| `pll_ui_R_escD` | **PROVED** and now known VACUOUS |
| one-world semantics for `LJF◯` and its soundness (`sndI/S/R/L`, `no_inv_of_model`) | **PROVED** |
| the repaired book `GuardBook`, `EscW`, `GuardBound` | DESIGN |
| `refute_blocked` | **PROVED** |
| `satE2R_of_escW`, `satA2R_of_escW`, `pll_ui_R_escW` | **PROVED** |
| `escWOfCut`, `guardLoopW`, `satA2RW_of_uentryRW` | **PROVED** |
| the fire-cost arithmetic (`hgt_fireCost`, `hgtL_ge`, `szS_ge_two`, `hgtS_ge`, `hgtI_up_ge`, `hgt_fire_above_guard`) | **PROVED** |
| **`SatE2RW p`, `SatA2RW p`, `UEntryRW p`** | **OPEN** |
| `bindBackI`, `hgt_bindBackI`, `hgt_keptSpan`, `bb_keptSpan` | **PROVED** |
| `escC_crossDown`, `escC_crossAtom`, `escC_crossMem`, `escOfCutC` | **PROVED** |
| `hgt_goalSpan`, `hgt_orSpanL` | **PROVED** |
| the escape crosses a disjunctive, a chained, or a goal-antecedent binder | **NO** — §4.3, statement-level; not refuted, unavailable |
| `EscBindOpenR p` | **OPEN**, and §4.3 says why it should not be assumed |
| the station-growth lemma `(grow)` of §6(b) | **REFUTED** (`Grow.growE_refuted`) |
| the mutual family for `interpR`, ◯-free or otherwise | NOT BUILT — §1 says why it was not attempted |
| N4 for PLL | **OPEN**, over `SatE2RW` + `SatA2RW`, with §4 in the way |

Before this run N4 rested on `SatE2RD` + `SatA2RD`.  After it, one of those
two is refuted, the pair is replaced by `SatE2RW` + `SatA2RW` with the whole
mechanism re-proved over the repaired book, and the one step the induction
lacks is named, measured and exhibited.

---

## 6 · What the next package should do

Three directions, in the order they should be tried.

**(a) Settle the binder step, not the bookkeeping.**  §4.3 is the whole of
what is missing.  It is not a proof problem inside a clause; it is the
absence of a clause.  Any candidate must say what an escape created under a
binder means above it.

**(b) Park the binder into the STATION instead of the context — REFUTED in
this run.**  The inversion phase adds `M₀` to `K`, which is invisible to
`interpR`, so the loop test still fires below the binder at the same station.
Parking `M₀` into `done` instead makes the station below the binder strictly
larger as a SET, `sameSet` fails, and no cut site lies below a binder at all
— the crossing would never be needed.  The measure survives it (the station
component is second, the height component drops at the binder, and the step
builds a CONCLUSION, whose height nothing constrains), so the whole repair
rests on one new lemma:

    E^R(done | seen),  M₀   ⊢   E^R([M₀], done | seen)          (grow)

**`(grow)` is FALSE** (`wip/ui_routeB_r_grow.lean`), and the record is why.
At a record that has already cut a fire row, `E^R(done | seen)` has LOST that
row; at the larger station the recorded pair is no longer set-equal, the loop
test does not fire, and `E^R([M₀], done | seen)` HAS the row back.  The
larger station's interpolant is strictly stronger and the extra strength is
not recoverable from `M₀`.  At the cell of §4.4 with `M₀ := ↑a`:

    Grow.rowsA    : at `doneA = [↑a, X, ↑p]` the row of `X` is the guarded
                    fire, not `⊤` (compare `BindCell.cellRows`)      [propext]
    Grow.ev_guard : that guard holds in the model — the atom `a` is now in
                    the station                                     [propext]
    Grow.ev_fire  : its fire does not — it delivers `↑n`             [propext]
    Grow.ev_grow  : so `E^R([↑a], done | seen)` is FALSE at every fuel ≥ 4
    Grow.growE_refuted :
        Inv [↑a, E^R(done | seen)] [] .tru (E^R([↑a], done | seen)) → False
                                                    [propext, Quot.sound]

So (b) is closed.

**(c) Give up the localised loop.**  The escape mechanism exists to justify
`interpR`'s `⊥`/`⊤` rows by a loop argument localised at a recording site.
The memory note *Visser amalgamation template* records the alternative: a
budgeted layered bisimulation, where the bound is semantic and no derivation
has to travel between contexts at all.

A standing note, unchanged from WP12c: the `∃p` and `∀p` sides call each
other (`UStabQ → TStabQ`, `UEntryQ → aMinQ`), so no half of the family can be
developed conditionally on the other; and the ◯-free instance must be built
first (CLAUDE.md rule 8) against `ipc_ui_routeB` (`wip/ui_routeB_wp4.lean`).

---

## 7 · Gates watched failing

One per module, quoted.

* `wip/ui_routeB_r_bind.lean` — `hgt_bindBackI` pinned at `[]`:
  `'LJFO.hgt_bindBackI' depends on propext, which the bound does not allow.
  declared: []`
* `wip/ui_routeB_r_bindcell.lean` — `cellDeriv` pinned at `[]`:
  `'LJFO.BindCell.cellDeriv' depends on propext, which the bound does not
  allow.  declared: []`
* `wip/ui_routeB_r_refute.lean` — `satE2RD_refuted` pinned at `[propext]`:
  `'LJFO.Refute.satE2RD_refuted' depends on Quot.sound, which the bound does
  not allow.  declared: [propext]`
* `wip/ui_routeB_r_escw.lean` — `refute_blocked` pinned at `[]`:
  `'LJFO.refute_blocked' depends on propext, Quot.sound, which the bound does
  not allow.  declared: []`
* `wip/ui_routeB_r_grow.lean` — `Grow.ev_grow` pinned at `[]`:
  `'LJFO.Grow.ev_grow' depends on propext, which the bound does not allow.
  declared: []`
