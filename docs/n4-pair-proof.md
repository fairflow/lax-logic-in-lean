# WP12b — the proof stage for the pair-recording loop check `interpR`

Route (B), node **N4**.  WP12's Stage 0 refuted nothing
(`docs/n4-pair-design.md`, `docs/ui-ljfo-clause-table.md` §4.29), so this is
the genuine proof attempt Matthew authorised at 09:45 ("a selective and short
campaign we hope, followed by a genuine proof attempt if the campaign does
not refute the planned results").  Started 15:35, 2026-09-06.

Every claim below is **PROVED** (a named Lean declaration, sorry-free, pin
measured with `#axioms_within_pin` and asserted with `#axioms_within`),
**REFUTED** (kernel-checked countermodel), **OPEN** (a typed obligation, no
term built) or **DESIGN** (a statement written down, not yet through a
refutation stage).

Modules, all leaves under `wip/`, `LJF/` untouched:

| module | contents |
|---|---|
| `wip/ui_routeB_r_meas.lean` | the state space, the founding theorem, the pair machinery, `κ₂`, the two flattening lemmas |
| `wip/ui_routeB_r_cong.lean` | the edge mirror `edgesR`, `stepR_congr` |
| `wip/ui_routeB_r_bound.lean` | the descent `edges_decreaseR`, `rFounded`, `rBound`, literal stabilisation |
| `wip/ui_routeB_r_gate.lean` | stage 0 on the designed cells; two gates watched failing |
| `wip/ui_routeB_r_sound.lean` | the easy halves for `interpR`; `eSoundR`, `aSoundR`; one gate |
| `wip/ui_routeB_r_mono.lean` | fuel monotonicity for `interpR` |
| `wip/ui_routeB_r_ui.lean` | `SatE2R`/`SatA2R`; `hasUI_R`; `pll_ui_R`; one gate |
| `wip/ui_routeB_r_esc.lean` | the escape-carrying generalisation (DESIGN) and its specialisation |

---

## 1 · Stage 1 — literal stabilisation: `RBound` PROVED

    RFounded rst p μ  :=  ∀ prev₁ prev₂ s,
        (∀ t, μ t < μ s → atStR prev₁ t = atStR prev₂ t) →
        atStR (stepR rst p prev₁) s = atStR (stepR rst p prev₂) s

    rBound p : Σ′ μ : RState → Nat, RFounded id p μ                    PROVED
    rStabLitE_uncond p done   : Σ′ f₀, ∀ f ≥ f₀,
        interpR p f [] done none [] = interpR p f₀ [] done none []     PROVED
    rStabLitA_uncond p done G : Σ′ f₀, ∀ f ≥ f₀,
        interpR p f [] done (some G) [] = interpR p f₀ [] done (some G) []
                                                                       PROVED

at EVERY station — no saturation, no parking, no ◯-freeness hypothesis: the
bound is a statement about the recursion, not about a cell.  Pins
`[propext, Quot.sound]` — **choice-free**.

### 1.1 The measure

`docs/n4-bound.md`'s shape, with the first component counting PAIRS:

    rMu s  =  κ₂ s · W s + ν s
    κ₂ s   =  the candidate pairs (Q, T) — Q an antecedent of the closure,
              T a subset of the closure — not yet recorded in `seen`, up to
              set-equality of the station
    W s    =  3 ^ (mxW (clSt s) + 1)                             (`bigWR`)
    ν s    =  2·sum3 todo + sum3 done + goalW goal               (`nuR`)

`clSt`, `bigW`, `ν` are `wip/ui_routeB_n4q_meas.lean`'s, reused through the
projection `qOf` that erases `seen`; they never read the fourth slot.

`κ₂` is the length of `ddupPair (candFreeR s)`, where the candidate stations
are the sublists of the deduplicated closure (`powerL (ddupN (clStR s))`) and
a station is mapped into that enumeration by

    canonSt L T  =  the members of L that lie in T                (recursive,
                     so its equations are definitional)

with the three facts that make the counting work:

    canonSt_sameSet : (∀ X ∈ T, X ∈ L) → sameSet (canonSt L T) T = true
    canonSt_id      : L.Nodup → T ∈ powerL L → canonSt L T = T
    seenMemR_congr  : sameSet T S = true →
                      seenMemR seen Q T = seenMemR seen Q S

`canonSt_id` is the one that buys injectivity of the transfer without any
quotient: two distinct members of `powerL L` for `Nodup L` cannot be
set-equal, because `canonSt L` is the identity on them.

### 1.2 Why a FILTERED count and not a difference of bounds

The obvious `κ₂ s := B(clSt s) − |canonSeen seen|` does not work.  Along an
ordinary edge the closure SHRINKS while `seen` persists, so both `B(clSt s)`
and any count of records restricted to the closure shrink, and a difference
of two shrinking quantities is not monotone.  Counting the CURRENT
candidates that are not recorded has no such problem: a shrinking closure
only removes candidates, and records left outside the current closure are
simply not counted.  This is exactly the shape of `κ` in
`docs/n4-bound.md`; the pair version had to be built the same way.

The price is that `κ₂` is not kernel-computable at a designed cell — the
candidate enumeration is exponential in the closure.  Its two lemmas are
cell-INDEPENDENT combinatorics and are discharged by proof:

    kap2_le : clStR t ⊆ clStR s → t.seen = s.seen → κ₂ t ≤ κ₂ s
    kap2_lt : clStR t ⊆ clStR s → t.seen = (Qa, done) :: s.seen →
              Qa ∈ caOf (clStR s) → (∀ X ∈ done, X ∈ clStR s) →
              seenMemR s.seen Qa done = false → κ₂ t + 1 ≤ κ₂ s

### 1.3 The edge table

`docs/n4-bound.md` §3 unchanged except for its last row.  Every ordinary
edge carries `seen` and drops `ν` (`rMu_lt_of_ordinary`); the guard edge

    ([], done, g, seen)  →  ([], done, some ↑Qa, (Qa, done) :: seen)

records a pair that is a candidate at the source — `Qa ⊃ N ∈ done ⊆ clSt s`
gives `Qa ∈ caOf (clSt s)` and `done ⊆ clSt s` — and that is unrecorded
there, since the loop check did not fire; so `κ₂` drops by one while `ν` may
rise, bounded by `W` (`guard_ltR`, `rMu_lt_of_guard`).

`stepR_congr` (the mirror `edgesR` is complete) and `edges_decreaseR` (the
descent) compose to `rFounded`, and `interpGR_stab_of_founded` gives the
explicit threshold `μ s + 1`.

### 1.4 Stage 0, and the gates watched failing

`κ₂`'s lemmas are cell-independent; what IS cell-dependent is the rest of the
edge table, and it is decided in the kernel on the designed cells
(`wip/ui_routeB_r_gate.lean`) against an edge list whose adequacy is itself
decided:

    edgeOKR s t  :=  clStR t ⊆ clStR s  ∧
                     (seen carried  → ν t < ν s)  ∧
                     (seen extended → ν t < ν s + W s)

* `adeq_r_circFree`, `adeq_r_modal` — masking the level below to `edgesR s`
  changes nothing at `s`, at cells (i)–(vi), (m1), (m6), (m10).
* `desc_r_circFree` — the test holds along every edge of the reachable set
  within three steps, at cells (i)–(vi) and at the two cells the `PQEquiv`
  campaign designed, (vii) and (ix).
* `desc_r_modal` — the same within two steps at (m1), (m6), (m10).

**Gates, each a kernel-checked `= false`:**

* `gate_r_nu_goal_term` — drop `3 ^ wNeg goal` from `ν` and the check goes
  red at cell (i), in both modes.
* `gate_r_kappa` — treat a guard edge as an ordinary one (no `κ₂` to pay for
  it) and the check goes red at the same cell: the guard edge RAISES `ν`.
* `gate_r_control` — the committed test passes at the same cell and depth,
  so neither gate is vacuous.

---

## 2 · Stage 2 — soundness PROVED

    eSoundR p f todo done seen :
        Inv (todo ++ done) [] .tru (interpR p f todo done none seen)
    aSoundR p f todo done G seen :
        Inv (interpR p f todo done (some G) seen :: (todo ++ done)) [] .tru G

at every state and every `seen`.  Pins `[propext, Classical.choice,
Quot.sound]`; choice at `cutInv` alone.

This is NOT a transcription of `LJF/OFuelPSound.lean` (1937 lines).
§4.28(2)'s observation — the cut rows are `⊥` in a `∀p` aggregate and `⊤` in
an `∃p` aggregate, hence trivially sound — is already a theorem in the shape
needed: it is the two EASY halves of `PQEquiv`
(`wip/ui_routeB_pqequiv.lean`, WP10),

    E^P  ⊢  E^R          (∃p: dropping a conjunct of an `nAndAll` weakens)
    A^R  ⊢  A^P          (∀p: dropping a disjunct of an `nOrAll` strengthens)

whose proof never inspects the recording test — it only SPLITS on it — and
holds at every `seen` and under every reset policy.  Transcribed for
`interpR` as `easyLvlR`, soundness is then one `cutInv` on each side against
`eSoundP` / `aSoundP`.

**Gate watched failing**: `gate_r_sound_nonvacuous` — `interpR = interpP` is
kernel-`false` at cell (i) from fuel 2 on, in both modes, so the transfer has
content; the control at fuel 1 is `true`, so the gate measures the loop check
and not a transcription difference.

**Also PROVED** (`wip/ui_routeB_r_mono.lean`), the prerequisite §4.28 names
for merging thresholds inside a cofinality induction:

    interpR_monoE : Inv [interpR p (f+1) todo done none seen] [] .tru
                        (interpR p f todo done none seen)
    interpR_monoA : Inv [interpR p f todo done (some G) seen] [] .tru
                        (interpR p (f+1) todo done (some G) seen)

at every state, every `seen`, every reset policy (`interpGR_mono*`).

---

## 3 · Stage 4 — the route plumbed

    hasUI_R : SatE2R p → SatA2R p → Saturated done → ParkedCtxP done →
              HasUI p done G                                      PROVED
    stabilisationAllP_of_R : SatE2P p → SatA2P p → SatE2R p → SatA2R p →
              StabilisationAllP p                                 PROVED
    pll_ui_R : (∀ p, SatE2P p) → (∀ p, SatA2P p) →
               (∀ p, SatE2R p) → (∀ p, SatA2R p) → PLL_UI          PROVED

`hasUI_R` is `hasUI_of_stabEq` (`wip/ui_routeB_n3.lean`) with `interpP`
replaced by `interpR` throughout.  Because stabilisation is LITERAL, both
minimality clauses are a rewrite: no cut is spent inside N3 forward, and the
pair exhibited for the cell is

    E := interpR p f₀ [] done none [],   A := interpR p f₁ [] done (some G) []

at the two thresholds of §1.  `interpP` re-enters only at N3 BACKWARD, where
`stabilises_of_hasUI′` turns the pair into `interpP`'s own interderivable
stabilisation; the two recursions are never compared fuel by fuel.

`SatE2P` / `SatA2P` are NOT open — they are inhabited by `satE2P` / `satA2P`
(`LJF/OFuelPCofinal.lean`, PROVED 2026-09-05).  They are carried as variables
here only because these modules must not import `LJF.OFuelPFam` (a 237 MB
olean, 25-minute build).

**Gate watched failing**: `gate_r_ui_threshold` — the `∀p` chain at cell (i)
is kernel-`false` one fuel below its measured threshold; the control at 4↦5
and 5↦6 is `true`.

---

## 4 · Stage 3 — cofinality: NOT proved

### 4.1 The residual, verbatim

`wip/ui_routeB_r_ui.lean`, `LJF/OFuelPMin.lean` Part 5 with
`interpP p e [] done g` replaced by `interpR p e [] done g []`:

```lean
def SatE2R (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      UpFrom (fun e => Inv (interpR p e [] done none [] :: Δ) [] j ψ)

def SatA2R (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
      UpFrom2 (fun e f => Inv (interpR p e [] done none [] :: Δ) [] .tru
        (interpR p f [] done (some (jGoal j G)) []))
```

### 4.2 Cofinality for `interpR` does NOT follow from cofinality for `interpP`

This is worth stating because it is the reason Stage 3 is a work package and
not a corollary.  The two easy halves point the WRONG WAY for a transfer:

* `∃p`.  `SatE2P` delivers `interpP_e, Δ ⊢ ψ`.  To reach
  `interpR_e, Δ ⊢ ψ` one needs `interpR_e ⊢ interpP_e` — the HARD half.  The
  easy half gives `interpP_e ⊢ interpR_e`, i.e. `interpR` is WEAKER, and a
  weaker interpolant does not inherit cofinality.
* `∀p`.  `SatA2P` delivers `interpP_e, Δ ⊢ interpP_f(some G)`.  To reach
  `… ⊢ interpR_f(some G)` one needs `interpP_f ⊢ interpR_f` on the `∀p`
  side — again the hard half; the easy half runs `interpR_f ⊢ interpP_f`.

Fuel monotonicity and literal stabilisation do not help: they move along the
fuel, not between the two recursions.  So the argument has to be run again,
by induction on the DERIVATION, which is where the loop check pays for
itself (§4.28): a derivation that re-attacks `Qa ⊃ N` at a station with the
same members contains a derivation of the guard sequent `done ⊢ Qa` as a
PROPER sub-derivation, the induction hypothesis applies to it at the guard
state, and the consequence re-appears as an ESCAPE.

### 4.3 The escape-carrying statement as finally kept — DESIGN

`wip/ui_routeB_r_esc.lean`.  The escapes are exactly the rows the loop check
cut, one list per mode:

```lean
def escRowsR (p : String) (f : Nat) (done : List Neg) (seen : SeenR) : List Neg :=
  (seen.filter (fun QT => sameSet QT.2 done)).map
    (fun QT => interpR p f [] done (some (.up QT.1)) seen)

def escConjR (p : String) (f : Nat) (done : List Neg) (seen : SeenR) : List Neg :=
  (splits done).flatMap (fun Xr =>
    match Xr with
    | (.imp Qa N, rest) =>
        if seenMemR seen Qa done then
          [Neg.imp (.down (interpR p f [] done (some (.up Qa)) ((Qa, done) :: seen)))
                   (interpR p f [N] rest none seen)]
        else []
    | _ => [])
```

and the statements the induction must prove, at EVERY `seen`:

```lean
def SatE2RE (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR), Saturated done →
    ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      UpFrom (fun e =>
        Inv (nAndAll (interpR p e [] done none seen :: escConjR p e done seen) :: Δ)
          [] j ψ)

def SatA2RE (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg) (seen : SeenR), Saturated done →
    ParkedCtxP done → PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
      UpFrom2 (fun e f =>
        Inv (nAndAll (interpR p e [] done none seen :: escConjR p e done seen) :: Δ)
          [] .tru
          (nOrAll (interpR p f [] done (some (jGoal j G)) seen ::
                   escRowsR p f done seen)))
```

Both are OPEN — no term of either type is built.  What IS proved is the
specialisation, which is the check that the generalisation is the right one:

    escRowsR_nil, escConjR_nil : at `seen = []` both escape lists are []
    satE2R_of_escapes : SatE2RE p → SatE2R p                       PROVED
    satA2R_of_escapes : SatA2RE p → SatA2R p                       PROVED
    pll_ui_R_esc : (∀ p, SatE2P p) → (∀ p, SatA2P p) →
                   (∀ p, SatE2RE p) → (∀ p, SatA2RE p) → PLL_UI    PROVED

The escape SHAPE is the one WP12 Stage 0's leg R2 decided on designed cell
(ix) (`docs/n4-pair-design.md` §3): the sufficient datum `b` is not reached
by `A^R` at the same-station residue, IS reached by `A^R(r) ∨ A^R(g)`, and
lands at the guard `g`.  The two statements above have NOT themselves been
through a refutation stage; that is the FIRST task of the work package that
attempts the induction (rules 7 and 9), before any family build is scoped.

### 4.4 Why the induction was not attempted in this run

The cofinality argument for `interpP` is `LJF/OFuelPFam.lean`: 1958 lines, an
18-definition mutual founded on `μ = (normalised derivation height, station
weight, sizeOf)`, whose olean is 237 MB and whose build is 25 minutes.
Re-authoring it for `interpR` with escapes is a work package of that scale,
not of the four hours this stage was budgeted; and this run's modules are
forbidden to import it, so no part of a re-authoring could have been checked
against it here.  The scaffolding it will need — literal stabilisation,
soundness, fuel monotonicity, the specialisation above — is what this
package delivers.

---

## 5 · Status

| claim | status |
|---|---|
| `RFounded`, `interpGR_founded_eq`, `interpGR_stab_of_founded` | PROVED |
| `κ₂` non-increasing / strictly down at a guard edge (`kap2_le`, `kap2_lt`) | PROVED |
| `stepR_congr` — the edge mirror is complete | PROVED |
| `edges_decreaseR` — the descent | PROVED |
| **`RBound p`** (`rBound`) | **PROVED**, choice-free |
| literal stabilisation at every station (`rStabLit{E,A}_uncond`) | PROVED, choice-free |
| a `ν` without the goal term founds the recursion | REFUTED (`gate_r_nu_goal_term`) |
| a measure without `κ₂` founds the recursion | REFUTED (`gate_r_kappa`) |
| the easy halves for `interpR` (`easyLvlR`) | PROVED |
| **soundness** (`eSoundR`, `aSoundR`) | **PROVED** |
| `interpR = interpP` | REFUTED (`gate_r_sound_nonvacuous`) |
| fuel monotonicity (`interpR_mono{E,A}`) | PROVED |
| `hasUI_R`, `stabilisationAllP_of_R`, `pll_ui_R` | PROVED |
| `satE2R_of_escapes`, `satA2R_of_escapes`, `pll_ui_R_esc` | PROVED |
| **`SatE2R p`, `SatA2R p`** | **OPEN** |
| `SatE2RE p`, `SatA2RE p` (the generalisation to prove them by) | OPEN, and DESIGN — no refutation stage yet |
| N4 for PLL | **OPEN**, over `SatE2R` + `SatA2R` alone |

Before WP12b, N4 for PLL rested on `QBound` + `PQEquiv` for `interpQ`, of
which `QBound` was proved (WP9) and `PQEquiv` was reduced to the two hard
halves `PQHard`, whose per-fuel form WP11 showed to be the wrong statement
(its induction hypotheses are REFUTED at residue states).  After WP12b it
rests on cofinality for `interpR` alone — a statement of the same kind as
`SatE2P` / `SatA2P`, which are theorems for `interpP`, and reached by the
same method rather than by a per-fuel comparison of two recursions.
