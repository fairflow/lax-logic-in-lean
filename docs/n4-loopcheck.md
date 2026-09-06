# The loop-checked recursion `interpQ`: design, cells, and what N4 still owes

Route (B), node N4 — *stabilisation of the interpolant chains at every
saturated parked station*, the open theorem of the campaign (uniform
interpolation for PLL is equivalent to it, both directions proved).  Written
2026-09-06, WP8.  Every claim below is PROVED (named Lean declaration, pin
measured), REFUTED (kernel-checked counterexample), or OPEN — kept rigidly
distinct.

Modules: `wip/ui_routeB_n4q.lean` (the definition and `p`-freeness),
`wip/ui_routeB_n4q_cells.lean` (the twelve designed cells),
`wip/ui_routeB_n4q_thm.lean` (the theorems and the two obligations).

---

## 1 · Why a loop check, and what it is

`interpP`'s ∀p attack row for a parked implication `Q ⊃ N ∈ done` at a goal
`↑G` is (`LJF/OFuelPMin.lean`, `truStationRowsP`)

    A_f(done ⇒ ↑Q)  ∧  A_f(N :: rest ⇒ ↑G)

— the guard at the FULL station, which is route (B)'s retention principle.
When `↑G` IS `↑Q` the row contains the same call one fuel down, so the chain is
strictly `sizeNeg`-ascending and the LITERAL form of N1 is false at every
saturated station carrying a compound implication (`not_aStabEq1` …
`not_aStabEq6d`, `docs/n4-circfree-cases.md` §1).  Up to interderivability the
chain does stabilise on ◯-free stations (`n4_circFree_uncond`, by transport
from Pitts), and the reason is that the looping disjunct adds no consequence.

`interpQ` is `interpP` with the loop cut *in the definition*.  It carries

    seen : List Pos

— the antecedents whose own goal has already been attacked — and

* the ∀p attack row of a parked compound implication `Q′ ⊃ N` becomes `⊥` —
  the unit of the aggregate's `nOrAll` — when `Q′ ∈ seen` (`parkRowA`);
* the ∃p row's guarded conjunct `(↓A(done ⇒ ↑Q′) ⊃ E(N :: rest))` becomes `⊤`
  — the unit of the aggregate's `nAndAll` — on the same test, the residual
  component `E(rest)` being kept (`parkRowE`);
* a guard call that IS emitted is made at `Q′ :: seen`;
* every other clause of `interpP` is transcribed verbatim with `seen`
  threaded and unchanged.

The two clauses that differ from `interpP`, in full:

    parkRowE prev done Q′ N rest res seen  =
        (if Q′ ∈ seen then ⊤
         else ↓A_prev(done ⇒ ↑Q′ | Q′ :: seen) ⊃ E_prev(N :: rest | seen))
      ∧ E_prev(res ++ rest | seen)

    parkRowA prev done Q′ N rest goal seen =
        if Q′ ∈ seen then ⊥
        else A_prev(done ⇒ ↑Q′ | Q′ :: seen)  ∧  A_prev(N :: rest ⇒ goal | seen)

with `res = [↓N′ ⊃ N]` for the Dyckhoff row and `res = []` for the four other
compound shapes.

**Recording at the guard CALL SITE, not at the aggregate**, is the second
design decision, and it is what makes the measure of §4 close: `seen` is then
extended only at a guard call and only with an antecedent not already in it,
so it is monotone along EVERY edge of the recursion and strictly increasing on
exactly the edges where the weight rises.  The alternative — a ∀p aggregate at
a shift goal `↑Q` putting `Q` on `seen` for its own rows — was built first and
measured: it gives smaller interpolants and earlier thresholds (cell (iii) 8
against 12; S1 identical), but `seen` then has to be read as
`seenOf(goal, seen)`, which DROPS at the ∃p companion of a disjunctive
hypothesis in ∀p mode

    ↑(P₁∨P₂) :: todo, done, some ↑Q   ⟶   (b ++ todo), done, none

so the guard deficiency can rise there while the weight falls, and the
lexicographic measure does not close.  The committed definition records at the
call site.

**Form of the definition.**  `interpQ` is written in STEP form,

    interpG rst p 0     = the fuel-0 defaults (⊤ in ∃p mode, ⊥ in ∀p mode)
    interpG rst p (f+1) = stepQ rst p (interpG rst p f)

rather than as one thirty-clause `interpP`-style match.  Three consequences,
all of them why the module exists at all: it is STRUCTURAL in the fuel, so it
elaborates in 11 s; the eleven inlined copies of `interpP`'s row bodies become
five named functions (`eRowsQ`, `aRowsQ`, `parkRowE`, `parkRowA`,
`laxPrefixQ`), so the `p`-freeness proof is one lemma per function against an
arbitrary previous level instead of a `fun_induction` over thirty clauses; and
"the recursion bottoms out" becomes a statement about `stepQ` alone (§4).

---

## 2 · The reset policy: the blueprint's per-station check is REFUTED

The blueprint's WP3 loop elimination is a PER-STATION check: `seen` grows
within a station and is reset whenever the station changes, "because `seen`
grows within a fixed station and the antecedents of a station are finitely
many".  Both policies are instances of one recursion, parameterised by the
reset map `rst : List Pos → List Pos`:

    interpQ0 = interpG (fun _ => [])      per-station
    interpQ  = interpG id                 global

**The per-station policy does not terminate, and the counterexample is
◯-FREE.**  It is cell (iii) of `docs/n4-circfree-cases.md`,

    done = [↓(a ⊃ ↑b) ⊃ ↑c],   goal ↑↓(a ⊃ ↑b),

and the surviving loop is not through a guard at a fixed station but through
the ∀p GOAL INVERSION at an implication goal:

    A(done ⇒ ↑↓(a ⊃ ↑b))     [reached from a Dyckhoff guard call, which
                              recorded ↓(a ⊃ ↑b), so the row here is cut]
      --invert ↑↓M-->  A(done ⇒ a ⊃ ↑b)
      --branch b = [↑a]: `invertPos` moves ↑a into the station, seen RESET-->
        E([↑a] ++ done)
      --Dyckhoff ∃p guard-->  A([↑a] ++ done ⇒ ↑↓(a ⊃ ↑b))    and round again,

with the station one `↑a` longer each time round.  A per-station `seen` cannot
see it, because the station is never the same twice.  Kernel-checked:

    q0_3_not_const : ∀ f ∈ [12,13,14,15],
        interpQ0 "p" f [] cell3 (some goal3) [] ≠ interpQ0 "p" (f+1) [] cell3 (some goal3) []
    q_3_const_there : ∀ f ∈ [12,13,14,15],
        interpQ  "p" f [] cell3 (some goal3) [] =  interpQ  "p" (f+1) [] cell3 (some goal3) []

both `[propext]`.  (This is a refutation of the *design*, on the fuels at which
the global policy has already bottomed out; the `∀ f` ascent lemma is not
proved, and is not needed to settle which policy to build on.  Measured, not
kernel-checked: `interpQ0`'s chain at cell (iii) is still climbing at fuel 16.)

The policy that terminates carries `seen` across station changes as well.  It
is monotone along every edge of the recursion, which is what §4's measure
needs, and it is the definition `interpQ` names.

**The second repair, and it is not cosmetic.**  The first draft cut only the
∀p attack row and left the ∃p row's guard call unconditional.  That still
loops, again at cell (iii): `E(station) → A(station ⇒ ↑↓(Q′ ⊃ N′)) → invert →
A(station ⇒ Q′ ⊃ N′) → branch → E(b ++ station) → …`.  The check has to be
SYMMETRIC — `⊥` for the ∀p disjunct, `⊤` for the ∃p conjunct — which is also
what makes the polarity argument of §3 uniform.  Both repairs were found by
measuring the chains, not by reading the definition; and the first draft's
chain at cell (iii) plateaus at fuels 2 and 3 and then resumes climbing, which
is what a FALSE fixpoint looks like and is the reason the certificates of §5
check three or four fuels above the threshold and never one.

---

## 3 · Soundness is preserved, in the easy direction

Dropping a disjunct of a ∀p aggregate makes `A` STRONGER; dropping a conjunct
of an ∃p aggregate makes `E` WEAKER.  The two soundness statements are

    eSoundP : done ⊢ E                aSoundP : A, done ⊢ G

so a weaker `E` and a stronger `A` both make them easier, and the pair
(`E` weaker, `A` stronger) is consistent with every occurrence in the
definition:

| occurrence | in | polarity | effect |
|---|---|---|---|
| `E_prev(N :: rest)`, `E_prev(res ++ rest)` | ∃p aggregate | positive | weaker ⊆ weaker |
| `A_prev(done ⇒ ↑Q′)` in `↓A ⊃ E′` | ∃p aggregate | negative | stronger ⊆ weaker |
| `A_prev(…)` rows | ∀p aggregate | positive | stronger ⊆ stronger |
| `E_prev(b ++ todo)` in `↓E ⊃ A′` | ∀p aggregate | negative | weaker ⊆ stronger |

This is an argument, not a proof: the soundness pair for `interpQ` is not
built here.  It is not needed for N4 along the route of §5, which goes through
`PQEquiv` and inherits `interpP`'s own soundness.

PROVED here: `interpG_pfree` — the interpolant never mentions `p`, at any fuel,
under either policy, `[propext, Quot.sound]`.  That is the only property of
`interpQ` the pair needs beyond the equivalence.

---

## 4 · Literal stabilisation: what is proved, and the one edge that is open

The step form turns "the recursion bottoms out" into one statement:

    QFounded rst p μ  :=  ∀ prev₁ prev₂ s,
        (∀ t, μ t < μ s → prev₁ t = prev₂ t) →
        stepQ rst p prev₁ s = stepQ rst p prev₂ s

over states `s = (todo, done, goal, seen)`: the step at `s` consults the level
below only at states of strictly smaller `μ`.

**PROVED, axiom-free** (`wip/ui_routeB_n4q_thm.lean`):

    interpG_founded_eq : QFounded rst p μ → ∀ n s, μ s ≤ n →
        ∀ f g, n ≤ f → n ≤ g → interpG rst p (f+1) s = interpG rst p (g+1) s
    interpG_stab_of_founded : QFounded rst p μ → ∀ s f, μ s + 1 ≤ f →
        interpG rst p f s = interpG rst p (μ s + 1) s

by strong induction on `μ s`, with the explicit threshold `μ s + 1`.  Hence
`qStabLitE_of_bound`, `qStabLitA_of_bound`: a bound gives literal stabilisation
at EVERY station, with no saturation hypothesis, because `QBound` is a
statement about the recursion and not about a cell.

**OPEN: `QBound p := Σ′ μ, QFounded id p μ`.**  For `interpP` no such `μ`
exists — the guard row at the goal `↑Q` calls the same state one fuel down
(`not_fuelStep1A`).  For `interpQ` the shape of the measure is forced by the
edges, and this is the exact state of it:

Write `ν(todo, done, goal) = 2·sum3 todo + sum3 done + 3^(wNeg goal)` (`0` for
the ∃p goal), the measure `eMinPP`/`aMinPP` already run on.  Then

| edge | ν | `seen` |
|---|---|---|
| processing (`todo` head), fire | strictly down | carried |
| ∃p residual / Dyckhoff residual / opened box | strictly down | carried |
| ∀p station row, second component `A(N :: rest ⇒ goal)` | strictly down | carried |
| ∀p goal inversion at `↑(P₁∨P₂)`, `↑↓M`, `∧`, the lax prefix | strictly down (goal) | carried |
| ∀p at an implication goal `Q ⊃ N` | strictly down (`p3_21`) | carried |
| **the guard edges** `→ A(done ⇒ ↑Q′)` | **UP** | **GROWS strictly** |

so the measure is lexicographic, `μ = (K − |seen|, ν)` with

    K  =  |{ Q′ : Q′ a compound antecedent reachable at this cell }| .

The guard edges strictly decrease the first component, because the row fires
only when `Q′ ∉ seen` and the call is made at `Q′ :: seen`; every OTHER edge
carries `seen` unchanged, so the first component is constant there and `ν`
strictly decreases.  That is the whole of the descent argument, and it is why
the recording had to move to the guard call site (§1).

**What is left to build**, and it is no longer an edge of the recursion:

1. the subformula-closure invariant that bounds `K` — that the compound
   antecedents reachable from a cell form a FINITE set, non-increasing along
   every edge.  Same shape as `interpP_circFreeN` (thread the invariant, kill
   the unreachable arms on the hypotheses).  The one place it needs care is the
   ∀p implication goal, where `invertPos Q` moves branches INTO the station —
   the growth that refuted the per-station policy (§2) — so the invariant must
   be stated over the subformula closure of the ORIGINAL cell and not over the
   current station.
2. the per-clause `ν` descent.  Every inequality is already in the repository:
   `ljf_dec_e` / `ljf_dec_a` discharge exactly these for `eMinPP` / `aMinPP`
   (`LJF/OFuelPMin.lean`), including `p3_2` for the opened box
   (`2·3^(wPos R) < 3^(wPos R + 1)`) and `p3_21` for the implication goal.

Neither is built.  `QBound` is OPEN.

---

## 5 · The cells: every one stabilises literally

Rule 9: designed cells, no enumeration.  The six ◯-free cells are those of
`docs/n4-circfree-cases.md` — on five of which `interpP`'s literal chain is
REFUTED — and five modal shapes chosen from the ways the recursion can loop
through a box, plus the running cell S1 of `docs/ui-ljfo-clause-table.md`
§4.12.  Each verdict is a KERNEL-CHECKED equation
`interpQ p f … = interpQ p W …` at three or four fuels above the threshold `W`
(`decide +kernel`, 26 decisions in 4.5 s, every one `[propext]`).

| cell | station ⇒ goal | `interpP` | `interpQ` const from |
|---|---|---|---|
| (i) | `[(a∨b) ⊃ ↑c] ⇒ ↑(a∨b)` | REFUTED | **4** (∃p: 3) |
| (ii) | `[(a∨b) ⊃ ↑c, (c∨d) ⊃ ↑a] ⇒ ↑(a∨b)` | REFUTED | **6** (also at `↑(c∨d)`) |
| (iii) | `[↓(a ⊃ ↑b) ⊃ ↑c] ⇒ ↑↓(a ⊃ ↑b)` | REFUTED | **12** (∃p: 9) |
| (iv) | `[↓↑a ⊃ ↑b] ⇒ ↑↓↑a` | REFUTED | **4** |
| (v) | `[p ⊃ ↑c, ↑p] ⇒ ↑c` (unsaturated) | 3 | **3** |
| (vi) | `[(a∨b) ⊃ ↑c, ↓↑c ⊃ ↑d] ⇒ ↑d` | REFUTED | **5** (inner goal: 6) |
| (m1) | `[◯a] ⇒ ◯b` — a parked box under a lax goal | — | **4** |
| (m2) | `[↓◯a ⊃ ↑b] ⇒ ↑↓◯a` — a self-referential ◯ guard | — | **6** (at `◯a`: 5) |
| (m3) | `[◯↓((a∨b) ⊃ ↑c)] ⇒ ◯c` — opening re-creates a parked implication | — | **7** |
| (m4) | `[↓◯a ⊃ ◯b] ⇒ ◯b` — firing re-creates a box | — | **6** |
| (m5) | `[◯a, ↓◯a ⊃ ↑b] ⇒ ◯b` — box and ◯-implication together | — | **7** |
| **S1** | `[↓◯(↓(d ⊃ ↑a)) ⊃ ↑e, c ⊃ ◯g]` | — | **12** at `↑e`, **13** at `◯g`, **12** for `∃p` |

Controls, also kernel-checked: `interpQ = interpP` where no parked compound
implication is ever reached (cell (v); a bare box `[◯a]`; a `q`-implication
with a boxed body `[c ⊃ ◯g]`), and `interpQ ≠ interpP` at cell (i) from fuel 2
— so the change is located exactly at the rows it is meant to change.

**The refutation candidate of this package did not fire.**  The modal shapes
were chosen because a per-station `seen` cannot cut a loop through a box: the
box row moves to a NEW station `[↑R] ++ rest`, so a chain of stations that keeps
reopening boxes is exactly the Ghilardi–Zawadowski shape that would make PLL
lack uniform interpolation.  Under the global policy every one of them bottoms
out, and so does S1 — the cell that stopped the cofinality proof at the
founding (§4.11) and survived the sharpened instance screen (§4.12).  So no
designed cell refutes N4, and the modal case remains OPEN in the direction of
proof, not of refutation.

The thresholds also say what a closed-form bound must look like: it is not the
station's weight (cell (v) is heavier than cell (i) and stabilises later than
(i) but earlier than (iii)), and it grows with the DEPTH of the guard graph —
S1's 12 against cell (i)'s 4 — which is what §4's lexicographic measure
predicts, the first component being the number of distinct guard goals.

---

## 6 · N4 for `interpP`, over two obligations

`interpQ` stabilising says nothing about `interpP` on its own.  The bridge is

    PQEquiv p := ∀ f done g,
        Inv [interpP p f [] done g] [] tru (interpQ p f [] done g []) ×
        Inv [interpQ p f [] done g []] [] tru (interpP p f [] done g)

the redundancy lemma of `docs/n4-circfree-cases.md` §3.3, as data.  The EASY
halves are `interpQ ⊢ interpP` on the ∀p side (the dropped disjunct is `⊥`) and
`interpP ⊢ interpQ` on the ∃p side (the dropped conjunct is `⊤`); the HARD
halves are the redundancy claim — the self-attack disjunct is implied by the
retained ones.  It is stated as ONE interderivability and not as two
implications because §3's polarity table makes the four halves a single
simultaneous induction: `A^Q ⊢ A^P` needs `A^P ⊢ A^Q` under the `↓A ⊃ E′` of
`parkRowE`.

PROVED from the two obligations, `[propext, Classical.choice, Quot.sound]`
(the choice from `cutInv`'s `Type`-valued packaging alone):

    n4_of_interpQ    : PQEquiv p → QBound p → ∀ done G,
                       EStabilises p done × AStabilises p done G
    hasUI_of_interpQ : SatE2P p → SatA2P p → PQEquiv p → QBound p →
                       Saturated done → ParkedCtxP done → HasUI p done G

`cutInv` (§4.22) composes, four times, through `chain1` and `IDeriv.trans`.
Note what the conclusion does NOT need: no saturation, no parking, no
◯-freeness — both obligations are statements about the recursion itself, so
N4 comes out at every cell at once, and `hasUI_of_interpQ` adds the station
hypotheses only because `hasUI_of_stabilises` does.

`n4_circFree_intrinsic` is the ◯-free instance of the same route, and
`n4_circFree_byPitts` is the cross-check by elaboration: the same conclusion
is already inhabited on ◯-free cells UNCONDITIONALLY
(`n4_circFree_uncond`), over the same cofinality variables and with neither
obligation among its hypotheses.  So the obligations cannot be inconsistent
with a machine-checked theorem there — and the loop-checked route buys nothing
◯-free.  The modal case is what it is for.

---

## 7 · Status

| claim | status |
|---|---|
| `interpQ` defined, structural in the fuel, 11 s | PROVED (elaborates) |
| `interpG_pfree` | PROVED `[propext, Quot.sound]` |
| the per-station reset policy terminates | **REFUTED**, ◯-free cell (iii) |
| recording at the aggregate closes the measure | **REFUTED**, the ∨-hypothesis edge (§1) |
| literal constancy at the twelve cells, at the fuels tabled | PROVED `[propext]` |
| `interpQ = interpP` where no compound implication is reached | PROVED `[propext]` |
| `interpG_founded_eq`, `interpG_stab_of_founded` | PROVED, axiom-free |
| `n4_of_interpQ`, `hasUI_of_interpQ`, `n4_circFree_intrinsic` | PROVED over `PQEquiv`, `QBound` |
| `QBound p` (the measure) | **OPEN** — §4, two named components |
| `PQEquiv p` (the redundancy lemma) | **OPEN** — §6 |
| soundness of `interpQ` | not built; §3 is an argument, not a proof |
| N4 for PLL | **OPEN**, in neither direction; no designed cell refutes it |

The two obligations are `Type`-valued parameters, never `sorry` (rule 1): no
declaration in the three modules asserts anything it has not proved.
