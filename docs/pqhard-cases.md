# `PQHard`: Stage 0c — the induction hypothesis, measured

Route (B), node **N4**, WP11.  The obligation the route now rests on
(`wip/ui_routeB_pqequiv.lean`):

    PQHard p :=
      (∀ (f : Nat) (done : List Neg),
          Inv [interpQ p f [] done none []] [] .tru (interpP p f [] done none)) ×
      (∀ (f : Nat) (done : List Neg) (G : Neg),
          Inv [interpP p f [] done (some G)] [] .tru (interpQ p f [] done (some G) []))

Written 2026-09-06.  Every claim below is PROVED (Lean declaration, pin
measured), REFUTED (kernel-checked countermodel), or OPEN — kept rigidly
distinct; a run past its deadline is `TIMEOUT — SKIPPED, no verdict`.

Harness: `_probe/stage11.lean`.  Same transfer and decider as
`_probe/stage0.lean`: `Inv.sound` + `polInvT`, `FRJ.Arity.decideByEngine` on
`ofPLL`, certified in process, after `Rewrite.simplifyWith Rewrite.fullSetC
200`; config rounds 16, jmax 3, pmax 2, lamCap 24, maxRS/maxIS 3000.

**Control gate, watched** (`stage11 gate`): `p ⊢ ◯p` **PROVED**, `◯p ⊢ p`
**REFUTED** — both in 0 ms, nrm size 4.

---

## 1 · Why these states

The `∀p` hard half `A^P(s) ⊢ A^Q(s | seen)` survived every state
`docs/pqequiv-cases.md` §3–§4 decided, and the `∃p` hard half
`E^Q(s | seen) ⊢ E^P(s)` is REFUTED there whenever `seen` records a compound
antecedent of the station.  A `∀p` induction cannot simply avoid the `∃p`
half: exactly three rows of the recursion carry an `∃p` interpolant in
NEGATIVE position, and all three are reachable inside a guard task.

| where | the row |
|---|---|
| `aggQ`, goal `Q ⊃ N` | `↓E(b, done │ seen) ⊃ A(b, done ⇒ N │ seen)`, `b ∈ invertPos Q` |
| `stepQ`, `↑(P₁∨P₂) :: todo`, `∀p` | `↓E(b ++ todo │ seen) ⊃ A(b ++ todo ⇒ G │ seen)` |
| `aRowsQ`, `.circ R`, `box = true` | `↓E([↑R], rest │ seen) ⊃ A([↑R], rest ⇒ goal │ seen)` |

A row-wise `impMono` transfer of the first two needs `E^Q ⊢ E^P` at the row's
antecedent state, which is the refuted direction.  Stage 0c measures what
happens at exactly those states.

**The site.**  Two ◯-free cells whose guard task contains an implication
goal, so that the first row above occurs inside it:

* cell (iii) `d3 = [↓(a ⊃ ↑b) ⊃ ↑c]`, recorded antecedent `qd = ↓(a ⊃ ↑b)`;
  guard goal `↑qd`, then `aggQ` at the goal `a ⊃ ↑b`, branch `b = [↑a]`;
* cell (vii) `d7 = [↓((a∨b) ⊃ ↑c) ⊃ ↑g]`, recorded antecedent
  `q7 = ↓((a∨b) ⊃ ↑c)`; guard goal `↑q7`, then `aggQ` at `(a∨b) ⊃ ↑c`,
  branch `b = [↑a]`.

The row's antecedent state is `s = ([↑a], done, none │ [Q′])`, its consequent
state `s′ = ([↑a], done, some ↑g′ │ [Q′])` (`↑b` for (iii), `↑c` for (vii)).
`C` is the conjunct `interpQ` drops at `s`, at the fuel it occupies inside
`E^P(s)` (the branch costs one fuel, entering the station aggregate a second):

    C := ↓A^P_{f-2}([], ↑a :: done, some ↑Q′) ⊃ E^P_{f-2}([N_{Q′}], [↑a], none)

## 2 · The questions

    Q0  E^P(s) ⊢ E^Q(s│seen)                          -- a THEOREM (`pqEasyE`): calibration
    Q1  E^Q(s│seen) ⊢ E^P(s)                          -- the naive ∃p, row-wise
    Q2  E^Q(s│seen) ∧ C ⊢ E^P(s)                      -- the relativised ∃p
    Q3  A^P(s′) ⊢ A^Q(s′│seen)                        -- the naive ∀p at the consequent
    Q4  (↓E^P(s) ⊃ A^P(s′)) ⊢ (↓E^Q(s│seen) ⊃ A^Q(s′│seen))   -- the ROW
    Q5  E^Q(s│seen) ⊢ A^Q(s′│seen)                    -- is the Q-row trivial?

## 3 · The verdicts

| cell | fuel | sizes `E^P`/`E^Q`/`A^P`/`A^Q`/`C` | Q0 | Q1 | Q2 | Q3 | Q4 | Q5 |
|---|---|---|---|---|---|---|---|---|
| (iii) | 3 | 1/1/1/1/3 (degenerate, NFEQ both) | — | PROVED | PROVED | PROVED | PROVED | REFUTED |
| (iii) | 5 | 1/1/1/1/3 (degenerate, NFEQ both) | — | PROVED | PROVED | PROVED | PROVED | REFUTED |
| (iii) | 6 | 15/7/7/1/7 | **TIMEOUT** | **TIMEOUT** | — | — | **TIMEOUT** | — |
| (iii) | 7 | 15/7/7/1/7 | not run | **TIMEOUT** | PROVED (nrm 3) | PROVED (nrm 9) | **TIMEOUT** | REFUTED (nrm 9) |
| (vii) | 6 | 21/7/13/1/13 | **TIMEOUT** | not run | PROVED (nrm 3) | PROVED (nrm 15) | not run | REFUTED (nrm 9) |

Deadlines: 300 s except cell (iii) fuel 6 Q1 and Q4, run at 600 s and still
past deadline.  Every TIMEOUT is reported as a skip, no verdict.

**The calibration is decisive about the skips.**  Q0 is `pqEasyE` — a
machine-checked theorem of `wip/ui_routeB_pqequiv.lean`, pin
`[propext, Classical.choice, Quot.sound]` — and the decider does NOT decide
it at these sizes within 300 s, at either cell.  So the TIMEOUTs on Q1, Q4
and Q7 (below) are a property of the decider at `|E^P| ≥ 15`, not evidence
about the statements.  Stage 0c could not reach the naive `∃p` hypothesis at
the states the `∀p` row needs it; at the fuels where it could (3 and 5) the
interpolants are literally constant of size 1 and settle nothing.

**What did get verdicts**, at both designed sites and at the only fuels where
the cells are non-degenerate:

* **Q2 PROVED** — `E^Q(s│seen) ∧ C ⊢ E^P(s)`, and the implication's normal
  form is size 3, i.e. after normalisation `E^Q ∧ C` and `E^P` coincide: the
  dropped conjunct is EXACTLY what is missing at the site, nothing else.
* **Q3 PROVED** — the naive `∀p` hypothesis at the row's consequent state,
  where `A^Q` is not trivially derivable.
* **Q5 REFUTED** — `E^Q(s│seen) ⊬ A^Q(s′│seen)`: the Q-row is NOT vacuously
  true, so the row does not transfer for a trivial reason.

**A consequence, not a separate run.**  Q2 and Q3 compose: from `C`, the
P-row `↓E^P(s) ⊃ A^P(s′)` and `E^Q(s│seen)`, Q2 gives `E^P(s)`, the P-row
gives `A^P(s′)`, and Q3 gives `A^Q(s′│seen)`.  So at both designed sites

    C, (↓E^P(s) ⊃ A^P(s′))  ⊢  (↓E^Q(s│seen) ⊃ A^Q(s′│seen))

— **the row DOES transfer once the induction is relativised by the dropped
conjunct**, and the two measured verdicts are what says so.

## 4 · The candidate that Stage 0c could not test

`_probe/stage11.lean` also carries

    Q7  E^Q(s│seen) ∧ A^P_{f+2}([], done, some ↑Q′) ⊢ E^P(s)
    Q9  A^P_{f+2}([], done, ↑Q′) ∧ (↓E^P(s) ⊃ A^P(s′)) ⊢ (↓E^Q(s│seen) ⊃ A^Q(s′│seen))

relativising by the GUARD interpolant rather than by `C` — the hypothesis the
`∀p` side actually holds where `seen` grows, since the first conjunct of
`parkRowA`'s P-row is `A^P([], done, some ↑Qa)` at exactly that fuel.  At cell
(iii) fuel 6, **TIMEOUT — SKIPPED**: building the relativiser
`nrm (eraseNeg (interpP p (f+2) [] d3 (some (.up qd))))` alone exceeds the
300 s deadline.  No verdict either way.

## 5 · What Stage 0c settles, and the obstruction that remains

1. **The naive simultaneous hypothesis is dead, and not only in one half.**
   Write

       HardLvl p f := (∀ todo done seen, Inv [interpQ p f todo done none seen] [] .tru
                                             (interpP p f todo done none))
                    × (∀ todo done G seen, Inv [interpP p f todo done (some G)] [] .tru
                                             (interpQ p f todo done (some G) seen))

   `HardLvl p 0` is provable (`⊤ ⊢ ⊤`, `⊥ ⊢ ⊥`), and `HardLvl p f` is FALSE
   for `f = 3, 4, 5` at cell (i) by the kernel-certified countermodels of
   `docs/pqequiv-cases.md` §3.  Hence **no step lemma
   `HardLvl p f → HardLvl p (f+1)` can exist**: an induction of that shape is
   REFUTED, not merely unproved.

2. **The relativised shape is the live candidate.**  Both inductions carry,
   for each `Q′ ∈ seen`, the conjunct `interpQ` dropped at `Q′`'s recording
   site,

       C_{Q′} := ↓A^P_k([], D_{Q′}, some ↑Q′) ⊃ E^P_k([N_{Q′}], R_{Q′}, none)

   (`D_{Q′}` the station at which `Q′ ⊃ N_{Q′}` is parked, `R_{Q′}` the
   residual station, `k` the fuel of the recording site).  §3 measures that
   this closes the `∃p` half and the `∀p` row at both designed sites.  The
   fuel bookkeeping is sound: `C_{Q′}` is ANTITONE in the fuel — `A^P` is
   monotone and `E^P` antitone, both PROVED in `wip/ui_routeB_pqmono.lean`
   (`interpP_monoA`, `interpP_monoE`) — so recording `C_{Q′}` once, at the
   fuel of its recording site, serves every lower fuel the recursion reaches
   below it.

3. **The obstruction, stated exactly.**  `seen` grows at ONE place: the guard
   call of `parkRowE` / `parkRowA`, `prev [] done (some ↑Qa) (Qa :: seen)`.
   Transferring the `∀p` row there needs the relativised `∀p` hypothesis at
   `Qa :: seen`, hence needs `C_{Qa}` supplied at that point.  `C_{Qa}` is a
   conjunct of `E^P([], done, none)` — it is the guarded component of
   `eConjRowsP`'s row for the split `(Qa ⊃ N, rest)`
   (`LJF/OFuelPMin.lean`: `dykConjMemP`, `orimpConjMemP`, `shimpConjMemP`,
   `andimpConjMemP`, `cimpConjMemP`) — and the `∀p` derivation has only
   `A^P([], done, some ↑Qa)` in hand at that point, never `E^P` at the
   station.  **Where `C_{Qa}` comes from on the `∀p` side is OPEN**; it is the
   one gap between the measured evidence and a proof.

4. **Fuel monotonicity is no longer missing.**  Stage 1 is PROVED for both
   recursions and at every state, `seen` and reset policy
   (`wip/ui_routeB_pqmono.lean`): `interpG_monoE`, `interpG_monoA`,
   `interpP_monoE`, `interpP_monoA`, and the `+ k` versions.  `interpQ_monoA`
   is what lifts the self-attack row at the guard state, where the row of
   `interpP` is the SAME state one fuel down.

## 6 · Status

`PQHard p` is **OPEN**, unchanged and unweakened: no term of that type is
built, and no `sorry` asserts it.  Nothing in Stage 0c refutes it; the
top-level per-fuel statement it names survived its designed candidate in
`docs/pqequiv-cases.md` §4.  The cofinal fallback `PQHardCof` of the WP11
brief was not reached and remains unbuilt.
