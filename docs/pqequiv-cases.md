# `PQEquiv`: the designed cells, the verdicts, and the statement kept

Route (B), node **N4**, WP10 — the redundancy obligation

    PQEquiv p := ∀ (f : Nat) (done : List Neg) (g : Option Neg),
        IDeriv (interpP p f [] done g) (interpQ p f [] done g [])
    IDeriv M N := Inv [M] [] .tru N × Inv [N] [] .tru M

(`wip/ui_routeB_n4q_thm.lean`), the second of the two obligations
`n4_of_interpQ` runs on.  Written 2026-09-06.  Every claim below is PROVED
(named Lean declaration, pin measured), REFUTED (kernel-checked
counterexample), or OPEN — kept rigidly distinct.

Modules: `wip/ui_routeB_pqequiv.lean` (the easy halves and the residual
obligation).

---

**Provenance.**  The WP10 run built the easy halves and this harness, then was
killed with the machine (2026-09-06 ~04:30, the parallel family rebuilds of
§4.26); its verdicts were lost.  The verdicts below were re-run in the
campaign worktree ONE AT A TIME, each under a 300 s deadline, by
`_probe/stage0.lean` (top level), `_probe/stage0inner.lean` (inner states)
and `_probe/stage0c.lean` (the designed top-level candidate), between 07:45
and 09:25 BST on Matthew's instruction ("run a selection of the candidates
one at a time; two hours max; then switch to the proof").

## 1 · The transfer and the decider

`Inv.sound` (`LJF/OBridge.lean`) and `polInvT` (`LJF/OPolInv.lean`) give
`Nonempty (Inv [M] [] .tru N) ↔ Nonempty (LaxND [eraseNeg M] (eraseNeg N))`,
and `LaxND [φ] ψ ↔ LaxND [] (φ ⊃ ψ)`.  The decider is
`FRJ.Arity.decideByEngine` on `ofPLL`, certified in-process
(`checkClosed_sound`, `decideGbuW_of_check`), after normalisation by
`Rewrite.simplifyWith Rewrite.fullSetC 200`.  Config: rounds 16, jmax 3,
pmax 2, lamCap 24, maxRS/maxIS 3000.  Verdicts are `PROVED` / `REFUTED`
(both certificate-carrying) / `FLAG(not-closed)`; a run past its deadline is
`TIMEOUT — SKIPPED, no verdict`.

Gate watched (the control, every batch): `p ⊢ ◯p` PROVED, `◯p ⊢ p` REFUTED,
and the CROSS cells `interpP` at (i)-∀p against `interpQ` at (vi)-∀p REFUTED
in both directions — so a `PROVED` below is not the decider saying yes to
everything.

## 2 · Top level (`seen = []`): the statement `PQHard` names — no refutation

Cells (i), (iii), (vi) (◯-free, first), (m1), (m6), (m10) (modal), both
modes, fuels 1–3 everywhere and fuel 4 on (i) and (iii): **40 runs, every
direction PROVED, no timeout, and `NFEQ = true` in every run** — after
normalisation the two interpolants are literally the same formula at these
cells and fuels.  Sizes 1–15 before normalisation, 3 after.  So these cells
refute nothing and establish nothing beyond consistency: the loop check is
invisible at the top level here.

## 3 · Inner states, the guard task with `Q′` already recorded

State `([], done, some ↑Q′, [Q′])` (∀p) and `([], done, none, [Q′])` (∃p) for
each compound antecedent `Q′` of the cell — the states an induction on the
fuel would need the hard halves at.

| cell | fuel | ∀p naive `A^P ⊢ A^Q` | ∃p naive `E^Q ⊢ E^P` | note |
|---|---|---|---|---|
| (i) | 2 | PROVED (NFEQ) | PROVED (NFEQ) | |
| (i) | 3 | PROVED (NFEQ) | **REFUTED** (`|E^P|=5`, `|E^Q|=3`) | the dropped conjunct is a consequence `E^Q` lacks at this fuel |
| (i) | 4 | PROVED (`|A^P|=15`, `|A^Q|=3`, nrm 19) | **REFUTED** | |
| (iii) | 2–4 | PROVED (NFEQ) | PROVED (NFEQ) | |
| (m10) | 2–4 | PROVED (NFEQ) | PROVED (NFEQ) | |
| (m6) | 2 | PROVED (NFEQ) | PROVED (NFEQ) | |
| (m6) | 3, 4 | PROVED (NFEQ) | **REFUTED** (`|E^P|=4`, `|E^Q|=3`) | |
| (vi) | 2 | PROVED (both antecedents) | PROVED | |
| (vi) | 3 | PROVED (first antecedent) | TIMEOUT on the second antecedent — SKIPPED | |
| (vi) | 4 | PROVED (`|A^P|=29`, `|A^Q|=17`, nrm 47) | TIMEOUT — SKIPPED | |
| (i) | 5 | PROVED (`|A^P|=35`, `|A^Q|=3`) | **REFUTED** (`|E^P|=17`, nrm 17) | |
| (iii) | 5 | PROVED (NFEQ) | **REFUTED** (`|E^P|=9`, `|E^Q|=3`, nrm 13) | cell (iii) joins at fuel 5 |

The easy halves PROVED in every run, as they must (they are theorems).

**What this settles.**  The naive per-state induction hypothesis is FALSE
on the `∃p` side: at a state whose `seen` records `Q′`, `interpQ`'s
`∃p` interpolant has dropped the conjunct `↓A(done ⇒ ↑Q′) ⊃ E(N :: rest)`,
and that conjunct is NOT a consequence of the rest at the same fuel — it is
a consequence of the station (`X, done ⊢ Q′` and `done ⊢ Q′ ⊃ N` give
`done ⊢ X ⊃ E(N :: rest)`) that `interpP` adds explicitly as a row and
`interpQ` reaches, if at all, only through cofinality.  On the `∀p` side
the naive hypothesis survived every decided cell.  Hence: the `∀p` hard half
can be attempted by a direct induction on the fuel (the self-attack row at
the guard state is the SAME state one fuel down, so the induction
hypothesis applies to it, and fuel-monotonicity of `A^Q` lifts it); the
`∃p` hard half at inner states needs the dropped conjunct supplied by the
context, and whether the TOP-level per-fuel `∃p`/`∀p` statements survive
where such an inner `E` sits in the negative position of a `∀p` row is the
question §4 asks.

## 4 · The designed top-level candidate, and the residue states (`_probe/stage0c.lean`)

Cell (vii) `[↓((a∨b) ⊃ ↑c) ⊃ ↑g] ⇒ ↑↓((a∨b) ⊃ ↑c)`: a Dyckhoff-parked
implication whose antecedent has a DISJUNCTIVE antecedent, so that inside
the guard task the `∀p` goal inversion produces branching rows
`↓E([↑a] ++ done | [Q′]) ⊃ A(… ⇒ ↑c | [Q′])` whose `E` sits at a state where
§3 says `E^Q ⊬ E^P`.  If the per-fuel top-level statement can fail, this is
where.  Cell (viii) adds a box hypothesis and a lax goal.

| cell | fuels | ∀p `A^P ⊢ A^Q` | ∃p `E^Q ⊢ E^P` | `NFEQ` |
|---|---|---|---|---|
| (vii) | 2, 3, 4, 5, 6 | PROVED at every fuel | PROVED at every fuel | true at every fuel (sizes 1, 1, 7, 7, 27 / 3, 3, 3, 13, 13) |
| (viii) | 3, 4, 5 | PROVED | PROVED | true (sizes 7, 7, 24 / 2, 2, 21) |

**The top-level per-fuel statement survives its designed refutation
candidate**: at the top level the two interpolants are literally equal
after normalisation up to fuel 6, i.e. the loop check's effect inside the
guard task is absorbed before it reaches the top.

Residue inner states (goal a residue of `Q′`, `Q′ ∈ seen`; the `∀p` naive
hypothesis at the states a direct induction visits after the guard):

| state | fuels | ∀p naive `A^P ⊢ A^Q` | sizes `|A^P|`/`|A^Q|` |
|---|---|---|---|
| (i) `done ⇒ ↑a`, seen `[a∨b]` | 3, 4, 5 | PROVED (NFEQ false) | 7/1, 7/1, 19/1 |
| (iii) `↑a :: done ⇒ ↑b`, seen `[Q′]` | 3, 4, 5 | PROVED | 1/1, 1/1, 7/1 |
| (vii) `↑a :: done ⇒ ↑c`, seen `[q7]` | 3, 4, 5 | PROVED | 1/1, 1/1, 13/1 |

## 5 · What the candidates stage settles (2026-09-06, 08:17)

* `PQHard` as stated — per fuel, `seen = []` — is NOT refuted: forty top-level
  runs on six cells, ten on the designed candidate (vii), six on (viii),
  every direction PROVED.  No certificate against it exists.
* The naive per-state induction hypothesis is REFUTED on the `∃p` side at
  every state whose `seen` records a compound antecedent of the station
  (cells (i), (iii), (m6); fuels 3–5; kernel-certified countermodels), and
  survives on the `∀p` side at every guard and residue state tested (fuels
  2–5, sizes up to 35 against 3).
* Two skips: cell (vi) inner states at fuels 3 and 4 (the second antecedent's
  `∃p` half, then the `∀p` half at fuel 4) hit the 300 s deadline — no
  verdict, reported as such.
* Consequence for the proof (WP11): the `∀p` hard half may be attempted by a
  direct induction on the fuel over the generalised state and every `seen`
  (at the guard state the self-attack row of `interpP` is the SAME state one
  fuel down, so the induction hypothesis applies to it and fuel
  monotonicity of `A^Q` lifts it); the `∃p` hard half must be relativised —
  at `seen ∋ Q′` the dropped conjunct `↓A(done ⇒ ↑Q′) ⊃ E(N :: rest)` has to
  come from the context — and how the two inductions mesh where an inner
  `E` sits in the negative position of a `∀p` row is exactly what is not
  yet known.  Fuel monotonicity (no lemma exists) is the first thing to
  prove.  If no per-fuel induction hypothesis survives the decider, the
  cofinal form `∀ f, Σ g, E^Q_g ⊢ E^P_f` / `∀ f, Σ g, A^P_f ⊢ A^Q_g` is the
  honest restatement, and it suffices for N4 (`n4_of_interpQ` only needs
  the hard halves at all fuels above the literal threshold).

