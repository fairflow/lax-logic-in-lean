# `Gbu◯(G)`: the ◯-obligations, read off Theorem 8

*2026-08-29.  Branch `claude/frjv-completeness-693c52`, worktree
`strange-thompson-902a24`.  Companion to `docs/gbu-adoption-plan.md`.*

Stage 3 of the adoption is complete over IPC: §5's Lemmas 7–12,
Theorem 7 (termination), Theorem 8 (correctness of `BSearch`), Theorem 9
(the duality) and Theorem 10 (completeness of both calculi) are proved
in `wip/gbu.lean`, `wip/gbu_db.lean` and `wip/gbu_search.lean`, all
pinning `[propext, Quot.sound]`.

`Gbu(G)` is a calculus for IPC.  Our `Form` carries a `◯` constructor,
so `search` takes two hypotheses,

    hcircL : ∀ X ∈ Sf^L(G), X is not ◯-shaped
    hcircR : ∀ X ∈ Sf^R(G), X is not ◯-shaped

and the elaborator reports where they are consumed.  They are consumed
at exactly **three** points, marked `◯-SEAM` in the proof.  Those three
points are the complete obligation list for `Gbu◯(G)`: the rules are
read off the gaps, not guessed.

---

## The method

Every case of Theorem 8 has the same shape.  To justify applying a rule
`R` with premises `τ₁ … τₙ` at a sequent `τ` whose database query has
failed, one needs

    (INV_R)    D ▷ τⱼ   implies   D ▷ τ        for each premise τⱼ,

so that `D ⋫ τ` gives `D ⋫ τⱼ` and the recursion may proceed.  `INV_R`
is proved by applying **one FRJ rule** to the database row for `τⱼ` and
then closing under (DB2).  Hence:

> a rule of `Gbu(G)` exists exactly where a rule of `FRJ(G)` exists with
> the matching conclusion, and its side conditions are that rule's side
> conditions.

The `Gbu◯` rules are therefore *determined* by the `FRJV(G)` rule table,
subject only to soundness.  The complete list of `FRJV` rules with a
`◯`-conclusion:

| judgment | rule | premises | conclusion | side conditions |
|---|---|---|---|---|
| regular | `circIn` | `Γ ⇒ Z` (tag `t`) | `Γ ⇒ ◯Z` | `t = barren ∨ (t = chain W ∧ Covers Γ W Z)` |
| regular | `joinCirc`, `joinCircP` | irregular family (+ regular family) | `Γ ⇒ ◯Z` | the join conditions |
| irregular | `circNotIn` | `Γ ⇒ Z` (**regular**, tag `t`) | `∅ ; Θ → ◯Z` | `∀X∈Θ, X ∈ Cl(Γ) ∧ X ∈ Ĝ`; the same tag condition |
| irregular | `axIC` | — | `∅ ; vacZone_A(G,ats) → ◯F` | `ats ⊆ Ĝ_at`, `classForce ats F = false` |

---

## Seam 1 — a `◯`-formula in the regular left zone

    Ψ, ◯Z ⇒g C            no rule of Gbu applies

**The rule is forced, and it is the PLL ◯-elimination:**

    Ψ, Z ⇒g ◯C
    ───────────────  L◯          (goal ◯-shaped)
    Ψ, ◯Z ⇒g ◯C

* *Soundness*: `⋀(Ψ,◯Z) ⊃ ◯C` follows from `⋀(Ψ,Z) ⊃ ◯C` by ◯E.  With
  an unrestricted goal the rule is **unsound** — `◯Z ⊬ Z` — so the
  ◯-shape of the goal is not a convenience, it is the rule.
* *Invertibility (`INV_L◯`)* is **free**: `D ▷ (Z::Ψ ⇒g C)` gives
  `Z ∈ Cl(Γ)`, hence `◯Z ∈ Cl(Γ)` by the `Clo.circ` clause already in
  `FRJ/Basic.lean:1127`.  No FRJ rule is applied, exactly as for
  `L∧`/`L∨`/`L⊃`'s right premise.
* *Measure*: `Cl(◯Z::Ψ) ⊆ Cl(Z::Ψ)` so `unclosed` does not rise, and
  `|Z| < |◯Z|` so `seqSize` drops.  `Wg` is unaffected.

**But `L◯` does not remove `◯` from the critical case.**  When the goal
is not ◯-shaped, `◯Z` stays in the context and reaches the critical
sequent.  So `Ĝ` must be widened to its three-zone form

    Ĝ = Ĝ_at ∪ Ĝ_imp ∪ Ĝ_circ

and **Lemmas 11 and 12 must be re-proved with a non-empty ◯ zone.**
That is where the weight of the extension actually falls.  Both current
proofs discharge the V-join's premise

    hcirc : ⋃ⱼ (Σⱼ)^◯ = []

from `Ω ⊆ Ĝ_at ∪ Ĝ_imp`; with ◯ admitted this is false and `joinAt` /
`joinOr` no longer apply.  Their modal variants `joinAtP` / `joinOrP`
apply instead, at the cost of a second, *regular* premise family `Δs`
and the condition

    hJ5 : ∀ Y, ◯Y ∈ ⋃ⱼ (Σⱼ)^◯ → ∃ i, Y ∈ Cl(Δ_i).

In `Search` terms this is a **new database query**, beside `▷`:

    for each ◯Y ∈ Ω:  ∃ (Δ ⇒ F) ∈ D  with  Y ∈ Cl(Δ)

i.e. "some row refuting the goal already forces `Y`".  If that query
fails for some `◯Y ∈ Ω`, the Search pattern says a non-invertible rule
must fire — and the only candidate premise is `Ω, Y ⇒g F`, which is
sound only when `F` is ◯-shaped, i.e. it collapses back into `L◯`.  For
a **prime** goal `F` with `◯Y ∈ Ω` there is no rule at all: `◯Y` cannot
help prove an atom.  So the cell is neither `Gbu◯`-provable nor (unless
`hJ5` is dischargeable) `FRJV`-refutable.  **This is a candidate
location for the residual incompleteness**, and it should be tested
against the 6-cell residue before any rule is written.

## Seam 2 — a `◯` goal in a regular sequent

    Ψ ⇒g ◯Z

**The rule is forced by `circIn`:**

    Ψ ⇒g Z
    ────────  R◯
    Ψ ⇒g ◯Z

* *Soundness*: the unit, `Z ⊃ ◯Z`.  Unconditional.
* *Invertibility (`INV_R◯`)*: needs `D ▷ (Ψ ⇒g Z) → D ▷ (Ψ ⇒g ◯Z)`,
  i.e. the database row `⟨t, Γ ⇒ Z⟩` must be closable under `circIn`,
  which demands

        t = barren   or   (t = chain W  and  Covers Γ W Z).

  This is **not** free.  It is a strengthening of saturation:

        (DB◯)   if ⟨t, Γ ⇒ Z⟩ ∈ D then some row subsuming ⟨_, Γ ⇒ ◯Z⟩ ∈ D.

  This is the same `Covers` / `KeptChain` retention obligation that the
  LJF◯ campaign met as `CimpAnt` (see `docs/…ljfo-cimpant-terminus`),
  arriving here from the other side.  It is a condition on the
  *database*, not on the rule.
* *Measure*: `seqSize` drops, `unclosed` and `tp` unchanged.  Fine.

## Seam 3 — a `◯` goal in an irregular (focused) sequent

    Ω →g ◯Z          Ω ⊆ Ĝ

Reachable: `R∨ₖ` at `Ω ⇒g C₁ ∨ ◯Z` produces it directly.

Two FRJV rules have this conclusion.

**`axIC` gives a discharge, not a rule.**  Its `Gbu` reading is the
◯-analogue of `evalI_axI`: if `Ω ⊆ vacZone_A(G, Ω^at)` — every member of
`Ω` is classically forced by `Ω`'s own atoms, i.e. `Ω` is *classically
saturated* — and `classForce Ω^at Z = false`, then the database already
refutes the sequent and (BSr1) is violated.  Note this is exactly the
maximal-world condition of the endpoint investigation; the classically
saturated `Ω` is a one-point endpoint.

**`circNotIn` gives the rule, and it releases focus:**

    Ω ⇒g Z              ← REGULAR
    ──────────  R◯ₙᵢ
    Ω →g ◯Z

* *Soundness*: the unit again.
* *Invertibility*: `circNotIn` applied to the regular row, with
  `Θ := Ω`, whose condition `∀X∈Ω, X ∈ Cl(Γ) ∧ X ∈ Ĝ` is supplied
  exactly as in `gbuInv9`; plus the same tag obligation as Seam 2.
* **There is no focus-preserving `R◯ᵢ`.**  It would need
  `Σ;Θ → Z ⟹ Σ;Θ → ◯Z` on the FRJ side, which is unsound: `◯Z` is
  *weaker* than `Z`, so refuting it is harder.  Consistently, no such
  `FRJVi` rule exists.  So focus release is not a design choice.

* **⚠ `R◯ₙᵢ` breaks the measure `Wg`.**  `tp` rises (irregular → regular),
  `unclosed` is unchanged (nothing is added to the left zone — this is
  what makes it different from `R⊃ₙᵢ`, whose drop comes from
  `A ∈ Sf^L(G) ∖ Cl(Ω)`), and `seqSize` sits below `tp`.  Lexicographic
  `⟨unclosed, tp, size⟩` therefore does **not** decrease.

  Reordering does not help: `tp` is needed only for `L⊃`'s left premise
  `Ω →g A` (where the goal `A` may be larger than the goal it replaced),
  and any component placed above `tp` must be non-increasing there —
  which the ◯-degree of the goal is not.

  **This is now settled, and the conjecture recorded here on
  2026-08-29 is REFUTED.**  See `wip/gbu_measure.lean`:

  * `not_wf_stepC` — the extended step relation has a **two-cycle**, for
    every `G`.  With `Γ = ◯Z ⊃ B, Ψ`,

    ```
        Γ →g ◯Z   is a premise of   Γ ⇒g Z      by L⊃ on ◯Z ⊃ B
        Γ ⇒g Z    is a premise of   Γ →g ◯Z     by R◯ₙᵢ
    ```

    so `¬ WellFounded (StepC G)`.  Axiom-free.
  * `no_measure_stepC` — hence **no** measure `m` from sequents into
    **any** well-founded order can decrease along every step.  Not "the
    reordering is hard": impossible.  (The statement is about the step
    relation, which is what Theorem 7 and `step_wf` are about.  A
    measure allowed to consult `D` is not excluded, but neither Lemma 8
    nor Theorem 8's recursion has one.)

  **The measure that does work** carries a store `U` — the implications
  of the current context already focused on — in the state:

      Wg◯(τ, U) = ⟨ |Sf^L(G) ∖ Cl(Ψ)| , Σ_{X∈Ψ} |X| , |Ψ^⊃ ∖ U| , |C| ⟩

  lexicographic, decreasing on all twenty steps (`wgo_step`), whence
  `stepU_wf`.  Two things about it are worth stating.

  * **`tp` disappears.**  In the paper `tp` exists for exactly one step,
    the left premise of `L⊃`, where the goal may grow; `|Ψ^⊃ ∖ U|`
    covers that step instead.  And `tp` cannot be kept: it is precisely
    what `R◯ₙᵢ` increases.
  * **`ctxSize` is new and load-bearing.**  It is what the
    context-shrinking left rules (`L∧`, `L∨`, `L⊃`-right, `L◯`)
    decrease, which is what lets `|Ψ^⊃ ∖ U|` be reset whenever the
    context changes — necessary, because `L∧` can expose implications
    that were not in `Ψ^⊃` before, so the store count is not monotone on
    its own.

  `stepC_of_stepU` certifies that this is bookkeeping and not a
  different calculus: every `StepU` step erases to a `StepC` step.  The
  only thing the store does is forbid re-focusing an implication already
  focused on at the same context — exactly the move the two-cycle
  repeats.

  **Consequence for the search.**  When Lemma 11's witness `A ⊃ B` is
  already in `U`, `BSearch` must not recurse on the left premise; it
  reuses the derivation of `Ω →g A` built when the implication was
  banked (the context is unchanged along that whole stratum, since
  `ctxSize` is constant there) and recurses only on the right premise,
  whose `ctxSize` strictly drops.  So `U` should be a store of
  DERIVATIONS, not just of formulas.  Completeness of the strategy
  survives: Lemma 11 is used unchanged.

---

## What to do next, in order

1. ~~**Settle the measure** (Seam 3).~~  **DONE 2026-08-29**, see above:
   the naive measure is impossible (`no_measure_stepC`) and the
   store-carrying `Wg◯` works (`stepU_wf`).  What remains is to rebuild
   `SearchOk` over `SeqU` and thread the derivation store.
2. **Test Seam 1's prime-goal gap** against the known residue before
   adding rules.  If the 6-cell residue lands there, the extension is
   *not* a matter of adding rules and the calculus needs repair.
3. **Then** add `L◯`, `R◯`, `R◯ₙᵢ` and re-prove Lemmas 11/12 over
   `joinAtP` / `joinOrP`, in that order, reusing every case of `search`
   verbatim (the ◯-free cases must still compile — that is the
   template-extension discipline).
4. The tag obligation (DB◯) is shared by Seams 2 and 3 and is a
   condition on the database; it is the same object as the LJF◯
   campaign's retention condition, and should be stated once.

## Status of the IPC layer

| result | source | Lean | pins |
|---|---|---|---|
| Lemma 7 (soundness) | 3122 | `seqValid_of_GbuR/I` | `[propext, Quot.sound]` |
| Theorem 6 | 3107 | `pll_of_provableGbu`, `ipl_of_provableGbu` | ditto |
| Lemma 8 (weight) | 3200 | `wg_step` | ditto |
| Theorem 7 (termination) | 3210 | `step_wf`, `wgLt_wf` | ditto |
| Lemma 9 (invertibility, 10 clauses) | 3300 | `gbuInv1`–`gbuInv10` | ditto |
| Lemma 11 (`At` success) | 4160 | `gbuSuccAt` | ditto |
| Lemma 12 (`∨` success) | 4193 | `gbuSuccOr` | ditto |
| Theorem 8 (`BSearch`) | 4215 | `search` | ditto |
| Theorem 9 (duality) | 4320 | `gbu_frj_duality` | ditto |
| Theorem 10 (completeness) | 4353 | `provableV_of_not_pll`, `provableGbu_of_pll` | ditto |

Open on the IPC layer: the **finite** saturated database of §4 with a
decidable `▷` (stage 4 of the adoption).  `saturated_fderivable` shows
saturation itself is not the obstruction — the set of all derivable
sequents is saturated — so what is missing is finiteness plus
decidability, i.e. the forward-closure procedure, not a theorem.
