# The uniformity endgame: from height-fuel to Γ-only fuel

*Status map written 2026-07-10 evening, after P4a landed.  This is the
design record for the final layer of the uniform-interpolation
mechanisation: what is proved, what remains, and the two candidate
routes for the last step, with the failure analysis that selects
between them.*

## What is proved (all in the build graph, audits pinned)

| Layer | Statement | File |
|---|---|---|
| Quantifiers v2 | `interE p fuel Γ`, `interA p fuel Γ C` — Pitts/Iemhoff/UIML clause tables adapted to retention | `PLLG4UI.lean` |
| p-freeness | `p ∉ atoms (interE/interA …)` | `PLLG4UI.lean` |
| E1/A1 | `Γ ⊢ interE`, `interA, Γ ⊢ C` (every fuel) | `PLLG4UI.lean` |
| Fuel monotonicity | `interE_{f+1} ⊢ interE_f`, `interA_f ⊢ interA_{f+1}` + multi-step | `PLLG4UI.lean` |
| **Adequacy (P4a)** | for height-`n` derivations of `Γ ∪ Δ ⊢ C`, Δ p-free, any `fuel > n`: `(p∉C → interE, Δ ⊢ C) ∧ (interE, Δ ⊢ interA)` | `PLLG4UIAdq.lean` |
| Set-congruence | set-equal contexts give ⊣⊢ quantifiers | `PLLG4UIStab.lean` |
| Lax fixpoint lemma | `◯((α ∨ ◯(α∧β)) ∧ β) ⊣⊢ ◯(α∧β)` — pure monad, no Löb | `PLLG4UIStab.lean` |

The missing layer is **uniformity**: the packaged interpolant must sit
at a fuel computed from Γ (resp. Γ, C) alone, while P4a's fuel grows
with the derivation.  Equivalently: the *stabilization* directions

    SE: interE p H(Γ) Γ ⊢ interE p f Γ          (f ≥ H(Γ))
    SA: interA p f Γ C ⊢ interA p H(Γ) Γ C       (f ≥ H(Γ), modulo an
                                                  interE-ambient)

with `H(Γ) := defect(Γ) + O(1)`, `defect` = space formulas not yet in
the context set (the decider's own budget).

## The E-side closes; the analysis

SE has a clean proof by the **whole-context strategy**: derive each
clause of `interE_{f+1}` from the *entire* `interE_H` (not from its
corresponding clause):

* grown-context clauses — project `interE_H`'s own clause one level
  down, then compose fuel-monotonicity with the defect-descent
  induction hypothesis (strictly smaller defect);
* same-set clauses — set-congruence collapses them onto the state
  itself, closed by the inner induction on `f`;
* **guarded clauses need no guard analysis at all**: an implication
  whose consequent is derivable from the ambient conjunction is
  derivable outright (weakening) — and the consequent always is, by
  the two bullets above.  The ◯-clauses close the same way through
  `laxR`/`box_mono`.

## The A-side wall: the offset cascade

SA resists the same strategy.  Mapping a source disjunct of
`interA_f` onto the target disjunct of `interA_H` requires rebuilding
the target's **guard components** `interE_{H-1}(Γ') ⇢ interA_{H-1}(Γ', G)`.
For *grown* Γ′ the defect-descent pays as always.  For *same-set* Γ′
the required component sits at level `H−1` — **one below the
threshold** — and every attempt to lower a level-`f` fact to level
`H−1` regenerates the same demand one level lower: an off-by-one
cascade that terminates only when the state descends (defect grows),
which same-set positions by definition never do.  Three session-hours
of invariant surgery (target-level quantification, threshold shifts
`H+1`, `H+2`, mono-first detours, adequacy sandwiches) all reproduce
the cascade; we record this as strong evidence that **SA is not
provable by disjunct-to-disjunct mapping over the v2 definition**, and
that this is the precise shadow of the termination failure that broke
Iemhoff's original proof: the same-set guard is the reset-without-
growth case wearing a different hat.

## The two closing routes

**Route T (truncation — recommended, the GL/UIML playbook).**  Change
the definition once more (v3): make the quantifier recursion
*well-founded* on ⟨defect, goal-weight⟩ by omitting same-set clause
recursions (retention makes the omitted premise the conclusion's own
sequent — the adequacy proof already skips those steps without
touching any clause, so P4a transfers almost verbatim), and replacing
the one genuinely self-referential piece — the ◯-goal disjunct
`◯(E ⇢ A(Γ ⇒ ◯D))` — by its **one-step-unfolded truncation**
`◯(E ⇢ ⋁(other disjuncts))`, exactly Bílková's `N`-device.  Fuel
disappears entirely; uniformity is definitional.  New obligations:
(a) soundness/p-freeness/adequacy re-runs (mechanical; the P4a case
analysis carries over, with the Δ-side `laxL` commute now consuming
the N-disjunct); (b) the **N-redundancy lemma** — the truncated
disjunct entails the disjunction of the others in the consumers'
context — whose engine is the lax fixpoint lemma just proved
(the collapse is monad multiplication; GL needed the 4-axiom).
This is the identified genuinely-novel lemma; nothing like it is in
the literature for lax logic.

**Route S (cascade-closing, kept as fallback).**  Prove SA directly by
finding an invariant that breaks the off-by-one — e.g. a vector-valued
statement over all goals at a state with a Ruitenburg-style
periodicity argument.  Empirics support it (machine-verified
stabilization at fuel ≈ 3 on every tested instance, both quantifiers,
through fuel 8), but the only known proof technologies are open
research (Litak's Open Problem 1 is the substitution cousin for PLL).

## Also true and worth stating in the paper

* P4a alone already yields **ordinary Craig-style interpolation
  statements per instance** and a *per-derivation* uniform
  interpolant; only the single-formula-for-all-consequences form
  awaits the truncation step.
* The height-inclusive collapse (`n < fuel` is the entire adequacy
  invariant) is a reusable observation for any retention calculus:
  cumulative contexts absorb what termination orders were paying for.
* Empirical stabilization data (probe files in the session scratchpad,
  verified by the kernel decider): every instance stabilizes by fuel 3;
  the movers grow syntactically forever while staying ⊣⊢-constant —
  any mechanisation of Route S must live in the Lindenbaum quotient.

## Route T, second design pass (2026-07-11): the jump system

Working the v3 definition against the rules exposed one more knot the
first pass had underestimated: `impLLax`'s first premise (`Γ ⊢ A` with
`◯A⊃B ∈ Γ` retained) keeps the context **identical** and only jumps
the goal — the retention repair transfers the very payment that made
Iemhoff's recursion terminate.  The GL/iSL mechanisations never face
this: their modal premises always shrink the context weight.  What
falls out:

* **Empirical validation first** (session probes; algebraic
  differencing over Heyting-algebras-with-a-nucleus — sound for PLL,
  linear-time on megaformula values — plus the kernel decider on small
  instances): the *omission law* (same-set clauses dropped) and the
  *N-truncation* match the stabilized v2 values; a jump **budget**
  `b` stabilizes empirically by `b ≈ 2–3`.  The *bare law*
  (`◯(E⇢Z) ⊣⊢ ◯Z` under ambient `E`) validated on most of the battery
  but **flagged a divergence on the gap-theorem context**, which
  prompted the v3.1 repair: keep v2's guarded shapes verbatim and
  make every same-context reference — `E` and `A` alike — pay the
  budget.  **Resolution (later the same night):** the flag was a
  *comparison* artifact — `E`-values descend pointwise toward the
  fixpoint as fuel grows (fuel-mono direction), and v2 simply had not
  converged by fuel 4–5 on that context: the fuel-5→6 step dropped by
  exactly the 40 points separating it from v3.1, while v3.1 was
  already budget-stable at `b = 2`.  So v3.1 computes the limit
  directly.  The guarded v3.1 shapes are kept regardless: the
  adequacy case-map consumes guarded pairs (the IHs deliver exactly
  that shape), and the design principle stands on its own — only
  congruence-grade equivalences may be folded into a quantifier
  definition; ambient-relative ones (the bare law included) belong to
  consumption sites.  Budget-annotation is congruence-grade once
  absorption holds, so it is safe in any polarity.
* **The consumer-side bookkeeping cannot mirror the budget.**  A
  Δ-side decomposition between two Γ-side jumps changes the consumer
  sequent (so no splicing) without touching the quantifier's
  arguments; cumulative Δ-stages are bounded only by Δ's piece
  closure, which uniformity must not mention.  So a refined
  "chain-credit" judgment does not close the gap by itself: the glue
  has to live at the **value level**.
* **The absorption lemma** (the genuinely novel step, replacing the
  first pass's N-redundancy): for `b` at least the jump-goal count,
  `itpA@(b+1) ⊢ itpA@b` (with `itpE` dually) — one-step budget
  stabilization.  Proof design, validated case-by-case: a lazy
  orL-cascade down the source's jump components, keeping the target
  goal un-introduced; a chain of length `> K` must repeat a jump goal
  (pigeonhole — premise-1 chains keep the context fixed, goals range
  over the space's `≤ K` jump goals); at the repeat, the *spliced*
  target chain (length `a < j`) is introduced instead, and the leaf
  hypothesis `A@(b−j+1)(g)` reaches the target component `A@(b−a)(g)`
  by **budget monotonicity** (`b−j+1 ≤ b−a` — the slack `j−a ≥ 1` is
  exactly what the repeat buys); the skipped coefficients are simply
  never used (∧-decrease as projection).  Budget-mono is the easy
  half; the cascade is the hard half; `lax_fixpoint`/`box_guard`
  handle the ◯-goal self-reference separately.

  Intended Lean statement — **corrected 2026-07-11 morning after
  hand-executing the boxed cases**: the *pure* form
  `[itpA@(b+1)] ⊢ itpA@b` is stronger than anything the adequacy
  landing needs, and its γ-box positions demand an E-glue one budget
  below the band at every crossing — an infinite regress (each route
  tried funnels into the pure descent at ◯-shaped jump goals).  The
  landing always holds the ambient `E(Γ)`, and the correct statement
  is **ambient-relative** (`wip/absorb_base.lean`, threshold
  `kcap S := 2·S.card + 4` overcounting the jump states):

      itp_stab : kcap S < b → ∀ fuel,
        (∀ Γ,   G4c [itpE@(b-1)] (itpE@b)) ∧
        (∀ Γ C, G4c [itpE@b, itpA@b Γ C] (itpA@(b-1) Γ C))

  The E-half needs no extra ambient — E is its own.  With ambient E
  the box barrier dissolves: budget-mono (`E@b ⊢ E@(b−1)`, the easy
  direction) matches any lower guard, `box_guard_collapse` opens the
  guarded box against the ◯-shaped target, and `laxL` re-imports the
  ambient at every box crossing, so the inner value lands *in
  context* — which is exactly what the pigeonhole/splice shortcut
  consumes (at a repeated jump state, `itp_budget_mono_le` lifts the
  in-context low-budget value into the spliced target slot).  The
  cascade auxiliary still carries a seen-state list; fresh states
  descend (orL/andL one level, matching target component
  introduced), repeats stop by the mono-splice.  Grown-context and
  goal-decomposition obligations discharge by the fuel-level IH.
  A pure upper band (`itp_absorb_of_base` over a pure base) is being
  ground in parallel as insurance, but the ambient-relative form is
  the mainline: it is what the adequacy case-map's jump landings
  actually consume (their context is `interE@B, Δ`).
* **Adequacy then transfers P4a-style**: fuel > height exactly as
  before (fuel-mono re-proved for v3), with absorption as the new
  `E_step`-analogue gluing jump landings, and one application of the
  syntactic fuel-indifference lemma (`μ = (defect + b)·(W₀+1) + goal
  weight` strictly decreases on every call) converting "every fuel
  above the height" into the fixed, Γ-only packaged formula.  Fuel
  disappears; uniformity is definitional.

### Adequacy case-map: the landings that differ from P4a

Dry-run of all fifteen rules against the v3 clauses; only these
deviate from the P4a proof text (everything else is verbatim modulo
the extra guard-splits):

* `impR`, same-set antecedent (`C₁ ∈ Γ`): the unguarded `A13`
  disjunct lands from the premise IH through **set-congruence**
  (`itp_congr`, the v2 lemma re-proved for v3 — new obligation).
* `laxR`: the basic ◯-disjunct is bare (`◯(A(Γ,D))`) — lands by
  `laxR` + IH directly; simpler than v2 (no guard-click).
* `laxL`, Δ-side box (goal `◯D`): land the **truncation disjunct**
  `◯(⋁others)` — `laxL` the Δ-box, **cut in the IH**, orL: an
  `others`-disjunct closes by `laxR`+`orAll_intro`, the truncation
  disjunct itself closes by *identity* (the monad-multiplication
  move).  Verified against the rules 2026-07-11.
* `impLImp` at a present piece (`B⊃D ∈ Γ, D ∉ Γ`) and `impLLax`
  Γ-side (the jump cases): premise-1's IH arrives at the top budget;
  **absorption** lowers it into the `b−1` component slot; the E-side
  jump conjunct then fires by MP to unlock `E(B::Γ)` for premise-2's
  IH — the P4a `hfire` pattern with absorption as new glue.
* `impLLaxLax` with Γ-side principal and Δ-side witness: land the
  bare γ-disjunct `◯(A@b'(Γ,◯A))` by `laxL` on the Δ-box + cut-in
  IH₁ (+ absorption) + `laxR`-identity; its E-side twin fires by
  self-witnessing MP as in v2 (verified: bare form still
  self-witnesses, since `A1` supplies premise-1 directly).

Consolidated new-obligation list for the v3 tower: `itp_congr`,
absorption (+ its easy half budget-mono), fuel-mono, `E1`/`A1`,
p-freeness, fuel-indifference (packaging only), piece-closure
instantiation of the space `S` (packaging only; use the linear
piece-closure finset, not `enum`, so the budget cap and the measure
stay small).
