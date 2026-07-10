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
