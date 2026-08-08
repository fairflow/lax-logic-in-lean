# PROGRESS — the polarised UI campaign

2026-08-08 · live log, updated in place as work continues. The previous
campaign's log is `PROGRESS.md` (§§1–90, shelved 2026-08-07); this file is the
new campaign only. Companion documents: `docs/lax-logic-interpolation-handoff.md`
(the programme), `docs/lax-interpolation-candidates-strategy.md` (the candidate
method), `docs/ui-two-routes.md` (the routes and their state).

Verification: `lake build` (the focused stack is on the library root).

---

## §1. What is built (all sorry-free, on the root, 2026-08-08 morning)

| file | content | audit |
|---|---|---|
| `LaxLogic/PLLJudgmental.lean` | two-judgment PLL, sound + complete, `equiv_nd`, `equiv_lax` | none at all |
| `LaxLogic/PLLPolar.lean` | polarised syntax, `circ : Pos → Neg`, roundtrip, `phase` | `[propext]` |
| `LaxLogic/PLLFocused.lean` | focused calculus, four judgments with the `JD` flag; **soundness** | clean |
| `LaxLogic/PLLCandidate.lean` | `Cand p` — the 13 closure clauses read off the rules | (definition) |

Findings along the way, each in its file's header or commit:

* `CircInvert` is free — `circE` with the identity continuation (monad law).
* At `.lax`, ⊃-right would be the converse of K (refuted `wip/converseK.lean`);
  `impR`/`andR` are `.tru`-only. Found by the soundness proof, not inspection.
* `circL` is the only rule that reads the flag — the entanglement is confined.
* Candidates must be indexed over **inversion sequents**: over stable sequents
  the join clause is not even statable (no `⊔` on `List Neg`).
* The contraction-count is `cl_circL`, guarded, `.lax`-only — the strategy
  document's "cheap early test" comes out positive.
* The load sits on **`cl_orL`**, the one clause `∨` contributes. Third
  independent arrival at ∨ (after the ∃p/∀p split and the ∨-free finiteness).

## §2. The attack on `cl_orL` — plan (2026-08-08, midday)

The candidate semantics to try first, because it is the one the ∃p argument
already suggests: for a fixed `p`-free "budget" of hypotheses,

    C_θ Γ Ω j N  :=  the p-free content of (Γ; Ω ⊢ N at j) is entailed by θ

made precise as: every p-free consequence of the sequent is a consequence of θ.
The join clause for C_θ is then exactly the statement that the p-free
consequences of a disjunction are the intersection of the branches' p-free
consequences — which is TRUE and easy (∨-left). The place it can fail is not
the join itself but **extremality**: whether among the satisfying θ there is a
least one (the ∃p of the sequent), and that is the directedness question of
`docs/ui-two-routes.md` §1 again, now in candidate form.

So the attack decomposes:

1. define the p-free consequence relation of an inversion sequent;
2. prove the 7 unconditional clauses for `C_θ` (expect: routine, ∨-left included);
3. prove the 6 guarded clauses (expect: `cl_circL` needs the lax phase — the
   place to watch);
4. extremality: the least θ. This is where directedness lives and where the
   outcome (theorem vs impossibility) will be decided.

Status: starting.

---

*(append below as progress happens; do not rewrite above)*

## §3. The join clause FELL — all thirteen clauses hold (2026-08-08, afternoon)

`LaxLogic/PLLCandOr.lean`, on the root, sorry-free, `lake build` 8668 green.

**The result.** For any budget `θ`, the consequence candidate

    Cθ θ Γ Ω j N := Nonempty (LaxND (θ :: ⌜Γ⌝ ++ ⌜Ω⌝) (wrap j ⌜N⌝))

satisfies **all thirteen closure clauses**, assembled as `candOf p θ : Cand p`.
In particular:

* `cθ_orL` — **the join clause, the one the difficulty was traced to, is
  ∨-elimination**. A theorem, `[p,C,Q]`.
* `cθ_circL` — the contraction clause holds by `laxElim` **with the
  ◯-hypothesis retained**: `Q` enters `Ω` while `◯Q` stays in `Γ`. The
  retention discipline of the G4c repairs reappears as a fact about the
  candidate, not a rule design. Choice-free `[p,Q]`.
* `cθ_strengthen` — budgets are closed under strengthening, `[propext]` only.

**Two corrections found by discharging** (the strategy document's discipline
working as intended): `cl_impL` and `cl_andL` as first extracted were
trivially satisfiable — the continuation had lost its new hypothesis. Fixed in
`PLLCandidate.lean` (`N :: Γ` resp. `M :: Γ` in the continuation; `cl_andL'`
added for the second projection).

**What this means.** Candidacy is CHEAP — every budget is a candidate, and
p-freeness was not even needed for the closure clauses. So the closure clauses
do NOT carry the difficulty of uniform interpolation; the entire content has
moved into **extremality**, stated precisely as `ExtremalBudget p Γ Ω j N`:

    a p-free θ with Cθ θ (the sequent), entailed by every p-free θ' whose
    candidate also accepts the sequent — the WEAKEST p-free budget.

Uniform interpolation IS the inhabitation of `ExtremalBudget` for every
sequent. This is the ∃p/∀p asymmetry of `docs/ui-two-routes.md` §1, reached a
second way; the directedness criterion is what inhabitation will need.

**Assessment, plainly.** The candidate method did what its document promised —
each mis-stated clause was caught by attempting its discharge, and the load was
localised — but the localisation's lesson is that closure was never the hard
part for THIS candidate family. The hard part is extremality, and for that the
finite ∨-free fragment (`neg_exactly_four`, the eight-element algebra) is the
natural place to try inhabitation first: at ZERO variables `ExtremalBudget`
should be computable outright.

Next: inhabit `ExtremalBudget` in the closed fragment (p not occurring at
all — the degenerate sanity case), then at one variable over the ∨-free
fragment, where L_p is finite and the candidate set can be enumerated.

## §4. THE CONVERGENCE THEOREM — extremality IS ∀p, machine-checked (2026-08-08)

`extremal_iff_forallp` + `cθ_iff_entails` (`PLLCandOr.lean`, pinned clean):
acceptance curries — `Cθ θ S ↔ θ ⊢ ⌜S⌝` — so the extremal budget of a sequent
is precisely **the greatest p-free formula entailing the sequent formula**,
i.e. the propositional quantifier **∀p ⌜S⌝**. The candidate route, run to
completion, lands exactly on the object the algebraic route (ui-two-routes §1)
identified as the hard half. ∃p never appears: the closure clauses absorbed it.
Also `extremalOfPFree`: when ⌜S⌝ is itself p-free it is its own extremal
budget (minimality not even needing the competitor's p-freeness).

**The reduction, now proved rather than suspected.** UI for PLL ⟺ for every
sequent formula φ, the set T = {ψ p-free : ψ ⊢ φ} has a greatest element.
T is an IDEAL — downward closed, and ∨-closed (ψ₁ ⊢ φ, ψ₂ ⊢ φ ⟹ ψ₁∨ψ₂ ⊢ φ).
So the question is PRINCIPALITY of these ideals, and failure requires an
infinite strictly ascending chain of p-free formulas below φ.

**The refutation hunt this licenses.** At ONE variable, "p-free" = CLOSED, and
the repository already has a mechanised infinite strictly ascending chain in
RN(◯,{}): the boxed odd rungs `chainF k = ◯t(2k+1)`, `chain_step_strict`
(wip/chainStrict.lean, 2026-08-02). So UI for PLL FAILS iff some one-variable
φ(p) has its closed lower ideal generated by such a chain — a φ that every
`chainF k` entails, while every closed θ ⊢ φ sits below some `chainF k`.
That is a concrete, finite-to-state hunt, and it is exactly where Matthew's
1-pv instinct pointed. In IPC Pitts guarantees every such ideal is principal;
◯ is the only new ingredient, and the chain that could break principality is
made of ◯'s.

Next: the hunt for that φ — or the proof that no such φ exists, which would be
the 1-pv base case of UI. Either outcome is the paper.
