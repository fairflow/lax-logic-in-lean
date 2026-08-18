# Proof-complexity audit: FRJ before and after desliming

*Branch `frj-deslime`, 2026-08-18. Baseline `bc5183c` (= `frj-lax`), after
`e0b0881`. Both revisions build green, sorry-free, with identical
`#guard_msgs`-pinned axioms.*

The transformation: each of the 13 slimed constructors had its computed
index replaced by a fresh variable plus an equation field.

    | impInI … (d : FRJi G St (nf G (Th ++ Lam)) B) … :
        FRJi G (nf G (St ++ Lam)) (nf G Th) (.imp A B)        -- before

    | impInI … (d : FRJi G St (nf G (Th ++ Lam)) B) …
        {St' Th' : List Form}
        (hSt : St' = nf G (St ++ Lam)) (hTh : Th' = nf G Th) :
        FRJi G St' Th' (.imp A B)                             -- after

`#slime` now reports **0 of 13** and **0 of 8**, against 9 and 4 before.

## 1. Overall gain: none, and that is the expected answer

| | before | after |
|---|---|---|
| `FRJ/Calculus.lean` | 592 lines | 605 lines |
| every other module | — | **unchanged in size** |
| case analyses, transports, tactic lines | — | **unchanged** |
| clean rebuild, per module | 11–13 s | 11–14 s |
| axioms | `[propext, Quot.sound]` | identical |

Net: **+13 lines, no measurable time difference.** Desliming was
behaviour-preserving by construction: 283 equation arguments were
introduced across six modules, and every one is discharged by `rfl`,
which unifies the fresh variable with the computed context and restores
exactly the old definitional behaviour.

So the deslime bought no simplification. What it bought is that `cases`
now works on the family at all without the index being pinned — and that
is a precondition for simplification, not simplification itself.

## 2. Where the theory was paying for slime

The real measurement. In a pattern, `rfl` re-specialises the index to the
computed context — the old slimed behaviour. `_` leaves it a variable.
**Whatever still builds under `_` never needed the computed context.**

| module | pattern equations | still needed | never needed |
|---|---|---|---|
| **`Extract.lean`** | 55 | **9** | **46 (84%)** |
| `Step.lean` | 13 | ~13 | 0 |
| `Sound.lean` | 26 | ~26 | 0 |
| `Minimal.lean`, `Fallible.lean` | 0 | — | — |
| `Saturate.lean` | 1 | 1 | 0 |

(`Step` and `Sound` are reported coarsely: generalising all of them at
once produced 25 errors in each, so a blanket generalisation fails and
the clauses are load-bearing. `Extract` was bisected exactly.)

**Extract's nine survivors are all in one theorem.** Every other clause
generalised cleanly. The theorem is

    preR_root_lbl : (preR d).lbl (preR d).root = Γ

— literally *"the label of the constructed model's root is the sequent's
context"*. That is the one statement in the module whose content **is**
the computed context, and it needs the equation in all nine of its
clauses. Everything else — `RegIdx`, `regIdxElems`, `regIdxComplete`,
`preI`, `PremIdx`, `premIdxElems`, the `DecidableEq` instances, the
closure lemmas — carried the computed context for nothing across 46
clauses.

## 3. Which parts gained most

The split is principled, not accidental:

* **Model construction gained most.** `Extract.lean` builds structure
  *indexed by* the derivation. It does not care what the context is, only
  that the derivation has one — so 84% of its slime coupling was pure
  cost, imposed by the encoding rather than the mathematics.
* **Soundness and the step relation gained least.** `Sound.lean` proves
  what the constructed model *forces*, and `Step.lean` proves
  `Γ ⊆ Ĝ` and the `Lhs`-closure lemmas. Both reason about contexts, so
  resolving the index is doing real work. Their equations stay.

That is a useful diagnostic in its own right: a module whose equations
all generalise was never about the indices, and its lemmas can now be
stated more generally than the slimed encoding permitted.

## 4. Duplication the deslime exposed but did not remove

`Sound.lean` contains **130 term applications** of derivation
constructors — the same derivation, e.g.

    FRJr.joinAt prem hJ1 hJ2 hcirc hF hFnot hg

written out in full repeatedly inside statements, four times in a single
lemma. Desliming made this visible by requiring ` rfl` on every one. The
duplication is pre-existing and independent of slime; abbreviating it is
a separate, obvious cleanup.

## 5. What did NOT change: the fidelity question

Desliming moved `nf` out of the indices. It did **not** remove it: the
constructors still carry `hTh : Th' = nf G Th`, so only normalised
contexts are derivable, and `FRJi G Σ Θ C` is the same relation it was.

**The completeness question is therefore untouched.** The three
possibilities in `docs/slime-census.md` §"What this does and does not put
in doubt" — conservative normalisation, a weaker judgment, or genuine
incompleteness — all remain open. What has changed is that the family can
now be case-analysed without fighting the unifier, which is what
investigating them requires.

## 6. Method note

The blanket `rfl` pass is the right first move: it gets to green fast and
cannot change what is proved. The generalisation pass (`rfl` → `_`, keep
what builds) is a separate, cheap, and highly informative second move —
it is what turns "the slime is gone" into a measurement of what the slime
was costing. Run both, in that order, and record the split.
