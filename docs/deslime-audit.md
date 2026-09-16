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

*(As written on 2026-08-18, before §8. Superseded in part — see §8.)*

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

---

## 7. `nf` is ours, not the paper's — and the replacement is extensional

*Added 2026-08-18 after Matthew questioned whether `nf` is needed at all.*

**The paper has no normal form.** `frj-corr.tex` line 674: *"Capital Greek
letters `Γ`, `Σ`, … denote **sets of formulas**"*. `normalis|canonical`
occurs **zero** times in its 6 682 lines.

**`nf` is ours**, added by `c78c121` (16 Aug), *"canonical contexts —
`nf`, the piece the conversion was missing"*. Its own message names the
cause:

> …on List it is not, since `++` is neither commutative nor idempotent.
> Nor is there a transport: "same members ⇒ same derivations" is FALSE
> here, **because `Ax^I` pins its own Θ** … so no derivation exists at a
> permuted Θ.

"`Ax^I` pins its own Θ" is green slime, named as the cause. So the chain
is: slime → the Finset→List conversion stalls at Lemma 6.3 → `nf`
invented to force the computed forms to coincide.

### The conversion itself was right, for an independent reason

Finset was ditched because it carries choice, and that stands on its own.
Measured:

| | axioms |
|---|---|
| `List.Mem`, `List.elem`, `List.filter` | **none at all** |
| `List.instDecidableMemOfLawfulBEq` | `[propext]` |
| `FRJ.nf` | `[propext]` |
| `Finset.instUnion`, `Finset.erase`, `Finset.image` | `[propext, Classical.choice, Quot.sound]` |

So: the move to `List` was correct and remains correct. `nf` was the
wrong *way* to do it — a canonical-representative device standing in for
set equality, forced by an encoding defect rather than chosen.

### The replacement

Plain list equality will hit the same wall: Lemma 6.3 splits a given zone
`Θ₁` as `Θ ∪ Λ`, which on Finset was a literal index equality
(`Finset.sdiff_union_of_subset`) and on lists is not. The faithful
replacement is **extensional**:

    (hTh : ∀ x, x ∈ Θ' ↔ x ∈ Θ ++ Λ)      -- instead of  Th' = nf G (…)

which is what "denote sets of formulas" actually says, makes the Θ-split
a membership argument exactly as the paper argues it, leaves `nf` with no
job, and is choice-free by construction (`List.Mem` has no axioms).

**This was impossible while the index was pinned**: an extensional side
condition is useless if the constructor forces a literal `Θ`. Desliming
is precisely what makes it available.

### Scope

`nf` has 116 mentions across eight modules (Saturate 34, Minimal 25,
Basic 16, Step 16, Calculus 8, Fallible 8, Sound 7, Audit 2). A probe
that dropped `nf` from the three irregular rules left `Calculus.lean`
compiling — the change is coherent — and failed at the first downstream
module; the rest were not reached.

Recommended order: convert `Ax^I` alone to the extensional form and
confirm the Θ-split of Lemma 6.3 goes through before touching the rest.
That is the step that would close possibility (2) of §5 — that
completeness holds of a weaker judgment than the paper's.

---

## 8. Done: `nf` deleted, contexts are sets

*2026-08-18, commits `a1361c6`, `495f7c3` and this one, branch
`frj-deslime`.*

§7's plan was carried out in full, and further than planned: **every**
context equation of the irregular judgment is now extensional, not just
`Ax^I`'s.

### The definition

    CtxEq l m  :=  ∀ x, x ∈ l ↔ x ∈ m          notation  `l ≐ m`

Choice-free by construction (`List.Mem` depends on no axioms at all), and
`#print axioms CtxEq` is now pinned in `FRJ/Audit.lean`.

### The rules

| rule | before | after |
|---|---|---|
| `Ax^I` | `Θ' = nf G ((Ĝ_at \ {F}) ++ Ĝ_imp ++ Ĝ_◯)` | `Θ' ≐ …` |
| `∨` | `Σ' = Σ₁ ++ Σ₂`, `Θ' = nf G (Θ₁ ∩ Θ₂)` | `Σ' ≐ …`, `Θ' ≐ Θ₁ ∩ Θ₂` |
| `⊃∈` | premise index `nf G (Θ ++ Λ)`; `A ∈ Cl(nf G (Σ ++ Λ))`; `Σ' = nf G (Σ ++ Λ)`, `Θ' = nf G Θ` | premise index free with `Θ₁ ≐ Θ ++ Λ`; `A ∈ Cl(Σ ++ Λ)`; `Σ' ≐ Σ ++ Λ`, `Θ' ≐ Θ` |
| `Ax^I◯` | `Θ' = vacZoneA G ats` (and `vacZoneA` itself wrapped in `nf`) | `Θ' ≐ vacZoneA G ats`, `nf` wrapper gone |

`FRJ.nf` and its six lemmas (`mem_nf`, `nf_ext`, `nf_idem`, `nf_subset`,
`nf_subset_self`, `mem_nf_of_subset`) are deleted from `FRJ/Basic.lean`.

### A fidelity error `nf` was hiding

`⊃∈`'s side condition in the paper is `A ∈ Cl(Σ ∪ Λ)`. Ours read
`A ∈ Cl(nf G (Σ ∪ Λ))` — strictly stronger, since `nf` throws away
everything outside `Ĝ`. Under `wfI` the two coincide, so nothing was
unsound; but the rule as written was not the paper's. It is now.
`docs/frj-fidelity.md` is corrected accordingly: the `⊃∈` zone split was
filed there as a divergence and is not one.

### The payoff, in the two completeness files

The Θ-split of Lemma 6.3 was, in `FRJ/Minimal.lean` and
`FRJ/Saturate.lean`:

    have hzone : nf G (sdiff w.th Λ ++ Λ) = w.th := by
      conv_rhs => rw [w.thNf]
      refine nf_ext (fun x _ => ?_)
      …
    der := .impInI (by rw [hzone]; exact w.der) cap_sdiff_eq_nil hAclo hC rfl rfl

and is now

    have hzone : w.th ≐ sdiff w.th Λ ++ Λ := …
    der := .impInI w.der hzone cap_sdiff_eq_nil hAclo hC (CtxEq.refl _) (CtxEq.refl _)

— no rewrite, no transport of the premise derivation, and the `thNf`
canonicity field of `IrrWit` deleted along with the twelve obligations
that discharged it.

### The certificate: the transport is a theorem

`c78c121`, which introduced `nf`, recorded that a transport is FALSE for
this family, *"because `Ax^I` pins its own Θ"*. That pinning was the
slime. `FRJ/Calculus.lean` now proves

    transportI : FRJi G Σ Θ C → Σ ≐ Σ' → Θ ≐ Θ' → FRJi G Σ' Θ' C

pinned at `[propext, Quot.sound]`. This is the precise sense in which the
mechanised irregular judgment is the paper's judgment on **sets** of
formulas. It is computational: it rebuilds the derivation rule by rule.

### What was checked

* `lake build FRJ` — 8572 jobs green, 0 sorries;
* `#slime FRJ.FRJr` 0/13, `#slime FRJ.FRJi` 0/8;
* axioms unchanged — `soundness`, `completeness_of_supply`,
  `completeness_of_discrete`, `provable_nn_circ_bot`, `wfI`, `minMod`
  all `[propext, Quot.sound]`, no `Classical.choice`, no `sorryAx`;
* `lean_exe frjsat` rebuilt (it had been left broken by the deslime
  commit `e0b0881`) and re-run: same 45 `pass`/`control-ok` verdicts, the
  single `corner_poisoned_ups` flag still clearing at raised budget, and
  the erasure-transfer attack (E) still 8/8.

### What this does and does not settle

It **closes** the "conservative normalisation" reading of §5 as a
*source of doubt*: there is no normalisation left to be conservative
about, and the judgment is now provably invariant under set-equality of
contexts. It **does not** decide whether FRJ(G) completeness holds — the
remaining two possibilities of §5 (a weaker judgment, or genuine
incompleteness) are untouched, and the engine's verdicts are unchanged,
which is itself evidence that `nf` was not the obstruction.

## 9. The regular judgment too: `transportR`

*2026-08-18, same branch, immediately after §8.*

The nine context equations of `FRJr` — `Ax^R` and the eight join rules —
were converted the same way, from `Γ' = joinCtxAt stab th rhs F` to
`Γ' ≐ joinCtxAt stab th rhs F`. Nothing forced this: no set-splitting
operation acts on a regular context, so `nf` was never implicated there.
It was done for the statement it buys.

Two routes were available for `preR`, whose specification
(`preI_spec`, `preR_root_lbl`) had held with a literal `=`:

* **A**: make `preR` mount the derivation's own `Γ`, as was done for
  `Ax^I◯` in §8. This propagates into ~40 membership sites across the
  eight join lemmas of `FRJ/Sound.lean` and was abandoned.
* **B**: leave `preR` mounting the computed join context and relax
  `preR_root_lbl` to
  `(preR d).lbl (preR d).root ≐ Γ`. Every consumer of the old equation
  was a rewrite in one direction only, so each became one application of
  the equivalence. This is what is in the tree.

The regular transport is then

    transportR : FRJr G t Γ C → Γ ≐ Γ' → FRJr G t Γ' C

at the SAME tag, pinned at `[propext, Quot.sound]`. Its two interesting
cases are the two rules whose side condition reads the context:

* `⊃∈` carries `A ∈ Cl(Γ)`, which travels by the existing
  `clo_mono : Γ ⊆ Δ → Clo Γ A → Clo Δ A`;
* `◯∈` carries the pledge `Covers Γ W Z`, which needed a new lemma

      covers_mono : Γ ⊆ Δ → Covers Γ W Z → Covers Δ W Z

  (induction on the pledge; the only context-dependent clause is `imp`,
  discharged by `clo_mono`). `covers_mono` depends on no axioms at all,
  and is pinned as such.

Together with §8's `transportI`, both halves of the judgment are now
invariant under set-equality of contexts, and that invariance is a
machine-checked theorem rather than a design intention.

### What was checked, again

* `lake build FRJ` — 8572 jobs green, 0 sorries; `LaxLogic`, `Meta`,
  `Reject`, `FRJO` green;
* `#print axioms transportR` `[propext, Quot.sound]`, `covers_mono`
  axiom-free, both `#guard_msgs`-pinned in `FRJ/Audit.lean`; the headline
  pins unchanged;
* `lean_exe frjsat` rebuilt and re-run: 40 `pass`, 5 `control-ok`, 0
  `FAIL`, the single `corner_poisoned_ups` flag again clearing at raised
  budget, erasure-transfer attack (E) again 8/8 — verdict-for-verdict
  identical to §8's run.
