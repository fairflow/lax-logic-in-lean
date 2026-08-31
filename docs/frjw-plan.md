# FRJW — the calculus, and the campaign

**Status:** plan, awaiting review. No Lean written against it yet.
**Branch:** `frjw-dev`. **Predecessor:** FRJV (`FRJ/CalculusV.lean`).

Terminology: an object of `FRJWr` / `FRJWi` is a **disproof** (regular /
irregular). "Proof" is reserved for the provability calculi — Gbu◯,
LaxND, G4c, SC.

---

## 1. What FRJW is

FRJW is FRJV with one rule added and one deleted.

**Added — `Lift` (working name `(R^bar)`).** A regular disproof becomes
an irregular one over any retained `Ĝ`-context inside the closure of its
own context:

        Γ ⇒ C          Θ ⊆ Ĝ,   Θ ⊆ Cl(Γ)
    ─────────────────────────────────────────  (Lift)
                   ∅ ; Θ → C

As a constructor:

```lean
| lift {t : Tag} {Γ Θ : List Form} {C : Form}
    (d : FRJWr G t Γ C)
    (hΘ : ∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) :
    FRJWi G [] Θ C
```

**Deleted — `⊃∉` (`impNotIn`).** It is `Lift` composed with `⊃∈`:
from `d : Γ ⇒ B` and `Clo Γ A`, `⊃∈` gives `Γ ⇒ A ⊃ B` with no side
condition, and `Lift` gives `∅ ; Θ → A ⊃ B`. `⊃∉`'s extra condition
`¬ Cl(Θ) ∋ A` is not needed.

**Kept — `◯∉` (`circNotIn`).** Not redundant: its premise is a regular
disproof of `Z`, not of `◯Z`, so it climbs the modality and `Lift` does
not. Every other FRJV rule is unchanged.

---

## 2. Why `Lift` is the right addition

Three facts, all machine-checked, `[propext, Quot.sound]`.

**(a) The irregular duality has a hole.** For every `G`, `Z`, `Σ`, `Θ`,
FRJV has no irregular disproof of `◯(◯Z ⊃ Z)`
(`FRJ.V.WCounter.no_irregular_circ_imp_self`): only `◯∉` and `Ax^I◯`
conclude a `◯` goal; `◯∉` needs a cleanly tagged regular disproof of
`◯Z ⊃ Z`, forbidden by `not_clean_imp_self`, and `Ax^I◯` needs
`classForce ats (◯Z ⊃ Z) = false`, impossible because `◯` is transparent
to `classForce` and the body is `¬x ∨ x`.

**(b) Gbu◯ cannot fill it, and must not.** `∅ →g ◯(◯p ⊃ p)` is not
derivable (`FRJ.Gbu.not_gbuIC_Gcc`) — `soundIC` gives the irregular
judgment the same reading as the regular one, `∀w. w ⊩ Ψ → w ⊩ C`, and
`◯(◯p ⊃ p)` is refuted by the model `GccWitness` extracts.

**(c) A regular disproof exists but cannot be used.** `provableV_Gcc`
disproves `◯(◯p ⊃ p)` by the barren `⋈^◯` join. It is unusable where an
irregular disproof is required, because the two judgments assert
different things:

* a *regular* disproof is existential — `modR d` builds one model and
  `lemma39R` says `C` fails at its root;
* an *irregular* disproof is a schema — by `lemma39I`, `C` fails at ANY
  infallible world `w` of ANY premodel with `lbl w ⊆ Cl(Σ ++ Θ)`, the
  disproof's regular components grafted above `w`, and `w ⊩ Σ ∩ sfm C`.

The joins `⋈^At`, `⋈^∨`, `⋈^◯` build a FRESH root and need their premise
formulas to fail *there* — at a world the join built. Only the schema
reading gives that, which is why join premises are irregular.

`Lift` is exactly the bridge from (c) to the schema, and it is sound
because forcing is monotone: the component's root sits above `w` and
refutes `C`, so `w` refutes `C`.

---

## 3. What is already checked

| fact | name | file |
|---|---|---|
| `Lift`'s `lemma39I` clause | `not_force_of_rootAbove` | `wip/rbar.lean` |
| no irregular FRJV disproof of `◯(◯Z ⊃ Z)` | `no_irregular_circ_imp_self` | `wip/gbu_weakening.lean` |
| `∅ →g ◯(◯p ⊃ p)` not Gbu◯-provable | `not_gbuIC_Gcc` | `wip/gbu_search_circ.lean` |
| regular FRJV disproof of `◯(◯p ⊃ p)` | `provableV_Gcc` | `wip/gbu_search_circ.lean` |
| its extracted countermodel, dumped | `dumpModel` / `countermodel_Gcc` | `wip/gbu_search_circ.lean` |

`not_force_of_rootAbove` was negative-tested: the same one-line proof does NOT
typecheck for a tagless `◯∉`, so the gate discriminates.

---

## 4. The task in hand

**Before the first build**, in a fresh Claude worktree, clone the Lake cache
from the repository root — it is an APFS clone, so it is instant, and without
it the first build recompiles the whole development:

```
cp -Rc <repo-root>/.lake .lake
```

The repo root is `lax-logic-in-lean`, not `LaxLogic/`. Push with
`scripts/campaign-push.sh frjw-dev`; never push the local `claude/…`
worktree branch name.

Then, in order. Each stage ends when its deliverable is pushed.

**W1 — transcribe.** `FRJ/CalculusW.lean`: copy `FRJVr`/`FRJVi`, add
`lift`, delete `impNotIn`. `#slime` must report 0; `#rules` must show one
constructor per rule.

**W2 — conservativity.** Every FRJV disproof is an FRJW disproof:

    FRJVr G t Γ C → FRJWr G t Γ C        FRJVi G Σ Θ C → FRJWi G Σ Θ C

The only non-trivial case is `impNotIn`, reconstructed as `lift (impIn d hA _) hTh`.
Do this BEFORE soundness — it is what licenses reusing the FRJV corpus.

**W3 — soundness.** Port `lemma39R` / `lemma39I` with `RegIdx (lift d) := Unit`,
`preI (lift d) _ := preR d`. The new `lemma39I` case is `not_force_of_rootAbove`,
already proved. **The real obligation is not this case but the joins':**
each join must still discharge

    RootAbove P hP w (preI (prem j) i) …

for components now supplied by `lift`. `lift`'s `hΘ` is verbatim `⊃∉`'s
`hTh`, so the interface is unchanged — but that is an argument, not a
proof, and W3 is where it gets checked.

**W4 — the duality gap closes.** Show `∅ ; ∅ → ◯(◯p ⊃ p)` is an FRJW
disproof (`lift GccWitness.2 (by simp)`), i.e. the (a)/(b) mismatch is
gone. This is the test that the whole exercise was for.

**W5 — the two invertibility clauses.** Both should now be immediate:

    (∨-inv)  D ▷ (Ω ⇒g C₁) ∧ D ▷ (Ω ⇒g C₂)  ⟹  D ▷ (Ω ⇒g C₁ ∨ C₂)
    (★)      D ▷ (Ω ⇒g Z)  ⟹  D ▷ (Ω ⇒g ◯Z)      (Ω ⊆ Ĝ_at ∪ Ĝ_imp, Υ dead)

`(∨-inv)` by `⋈^∨` on two `lift` premises; `(★)` by `lift` then
`gbuSuccCirc`. That these two fall out is the coherence check on the
design: they were the search's two unmet needs, and neither was part of
the motivation for `Lift`.

**W6 — completeness.** Rebuild the Gbu◯ search over FRJW. Not before W5.

---

## 5. Screen before you build

Per `METHOD.md`, statements get an extensional attack before a proof is
scoped. For FRJW the two live risks are:

1. **Termination of search, not soundness.** `Lift` makes `EvalI` at
   least as strong as `EvalR` over `Ĝ`-contexts, so the `∨` and `◯`
   branches take the join route far more often. Re-check the `Wg`
   measure against the new traffic before W6.
2. **`RootAbove` at the joins** (W3). Build the smallest join over a
   `lift` premise by hand and watch it typecheck, before porting all
   eight join constructors.

Then the standard four directions, in order: corpus replay (the ρ-sweep
harness `lake exe frjvrun sweep`, ported), boundary cells (`⊥`, empty
contexts, `Θ = ∅`, `Γ = ∅`), frontier extension, branch coverage.

---

## 6. Not in scope

`searchO` and its two supplies `BigAnte` / `CleanReg` are RETIRED, not
inherited: `residues_unsatisfiable` shows the pair is contradictory at
`◯(◯p ⊃ p)`, so the theorem is vacuous for any modal `G`. Do not attempt
to discharge either. The FRJW search of W6 is built fresh, on the
invariant `¬ D ▷ (Ω ⇒g C)` that W5's two clauses make propagable.

---

## Fidelity / divergence log

FRJW is a NEW calculus: fresh proofs of everything, soundness included;
no FRJV theorem migrates by renaming or aliasing; FRJV files stay
byte-for-byte untouched.  A later merge back into FRJV would produce a
third name (FRJ◯).  This log records divergence from **FRJV** (the
predecessor); divergence from the paper is FRJV's own log
(`docs/refat-plan.md`, V1–V5), which carries over unchanged.

| # | Divergence from FRJV | Where | Why |
|---|---|---|---|
| W1 | `lift` added to the irregular family: `Γ ⇒ C` with `Θ ⊆ Ĝ`, `Θ ⊆ Cl(Γ)` yields `∅ ; Θ → C` | CalculusW | ours; the irregular duality hole at `◯(◯Z ⊃ Z)` (§2) |
| W2 | `⊃∉` (`impNotIn`) deleted; reconstructed as `lift (impIn d hA hgoal) hTh` — its extra condition `¬ Cl(Θ) ∋ A` is dropped, not reconstructed | CalculusW | redundant given `lift` (§1) |
| W3 | `DisprovableW` replaces the `ProvableV`-pattern name for `∃ t Γ, Nonempty (FRJWr G t Γ G)` | CalculusW | terminology: an FRJW object is a DISPROOF; `ProvableV G` read the wrong way round |
| W4 | everything else transcribed verbatim — machine-diffed: the `#rules` tables of the two families are identical modulo the V→W rename outside the `⊃∉`/`lift` swap (2026-08-31) | CalculusW | fidelity gate |

Stage-W1 gates in `FRJ/CalculusW.lean`: `#slime` pinned by
`#guard_msgs` at 0 computed indices for both families (13 + 8
constructors); the pin was watched to fail on an injected mismatch
before shipping.  `#rules` output inspected and diffed as above.
