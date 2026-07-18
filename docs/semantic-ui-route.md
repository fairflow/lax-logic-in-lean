# The semantic route to uniform interpolation for PLL

2026-07-18 · companion to `wip/semantic_ui.lean` (compiles; exactly two
`sorry`s = the two named open targets). Status words used precisely:
PROVED = machine-checked in that file today; OPEN = stated with `sorry`;
observations without Lean anchors are marked as such.

## 1. What was proved today, and what it compresses the problem to

Ghilardi's semantic method characterises the Pitts quantifiers by
*bisimulation*: ∃p.φ holds where some p-variant world forces φ; ∀p.φ
holds where every p-variant of every future forces φ. Today's file sets
this up for constraint models and proves the whole *universal-property*
layer:

* **A-bisimulation** (`ABisim`): zigzag for BOTH relations Rᵢ and Rₘ,
  matching fallibility, matching atoms in a protected alphabet A. The
  p-variant relation is `PBisim p` = protect everything except p.
* **Invariance** (`force_iff_of_bisim`, PROVED): forcing is invariant
  under A-bisimulation for formulas over A. The ⊃-case consumes
  i-zigzag; the ◯-case consumes i-zigzag for the future and m-zigzag
  for the constraint witness; the ⊥-case is why fallibility must match.
* **The universal properties** (PROVED, via the library's `soundness` +
  choice-free `completeness`): any p-free ψ satisfying the semantic
  spec `IsSemEx p φ ψ` satisfies

      φ ⊢ ψ        and        (φ ⊢ χ  ⟺  ψ ⊢ χ)   for every p-free χ

  (`semEx_upper`, `semEx_adjunction`), and dually `IsSemAll` gives
  `ψ ⊢ φ` and `(χ ⊢ φ ⟺ χ ⊢ ψ)` (`semAll_lower`,
  `semAll_adjunction`). These are exactly Pitts' defining properties of
  the uniform interpolants.

**Consequently uniform interpolation for PLL is now equivalent to ONE
open statement per quantifier** — definability:

    semEx_definable :  ∀ p φ, ∃ ψ, IsSemEx p φ ψ        (OPEN)
    semAll_definable : ∀ p φ, ∃ ψ, IsSemAll p φ ψ       (OPEN)

No cascade, no budgets, no threshold arithmetic: the entire task-#9
apparatus is bypassed. If definability is proved, UI follows by the
adjunctions; if it fails, UI fails semantically and the syntactic route
was doomed anyway. This is the value of the route: it terminates either
way, in the same currency as everything else in the repo.

## 2. The battle plan for definability

The intended engine is the constructive finite canonical model
(`PLLFinComp.lean`): worlds are closure-total triples (Γ, Δ, Θ) over a
subformula closure, finitely many per closure, enumerable, checkable.

**Candidate construction (∃-side).** Fix φ and p; let Σ be the closure
of φ and Σ' its p-free part. For each Σ'-triple T that extends to a
Σ-triple whose validated part contains φ, emit a *description* of T; the
candidate interpolant is the finite disjunction of these descriptions.
The novelty PLL forces: a description must pin the ◯-behaviour, and the
canonical model says how — the promises. A triple's description should
have the shape

    desc(T)  =  ⋀Γ_T  ∧  (⋀-of-refutation-content for Δ_T)  ∧  ¬◯(⋁Θ_T)

with the ◯-guarded promise conjunct carrying exactly the information
that the plain intuitionistic description cannot. Making "refutation
content" precise intuitionistically (no classical negation of Δ) is the
de Jongh-style induction — descriptions of a world in terms of the
descriptions of its proper successors — and the place where real work
lives.

**The two PLL-specific hazards, in expected order of difficulty:**

1. **The ∀∃ ◯-clause under amalgamation.** The ← direction of the spec
   requires: from "w forces desc(T)", BUILD a p-variant model and world
   forcing φ. The construction glues the ambient model to a canonical
   witness; the gluing must supply Rₘ-witnesses for every future of
   every glued world coherently. This is where an S4-style definability
   failure would enter (Ghilardi–Zawadowski: S4 has no uniform
   interpolation, and Rᵢ here is S4-shaped). The counter-pressure is
   full heredity — `force_hered` holds through ◯ — which is exactly
   what rescues IPC despite its preorder. Honest status: genuinely
   open which force wins; nothing in our evidence points to failure.
2. **Fallible worlds.** F-worlds force everything, so they are
   universal amalgamation absorbers — probably a HELP (gluing can dump
   incoherence into a fallible sink), but descriptions must not be
   fooled: matching fallibility is already a bisimulation clause, and
   Θ-promises are what distinguish a world pretending to be fallible
   from one committed against it.

**The induction has been started (PROVED, same file, 2026-07-18 pm):**
the universal p-variant constructor `redecorate` (same frame, atom p
re-decorated by any hereditary F-full set; the identity carrier is a
`PBisim p`), and with it the base and pointwise-compositional cases:

    ∃p.p = ⊤    ∀p.p = ⊥    ∃p.q = q  (q≠p)    ∀p.q = q  (q≠p)
    ∃p.⊥ = ⊥    ∀p.⊥ = ⊥    ∃p distributes over ∨    ∀p over ∧

(`semEx_prop_self`, `semAll_prop_self`, `semEx/semAll_prop_ne`,
`semEx/semAll_false`, `semEx_or`, `semAll_and`). What is deliberately
absent is the quantificational core — ∃ through ∧/⊃/◯ (two p-variants
must be AMALGAMATED into one) and ∀ through ∨ — which is exactly where
the canonical-model descriptions must enter and why the general theorem
is not a structural recursion.

**The amalgamation case at one variable — tried, and settled both ways
(PROVED, same file, 2026-07-18 eve):**

* *The obstruction is real and machine-checked*
  (`semEx_and_pointwise_fails`): ∃p.p = ⊤ and ∃p.¬p = ⊤ — but their
  witnessing decorations are INCOMPATIBLE (p everywhere vs p exactly on
  the fallible set), and ∃p.(p ∧ ¬p) = ⊥ (`semEx_p_and_neg_p`), so the
  pointwise candidate ⊤ ∧ ⊤ fails the spec on a one-world model. ∃p
  provably does not commute with ∧: amalgamation is exactly what a
  definability proof must supply.
* *The first genuinely modal quantifier values*
  (`semEx_neg_p`, `semAll_neg_p`, `semEx_box_p`, `semAll_box_p`):

      ∃p.¬p = ⊤    ∀p.¬p = ⊥    ∃p.◯p = ⊤    **∀p.◯p = ◯⊥**

  The last is the telling one: the strongest legal p-decoration is
  p := F, under which ◯p is literally ◯⊥, and `full_F` pins the value
  against every other variant. ◯⊥ — the free generator of the closed
  fragment — is the ∀p-shadow of the modality itself, and this matches
  the {⊥, ◯⊥, ⊤} landscape the one-variable descent probe observed for
  the syntactic interpolants: the two routes are computing the same
  objects.

**Strategic advice to the fresh session:** attack definability at ONE
propositional variable first, over the canonical models of the 1-pv
closures. Everything we know says this case is tiny: the deep probe
found five-class state spaces, and the RN(◯,{}) fragment machinery
(`lattice_cmp`, the closed-fragment enumeration) can *compute* candidate
descriptions and oracle-test the spec's two directions instance by
instance before any general proof is attempted. The two-sided oracle
(proof terms + certified countermodels) means every failed candidate
yields a three-world picture of *why* — the diagrams will tell us the
right description shape faster than theory will.

## 3. Relations to the ⊩ semantics of the Belief paper

Three connections, one now a theorem-adjacent fact, one a conjecture
shape, one a recorded dead-end.

**(a) Truth is bisimulation-invariant; evidence is not.** Invariance is
now proved for forcing. It FAILS deliberately for the realisability
semantics: a ⊩ˢ/⊩ᵖ-strategy receives κ(v), the *name* of the presented
world, and two bisimilar worlds carry different names. Indeed the
Belief paper's obstruction theorem turns exactly on what strategies can
and cannot see of the world's identity. So the realisability semantics
is a *refinement* of the bisimulation quotient: ⊩ distinguishes worlds
that truth cannot. Slogan (no Lean anchor yet): **the propositional
quantifiers live on the bisimulation quotient; evidence lives under
it.** A mechanisable statement: exhibit a model, a PBisim, related
worlds w Z w', and a formula ⊩ᵖ-realised at w but not at w' —
plausibly extractable from the obstruction model.

**(b) The uniform/reactive dichotomy transposes from futures to
atoms.** The Belief paper's central axis is how much evidence is told
about the FUTURE (⊩ᵘ nothing / ⊩ˢ the ◯-future / ⊩ᵖ every future). The
∀p-quantifier introduces the same axis for ATOMS: a realiser of ∀p.φ
should be *one element serving every p-decoration* of the model — a
p-uniform realiser, PLLᵘ's rigidity reappearing one level up. The
paper's lesson "uniformity validates strictly more" then predicts:
evidence for ∀p.φ is strictly stronger than a family of per-decoration
evidences, and the gap should again be exhibited by a disjunction
(◯(A ∨ B)-style) — now with the disjuncts separated by p-decorations
rather than by futures. Conjecture-shaped; a clean small target for
whoever works this seam: formulate `⊩ᵖ`-realisability of ∃p/∀p via
quantification over `Evidence`-decorations of the SAME frame, and test
the analogue of the bite on the split model. If it behaves, the Belief
paper gains a section: *propositional quantifiers as evidence
uniformity* — and UI becomes a statement about evidence, not just truth.

**(c) The constraint-translation route — CORRECTED (Matthew,
2026-07-18): not dead, but requires per-instance finite support.** One
might hope to DERIVE PLL-UI from the mechanised IPC-UI (the box-free
crown) through context completeness (Thm 6: PLL ⊢ φ iff ∀C, IPL ⊢ φ^C).
The naive form does fail — the constraints mention p, and commuting a
p-quantifier past the unrestricted ∀C would need a single finite
constraint set complete for the whole logic, which Corollary 10 refutes.
But — Matthew's point — Corollary 10 is a statement about ALL of PLL,
not about any one interpolation instance: for a SPECIFIC φ the
derivability facts the interpolant must govern may be controlled by a
FINITE set S_φ of constraints, and then a candidate interpolant is
constructible from { IPC-∃p.(φ^C) : C ∈ S_φ }. There is a natural
candidate for S_φ: Lemma 7 manufactures ONE standard constraint per
finite constraint model (the semantic completion), so S_φ = the
constraints of the canonical models over φ's subformula closure — a
finite set, by the finite canonical construction. OPEN: whether the
adjunction properties survive the assembly (the ∀χ over p-free χ ranges
over formulas outside φ's closure; the finite-support claim must be
proved against that quantifier, plausibly via the FMP bound). Status:
a live THIRD route (syntactic cascade / semantic definability /
finite-support constraint transfer), currently unexplored.

**(d) Shared infrastructure.** The finite canonical model is now
carrying three loads: the choice-free completeness (Belief §6.2), the
countermodel emitter, and — if this route lands — UI definability. One
construction, three dividends. The promise components Θ, introduced in
1997 to record ◯-refutations, would become precisely the ◯-part of the
world descriptions: the 30-year-old bookkeeping is the right amount of
information for the quantifiers. That would be a satisfying thing to
be able to say in print.

## 4. Relation to the syntactic route (task #9)

Independent. If definability lands, UI holds and the syntactic
`itpA`/`itpE` become one *candidate presentation* of the quantifiers
(their adequacy then provable by uniqueness-up-to-interderivability
against the semantic ones — a cleaner path than the H1/H2 cascade). If
the syntactic route closes first, its interpolants must satisfy the
semantic spec (by the same uniqueness), and the spec becomes the
crispest statement of what was proved. Either way `IsSemEx`/`IsSemAll`
are now the canonical interface; the two efforts meet there.

## 5. File map

| artefact | content |
|---|---|
| `wip/semantic_ui.lean` | ABisim, invariance, identity, specs, four adjunction theorems (all PROVED); two definability targets (OPEN) |
| `LaxLogic/PLLFinComp.lean` | the finite canonical model = the intended definability engine |
| `LaxLogic/PLLCountermodelEmit.lean` + diagrams | the two-sided oracle for testing candidate descriptions |
| `wip/lattice_cmp.lean`, `wip/slick_probe.lean` | 1-pv computation harnesses for candidate descriptions |
| task #9 / `PROGRESS.md` | the syntactic route (independent; meets this one at the spec) |
