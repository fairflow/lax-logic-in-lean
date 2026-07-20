# The semantic route to uniform interpolation for PLL

2026-07-18 · companion to `LaxLogic/PLLSemUI.lean` (sorry-free since the
2026-07-19 graduation: the two named open targets are `Prop`-level
conjectures `SemExDefinable`/`SemAllDefinable`). Status words used
precisely: PROVED = machine-checked; OPEN = stated as a conjecture;
observations without Lean anchors are marked as such.

**Update 2026-07-19 — see §0 below for the session's results: the
essential-fibre conjecture is PROVED (both image theorems), and
definability acquired a two-generator certificate method (substitution
instances + the lower transform of the doubled model) with a
computational value table at one variable.**

## 0. Results of 2026-07-19 (all machine-checked in `LaxLogic/PLLSemUI.lean`)

**(a) The essential fibre of the quantifiers — the conjecture is a
theorem.**  Call `p` *inessential* in M when M is PLL-equivalent to some
p-free formula (`Inessential`), *essential* otherwise.  The two warm-up
exercises:

    IsSemAll p M ⊤  →  ⊢ M          (semAll_true_derivable)
    IsSemEx  p M ⊥  →  M ⊢ ⊥        (semEx_false_refutes)

so ⊤ is never an essential ∀p-value and ⊥ never an essential ∃p-value.
The full image theorems, for p-free ξ:

    (∃ M, IsSemAll p M ξ ∧ p essential in M)  ⟺  ⊬ ξ
                                       (essential_semAll_image)
    (∃ M, IsSemEx p M ξ ∧ p essential in M)   ⟺  ξ ⊬ ⊥
                                       (essential_semEx_image)

Witnesses: `∀p.(ξ ∨ p) = ξ` and `∃p.(ξ ∧ p) = ξ` (`semAll_or_p`,
`semEx_and_p`); essentiality of the witnesses by separating the
substitution instances `p := ⊤` and `p := ⊥` at the countermodel that
classical completeness extracts from the underivability hypothesis.  On
the closed fragment this reads: **the essential ∀p-image is
RN(◯,{}) ∖ {⊤} and the essential ∃p-image is RN(◯,{}) ∖ {⊥}** —
exactly the conjectured structure theorem.  Concrete instances proved:
⊥, ◯⊥, ¬◯⊥ are essential ∀p-values (`essential_fibre_boxFalse`,
`essential_fibre_neg_boxFalse`), and the original data points carry
essential preimages: `∀p.p = ⊥` with p essential in p
(`essential_prop_self`), `∀p.◯p = ◯⊥` with p essential in ◯p
(`essential_box_p`).

**(b) The certificate method for definability.**  Decorating p by the
truth set of any formula χ is a legal redecoration, and forcing there is
forcing of the substitution instance M[p:=χ] (`force_truthDeco`).  This
yields sound, oracle-checkable criteria:

    ∃-side:  p ∉ atoms ψ,  M ⊢ ψ,  ψ ⊢ M[p:=χ]        ⟹  IsSemEx p M ψ
    ∀-side:  p ∉ atoms ψ,  ψ ⊢ M,  M[p:=χ₁],…,M[p:=χₖ] ⊢ ψ
                                                       ⟹  IsSemAll p M ψ

(`isSemEx_of_certificates`, `isSemAll_of_certificates`).  Every
certificate found by the search oracle is immediately a Lean proof of a
quantifier value.

**(c) The criteria are provably incomplete, and the first repair is the
doubling.**  `∀p.(p ∨ ¬p) = ⊥` (`semAll_em_p`), but every substitution
instance of p ∨ ¬p is an excluded-middle instance, forced at the
one-world classical model — so no finite family of instances derives ⊥
(`em_p_no_certificate`).  The proof instead *doubles* the model
(`double`: two copies stacked along the 2-chain, both relations
monotone into the upper copy; the projection is a total p-bisimulation)
and decorates p on the upper copy only (`emVariant`): a non-fallible
lower world then forces neither p nor ¬p.

**(d) The doubling is itself a certificate generator: the lower
transform.**  Within the cone over the base world, forcing on the two
copies of `emVariant` is computed by syntactic transforms
(`emVariant_force_true/false`, both axiom-free):

    (x, true)  ⊩ M   iff   x ⊩ M[p:=⊤]
    (x, false) ⊩ M   iff   x ⊩ lowT p M

    lowT p p       = ⊥            lowT p (A ⊃ B) = (lowT A ⊃ lowT B)
    lowT p (◯A)    = ◯(A[p:=⊤])                    ∧ (A[p:=⊤] ⊃ B[p:=⊤])

(pointwise on ∧, ∨, atoms ≠ p, ⊥).  So `lowT p M` joins the
substitution instances as one more premise available to the criteria
(`isSemAll_of_certificates_low`, `isSemEx_of_certificates_low`), and
the values beyond substitution fall mechanically:

    ∀p.(p ∨ ¬p) = ⊥      ∀p.(◯p ⊃ p) = ⊥      ∀p.(¬¬p ⊃ p) = ⊥
    (semAll_em_p)         (semAll_boxp_imp_p)   (semAll_nnp_imp_p)

**(d′) The third generator: the sideways-witness construction and
`sideT`.**  The Löb-shaped `◯(◯p ⊃ p)` defeats both substitution and
the doubling.  Its value falls to `lobModel`/`lobVariant`: ℕ-levelled
copies with `Rᵢ` level-monotone but `Rₘ` level-rigid **except the
single step 1 → 2**, `p` decorated on levels ≥ 2.  Level 1 forces ◯p
but not p, so `◯p ⊃ p` fails at level 0 over every non-fallible base
world; level-0 constraint witnesses stay at level 0, so a level-0 world
satisfies `◯(◯p ⊃ p)` only through fallible witnesses:

    ∀p.◯(◯p ⊃ p) = ◯⊥        (semAll_box_lob)

The p-worlds are Rₘ-reachable *sideways* (as constraint witnesses) but
never lie on the Rₘ-cone of level 0 — precisely the promise/Θ mechanism
of the canonical model, surfacing as a variant construction.  The
levels of `lobVariant` again evaluate by syntactic transforms
(`lobVariant_force_high/one/zero`): levels ≥ 2 are the `p:=⊤`
substitution, level 1 is `lowT` again, and level 0 is the new

    sideT p p       = ⊥        sideT p (A ⊃ B) = (sideT A ⊃ sideT B)
    sideT p (◯A)    = ◯(sideT A) ∧ ◯(A[p:=⊤])       ∧ lowT p (A ⊃ B)

with `sideT p (◯(◯p⊃p)) ≡ ◯⊥` exactly.  The criteria now carry the
full generator basis {substitution instances, lowT, sideT}
(`isSemAll_of_certificates_side`, `isSemEx_of_certificates_side`).

**Roadmap observation (no Lean anchor).**  The three generators are the
level-0 transforms of a tower of levelled models (2-chain, 3-level
sideways, …); the ◯/⊃-alternation depth of M bounds the tower depth it
can see, and the finite canonical model over cl(M) bounds it
per-instance.  A uniform definability proof at one variable now has a
concrete shape: show that for every 1-variable M the candidate value
(the maximum closed ξ ⊢ M) is derivable from finitely many generator
instances — the generator set standing in for the promise-aware world
descriptions.  Rows of the value table that resist the current basis
name the next construction.

**(e) Uniqueness** (`semEx_unique`, `semAll_unique`): any two
spec-satisfiers are interderivable, so "the value of ∀p.M" is
well-defined up to ≡ — the probe's candidates, once certified, ARE the
quantifiers.

**(f) The value-table probe** (`wip/semui_probe.lean`): for every
one-variable M up to weight 5 (plus named extras), compute the
candidate ∀p-value (maximum of the closed ξ ⊢ M, over the RN(◯,{})
ladder truncation — 7 classes at weight ≤ 8) and candidate ∃p-value
(minimum of the closed ξ with M ⊢ ξ), then search certificates over
the generator basis.

**(g) Probe results (run completed 2026-07-19; full table + analysis
in `docs/semantic-ui-1pv-table.md`): ALL 25 one-variable classes are
certified on BOTH sides** — the basis {substitution instances, lowT,
sideT} suffices for the whole table; every candidate is a unique
maximum/minimum over the 7-class ladder; the values attained are
{⊥, ◯⊥, ⊤, ¬◯⊥, ◯¬◯⊥}; the probe's values agree with every Lean
theorem where they overlap.  The doubling is needed exactly at
`◯p ⊃ p` and `p ∨ ¬p` (∀-side); the sideways construction exactly at
the ◯-guarded schemata `◯(◯p⊃p)`, `◯(p∨¬p)`, `¬◯p∨◯p` — all on the
∀-side.  (CORRECTION 2026-07-19: the probe's CERT-LOW on the ∃-row of
`¬◯p ∨ ◯p` was a weight-cap artifact; `p := ⊤` also certifies it.  No
∃-side value is known to require a frame-changing generator — that
necessity is machine-checked only on the ∀-side,
`em_p_no_certificate`.)  Definability at one
variable is therefore an empirically complete conjecture with a
uniform proof target: for every one-variable M, the generator
instances {M[p:=⊥], M[p:=⊤], lowT p M, sideT p M} derive the maximum
closed ξ ⊢ M (dually for ∃) — a purely syntactic statement over the
RN lattice.  Oracle pathology recorded in the table doc: failing
`search` cost is unpredictable (non-monotone in fuel); successes instant.

**(h) The reconstruction reduction (2026-07-19, overnight session;
PROVED in `LaxLogic/PLLSemUI.lean`).**  Writing `M[χ]` for the
substitution `substP p χ M`, define the p-free candidates

    allCand p M  :=  M[⊥] ∧ M[⊤] ∧ lowT p M ∧ sideT p M
    exCand  p M  :=  M[⊥] ∨ M[⊤] ∨ M[◯⊥] ∨ lowT p M ∨ sideT p M

Because each conjunct/disjunct is a generator instance, one direction
of each spec holds by construction, and (`isSemAll_of_reconstruction`,
`isSemEx_of_reconstruction`, `semAll/semEx_definable_of_reconstruction`)
**definability reduces to two sequent families**, the *reconstruction
sequents*:

    (∀-rec)   M[⊥], M[⊤], lowT p M, sideT p M  ⊢  M
    (∃-rec)   M  ⊢  M[⊥] ∨ M[⊤] ∨ M[◯⊥] ∨ lowT p M ∨ sideT p M

If (∀-rec) holds for M then `allCand p M` IS the ∀p-value of M; dually
for (∃-rec).  Both families are single derivability statements per
instance — decidable, and oracle-testable.

Status of the families, settled the same night, both ways:

**(i) The FIXED bases are REFUTED — machine-checked — and the repairs
identify the per-instance law.**

*∃-side* (`exRec_fails`, `exCand_not_value`): for the biconditional

    bicond p := (¬◯⊥ ⊃ p) ∧ (p ⊃ ¬◯⊥)          (weight 14)

decorating p by the ¬◯⊥-truth set forces `bicond p` everywhere, so
`∃p.(bicond p) = ⊤` (`semEx_bicond_top`, certified by the substitution
`p := ¬◯⊥`) — but on the four-world model w₀ < v₁, w₀ < v₂ < f
(Rₘ = id ∪ {v₂→f}, F = {f}, V(p) = {v₁,f}) all five `exCand` disjuncts
fail at the root while `bicond p` holds.  The oracle independently
confirms this failure and finds the next at `bicond` over ◯¬◯⊥
(weight 16); adding the corresponding ladder substitutions repairs
both.

*∀-side* (`allRec_fails`, `allCand_not_value`): the exhaustive sweep
(`wip/semui_sweep.lean`, ALL 2758 raw one-variable formulas of weight
≤ 7) found exactly 8 failures — all of the **Peirce/stability family**

    (X ⊃ p) ⊃ Y      with  X ∈ {◯⊥, ◯p, ◯◯⊥, ◯◯p},  Y ∈ {p, ◯p}

(plus ◯-prefixed variants).  Machine-checked witness:
`peirce p := (◯⊥ ⊃ p) ⊃ p` on the three-world chain a < b < f with
p decorated by the ◯⊥-truth set: the root forces all four `allCand`
generators but not `peirce p`.  The value exists:
`∀p.((◯⊥⊃p)⊃p) = ◯⊥` (`semAll_peirce`), certified by `p := ◯⊥` —
absent from the four-generator basis.  Adding `M[◯⊥]` to the ∀-pool
repairs ALL EIGHT sweep failures (oracle, instant).

*Deep alternation does NOT grow the frame-changing basis*: iterated
Löb formulas to depth 4, the gap shape `◯(¬◯p ⊃ ◯p)`, and `◯(¬p ∨ ◯p)`
all reconstruct from the existing generators — the escapes are always
ladder-rung SUBSTITUTIONS, never new levelled models (up to the depths
probed).

**The per-instance support law (the corrected conjecture).**  For every
one-variable M, the generator pool

    { M[χ] : χ a closed-fragment rung occurring (as a class) in M }
      ∪ { lowT p M, sideT p M }

reconstructs M on both sides — verified on: the full weight-≤5 value
table, all 2758 weight-≤7 formulas (∀-side with the ◯⊥-rung; ∃-side
as is), the Peirce-8, the bicond family through weight 16, and the
depth-3/4 battery.  Definability at one variable thus reduces (by the
PROVED reduction) to this per-instance reconstruction — a finite-
support statement of exactly the shape of route (c)'s corrected
Corollary-10 analysis: the two routes have converged on the same
per-instance finite object.

A *naive* structural induction on M does not prove the reconstruction:
in the ⊃-case, splitting a hypothesis `A` by (∃-rec for A) yields,
say, `A[⊥]` at the world, and the transform conjunct `A[⊥] ⊃ B[⊥]`
then gives only `B[⊥]` — reassembling `B` needs all of B's
generators, to which the case gives no access.  The missing
ingredient is a JOINT statement tracking which canonical decoration
the world inhabits across all subformulas simultaneously — precisely
what canonical-model descriptions provide.  So the intended uniform
proof is the de Jongh-style induction over the finite canonical model
of cl(M), with the generator family as its computational shadow — and
the refutations above say the descriptions must record exactly the
ladder rungs of cl(M), i.e. the promise/Θ data.

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
| `LaxLogic/PLLSemUI.lean` | ABisim, invariance, identity, specs, four adjunction theorems (all PROVED); two definability targets (OPEN) |
| `LaxLogic/PLLFinComp.lean` | the finite canonical model = the intended definability engine |
| `LaxLogic/PLLCountermodelEmit.lean` + diagrams | the two-sided oracle for testing candidate descriptions |
| `wip/lattice_cmp.lean`, `wip/slick_probe.lean` | 1-pv computation harnesses for candidate descriptions |
| task #9 / `PROGRESS.md` | the syntactic route (independent; meets this one at the spec) |

**(j) The constraint-commutation experiment (2026-07-19, Matthew's
proposal; probe `wip/semui_ctx_probe.lean`).**  Conjecture tested: for
each M there is a standard constraint C, built from M à la Lemma 7,
with

    ∀ᴵᴾᶜ p.(M^C) ≡ᴵᴾᶜ (∀p.M)^C          (dually ∃p)

where `M^C = subC C M` (mechanised), the PLL-values are the
spec-verified ones, and ∀ᴵᴾᶜ is computed by the box-free tower
(`itpA`/`itpE`), oracle-compared.  Constraints: Lemma 7's recipe
`(α_u, ⋁ covers)` over Rₘ-stable worlds of concrete finite models.

ORACLE-VERIFIED (two-world chain, fallible top; tower calibration row
`∀ᴵᴾᶜp.(p∨¬p) = ⊥` passed): the commutation HOLDS for `◯p`, `¬p`,
`◯⊥ ⊃ p`, `(◯⊥⊃p)⊃p` — and FAILS exactly at `◯p ⊃ p`:
`∀ᴵᴾᶜp.((a1⊃p)⊃p) = a1` (the IPC shadow of the Peirce family — an
independent cross-check of `semAll_peirce_family`) against
`(∀p.(◯p⊃p))^C = ⊥`.  REPAIR VERIFIED (same model): relative to the
frame theory Θ = {α_w ⊃ ⊥ : w fallible}, the failing row commutes —
the tower value is Θ-equivalent to ⊥.

ANALYSIS (recorded as analysis, not machine-checked): a single frozen
C realises exactly the REDECORATION approximation of ∀p — the IPC
quantifier sees decorations of the named frame but not frame-changing
variants.  Every non-fallible Rₘ-stable world contributes an
"α-top residue": at α_u-everywhere IPC-worlds the pair `(α_u, …)`
forces `C[p] ⊢ p`, so `C[p]⊃p`-type translations are forced under
every decoration and the relative value stays ≥ α_u > ⊥; no frame
theory over the same names removes it, and re-generating C from the
doubled model reproduces the residue one level up (the doubling
regress).  PREDICTION (OPEN, runs timeboxed out): frame-relative
commutation for ⊥-valued M holds iff every Rₘ-stable world of the
generating model is fallible; the three-chain and fork models (each
with a non-fallible stable world) fail even frame-relatively.  If
confirmed, the one-constraint form of the conjecture holds exactly up
to the redecoration approximation, and the frame-changing content
demands growing constraint families — reconverging, from the
constraint side, with the per-instance support law of §0(i).

Tooling note: tower cost (raw term construction before nf) is the
binding constraint — unpredictable in fuel/budget like the failing-search
cost; rows beyond weight ~7 translations need the fuel/budget caps of
the probe, and some still wedge.  All probe verdicts are sound on
`true`.

### (k) 2026-07-19 afternoon: graduation, and the sandwich lemmas (the constraint–ladder comparison, PROVED)

GRADUATION.  The theory file left `wip`: it is now
`LaxLogic/PLLSemUI.lean`, registered in the root module, sorry-free —
the two definability targets are `Prop`-level CONJECTURES
(`SemExDefinable`, `SemAllDefinable`), everything else PROVED (27
flagship theorems audited ≤ [propext, Classical.choice, Quot.sound]).
Per the meta-tactic: no sorried statement survives in the library;
conjectures are stated, not asserted.

THE EQUIVALENCE QUESTION (Matthew): are the two candidate
constructions of ∀p M — (A) constraint models C[_] built from cl(M)
(the TYPES-paper route), (B) ladder-level generator instances from
cl(M) — equivalent?  ANSWER, machine-checked in
`LaxLogic/PLLSemUICtx.lean` + `wip/semui_ctx_equiv.lean`:

* NOT equivalent for a single frozen C — the §0(j) oracle witness
  stands (M = ◯p⊃p over chain2: IPC value a1, translated PLL value ⊥);
* but PROVABLY equivalent ON THE SUBSTITUTION FRAGMENT, and every
  constraint-route value is SANDWICHED.  With ξ^C := subC C ξ the
  TYPES translation (each ◯ψ ↦ C[ψ^C]):

      ξ^C  ⊢ᴵᴾᶜ  ∀ᴵᴾᶜp.(M^C)  ⊢ᴵᴾᶜ  (M[p := χ])^C   (every χ)

  for every IPL p-free standard constraint C, where ξ is the semantic
  ∀p-value (IsSemAll) and ∀ᴵᴾᶜp is ANY Pitts-style IPC ∀-interpolant
  of the translation (abstract spec `IsIPCAll`; instantiated by the
  packaged tower quantifier `forallP` via the box-free crown
  `uniform_interpolation_IPC`, no sorryAx).  Dually for ∃
  (`IsIPCEx`/`existsP`, inequalities reversed).

The three lemmas behind it (all library, audited):

* `substND` — LaxND is closed under atom substitution
  (derivation-level, structural);
* `subC_substP` — THE BRIDGE: `(M[p:=χ])^C = (M^C)[p := χ^C]` for
  p-free C — the ladder's substitution instances ARE IPC instances of
  the translation;
* `ctx_sandwich_all`/`ctx_sandwich_ex` — the displayed sandwich
  (components `ctxAll_ge_value`, `ctxAll_le_instance` + duals).

CONSEQUENCE.  The gap between the two sandwich bounds is exactly the
frame-changing content of the ladder route (`lowT`/`sideT`): the
constraint route computes the substitution-reachable part of ∀p, on
the nose.  A full "theorem via constraint models" now has a precise
form: find, per M, a FAMILY of constraints (canonical + variant
saturations) whose joint value is exact — the sandwich reduces this to
closing the lowT/sideT gap on the constraint side.  OPEN, with the
§0(j) fallibility prediction as the first test.

### (l) 2026-07-19 afternoon: the two-sided oracle, packaged (`wip/oracle2.lean`)

Matthew's resource point — failing search must exhaust all routes, so
try cheap countermodels first; tools may be fallible because their
accepted outputs are verified — is now the packaged discipline.
`decide2` stages: low-fuel `search` (cheap positive) → battery sweep
(≤4-world frames × hereditary decorations, every candidate gated by
the VERIFIED `FinCM.checkB` — a wrong guess cannot certify) →
high-fuel `search` → `CounterEmit.emit` gated by closure size →
honest UNKNOWN.  `.refuted` verdicts upgrade to machine-checked
`¬ Nonempty (LaxND Γ C)` via `not_provable_of_check` by `decide` when
paper-grade certificates are wanted.  Benchmarks (numbers in
PROGRESS.md §9): 10/10 correct at 0 ms each, including the weight-40
Peirce reconstruction failure on which plain one-sided `search`
grinds >100 s interpreted and >120 s NATIVE — the countermodel stage,
not compilation, beats the unpredictable failing cost.  The compiled route
is nonetheless live: this branch is on v4.31.0, `lake exe oracle2`
builds in ~10 s and runs the suite in 0.02 s CPU (the lakefile's
laxrun-segfault comment was stale; fixed).

### (m) 2026-07-19 evening: the fallibility prediction — CONFIRMED on chain2/chain3, with verified countermodels

Compiled reruns of the §0(j) experiment (fuel-free `G4cTm.find`
oracle, `lake exe ctxprobe` / `ctxrel` / `ctxcert`; the fueled-search
chaos is gone — see §0(l) update below).

FULL chain2+chain3 frozen-C table (tool-grade oracle, 17 rows):
every SUBSTITUTION row commutes on both models and both quantifiers —
exactly as the sandwich (§0(k)) mandates; the failures are exactly
the frame-changing rows: `◯p⊃p` (LOW) on both models, `◯(◯p⊃p)`
(SIDE, NEW datum) on chain2.  Two chain3 rows inconclusive at budget
2 (tower unstabilised: `(◯⊥⊃p)⊃p` ∀-side, `¬◯p` ∃-side).

THE PREDICTION (was OPEN): frame-relative commutation (Θ = fallibility
axioms) for ⊥-valued M iff every Rₘ-stable world of the generating
model is fallible.  STATUS NOW:

* chain2 (all stable worlds fallible): rel-comm HOLDS on all three
  test rows — positive side, `find`-term grade (`ctxrel`).
* chain3 (non-fallible stable world 0): rel-comm FAILS on both
  ◯-rows, **CERTIFIED by checkB-verified countermodels** (`ctxcert`):
  the sequents `A, Θ ⊢ vA'` (tower value + frame theory ⊢ translated
  PLL value) are refuted by the ONE-WORLD model — a single
  non-fallible world with only `a0` true.  That world IS the α-top
  residue of the §0(j) analysis, now machine-checked: Θ holds there
  (a2 false), the IPC tower value holds, the translated value fails.
  The other direction `vA', Θ ⊢ A` is PROVED on every row — the
  sandwich's lower bound, concretely.
* fork (non-fallible stable worlds 0, 1): rel-comm FAILS on both
  ◯-rows, **CERTIFIED by the same one-world countermodel** (only
  `a0` true).  Tower-weight datum: the fork towers reach weight
  233–1476 and are CONSTRUCTED in 0 ms compiled — compilation
  dissolved the tower-construction wall of §0(j); the only guarded
  residual is `find` on very large PROVABLE inputs (the sandwich
  theorem covers that direction anyway).

The prediction is thus CONFIRMED on all three test models — the
failing half by checkB-verified one-world countermodels, the holding
half by find-terms.  The GENERAL iff-law stays OPEN, but the
certified countermodel is visibly uniform in the model: for ANY m
with a non-fallible Rₘ-stable world u, the one-world classical model
decorated `{a_u}` makes every `C[x]` equivalent to `x` (the u-pair's
disjunct-side is false, every other pair's guard is false), so the
translation collapses to identity there and the tower-∀ survives
while any ⊥-bounded translated value fails.  Formalising THAT
one-world argument was the short-lemma route to the general
fails-half — DONE the same evening, see §0(n).

CONSEQUENCE.  Frame theories over the SAME constraint names provably
cannot close the lowT/sideT gap (a one-world countermodel survives
any Θ that holds at the residue world).  The constraint-route theorem
must therefore enlarge the CONSTRAINT POOL (variant models' Lemma-7
constraints — doubled/Löb saturations), not the ambient theory.  This
is the per-instance finite-support picture arriving from the third
independent direction.

### (n) 2026-07-19 evening: the general fails-half — PROVED (`LaxLogic/PLLSemUIRes.lean`)

The uniform one-world argument of §0(m) is now a THEOREM, fully
general in the constraint and the frame theory.  The pieces (all
audited ≤ [propext, Classical.choice, Quot.sound]; the collapse needs
only [propext]):

* `residue n₀` — the one-world model: infallible, total relations,
  exactly `n₀` true.
* `ResiduePair n₀ bad C` — the Lemma-7 shape at a non-fallible
  Rₘ-stable world: a pair `(α_{n₀}, ⋁ covers)` with covers named in
  `bad`, every other pair named in `bad`, `n₀ ∉ bad`.
* `residue_applyC` — THE COLLAPSE: at the residue point,
  `C[x] ⊨ ↔ x ⊨` — the translation degenerates to the identity.
* `diag_row1`/`diag_row2` — the diagram `n₀ ∧ ⋀_{a∈bad} ¬a` DERIVES
  the translations `(◯p⊃p)^C` and `(◯(◯p⊃p))^C` over all constraint
  models (forced covers make worlds fallible; fallible worlds force
  p), via `completeness`.
* `residue_obstruction` — engine: the diagram transports any
  `IsIPCAll`-value of the translation to the residue point (spec +
  `soundness`), which then blocks derivability of anything it
  refutes.

**Headlines**:

    fails_half_boxp_imp_p :
      ResiduePair n₀ bad C → p ∉ {n₀} ∪ bad →
      IsIPCAll p isIPL ((◯p⊃p)^C) A →
      (Θ = n₀-avoiding negated atoms) →
      ¬ Nonempty (LaxND (A :: Θ) ⊥)

    fails_half_box_lob : likewise  ¬ (A :: Θ ⊢ (◯⊥)^C)

So for EVERY constraint of the Lemma-7 shape at a non-fallible stable
world, EVERY IPC ∀p-value of the two frame-changing rows, and EVERY
fallibility-style frame theory: the value cannot be brought down to
the translated PLL value.  The §0(m) certified instances are now
corollaries (`chain3_fails_half` re-derives the chain3 certificate
from the general theorem).  The "fails" half of the fallibility
prediction is thereby PROVED in full generality; only its converse
(commutation when ALL stable worlds are fallible — the chain2
direction) remains OPEN as a general law, currently verified
per-instance.

### (o) 2026-07-19 late: the holds-half — PROVED (fully-fallible constraints)

The converse of §0(n), same file.  `ThetaNamed Θ C` = every pair of C
is named by a Θ-negated atom — the Lemma-7 shape when EVERY Rₘ-stable
world of the generating model is fallible and Θ carries the
fallibility axioms (the chain2 situation).  Key lemma `theta_applyC`
([propext] alone): under `ThetaNamed`, Θ derives EVERY constraint
application `C[x]` — each guard is Θ-refuted, so the constraint
content evaporates.  Headlines:

    holds_half_boxp_imp_p ([propext, Quot.sound] — choice-free):
      ThetaNamed Θ C → (Θ p-free) →
      IsIPCAll p isIPL ((◯p⊃p)^C) A →
      A ≡_Θ ⊥        (both directions derivable)

    holds_half_box_lob :  likewise  A ≡_Θ (◯⊥)^C

Proof of the first: the spec's lower bound gives A ⊢ C[p] ⊃ p; Θ
gives C[p]; so A, Θ ⊢ p — a p-free context deriving the atom p —
and substituting p := ⊥ through the derivation (`substND`) lands
A, Θ ⊢ ⊥.  For the Löb row Θ derives the translated value `C[⊥]`
outright, and derives A itself via the spec's greatest-property at
the conjunction of Θ.  chain2's §0(m) verdict is corollary
`chain2_holds_half`.

**The dichotomy is complete for Lemma-7-shaped constraints**: with
all pair-names Θ-negated, frame-relative commutation HOLDS on both
frame-changing rows (§0(o)); with some pair at a Θ-avoiding name and
bad-named covers, it FAILS (§0(n)).  The fallibility prediction of
§0(j) is now a pair of THEOREMS, generalising every certified
instance.

### (p) 2026-07-19: the dichotomy at the MODEL level — PROVED (c0Of lifted)

`LaxLogic/PLLSemUIRes.lean`, final section.  Finite models as Boolean
tables (`FinModel`: n, ri, rm, fal); the Lemma-7 recipe in the
library:

    c0Of nm m = one pair (α_u, ⋁{α_v : v a cover of u})
                per Rₘ-stable world u,  α_w := prop (nm w)

with the naming `nm : Nat → String` a parameter (injectivity assumed
where needed — the codebase's own freshness pattern); `falAxioms nm m`
= the fallibility frame theory {¬α_w : w fallible}.  Shape lifts:
`c0Of_thetaNamed` (all stable worlds fallible ⟹ ThetaNamed) and
`c0Of_residuePair` (a non-fallible stable world ⟹ ResiduePair at its
name; needs only Rᵢ-reflexivity, for strictness of covers).  THE
MODEL-LEVEL DICHOTOMY, one iff per frame-changing row
(`model_dichotomy_boxp_imp_p`, `model_dichotomy_box_lob`):

    for ANY finite model m (Rᵢ reflexive), injective naming avoiding
    p, and ANY IsIPCAll-value A of the translated row:

      A ⊢_{falAxioms} translated PLL value
        ⟺  every Rₘ-stable world of m is fallible

(the converse derivations are the trivial/sandwich directions, so
the iff captures commutation).  Coherence pins: `c0Of` with the
probes' naming reproduces `chain2C`/`chain3C` literally (`by decide`).
The §0(j) prediction is now a machine-checked iff at the level it was
conjectured.

### (q) 2026-07-19: the POOL experiment — variant saturations REFUTED (certified)

The pool form of the constraint conjecture tested
(`wip/semui_pool.lean`, `lake exe poolprobe`): candidate value =
`A_a ∧ A_b ∧ A_c`, the meet of the tower ∀-values of M translated by
the Lemma-7 constraints of the model itself (alphabet a), its DOUBLING
(alphabet b), and its 3-level LÖB variant (alphabet c); target = the
translated PLL value, relative to the joint fallibility theory Θpool;
verdicts by the certified two-sided oracle.

VERDICT (chain3, both frame-changing rows; fork pending in the run
log): EVERY pool REFUTED — {a}, {a,b}, {a,c}, {a,b,c} alike — each by
a ONE-WORLD checkB-verified countermodel that forces ALL the residue
names simultaneously (chain3: a0, b3 = the double's (0,hi), c0 = the
Löb variant's (0,level0)).  THE MECHANISM: each conjunct A_i is an
interpolant over its OWN alphabet, so its forcing at a point depends
only on that alphabet — the residue argument applies to each conjunct
independently, and the JOINT residue point (all residue names on,
everything else off) defeats the whole meet.  Disjoint-alphabet
pooling cannot work, for the same one-world reason as single
constraints; `Cmeet`-style pooling (concatenating pairs into one
constraint) is already covered by the PROVED fails-half (the combined
constraint still carries a residue pair).

CONSEQUENCE for the route: the frame-changing content CANNOT be
reached from the constraint side by enlarging the constraint family —
single, frame-relative, meet-pooled, or concatenated.  What defeats
the residue on the semantic side is that `lowT`/`sideT` transform the
FORMULA (mixing `M[⊤]` into implications), not the ◯-interpretation.
The two routes therefore genuinely factor: constraints = the
substitution fragment (sandwich, exact); transforms = the frame
content (irreplaceably).  Obvious capstone target (one lemma away):
generalise `residue` to a set-valued valuation and prove the
disjoint-alphabet pool obstruction outright — the per-conjunct
argument is alphabet-local and composes.

Engineering note: the pool sequents reach weight ~10⁶ (the Löb-variant
towers); the battery + verified checker still certify in
milliseconds — the harness is comfortable three orders of magnitude
above the morning's weight caps.

### (r) 2026-07-19 late: the per-instance reconstruction law, made exact (mainline resumed)

`LaxLogic/PLLSemUILaw.lean`: the law is now a formal object.
`rungsIn M` = the atom-free subformulas of M; the pools

    poolAll p M = {lowT p M, sideT p M} ∪ {M[p:=χ] : χ ∈ ⊥ :: ⊤ :: rungsIn M}
    poolEx  p M = poolAll + the ◯⊥ instance

with candidates `allCandP = ⋀ poolAll`, `exCandP = ⋁ poolEx`.  PROVED
(unconditional in M, audited): the REDUCTIONS

    isSemAll_of_poolRec : [allCandP p M] ⊢ M → IsSemAll p M (allCandP p M)
    isSemEx_of_poolRec  : [M] ⊢ exCandP p M → IsSemEx p M (exCandP p M)

(∀ via the full-basis certificate criterion; ∃ by mapping each
disjunct to its p-variant — truth-set decorations / doubled model /
levelled model, fallible worlds through the ⊥-instance).  The LAW
itself = sorry-free Prop conjectures `ReconLawAll`/`ReconLawEx`
(stated at one variable), with `onevar_definable_of_laws`: the two
laws imply one-variable definability of both quantifiers.  PINNED in
Lean: `pool_reconstructs_peirce` — the per-instance pool reconstructs
the Peirce witness `(◯⊥⊃p)⊃p` that machine-refuted the fixed basis
(the occurring rung ◯⊥ supplies the decisive instance
`(◯⊥⊃◯⊥)⊃◯⊥ ≡ ◯⊥`).

SWEEP (superseding the fueled weight-≤7 sweep): `lake exe lawsweep`
tests the library's own law sequents over all raw 1-variable formulas
to weight 9 with the certified oracle — battery countermodels first
(a REFUTED verdict would be a checkB-verified counterexample to the
law), fuel-free find for positives.  Results recorded below when the
run lands.

### (s) 2026-07-19 night: the sweep corrects the law; clean to weight 8; one frontier row

The certified sweep immediately REFUTED the occurring-rungs-only
formalization: witness `((◯p)⊃p)⊃p` (Peirce pivot ◯p contains p, so
NO closed rung occurs — the pool degenerated to the fixed basis),
one-world-family countermodels checkB-verified; 39 such failures to
weight 8, all in the ◯p/◯◯p-Peirce family; the ∃-law had NO failures
anywhere.  CORRECTED LAW (committed): `poolAll` carries the BASE
rungs ⊥, ⊤, ◯⊥ unconditionally plus the occurring rungs — pinned in
Lean by `rungsIn_peirceBoxP` (`= []`, by decide) and
`occurring_only_insufficient` (the fixed-basis premises do not derive
the witness; `FinCM.not_provable_of_check` by decide on the sweep's
3-world model).

CORRECTED-LAW SWEEP: weights 1–8, 11,708 formulas, BOTH laws —
**zero refutations**; exactly ONE ∀-side UNKNOWN:

    M₀ := ((p ⊃ ◯⊥) ⊃ p) ⊃ p        (weight 8)

battery found no ≤4-world countermodel, `find` exhausted without a
proof — the next frontier row (its Peirce pivot p⊃◯⊥ again contains
p).  Weight 9 pending a longer run.

TIMING CORRECTION (from the reproduction probe, see §0(l) erratum):
the probes' "towers built in 0 ms" lines were an instrumentation
artifact — the compiler inlines used-once pure `let` bindings to
their first use, moving the construction past the timing brackets.
Honestly forced (IO-use between timestamps — a `let`-bound weight is
inlined past the bracket too; two instrumentation rounds were needed):
the fork towers (w 753/1476) really take 8 ms; pool towers a, b take
2–3 ms (raw 18,209 → nf 560); the ENTIRE cost of the pool run is ONE
object — the Löb-variant tower c, raw weight 432,814,618, costing
99.5 s to construct+traverse plus 2.7 s to normalise (nf weight
855,029; compression 506:1).  The VERIFIED checker certifies the
weight-856,179 pool sequent in < 1 ms with inputs pre-forced (the
countermodel has one world, where the checker is linear in formula
size).  Reproduction: `wip/semui_repro.lean`, `lake exe weightrepro`.

### (t) 2026-07-19 midnight: the frontier row settled — the ∀-law is refuted IN LEAN; the third generator is named

`((p⊃◯⊥)⊃p)⊃p`, the sweep's lone UNKNOWN, fully resolved
(`wip/frontier_row.lean`; pins in `LaxLogic/PLLSemUILaw.lean`):

* every closed substitution instance ≡ ⊤ (substitutions contribute
  nothing); `lowT ≡ sideT ≡ ¬¬◯⊥` (four find-term directions);
  ∀p-value = ◯⊥ (rung scan: only ⊥, ◯⊥ derive the row);
* the CERTIFIED countermodel — the 4-chain 0<1<2<3, Rₘ = id ∪ {2→3},
  top fallible, p at {1,2,3} — forces every pool member at the root
  (◯⊥ holds NON-fallibly at world 2, giving ¬¬◯⊥) while refuting the
  row (world 1 forces p without ◯⊥, so only worlds 2, 3 force p⊃◯⊥,
  and both force p);
* PINNED by kernel `decide` (seconds): `nnBoxBot_not_derives_frontier`
  ([propext, Quot.sound]), `poolAll_insufficient_frontier`, and
  **`reconLawAll_refuted : ¬ ReconLawAll`** — the corrected ∀-law is
  itself refuted in Lean.  The ∃-law stands untouched.

Instructive detour, on the record: my first hand countermodel (the
rigid-Rₘ 3-chain) was WRONG — at its middle world ¬◯⊥ holds because
the only ◯⊥-point above is fallible, so the root refutes ¬¬◯⊥; the
battery's silence exposed the error and forced the correct model,
whose key feature is a NON-fallible ◯⊥-world (Rₘ-witnessed by the
fallible top).  That frame family (4-chain, Rₘ rigid except 2→3) was
missing from both batteries and is now added to
`Search.defaultFrames` and the probe battery.

WHERE THE MAINLINE NOW STANDS: the ∀-side basis {substitutions at
rungs, lowT, sideT} is provably incomplete at weight 8 — the row
demands a THIRD frame construction whose level-0 transform descends
to ◯⊥ where both existing transforms stop at ¬¬◯⊥.  The certified
countermodel names its shape: the construction must separate
"◯⊥ non-fallibly above" from "p everywhere above", i.e. a variant
with a fresh Rₘ-side witness one level deeper than the doubling —
the tower of levelled models predicted by the roadmap, now forced at
depth 3.  Also noted: `CounterEmit.emit` missed this countermodel on
the small sequent [¬¬◯⊥] ⊢ row (its closure is within the gate) — an
emitter-incompleteness datum for the tooling ledger.

### (u) 2026-07-20: t₃ designed — the SPLIT variant (one-point cluster duplication)

The third generator is not a doubling at all.  **The split of C at
w₀** adjoins ONE fresh point ⋆ — a duplicate of w₀ sitting strictly
above w₀'s Rᵢ-cluster and below/inside its strict cone — and
decorates p on ⋆'s upset:

    W'  := W ⊎ {⋆}
    Rᵢ' := Rᵢ  ∪  {(x,⋆) : x Rᵢ w₀}  ∪  {(⋆,y) : w₀ Rᵢ y, y ∉ cluster(w₀)}  ∪  {(⋆,⋆)}
    Rₘ' := Rₘ  ∪  {(⋆,⋆)}  ∪  {(⋆,u) : w₀ Rₘ u, u ∉ cluster(w₀)}
    F'  := F;   V'(a) := V(a) ∪ {⋆ if w₀ ∈ V(a)}  (a ≠ p);
    V'(p) := ↑⋆ ∪ F'

    Z   := id  ∪  {(v,⋆) : v ∈ cluster(w₀)}

Zigzag checks (hand-verified, to be mechanised): i-forth from a
cluster point escapes upward to ⋆ or the shared cone; i-back from ⋆
lands in w₀'s cone; m-forth at (v,⋆) matches cluster witnesses to ⋆
itself (⋆ Rₘ' ⋆) and strict witnesses directly; Rₘ' ⊆ Rᵢ' holds
because ⋆'s modal successors are its own reflexive loop plus w₀'s
STRICT Rₘ-successors.  ⋆ inherits every protected atom and w₀'s
fallibility status, so the closed pattern is preserved — as
bisimulation invariance demands.

**Instance check (machine-certified already)**: the split of the
3-chain w < c < f (Rₘ = id ∪ {c→f}, F = {f}) at w IS the 4-chain
0<1<2<3 with Rₘ = id ∪ {2→3}, p at {1,2,3} — literally the certified
countermodel of §0(t): ⋆ = world 1.  At w the antecedent (p⊃◯⊥)⊃p
holds (the only p-free world is w itself, and w ⊭ p⊃◯⊥ because ⋆
forces p without ◯⊥) while p fails — M₀ refuted, with no stray
un-p'd copy of c to break the antecedent (the failure mode of the
plain doubling, whose lower copy of c forces p⊃◯⊥ without p).

**Unification observation**: the split at a non-fallible w also
refutes p ∨ ¬p there (w ⊭ p, and ¬p fails through ⋆) — the depth-1
job.  The split may thus be the UNIFORM generator whose iteration
(split of a split, at deeper points) is the whole transform tower —
de Jongh's generic-point trick surfacing as a construction.

**The syntactic transform** `splT p M` (to be mechanised): evaluate M
at w₀ in the split.  Three mutually-recursive cone-relative
evaluations — at the cluster (t), at ⋆ (s), on the strict cone
(p := ⊤ substitution) — with w₀-anchored ◯-clauses (the ⋆-successor
contributes an ∃-witness condition over w₀'s strict Rₘ-successors).
Equations sketched in the session log; the mechanisation
(splitVariant + PBisim + evaluation lemmas + extended criterion +
`semAll_frontier : ∀p.(((p⊃◯⊥)⊃p)⊃p) = ◯⊥`) is the next work item.

### (v) 2026-07-20 overnight: the split MECHANISED — `∀p.(((p⊃◯⊥)⊃p)⊃p) = ◯⊥` PROVED

`LaxLogic/PLLSemUISplit.lean` — sorry-free, full library green, all
seven theorems ≤ [propext, Classical.choice, Quot.sound]
(`#guard_msgs`-pinned for the two flagships).

**One correction to the §0(u) design, forced by the mechanisation.**
The one-point ⋆ satisfies the pointwise m-zigzag of `ABisim` only when
the cluster of w₀ is trivial.  In a general preorder the zag at a
cluster point v ≠ w₀ must match ⋆'s merged constraint row against v's
own row — impossible when the cluster is Rₘ-inhomogeneous.  The
mechanised form therefore duplicates the WHOLE Rᵢ-cluster of z
isomorphically (`SplitW C z := C.W ⊕ {v // v Rᵢ z ∧ z Rᵢ v}`), the
copies carrying the cluster's internal Rₘ-structure and escaping only
to strict Rₘ-successors of the world each copy duplicates.  On a
poset the cluster is {z} and the §0(u) one-point form is recovered
verbatim.  (A by-product observed en route: cluster collapse is NOT a
bisimulation for the ∀∃ ◯-clause — ◯ sees inside clusters — so the
duplication cannot be quotiented away.)

Contents of the new module:

* `splitModel C z`, `splitSet`, `splitVariant C p z` — the split with
  p on copies ∪ strict cone ∪ F.  All frame conditions PROVED.
* `splitVariant_pbisim` — the projection is a TOTAL p-bisimulation
  (each copy is a p-variant of the world it duplicates); the two
  `by_cases` route an original-side successor to its copy when it
  stays in the cluster, to itself when it escapes.
* `splitVariant_not_frontier` — at any z whose Rₘ-row is
  fallibility-free, `inl z` forces (p⊃◯⊥)⊃p but not p: z's copy ⋆
  forces p but never ◯⊥ (its constraint row is z's own, shifted off
  the cluster), so no cluster world can force p⊃◯⊥.
* `semAll_frontier (p) : IsSemAll p (((p⊃◯⊥)⊃p)⊃p) ◯⊥` — the
  frontier value.  Lower half: below ◯⊥ every future forces p⊃◯⊥
  outright.  Upper half: no ◯⊥ at w ⇒ (classically) some future x has
  a fallibility-free Rₘ-row ⇒ split at x refutes the row at x, and
  the IsSemAll spec's Rᵢ-guard accepts the future directly.
* `semAll_frontierRow` — the same at the pinned `frontierRow`;
  `boxBot_derives_frontier` — ◯⊥ ⊢ the row (previously only a found
  term); `poolAll_not_derives_value` — the transform pool cannot
  derive ◯⊥ at this row (compose with the certified countermodel):
  the split reaches what the pool provably cannot.
* `semAll_em_p_via_split` — ∀p.(p ∨ ¬p) = ⊥ re-proved via the split:
  the copy is the generic p-point.  The split subsumes the doubling's
  value.

**Still OPEN** (next session): (i) whether iterated splits subsume the
levelled construction too (the ◯(◯p⊃p) row) — single splits do not
obviously, since a split point with strict Rₘ-successors gives ⋆ a
◯p⊃p-witness; (ii) the syntactic transform layer `splT` over the
split (the analogue of lowT/sideT feeding the graded law): the copies
form an Rᵢ-blob whose ⊃-clauses are anchored at the cluster rather
than pointwise, so a formula-level transform must absorb the
cluster/strict sort distinction — note the finite canonical model is
a poset, where the trivial-cluster form may suffice; (iii) the graded
reconstruction law itself (downward-closed pivot sets, height =
◯/⊃-alternation conjecture).

### (w) 2026-07-20 overnight: the ◯-free fragment AGREES with IPC; iterated splits provably do NOT reach the levelled row

Two questions from Matthew, both answered.

**1. Do the uniform interpolants of the ◯-free fragment RN({p})
survive the PLL semantic quantifiers?**  YES — agreement with
Pitts's IPC values, theorem-backed and sweep-certified
(`LaxLogic/PLLSemUIOFree.lean` + `lake exe ofreesweep`).

For one variable the IPC values are closed and ◯-free: ⊤ (⊢ M) or ⊥
(⊬ M).  The risk was a ◯-free row acquiring a LADDER value (◯⊥,
¬¬◯⊥, …) — the quantifier escaping the fragment at the ground floor,
which would break the variable-by-variable climb (Matthew: "and if it
fails... so will our semantic approach").

*Necessity half, PROVED (both cones excluded):*

* `topExt C` — fallible top adjoined above everything,
  constraint-reachable from everywhere; `topExt_force_iff`: ◯-free
  forcing at original worlds UNCHANGED (the top forces everything, so
  it never constrains an implication — false for ¬◯⊥, which the top
  destroys); `topExt_boxBot`: ◯⊥ becomes global.  Hence
  `no_lower_bound_above_boxBot`: an underivable ◯-free M has NO lower
  bound in the ◯⊥-cone.
* `flat_neg_boxBot`: fallibility-free models force ¬◯⊥ globally
  (IPC countermodels, read with F = ∅, qualify).  Hence
  `no_lower_bound_above_negBoxBot` (◯-freeness not even needed).
* Corollaries pin the ∀p-value out of both cones
  (`semAll_value_not_above_boxBot` / `_negBoxBot`), give the ⊤-half
  (`semAll_value_of_derivable`), and package the conditional collapse
  `semAll_value_bot_of_cones`: a value in either cone (or ≡ ⊥) IS ⊥.
  Dual ∃-side exclusions: `semEx_value_not_derives_negBoxBot` /
  `_boxBot`.  Remaining OPEN step to the unconditional collapse: the
  two-cone COVERAGE of RN(◯,{}) ∖ {⊥} (every nonzero closed formula
  derivable from ◯⊥ or from ¬◯⊥).

*Evidence half, sweep-certified (weight ≤ 8, 1,758 ◯-free rows,
certified two-sided oracle): ZERO escapes, ZERO unknowns.*  Per row:
no rung among 7 tested ever derives an underivable M (∀-side), no
consistent M ever derives a rung (∃-side), the certified ∀-value
`allCandP` derives ⊥ on every underivable row (670/670 at w8), the
certified ∃-value `exCandP` is derivable on every consistent row and
derives ⊥ on every inconsistent one.  Cone coverage holds for all 7
rungs (section 0).  Note the agreement is not a substitution
triviality: on p ∨ ¬p the ⊥-collapse goes through `lowT` — the
frame-changing transforms are needed even to MATCH IPC on ◯-free
rows.

CONSEQUENCE for the climb: quantifying a variable of a ◯-free formula
stays in {⊥, ⊤} — the fragment tower does not leak at the base.  The
next rung of the climb test would be: one ◯, two variables.

**2. Do iterated splits reach the ◯(◯p⊃p) row?**  NO — machine-checked
(`PLLSemUISplit.lean`, final section, AXIOM-FREE).
`RmClusterInternal` (every constraint arrow stays inside its
Rᵢ-cluster) is preserved by `splitVariant` (internal copy arrows
mirror cluster arrows; an escaping arrow from a copy would contradict
its own strictness) and by `redecorate`, and cluster-internal
constraints force ◯A ⊃ A everywhere.  `SplitTower` (closure under
splits + redecorations) over `oneW` therefore forces ◯(◯p⊃p) at every
world of every member (`splitTower_oneW_forces_lob`) — while
`semAll_box_lob`'s value ◯⊥ demands a refuting p-variant at `oneW`'s
world.  The levelled construction's sideways step 1→2 is exactly an
Rₘ-arrow leaving its cluster — the one thing splits never create.
The transform basis genuinely needs BOTH surgeries (or a common
generalisation creating sideways constraint arrows: the natural
candidate for t-omega).

### (x) 2026-07-20: SUFFICIENCY PROVED — RN({p}) definable with Pitts's values, unconditionally

Matthew: "1,758 examples is impressive, but it ain't a proof."  Now it
is one (`PLLSemUIOFree.lean`, extended; audits pinned):

    ofree_semAll_definable : ∀ M ◯-free with atoms ⊆ {p},
      ∃ ψ, IsSemAll p M ψ ∧ (ψ = ⊤ ∨ ψ = ⊥)
    ofree_semEx_definable  : dually for ∃p

Two model operations, both semantic forms of CONSERVATIVITY (the same
fact as Matthew's q_M-atomisation — lax structure is invisible to
◯-free formulas — read model-side):

* `flatten C`: restrict to the non-fallible part.  ◯-free forcing at
  non-fallible worlds is UNCHANGED (fallible futures force
  everything, so they never constrain an implication) and the result
  is fallibility-free.  Consequence: any PLL countermodel of a ◯-free
  M yields a flat (IPC) one — completeness suffices, no separate
  IPC decision procedure and no proof-theoretic conservativity lemma
  is consumed.
* `ofreeGraft C K p`: fibre a flat model K over an ARBITRARY model C —
  worlds (x, k) above the base cone of x, never returning, Rₘ rigid
  in the K-coordinate, p read from K's decoration, all else from the
  base coordinate.  Base-identity ∪ projection is a total PBisim;
  at a non-fallible fibre the graft forces a ◯-free one-variable θ
  iff K does (fallible fibres absorbed as in `topExt`).

Sufficiency: underivable M → flatten a countermodel (from
completeness, classically) → fibre it over any C → at any
non-fallible w the p-variant world (w, d) refutes M → IsSemAll p M ⊥.
Dually consistent M → IsSemEx p M ⊤.  Derivable/inconsistent halves
hold for ARBITRARY M (`semAll_top_of_derivable`,
`semEx_bot_of_inconsistent`).

STRUCTURAL READING (Matthew's "worth looking deeper" question): within
the ◯-free fragment ONE uniform construction (the fibred graft)
covers every row — the per-row surgeries (doubling, levelling,
split) are a phenomenon of ◯-DEPTH, not of row count.  The graft is
exactly the amalgamation move (implant an external countermodel as a
p-variant while preserving the p-free type); the fragment result
says amalgamation is unobstructed below the first ◯.  The
obstruction begins where the p-free type is rich (the ladder) and
Rₘ-rows must be completed — the ∀∃ ◯-clause.  Next decisive probe
for the climb: the one-◯ two-variable fragment.

### (y) 2026-07-20 afternoon: the PARAMETRIC POINT-ADJUNCTION — one construction, three surgeries

Matthew's probe, mechanised (`LaxLogic/PLLSemUIAdjoin.lean`, sorry-free;
`adjoin_pbisim` AXIOM-FREE, `adjoin_reaches_lob` at the standard three).

    adjoin N n₀ U R : one point ⋆ anchored at n₀ —
      below-⋆ = below-n₀;  above-⋆ = U (up-closed over n₀);
      constraint row {⋆} ∪ R, R ⊆ U closed under Rₘ;
      fallibility + all valuations copied from n₀.

`ABisim.comp` (bisimulations compose) + **`adjoin_pbisim`**: any
p-bisimulation B : PBisim p C N extends along an anchored pair
(z, n₀) ∈ B.Z to the adjoined model, given five cover conditions
routing z's relational data through the accumulated Z.  `mback_cover`
is the PROMISE MECHANISM isolated: ⋆ may constraint-reach any world
Z-equivalent to a constraint successor of its anchor.  Because Z
accumulates, adjunctions ITERATE — later points may cite earlier ones
in U and R.

The three surgery cores, re-derived as instances:

* doubling core (`adjoinAtP_not_em`): strict parameters over a
  non-fallible trivial-cluster anchor refute p ∨ ¬p;
* split core (`adjoinAtP_not_frontier`): the SAME instance refutes
  ((p⊃◯⊥)⊃p)⊃p when the anchor's row is fallibility-free;
* levelled core (`lobTower_not_lob`): the two-storey tower — ⋆₁ over
  z with empty row, then ⋆₂ between z and ⋆₁ with row R = {⋆₁}, the
  sideways promise licensed through the accumulated pair (z, ⋆₁) —
  refutes ◯(◯p⊃p) at a constraint-rigid anchor.
  **`adjoin_reaches_lob`**: instantiated over the one-world model —
  exactly where `splitTower_oneW_forces_lob` proves every split-tower
  variant forces the row.  The R-parameter is the missing degree of
  freedom, isolated as one hypothesis.

Reading: the global surgeries are UNIFORMIZATIONS of these cores over
multiplicities one point cannot carry (fat cluster ⇒ one point per
cluster-mate; levels ⇒ the two-storey core repeated per world/level).
"Constructions that keep changing" compresses to ONE construction
with changing parameters (U, R, iteration depth).  Next climb rung
unchanged: one ◯, two variables — now with the right tool to test
whether a single parametric family covers it.

### (z) 2026-07-20: the AMALGAMATION REDUCTION — the variable-induction skeleton

Matthew's proposal (induction over the propositional variables, base
case = the RN({p}) proofs, inductive step = the same construction),
mechanised as a REDUCTION (`LaxLogic/PLLSemUIAmalg.lean`, sorry-free,
audits pinned).  His "both steps might collapse to one" is exactly
what happened: ONE construction serves every variable count, and the
whole induction is displaced into IPC.

New construction: `relGraft` — the graft ALONG A BISIMULATION.  Given
`B₀ : PBisim p (flatten C) K`, fibre K over C with one world (x, k)
per B₀-RELATED pair: fibres follow both coordinates upward, re-enter
the base only at fallible worlds (which force everything, so never
constrain), p read from K, all other atoms pointwise from the base —
consistent across the fibre because `B₀.atoms` guarantees agreement
on every atom ≠ p.  `relGraft_pbisim`: the graft is a p-variant of C.
`relGraft_force_iff`: a fibre forces a ◯-free θ (ANY atoms) iff K
does at its K-coordinate.

The reduction theorems:

    FlatAmalgAll p M ψ :  every fallibility-free world refuting ψ has
      a future with a p-variant (over fallibility-free models)
      refuting M                       [dually FlatAmalgEx]

    isSemAll_of_flatAmalg : boxFree M → boxFree ψ → p ∉ ψ →
      [ψ] ⊢ M → FlatAmalgAll p M ψ → IsSemAll p M ψ
    isSemEx_of_flatAmalgEx : dually with [M] ⊢ ψ

So for ◯-free M in ANY variables: the PLL semantic spec (over full
constraint models, fallibility and ◯ included) reduces to two
derivability facts + a purely IPC-side amalgamation property of the
candidate.  Fallibility and the ◯-machinery are discharged once and
for all by flatten + relGraft; what remains per variable count is
IPC's own amalgamation — where Pitts/Ghilardi live.

The loop closes: `flatAmalgAll_bot` discharges the amalgamation for
the one-variable value ⊥ via the fixed-countermodel graft, and
`semAll_ofree_bot'` re-derives the RN({p}) theorem through the
reduction — the base case IS the skeleton at the constant family.

OPEN (the genuine content of the induction): `FlatAmalgAll p M ψ₀`
for multi-variable ◯-free M with ψ₀ = Pitts's ∀p.M (e.g. the
mechanised `uniform_interpolation_IPC` value) — the SEMANTIC
amalgamation property of the IPC interpolant, natural route:
Ghilardi-style bounded-bisimulation descriptions over the finite
canonical model.  Note the wip crown cannot be imported into the
library (olean side-channel); the instantiation belongs in a wip
probe first.

### (aa) 2026-07-20 afternoon: the BOX-COMMUTATION LAW proved (residues isolated) + the one-◯ two-variable sweep CLEAN

**The law** (`LaxLogic/PLLSemUIBox.lean`, sorry-free; `semEx_box` at
[propext, Quot.sound] — choice-free):

    semAll_box : IsSemAll p φ ψ → BoxRowAmalgAll p φ ψ → IsSemAll p ◯φ ◯ψ
    semEx_box  : IsSemEx p φ ψ → BoxRowAmalgEx p φ ψ → IsSemEx p ◯φ ◯ψ

Each side has a FREE half proved unconditionally inside the theorem
(∀-forward: transfer ◯ψ across the bisimulation, each ψ-witness forces
φ by its own spec at the identity variant; ∃-backward: i-forth the
future, take the ◯φ-witness, m-back it, conclude by the ∃-spec).  The
hard halves are isolated as residues with all quantifier machinery
discharged — pure model surgery:

    BoxRowAmalgAll p φ ψ : a row refuting ψ pointwise amalgamates into
      ONE p-variant refuting ◯φ at the row's base
    BoxRowAmalgEx  p φ ψ : pointwise ψ-witnesses in every future row
      amalgamate into ONE p-variant forcing ◯φ

— exactly the ∀∃-amalgamation where the canonical-model descriptions
(Θ-promises) must enter.  CONSEQUENCE for the induction: the ◯-clause
reduces to the residues; ⊃ and ∨ remain the genuinely
quantificational connectives, the same division of labour as IPC.

**The sweep, definitive at weight ≤ 5** (`lake exe oneboxsweep`; 214
p-relevant rows over {p,q} with ≤ 1 ◯; p-free rows excluded as known
fixpoints; 24-element slice; certified two-sided verdicts):

    no-∀-max 0, no-∃-min 0, pool⊬M 0, pool⊬value 0, unknowns 0

Fragment PRESERVED: every ∀/∃-value lies in the one-◯ slice over q.
Values are COMPOSITIONAL throughout: box-commutation on every ◯-head
(∀p.◯(p∨q) = ◯q, ∀p.◯(q⊃p) = ◯¬q, …) and pointwise laws elsewhere
(∀p.(◯p∨q) = ◯⊥∨q, ∀p.(q⊃◯p) = q⊃◯⊥, ∀p.(◯q⊃p) = ¬◯q,
∀p.(◯p∧q) = ◯⊥∧q-form q∧◯⊥).  ∀-histogram: ⊥ 57, ⊤ 54, q 51, ¬q 18,
◯⊥ 17, ◯q 6, q∨¬q 2, q∧◯⊥ 2, q∨◯⊥ 2, ¬¬q/¬◯⊥/¬◯q/◯¬q/q⊃◯⊥ 1 each.
Tower coverage: the CURRENT stock (7 instances + lowT + sideT)
derives every row and every value — no new adjunction towers demanded
at this weight (1-var frontier appeared at w8; deeper weights remain
the true test).  Weight-6 partial: every ◯-row listed conforms to
box-commutation (incl. ◯(¬q⊃p) → ◯¬¬q, a slice-gap not an escape);
one w6 bound-cell defeats the current engine (silent find-grind).

Harness lessons (3 grind episodes this session): countermodel-first +
extended 23-frame battery + weight-gated decide2 + monotone pruning
(proofs propagate down the slice order, refutations up) took the
order matrix 16.8 s → 143 ms; residual wall = find on
unprovable-but-battery-missed cells and a 25-premise PROVABLE pool
sequent (left-rule thrash).  Feature chip spawned: node-budgeted
prove? for PLLSearch.

### (bb) 2026-07-20: the correspondence with the syntactic route's blocking lemma

Matthew's question: do the three open amalgamation statements relate
to `cascade_low_pos_box` (the sole sorry of the v3.1 syntactic
tower)?  YES — same mountain, two faces; the dictionary:

    syntactic (v3.1 tower)                semantic (this route)
    ------------------------------------  ------------------------------
    seals: γ-guards ◯(E⇢A), ◯-goal        the promises Θ / the Rₘ-row
      disjuncts committed before descent    that must be completed
    seen-sets cannot cross a seal         bisimulation data must be
                                            re-established inside the
                                            Rₘ-successor = BoxRowAmalg
    burned room cannot fund fresh          p-decoration freedom is a
      J+1 allotments (budget deficit)       shared resource (the 1-pv
                                            clash semEx_and_pointwise_
                                            fails, machine-checked)
    jump budget b                          bounded-bisimulation rank
    cascade_main_bf: box-free PROVED       FlatAmalg: IPC-standard
    dispatcher: residue provably about ◯   reduction: residue = the two
      (cascade_low_pos_box)                  BoxRowAmalg statements

Differences that matter: the syntactic lemma is QUANTITATIVE
(stabilisation at the explicit floor defect·(J+2)); the semantic
residues are qualitative (one amalgamated variant exists, no rank
ledger) — dropping the ledger is exactly why this route moves.  A
semantic win would make the floor moot: definability + uniqueness +
completeness force the syntactic approximants to stabilise up to ⊣⊢
at SOME per-instance finite budget, re-founding the tower without the
uniform floor arithmetic.  On dilators: the evidence (b = 2
stabilisation, five-class state spaces, per-instance finite support,
the clean fragment tables) says finite-rank description combinatorics
(Ghilardi), not ordinal machinery — the budget was the shadow price
of decoration freedom, not an ordinal.  And the week's constructions
are a toolkit aimed at the row-completion: `mback_cover` is the
promise license the syntactic seals lacked, made a dischargeable side
condition.

### (cc) 2026-07-20: first wave at the residues — the promise class discharged, first LAW-GENERATED values

The attack on the `BoxRowAmalg` residues opens where the machinery
already speaks the canonical language: the levelled model IS the
Θ-descriptions in model clothing (its docstring has said so since
§0(f)); level-0 constraint-rigidity is "a row all of whose promises
are withheld".  `PLLSemUIBox.lean` (extended; full build green;
audits pinned):

* `Lob0Refutes p φ` — φ refuted at level 0 of the Löb variant over
  every non-fallible base: the decoration-refutable class.
* `boxRowAmalgAll_lob0 : Lob0Refutes p φ → BoxRowAmalgAll p φ ⊥` —
  the ∀-residue discharged on that class (a fallibility-free row at
  level 0 has no φ-forcing member, so ◯φ fails at the base; the
  projection bisimulation anchors it).
* Instances `lob0_prop`, `lob0_em`, `lob0_nn` — and the law GENERATES
  values:

      ∀p.◯(p ∨ ¬p) = ◯⊥     (semAll_box_em — NEW)
      ∀p.◯(¬¬p ⊃ p) = ◯⊥    (semAll_box_nn — NEW)
      ∀p.◯p = ◯⊥            (semAll_box_p' — re-derived; agrees with
                              the direct semAll_box_p: consistency)

* ∃-side: `boxRowAmalgEx_prop` (decorate p everywhere) and
  `semEx_box_p' : ∃p.◯p = ◯⊤` (⊣⊢ the direct value ⊤ of the theory
  file's semEx_box_p, by uniqueness).

NOT covered, and honestly so: φ = ◯p ⊃ p fails `Lob0Refutes` (a
level-0 row may lack ◯p entirely, making the row formula vacuous);
`semAll_box_lob` reached it through the level-1 argument.  The
SECOND WAVE — the general residues via the finite canonical model —
needs the canonical-cone graft: adjoin the canonical model's cone
over a closure triple (Γ, Δ, Θ) above a world realising its p-free
description, discharge forcing by the truth lemma, and the
description-matching condition is where Γ/Δ/Θ earn their keep.  That
is the programme's centre of mass now.

Chip-protocol lesson (Matthew's note): spawn_task sessions report to
HIM; future chips must carry in-prompt: commit-to-branch, summary
file, completion signal — or use Agent-tool subagents for work that
must return here.  The node-budget chip is running; on its completion
signal I fetch and merge its branch directly.

### (dd) 2026-07-20: SECOND WAVE LANDED — the description graft, complete machine

`LaxLogic/PLLSemUIDesc.lean` (sorry-free, audits pinned, full library
green) — the canonical-cone graft in its general form, built and
PROVED in one session-tail:

* `DescPack C K p dom` — the description-realisation relation with
  bisimulation-style clauses: atom-agreement only on the tracked
  alphabet `dom` (for `canonFin cl`: the closure — this dissolves the
  filtration problem: no direct `PBisim C (canonFin cl)` can exist
  because canonFin forces every out-of-closure atom; on the graft all
  protected atoms read the BASE coordinate), `fall`, `iforth` (with
  fallible-base escape), `kback`, `mforth` (pairing fallible base
  escapes with fallible K-witnesses — the promise-side fallibility
  cover), `mback` (with fallible escape).
* `descGraft P` — base ⊎ R-fibres; fibres climb both coordinates
  (K-side Rᵢ-edges relaxed into fallible K-worlds so fallible-base
  paths re-enter legally; Rₘ-edges strictly PAIRED — the ◯-case
  demanded it); fibres exit to the base only at fallible worlds; `p`
  redecorated from the K-coordinate.
* `descGraft_pbisim` — the graft is a p-variant (projection; consumes
  NO agreement clauses).
* `descGraft_force_iff` — a fibre forces θ iff its K-coordinate does,
  ◯ INCLUDED.  The two fallibility absorptions carry the ◯-cases: a
  fallible base witness pairs with a fallible K-witness by `mforth`;
  an unpaired fallible K-future is itself fallible in the graft by
  `fall`.
* `boxRowAmalgAll_of_desc` / `boxRowAmalgEx_of_desc` — **the
  residues reduce to pack-existence**: per (C, x), a pack into some K
  and a K-world refuting (resp. forcing) ◯φ paired with x.

With K := `canonFin cl` and the truth lemma, the whole of the ◯-step
of the definability induction now rests on FINITE COMBINATORICS:
exhibit a closure triple with ◯φ ∈ fal (resp. ∈ val) realised over
the given world by a DescPack.  Constructing that pack — the
descriptions functor c ↦ trace(c) and its m-clauses — is the
remaining open mathematics, now a decidable-per-closure target the
oracle can probe row by row.  Subsumption note: ofreeGraft/relGraft
are morally the box-free flat instances of descGraft; the older files
stand as the simpler self-contained forms.

Also merged this round: the node-budgeted search from the chip session
(branch claude/agitated-nobel-443fbd, commit 7e1f1b2): proveBounded /
findBounded / prove?Bounded + Config.findBudget; find is a `mutual
partial def` with a visited-set (NOT well-founded recursion — the
chip corrected my misstatement; PLLSearchEx.lean's limitation note
still carries the wrong attribution — Matthew's file, flagged not
edited).

## §0(ee) The descriptions functor, the realisability gfp, and the probe verdict (2026-07-20 pm)

The "remaining open mathematics" of §0(dd) — the pack for K :=
`canonFin cl` — was built, measured, and REFUTED as the route; the
day ends with the route corrected and the gap row's residue
probe-supported.  Everything below `LaxLogic/PLLSemUITrace.lean`
(sorry-free, pins standard three; `packRel_realises` axiom-FREE) plus
two compiled probes (`wip/desc_probe.lean`, `wip/resid_probe.lean`).

**(i) The functor.**  `trace C cl c` := the closure description
⟨{χ ∈ cl | c ⊩ χ}, {χ ∈ cl | c ⊮ χ}, {χ ∈ cl | row(c) ⊮ χ}⟩, a
`MaxIn` triple — consistency by `cons_of_countermodel` (soundness
evaluated at c itself).  Of the six pack clauses the functor satisfies
exactly the four forth-and-safety ones, each PROVED: `trace_atoms`,
`trace_fall`, `trace_iforth`, and `trace_mforth` — the last the design
validation of the `mfal` component (promises propagate along Rₘ by
transitivity; descriptions are functorial for BOTH relations).  The
two back clauses FAIL, machine-checked on two-world instances
(`trace_kback_fails`, `trace_mback_fails`): the canonical model is
more saturated than an arbitrary base.  The functor is a lax morphism,
not a bisimulation.

**(ii) The gfp.**  All six pack clauses use R only positively, so
packs are closed under unions: there is a LARGEST pack,
`Realises C K p dom` (`packRel_realises`, axiom-free), and pack
EXISTENCE is absorbed — `boxRowAmalg{All,Ex}_of_realises` reduce each
residue to one membership per (C, x): a closure triple with ◯φ ∈ fal
(resp. ∈ val) Realises-related to x.  Necessary condition PROVED
(`realises_val_iff`): a realised triple's p-free part IS the p-free
trace — all realisation freedom is p-relevant.

**(iii) The pre-triple sandwich.**  `preTripleAll C cl p x φ` :=
⟨pfval(x), {◯φ} ∪ pffal(x), pfmfal(x)⟩ (p-free description of x
seeded with ◯φ falsified; dually `preTripleEx` with ◯φ validated).
PROVED both ways: the residue at (C,x) forces its consistency
(`preTriple{All,Ex}_cons_of_residue` — the killing variant's world is
the countermodel; p-free content crosses the bisimulation, the row
crosses mback), and consistency yields a closure-maximal extension
with the p-free part pinned, promises preserved and ◯φ placed
(`preTriple{All,Ex}_extend`, constructive lindenbaum).  So per
instance: residue ⟹ Cons(preTriple) ⟹ candidate triples exist;
candidate realised ⟹ residue.  The gap between the two arrows is
exactly realisability.

**(iv) The probe verdict on the gap (desc_probe, 9 proved-value rows,
90 decorated battery instances each, canonical worlds enumerated by
the budgeted two-sided oracle — consistency is ONE maximal sequent
per triple by disjOf-monotonicity).**  NO-CAND = 0 everywhere: the
syntactic crux held at every qualifying instance (matches necessity +
the proved residues).  But the ∀-side gfp is EMPTY on every instance
(alive = 0 of 1752–10074 candidates; even the trace itself never
survives), and the ∃-side survives only on the fallible-dominated
63–108 of 333 points.  Kill-chain isolated: canonical Rᵢ is
val-inclusion ONLY, so kback demands realisation of
promise-FORGETTING extensions (mfal := ∅); those must in turn realise
⟨cl∖{⊥}, ∅⟩, whose mback demands the exploded triple T⊥ ON THE ROW —
possible only over fallible row-worlds; over F-free rows everything
dies, and the death cascades down every kback chain.  The
rank-stratified reading (synchronous pruning rounds = bounded-rank
packs) dies by round 3 with a FORMULA-INDEPENDENT profile
(98/31/0 of 219 across ALL rows): stratification cannot rescue the
raw canonical target either.  VERDICT: K := full `canonFin cl` is
dead as the graft target for arbitrary C.  The graft machinery is
untouched — the correction is the choice of K.

**(v) The route corrected: canonical triples classify, small gadgets
kill (resid_probe).**  Probing the ∀-residue DIRECTLY per (frame, x)
— the p-decoration of C enters nowhere, all clauses are p-blind —
with the gadget family "chain of ≤ 2 points adjoined above x, exits
into the cone, in-chain and sideways Rₘ, free hereditary
p-decoration", the largest p-blind bisimulation computed as a gfp:
FAIL = 0 on all rows.  Calibration: the three discharged rows need
k ≤ 1.  THE GAP ROW `∀p.◯(◯p⊃p)`: all 47 instances discharged —
9 by redecoration, 18 by one point, 20 by the two-point tail
x ≤ a ≤ b with Rₘ a b in-chain and b's sideways m-exit into base
p-material — exactly the `lobTowerBase` shape already mechanised in
PLLSemUIAdjoin.  So `BoxRowAmalgAll p (◯p⊃p) ⊥` is probe-supported
TRUE with a 3-case gadget family, and the law value
`∀p.◯(◯p⊃p) = ◯⊥` is supported.  (One earlier FAIL was an artefact:
the onebox fork frames are NOT transitively closed as listed — the
`Frame` contract assumes closure; both probes now close frames on
intake.  The sweep results are unaffected — unclosed battery members
can only fail the verifier, never certify.)

**The corrected ledger for the ◯-step.**  The canonical triples
remain the CLASSIFIER (finitely many pre-triple classes per closure;
the consistency crux is the class condition, PROVED necessary), while
the DISCHARGE is by small adjunction-tail families per class — the
Lob0Refutes pattern, now with probe-derived shapes for the gap row.
Next opener: mechanise the gap row's 3-case discharge
(redecorate / 1-point / 2-point tail) as a Lob0-style class lemma in
the adjoin framework, deriving `∀p.◯(◯p⊃p) = ◯⊥` via `semAll_box`;
then extract the general per-class tail-synthesis principle from the
probe's shape data.

**§0(ee) addendum — mechanisation design notes for the class lemma
(same evening).**  (a) The gadget probe decorates no atom but p, so
its DIRECT-PBisim verdicts are blind to q-flips above x: a tail point
carries one fixed q-valuation but Z-pairs with many base worlds, so
for atom-rich C the naked gadgets fail the atoms clause.  This does
NOT invalidate the route: for single-variable rows the tracked
alphabet can be dom := ∅ (the discharge's hypothesis
`∀ q ∈ φ.atoms, q ≠ p → dom q` is vacuous for φ over {p}), and then
`DescPack`'s atoms clause vacates entirely — mechanise via
`descGraft` with K := the SMALL ABSTRACT TAIL (2–4 points), where
fibres read all atoms from the base by construction.  The probe's
shapes are then the R-relation's picture, valid for ALL C.  (b) The
remaining K-design care is the m-row fallibility escapes: `mforth`
from a paired world whose row meets F needs a fallible K-witness
(`u ∈ F ∧ s ∈ K.F`), but a fallible K-point must stay OFF the kill
spine's m-rows (it would force ◯p⊃p there).  So K wants a kill spine
γ ≤ α ≤ β (rigid γ-row; Rm α β; p at β) plus a fallibility park
reachable by Rm from the PARKING points only, with the pairing
R c γ/α/β/park chosen by c's position relative to x and its row.
Next session: extend the gadget probe with a q-decorated battery (to
watch the atoms clause directly), pin K on paper from the probe
shapes, then mechanise the pack (fall + four transfer clauses, atoms
vacuous) — the discharge is `boxRowAmalgAll_of_desc` with dom := ∅.

## §0(ff) The pillar ledger after the Litak–Visser adaptation (2026-07-20 night)

PROVED sorry-free: rank preservation (`force_iff_of_layered`, ◯ costs
2 under the ∀∃-clause) with the unbounded-invariance consistency
corollary; fragment finiteness (`frag_reps_exist'`,
PLLSemUIFrag.lean — Deriv/Interd calculus, DNF over components,
canonicalisation); the Henkin scaffold (PLLSemUIHenkin.lean —
canonDepth strict drop, WitTriple, witAmalgam with descGraft-style
valuation and all frame legality, `amalgamation_assembled` from two
claims); and the REFUTATION `layered_of_frag_agree_refuted` —
Litak–Visser Thm 4.7 is false over constraint models (chainF
conservativity: a fallible top with a trivial row is invisible to
formulas, but not to the fall zigzag).

The redesign boundary, exactly: (i) pointwise fall at linked pairs is
agreement-derivable (⊥ has rank 0) — only the ZIGZAG INTO fallible
successors fails; (ii) escape-iforth (partner or fallible successor,
DescPack style) survives the character argument, since a non-fallible
successor refutes its θ⁻; (iii) the consumer inventory of Lemma 5.4:
its Claim 1 uses the M-to-K zags (iback/mback) — into the CANONICAL
side, where the response is financed by canonical saturation and
membership reasoning, not by expressibility; its Claim 2 uses the
K-to-M forths for both relations.  So the single genuinely open
clause is FORTH-M FROM AGREEMENT: given rank-agreement of (Δ, m) and
a canonical row-member of Δ, must m's row contain a rank-lower
agreeing partner (or a fallible escape)?  Detection arguments keep
succeeding on candidate counterexamples (a distinctive row-member
changes ◯-truths), but no character derivation is in hand — status
OPEN, and probe-able: enumerate finite pointed pairs agreeing on the
rank-R variable-free representatives (forceB over the frag list),
then test forth-m directly.  That probe is the recorded next
computational step; the mechanisation next step is the weakened
LayeredBisim (escape clauses) with rank preservation re-proved (the
escapes absorb exactly as in descGraft_force_iff).

## §0(gg) Pillar 2: i-clauses proved; the m-clause analysis (2026-07-20 night V)

PROVED (PLLSemUIChar.lean, pins standard three): `agree_iforth` /
`agree_iback` — the character argument delivers the escape-form
i-zigzags from fragment-agreement at budget 2α+2; and
`layered_of_frag_agree_W` is ASSEMBLED with Z α := agreement at rank
2α, every clause proved except the two weak m-clauses (sorried;
probe: 2324 agreeing pairs, 0 violations, now under randomised
extension).

Why the m-clause is the genuinely hard one — the ∀∃ divergence:
Litak–Visser's Lewis arrow has a PURE-∀ forcing clause, so their
Thm 4.7 covers the modal zigzag by the same implication-character
argument as ≼.  PLL's ◯ is ∀∃: the ∃-component makes m-rows
formula-invisible (no PLL formula quantifies over ONE world's row —
row-membership is not hereditary), so there is no implication of
characters whose failure exhibits a row-partner.  Near-miss recorded:
χ := θ⁺ ∧ (θ⁻ ⊃ ⊥) is a formula, but the row-member u need not force
θ⁻ ⊃ ⊥ (θ⁻ can hold strictly above u) — intuitionistically there is
no exact-type formula, only up-set characters.  Note Rₘ ⊆ Rᵢ gives,
via the PROVED agree_iforth, an i-partner of the row-member; the gap
is precisely i-partner vs m-partner.  Candidate resolutions: (a) the
pure statement is true with an Rₘ-specific semantic argument (the
randomised hunt bears on this); (b) the W-form m-clauses are bypassed
entirely — the amalgamation consumes m-moves only at canonical-side
pairs, where the theory coordinate's PROMISES (mfal) finance the row
witnesses (trace_mforth is the proved prototype).  Route (b) is
independently needed for the wit_force ◯-case, so it is the default.
