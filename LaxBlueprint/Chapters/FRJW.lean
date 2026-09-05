import Verso
import VersoManual
import VersoBlueprint
-- The import runs ONE WAY: this chapter imports the development; no file of
-- the development imports verso.  That is what keeps verso out of the
-- ordinary build graph.
import FRJ.CalculusW
import FRJ.SoundW
import FRJ.Gbu.Circ
import FRJ.Gbu.W.Search
import FRJ.Gbu.W.Saturate
import FRJ.Gbu.W.LaxND
import wip.gbu_weakening
import wip.gbu_search_circ
import wip.rbar

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Gbu◯ and FRJW: proof, disproof, and the decision procedure" =>

These two calculi are one object and should be read as one.  `Gbu◯(G)`
proves; `FRJW(G)` disproves; both live over the signed subformulas of a
single fixed goal `G`, and every rule of one is mirrored by a rule of the
other.  Run together they decide `G`: for every formula, either a proof or
a countermodel, with no appeal to choice.

The duality is due to Fiorentini and Ferrari (*Duality between
unprovability and provability in forward proof-search for Intuitionistic
Propositional Logic*, ACM TOCL 21(3), 2020); the `◯`-extension on both
sides is ours.

A register point that prevents a great deal of confusion, and which the
sources hold to strictly: *an object of `FRJWr` or `FRJWi` is a
disproof.*  "Proof" and "derivation" are reserved for `Gbu◯` — and for
`LaxND`, `G4c` and `SC` elsewhere in the development.

# The calculus

:::group "frjw_calc"
FRJW is FRJV with one rule added and one deleted.
:::

:::definition "lift_rule" (parent := "frjw_calc")
*Lift.*  A regular disproof becomes an irregular one over any retained
`Ĝ`-context inside the closure of its own context:
$$`\frac{Γ ⇒ C \qquad Θ ⊆ Ĝ,\; Θ ⊆ \mathrm{Cl}(Γ)}{∅ ; Θ → C}`
Soundness is monotonicity of forcing: the component's root sits above `w`
and refutes `C`, so `w` refutes `C`.

The rule $`⊃∉` is deleted, being Lift composed with $`⊃∈`; $`◯∉` is kept,
since its premise is a regular disproof of `Z` rather than of `◯Z`, so it
climbs the modality where Lift does not.
:::

:::definition "regular_irregular" (parent := "frjw_calc")
The two families, and why there are two.  A *regular* disproof is
existential: the extracted model refutes the goal at its own root.  An
*irregular* disproof is schematic: the goal fails at any infallible world
of any premodel meeting the interface.

The joins $`⋈^{At}`, $`⋈^{∨}`, $`⋈^{◯}` build a *fresh* root and need
their premises to fail there, at a world the join has just constructed.
Only the schematic reading gives that, which is why join premises are
irregular — and why {uses "lift_rule"}[] is needed to get from a regular
disproof to a usable premise.
:::

:::theorem "duality_hole" (parent := "frjw_calc") (tags := "motivation") (lean := "FRJ.V.WCounter.no_irregular_circ_imp_self")
FRJV has *no* irregular disproof of $`◯(◯Z ⊃ Z)`, for any `G`, `Z`, `Σ`,
`Θ`.  Only $`◯∉` and $`Ax^{I◯}` conclude a `◯` goal; the former needs a
cleanly tagged regular disproof of $`◯Z ⊃ Z`, and the latter needs
`classForce` to reject a body of the form $`¬x ∨ x`, which it cannot,
because `◯` is transparent to `classForce`.
:::

:::theorem "gbu_gap" (parent := "frjw_calc") (tags := "motivation") (lean := "FRJ.Gbu.not_gbuIC_Gcc")
`Gbu◯` cannot fill the hole either: $`∅ →_g ◯(◯p ⊃ p)` is not derivable.
:::

:::theorem "provable_gcc" (parent := "frjw_calc") (tags := "motivation") (lean := "FRJ.Gbu.provableV_Gcc, FRJ.V.RBar.not_force_of_rootAbove")
A *regular* FRJV disproof of $`◯(◯p ⊃ p)` does exist, by the barren
$`⋈^◯` join — but it cannot be used where an irregular one is required.
Together with {uses "duality_hole"}[] and {uses "gbu_gap"}[] that is the
mismatch {uses "lift_rule"}[] removes.

The Lift clause of `lemma39I` was checked separately, and
negative-tested: the same one-line proof does *not* typecheck for a
tagless $`◯∉`, so the gate discriminates rather than passing everything.
:::

# The stages

:::group "frjw_stages"
Transcription, conservativity, soundness.
:::

:::theorem "w1_calculus" (parent := "frjw_stages") (lean := "FRJ.FRJWr, FRJ.FRJWi, FRJ.DisprovableW")
The two FRJW families and the disprovability judgment, obtained from FRJV
by adding {uses "lift_rule"}[] and deleting $`⊃∉`.  The stage gate is
`#slime` reporting zero computed indices in the return type of every
constructor of both families.
:::

:::theorem "w2_conservativity" (parent := "frjw_stages") (lean := "FRJ.disprovableW_of_provableV")
*Conservativity over FRJV.*  Every FRJV disproof is an FRJW disproof.  The
only non-trivial case is $`⊃∉`, reconstructed as `lift (impIn d hA _) hTh`.
Proved before soundness, because it is what licenses reusing the FRJV
corpus.
:::

:::theorem "w3_soundness" (parent := "frjw_stages") (lean := "FRJ.soundnessW")
*Soundness.*  A disproof yields a refutation: `DisprovableW G → ¬ PLL G`.
The conclusion is against the wider fallible class, because the fallible
join builds a model with a fallible world.

The Lift case of `lemma39I` was already available; the real obligation was
the joins', each of which must still discharge its `RootAbove` premise for
components now supplied by {uses "lift_rule"}[].
:::

# Cells, and the search that moves between them

:::group "frjw_cells"
The finite grid the decision procedure walks.
:::

:::definition "cell" (parent := "frjw_cells")
A *cell* is a triple `(mode, Ψ, C)`, naming one sequent of `Gbu◯(G)`
together with its judgment: `(true, Ψ, C)` is the regular $`Ψ ⇒_g C`,
`(false, Ψ, C)` the irregular $`Ψ →_g C`.  The same context and goal give
two different cells, and they are decided differently.

The word is apt because the cells form a finite grid.  A cell is
well-formed for `G` when $`Ψ ⊆ \mathrm{Sf}^L(G)` as a set and
$`C ∈ \mathrm{Sf}^R(G)`, so up to the set-reading of contexts there are at
most $`2 · 2^{|\mathrm{Sf}^L(G)|} · |\mathrm{Sf}^R(G)|` of them.  The
search never leaves the grid: every recursive call is at a well-formed
cell, which is why the two well-formedness hypotheses are re-established
at every step.

A cell is *critical* when every context member lies in `Ĝ` — atoms,
implications, `◯`-formulas — so no invertible left rule applies.  The
regular critical cells are where the paper's GBU(G) does its real work;
the irregular critical cells with a `◯`-goal and no modal member are the
*corner*.
:::

:::definition "measure" (parent := "frjw_cells")
The measure of a cell is the lexicographic triple
$$`\mathrm{wgC}\,G\,\mathrm{reg}\,Ψ\,C \;=\; (\mathrm{unclosed}\,G\,Ψ,\;\; \mathrm{tpC}\,\mathrm{reg}\,C,\;\; \mathrm{seqSize}\,Ψ\,C)`
where $`\mathrm{unclosed}\,G\,Ψ = |\mathrm{Sf}^L(G) ∖ \mathrm{Cl}(Ψ)|`,
$`\mathrm{tpC}` is 2 for a regular cell, 1 if `◯` occurs in the goal and 0
otherwise, and $`\mathrm{seqSize}` is the total formula size.  Every
recursive call goes to a cell of strictly smaller measure, and the order
is well-founded.

TO WRITE — the three components pay at different snapshots, and saying
which pays where is what makes the termination argument readable rather
than merely checkable.  §4 of `docs/frjw-explainer.md` has the trace.
:::

:::theorem "dichotomy_cell" (parent := "frjw_cells") (lean := "FRJ.Gbu.W.searchW, FRJ.Gbu.W.dichotomyW")
The dichotomy at cell level.  `searchW` proves, for every well-formed
cell, the Type-valued statement `WSearchOk`: *if the store does not
refute the cell, one can build the `Gbu◯` derivation of it.*  Type-valued,
so it delivers the derivation rather than asserting its existence.

`FRJ.Gbu.W.searchW` and `FRJ.Gbu.W.dichotomyW`
(`FRJ/Gbu/W/Search.lean`), pinned `[propext, Quot.sound]`.
:::

# The inversion bank: where the duality actually lives

:::group "frjw_bank"
One lemma per rule, and each one is the other calculus.
:::

:::proposition "inversion_bank" (parent := "frjw_bank") (lean := "FRJ.Gbu.W.gbuInv5")
This is the conceptual centre, and it is short enough to state whole.

At every cell the searcher asks the store a question and, on a negative
answer, takes one `Gbu◯` step and recurses.  For that to be sound each
recursive call needs a negative answer at its own cell, obtained by
contraposing a lemma of the form
$$`(\text{the store refutes the premise}) \;→\; (\text{the store refutes the conclusion})`
one per `Gbu◯` rule.  Contrapositively: if the conclusion is not refuted,
neither is the premise — exactly the hypothesis the recursive call needs.

Every proof in the bank is the same small move: unpack the store's answer
at the premise, take the *disproof* it stands for, apply one FRJW rule to
it, and put the result back.  So:

> each inversion lemma is literally the FRJW rule that mirrors one `Gbu◯`
> rule, stated as a fact about the store.

That is the duality, one rule at a time — and it is why the two calculi
cannot sensibly be presented apart.  `gbuInv5` is eleven lines and has the
shape of every other member: the `Gbu◯` rule `R⊃` takes $`Γ ⇒_g B` to
$`Γ ⇒_g A ⊃ B` under $`A ∈ \mathrm{Cl}(Γ)`; the FRJW rule $`⊃∈` takes
$`t : Γ ⇒ B` to $`t : Γ ⇒ A ⊃ B` under the same side condition.  Same
premise, same conclusion, same side condition, on the two sides.

The bank is consumed in exactly two ways: as a *closer*, where a scan comes
back positive on every branch and the resulting store row contradicts the
standing negative fact; and as a *payload*, supplying a recursive call's
negative hypothesis.  Nine sites and fourteen sites respectively.
:::

# The crown

:::group "frjw_crown"
What the two calculi deliver together.
:::

:::theorem "crown" (parent := "frjw_crown") (lean := "FRJ.Gbu.W.frjw_complete, FRJ.Gbu.W.gbuw_complete, FRJ.Gbu.W.decidePLL, FRJ.Gbu.W.provableGbuC_iff_pll, FRJ.Gbu.W.disprovableW_iff_not_pll")
After the closure and saturation stages have built a concrete saturated
store for every `G`:

* `FRJ.Gbu.W.decideGbuW` — `ProvableGbuC G ⊕' DisprovableW G`
* `FRJ.Gbu.W.decideGbuWData` — the same, delivering the objects
* `FRJ.Gbu.W.decidePLL` — `Decidable (PLL G)`
* `FRJ.Gbu.W.frjw_complete` — `¬ ProvableGbuC G → DisprovableW G`
* `FRJ.Gbu.W.gbuw_complete` — `¬ DisprovableW G → ProvableGbuC G`
* `FRJ.Gbu.W.provableGbuC_iff_pll` and `disprovableW_iff_not_pll`

all pinned `[propext, Quot.sound]`.  Against the Fiorentini–Ferrari paper,
the ledger in `FRJ/Gbu/Circ.lean` records Theorem 8 (correctness of
`BSearch`), Theorem 9 (the duality) and Theorem 10 (completeness of both)
as *closed for FRJW*, with `decidePLL` going beyond the paper.

Depends on {uses "dichotomy_cell"}[] and {uses "inversion_bank"}[].
:::

:::theorem "crown_syntactic" (parent := "frjw_crown") (lean := "FRJ.Gbu.W.PLL_iff_laxND, FRJ.Gbu.W.finite_poset_model_property, FRJ.Gbu.W.decideLaxND")
Read syntactically, through the bridge: `FRJ.Gbu.W.PLL_iff_laxND`,
`finite_poset_model_property` — a formula is a theorem of PLL iff it is
valid in every finite rooted poset constraint model — and
`FRJ.Gbu.W.decideLaxND`, natural-deduction provability decidable.  All
pinned `[propext, Quot.sound]`.

This is the constructive completeness the semantics chapter points forward
to: one construction yielding completeness, decidability and the finite
model property together, with no Zorn.  Depends on {uses "crown"}[].
:::
