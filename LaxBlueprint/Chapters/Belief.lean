import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Belief.Collapse
import LaxLogic.Belief.BooleanIso
import LaxLogic.Belief.Normality
import LaxLogic.Belief.Idealisation
import LaxLogic.Belief.OpenClosed
import LaxLogic.Belief.Falsum
import LaxLogic.Belief.Examples
import LaxLogic.Belief.Realisability

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- Names in the rendered signatures are printed relative to these namespaces.
open BeliefLax PLLND PLLND.BeliefReal

#doc (Manual) "Belief in lax logic" =>

The mechanised base of a paper in preparation, *Belief in Lax Logic*: the lax
modality read as idealised evidential belief.  The draft is
`docs/belief-paper-draft.md`; `docs/belief-mechanisation-index.md` maps each of
its claims to a declaration.  This chapter covers the results that live in the
library (`LaxLogic/Belief/`).  The paper also cites results of other chapters:
context completeness and the infinite closed fragment.  It is not yet
publishable: the closed-fragment ladder of its section 3.1 is still in `wip/`
and is not claimed here.

# Classical belief collapses

:::group "belief_collapse"
Over a Boolean algebra a belief modality is determined by what it believes of
falsity.
:::

:::definition "belief_closed" (parent := "belief_collapse") (lean := "closedNucleus")
The closed nucleus at `a`: the modality `x ↦ x ⊔ a`.
:::

:::theorem "belief_sup_bot" (parent := "belief_collapse") (lean := "nucleus_eq_sup_bot")
In a Boolean algebra every nucleus is closed: `j x = x ⊔ j ⊥`.  Uses
{uses "belief_closed"}[].
:::

:::theorem "belief_sceptic" (parent := "belief_collapse") (lean := "eq_id_of_bot_eq_bot")
The sceptic: a nucleus that does not believe falsity is the identity.
:::

:::theorem "belief_credulous_top" (parent := "belief_collapse") (lean := "eq_top_of_bot_eq_top")
The credulous: a nucleus that believes falsity believes everything.
:::

:::definition "belief_iso" (parent := "belief_collapse") (lean := "nucleusOrderIsoBot")
The sharp form: the nuclei of a Boolean algebra `B` are order-isomorphic to `B`
itself, by `j ↦ j ⊥`.  Depends on {uses "belief_sup_bot"}[].
:::

:::definition "belief_open" (parent := "belief_collapse") (lean := "openNucleus")
The open nucleus at `a`: the modality `x ↦ (a ⇨ x)`.
:::

:::theorem "belief_open_closed" (parent := "belief_collapse") (lean := "openNucleus_eq_closedNucleus")
In a Boolean algebra the open and closed nuclei coincide.
:::

:::theorem "belief_open_closed_em" (parent := "belief_collapse") (lean := "em_of_openNucleus_eq_closedNucleus")
Conversely, if the open and closed nuclei at `a` coincide then excluded middle
holds at `a`.  So the distinction between them is exactly what constructive
belief keeps and classical belief loses.
:::

:::theorem "belief_chain3" (parent := "belief_collapse") (lean := "chain3_card")
A small constructive witness: the three-element chain carries exactly four
nuclei.  Two further counts in the same file, for the four-element chain and the
four-element Boolean algebra, use `native_decide` and are not claimed as
machine-checked.
:::

# The modality as idealised belief

:::group "belief_ideal"
What the laws of the modality say when it is read as belief.
:::

:::theorem "belief_k" (parent := "belief_ideal") (lean := "nucleus_himp_le")
The K axiom holds: `◯(A → B) → (◯A → ◯B)`.  With {uses "belief_top"}[] this
makes the modality normal.
:::

:::theorem "belief_top" (parent := "belief_ideal") (lean := "nucleus_top")
Truth is believed: `◯⊤ = ⊤`.
:::

:::theorem "belief_intro" (parent := "belief_ideal") (lean := "belief_introspection")
Positive introspection, both ways: believing that one believes `M` is
believing `M`.
:::

:::theorem "belief_omni" (parent := "belief_ideal") (lean := "belief_consequence")
Logical omniscience: if `M` follows from `Γ`, then belief in `M` follows from
belief in each member of `Γ`.
:::

:::theorem "belief_nec" (parent := "belief_ideal") (lean := "belief_necessitation")
Necessitation: a theorem is believed.
:::

:::theorem "belief_noD" (parent := "belief_ideal") (lean := "belief_no_D")
The D axiom fails: consistency of belief, the negation of `◯⊥`, is not
provable.
:::

:::theorem "belief_bot" (parent := "belief_ideal") (lean := "belief_bot_not_provable")
Nor is inconsistent belief provable: `◯⊥` is not a theorem.
:::

:::definition "belief_cred" (parent := "belief_ideal") (lean := "belief_credulous")
From belief in falsity, belief in anything: a derivation of `◯M` from `◯⊥`.
:::

# Evidence

:::group "belief_evidence"
Realisability readings of belief, and where they part from truth.
:::

:::definition "belief_realU" (parent := "belief_evidence") (lean := "realU")
Uniform realisability: one realiser serves every constraint.
:::

:::definition "belief_realS" (parent := "belief_evidence") (lean := "realS")
Stratified realisability: the realiser may depend on the constraint.
:::

:::theorem "belief_bite" (parent := "belief_evidence") (lean := "bite_uniform_split")
Truth outruns uniform evidence: a belief in a disjunction can be forced with no
uniform realiser for it.  Uses {uses "belief_realU"}[].
:::

:::theorem "belief_dist" (parent := "belief_evidence") (lean := "uniform_dist_valid")
Uniform realisability validates distribution of belief over disjunction, which
the logic itself does not prove.
:::
