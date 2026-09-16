import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Overview" =>

:::author "mf" (name := "Matt Fairtlough")
:::

:::group "arch"
The two-sided architecture: a provability calculus and a refutation calculus
for Propositional Lax Logic, each certified, each able to answer the other's
failures with a concrete object.
:::

:::definition "pll" (parent := "arch")
Propositional Lax Logic (PLL) is intuitionistic propositional logic extended
by a modality $`◯` satisfying reflexivity, transitivity and strength.  Its
Kripke semantics uses constraint models: a poset of worlds with a modal
reachability relation, in which $`w ⊩ ◯A` holds when every constraint
reachable from $`w` forces $`A`.
:::

:::definition "two_sided" (parent := "arch")
Every question about a sequent is asked twice.  The *prove* prong searches
for a derivation in the focused calculus LJF$`◯`; the *refute* prong searches
for a countermodel via the forward refutation calculi of the FRJ family,
after Fiorentini and Ferrari.  A cell is closed when one prong returns a
kernel-checkable object; it is {bpref "pll"}[] that both prongs are
interpreted in.
:::

:::definition "frj_family" (parent := "arch")
The refutation side is a sequence of calculi, each a named divergence from
its predecessor with its own fidelity log: FRJ(G) for IPC, then FRJ$`◯`
and FRJV carrying the modality, and now FRJW.  A derivation in any of them
is a *disproof*; the word *proof* is reserved for the provability calculi.
Disproofs come in two families, *regular* (existential: the extracted model
refutes the goal at its own root) and *irregular* (schematic: the goal
fails at any infallible world of any premodel meeting the interface).
This distinction is what {uses "lift_rule"}[] exists to bridge.
:::
