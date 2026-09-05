import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.PLLNormal
import LaxLogic.PLLConfluence

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Normal forms and confluence" =>

Weak normalisation and confluence for the proof-term reduction.  Together
these give unique normal forms, and hence a decision procedure for
convertibility.  Strong normalisation is a separate and much harder matter,
treated in the next chapter.

# Normal forms

:::group "nf"
The neutral/normal mutual definition, and progress.
:::

:::definition "ne" (parent := "nf") (lean := "PLLND.Ne")
TODO — neutral terms: eliminations stuck on a variable.
:::

:::definition "nf" (parent := "nf") (lean := "PLLND.Nf")
TODO — normal forms, defined mutually with {uses "ne"}[].
:::

:::theorem "not_step_of_nf" (parent := "nf") (lean := "PLLND.not_step_of_nf")
TODO — normal forms do not reduce.  One half of the correspondence between
the syntactic characterisation {uses "nf"}[] and irreducibility.
:::

:::theorem "progress" (parent := "nf") (lean := "PLLND.nf_or_step")
TODO — progress: every term is in normal form or reduces.  With
{uses "not_step_of_nf"}[] this makes {uses "nf"}[] exactly the irreducible
terms.
:::

:::theorem "weak_normalisation" (parent := "nf") (lean := "PLLND.nf_of_SCh")
TODO — weak normalisation, obtained from cut elimination rather than by a
reduction argument: a cut-free sequent derivation reads back as a term
already in normal form.  Worth saying plainly that this route gives WN and
not SN, which is the gap the next chapter closes.
:::

# Confluence

:::group "confl"
Local confluence, confluence, and their consequences.
:::

:::theorem "local_confluence" (parent := "confl") (lean := "PLLND.local_confluence")
TODO — the diamond at one step.
:::

:::theorem "confluence" (parent := "confl") (lean := "PLLND.confluence")
TODO.  Follows from {uses "local_confluence"}[] together with termination.
:::

:::theorem "nf_unique" (parent := "confl") (lean := "PLLND.normal_form_unique")
TODO — uniqueness of normal forms, from {uses "confluence"}[].
:::

:::theorem "conv_joinable" (parent := "confl") (lean := "PLLND.conv_iff_joinable")
TODO — convertibility is joinability.
:::

:::theorem "conv_decidable" (parent := "confl") (lean := "PLLND.conv_iff_normalize_eq")
TODO — convertibility is equality of normal forms, which turns
{uses "conv_joinable"}[] into something computable.
:::
