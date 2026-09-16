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
Neutral terms: eliminations stacked on a variable, with nothing to reduce
because the head is not a constructor.
:::

:::definition "nf" (parent := "nf") (lean := "PLLND.Nf")
Normal forms, defined mutually with {uses "ne"}[].  The mutual definition
is forced by the shape of the calculus, not a convenience: a normal form may
contain a neutral, and a neutral's arguments must themselves be normal.
:::

:::theorem "not_step_of_nf" (parent := "nf") (lean := "PLLND.not_step_of_nf")
Normal forms do not reduce.  One half of the correspondence between the
syntactic characterisation {uses "nf"}[] and irreducibility — the half that
says the syntax is not too generous.
:::

:::theorem "progress" (parent := "nf") (lean := "PLLND.nf_or_step")
Progress: every term is in normal form or reduces.  With
{uses "not_step_of_nf"}[] this pins {uses "nf"}[] as *exactly* the
irreducible terms, which is what lets later results quantify over normal
forms and mean irreducibility.
:::

:::theorem "weak_normalisation" (parent := "nf") (lean := "PLLND.nf_of_SCh")
Weak normalisation, obtained from cut elimination rather than by a reduction
argument: a cut-free sequent derivation reads back as a term already in
normal form.

Worth saying plainly what this does and does not give.  It shows *some*
reduction sequence terminates — one strategy, the one the sequent calculus
happens to describe.  It says nothing about the others.  That gap is the
subject of the next chapter, and it is wider than it looks.
:::

# Confluence

:::group "confl"
Local confluence, confluence, and their consequences.
:::

:::theorem "local_confluence" (parent := "confl") (lean := "PLLND.local_confluence")
Local confluence: one step diverging can be brought back together.
:::

:::theorem "confluence" (parent := "confl") (lean := "PLLND.confluence")
Confluence.  Follows from {uses "local_confluence"}[] with termination, by
Newman's lemma — which is why the strong normalisation chapter is not merely
an ornament: this result depends on it.
:::

:::theorem "nf_unique" (parent := "confl") (lean := "PLLND.normal_form_unique")
Uniqueness of normal forms, from {uses "confluence"}[].  A term has at most
one normal form, so "the" normal form is well defined.
:::

:::theorem "conv_joinable" (parent := "confl") (lean := "PLLND.conv_iff_joinable")
Convertibility is joinability: two terms are convertible exactly when they
reduce to a common reduct.
:::

:::theorem "conv_decidable" (parent := "confl") (lean := "PLLND.conv_iff_normalize_eq")
Convertibility is equality of normal forms.  This is what turns
{uses "conv_joinable"}[] from a characterisation into a decision procedure:
normalise both sides and compare.
:::
