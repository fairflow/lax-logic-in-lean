import Verso
import VersoManual
import SemPaper.Sections.Introduction
import SemPaper.Sections.Calculus
import SemPaper.Sections.Constraint
import SemPaper.Sections.Subframe
import SemPaper.Sections.Tableau
import SemPaper.Sections.Deciders
import SemPaper.Sections.Algebra
import SemPaper.Sections.Duality
import SemPaper.Sections.Open
import SemPaper.Sections.References
import CLPPaper.Src
import CLPPaper.Layout

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper

#doc (Manual) "Semantics and Decision for PLL" =>

{buildStamp}`SemPaper/VERSION`

{texSetup}

What is machine-checked about the semantics of propositional lax logic and
its decision: soundness and completeness for the constraint models of
Fairtlough and Mendler and for subframe models, the translations between
them, a subframe tableau that decides PLL with a kernel-checked certificate on
either side (a natural-deduction derivation or a finite countermodel) without
`Classical.choice`, the other certified deciders of the library, and the
Heyting algebra with a nucleus on the variable-free formulas.  Every result
shown is PROVED in Lean, sorry-free; what is not is OPEN.

{include 0 SemPaper.Sections.Introduction}
{include 0 SemPaper.Sections.Calculus}
{include 0 SemPaper.Sections.Constraint}
{include 0 SemPaper.Sections.Subframe}
{include 0 SemPaper.Sections.Tableau}
{include 0 SemPaper.Sections.Deciders}
{include 0 SemPaper.Sections.Algebra}
{include 0 SemPaper.Sections.Duality}
{include 0 SemPaper.Sections.Open}
{include 0 SemPaper.Sections.References}
