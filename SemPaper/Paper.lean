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
import PaperKit.Stamp

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper PaperKit.Stamp

#doc (Manual) "Semantics and Decision for PLL" =>

{paperStamp (number := "I") (name := "Semantics")}`SemPaper/VERSION`

{texSetup}

What is machine-checked about the semantics of propositional lax logic and
its decision: soundness and completeness for the constraint models of
Fairtlough and Mendler and for subframe models, the translations between
them, a subframe tableau that decides PLL with a kernel-checked certificate on
either side (a natural-deduction derivation or a finite countermodel) without
`Classical.choice`, the other certified deciders of the library, the Heyting
algebra with a nucleus on the variable-free formulas, and Esakia duality for
Heyting algebras with a nucleus (finite and without choice, then general),
with the library's models placed in the dual.  Every result shown is PROVED
in Lean, sorry-free, or REFUTED by a kernel-checked counterexample; what is
neither is OPEN.

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
