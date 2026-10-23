import Verso
import VersoManual
import F0Paper.Sections.Introduction
import F0Paper.Sections.Preliminaries
import F0Paper.Sections.Downsets
import F0Paper.Sections.Independence
import F0Paper.Sections.Rationals
import F0Paper.Sections.Holes
import F0Paper.Sections.Structure
import F0Paper.Sections.Completion
import F0Paper.Sections.T6
import F0Paper.Sections.SelfSim
import F0Paper.Sections.Open
import F0Paper.Sections.References
import CLPPaper.Src
import CLPPaper.Layout

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper

#doc (Manual) "The Order of F0: Covers, Independence and the Rationals" =>

{buildStamp}`F0Paper/VERSION`

{texSetup}

What is machine-checked about the order of $`F_0`, the Lindenbaum algebra of
the variable-free formulas of propositional lax logic: covers at the bottom,
independence of the odd gaps, an explicit choice-free embedding of the
rationals, unfilled cuts, the completion, the infinite downset of the sixth
rung, and nested copies of $`F_0` inside itself.  Every result shown is PROVED
in Lean, sorry-free, or REFUTED by a kernel-checked counterexample; what is
neither is OPEN.

{include 0 F0Paper.Sections.Introduction}
{include 0 F0Paper.Sections.Preliminaries}
{include 0 F0Paper.Sections.Downsets}
{include 0 F0Paper.Sections.Independence}
{include 0 F0Paper.Sections.Rationals}
{include 0 F0Paper.Sections.Holes}
{include 0 F0Paper.Sections.Structure}
{include 0 F0Paper.Sections.Completion}
{include 0 F0Paper.Sections.T6}
{include 0 F0Paper.Sections.SelfSim}
{include 0 F0Paper.Sections.Open}
{include 0 F0Paper.Sections.References}
