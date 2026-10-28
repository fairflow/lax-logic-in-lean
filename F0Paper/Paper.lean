import Verso
import VersoManual
import F0Paper.Sections.Introduction
import F0Paper.Sections.Preliminaries
import F0Paper.Sections.Downsets
import F0Paper.Sections.Independence
import F0Paper.Sections.Rationals
import F0Paper.Sections.Holes
import F0Paper.Sections.Structure
import F0Paper.Sections.T6
import F0Paper.Sections.SelfSim
import F0Paper.Sections.FreeHA
import F0Paper.Sections.Filters
import F0Paper.Sections.Completion
import F0Paper.Sections.Established
import F0Paper.Sections.Open
import F0Paper.Sections.References
import CLPPaper.Src
import CLPPaper.Layout
import PaperKit.Stamp

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper PaperKit.Stamp

#doc (Manual) "The Order of F0: Covers, Independence and the Rationals" =>

{paperStamp (number := "III") (name := "F0Lattice")}`F0Paper/VERSION`

{texSetup}

What is machine-checked about the order of $`F_0`, the Lindenbaum algebra of
the variable-free formulas of propositional lax logic: covers at the bottom,
independence of the odd gaps, an explicit choice-free embedding of the
rationals, unfilled cuts, the infinite downset of the sixth rung, nested copies
of $`F_0` inside itself, the free Heyting algebra on countably many generators
as a Heyting subalgebra of one interval of $`F_0`, so that intuitionistic logic,
and PLL itself, embed faithfully into the variable-free formulas of PLL, which
filters are not
isomorphic to $`F_0`, and the Dedekind–MacNeille completion, built from cuts as the reals are built from the
rationals.  Every result shown is PROVED in Lean, sorry-free, or REFUTED by a
kernel-checked counterexample; what is neither is OPEN, or marked as a pen
argument.  The last two sections list what is established and what is open.

{include 0 F0Paper.Sections.Introduction}
{include 0 F0Paper.Sections.Preliminaries}
{include 0 F0Paper.Sections.Downsets}
{include 0 F0Paper.Sections.Independence}
{include 0 F0Paper.Sections.Rationals}
{include 0 F0Paper.Sections.Holes}
{include 0 F0Paper.Sections.Structure}
{include 0 F0Paper.Sections.T6}
{include 0 F0Paper.Sections.SelfSim}
{include 0 F0Paper.Sections.FreeHA}
{include 0 F0Paper.Sections.Filters}
{include 0 F0Paper.Sections.Completion}
{include 0 F0Paper.Sections.Established}
{include 0 F0Paper.Sections.Open}
{include 0 F0Paper.Sections.References}
