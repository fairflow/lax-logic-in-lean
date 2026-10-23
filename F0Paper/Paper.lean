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

This document reports what is machine-checked about the order of $`F_0`, the
Lindenbaum algebra of the variable-free formulas of propositional lax logic:
that it has covers at the bottom and so is not dense, that the odd gaps are
independent, that the rationals order-embed in it, explicitly and without
choice, that it has cuts it does not fill, how the covers and the threads fit
together, that its modality extends to its Dedekind–MacNeille completion, that
the downset of the sixth rung is infinite, and that $`F_0` contains an infinite
descending sequence of nested copies of itself.

Every result shown is PROVED in Lean, sorry-free, or REFUTED by a
kernel-checked counterexample, with the axioms it depends on stated at the end
of its section; what is neither is labelled OPEN.  Each result is stated in
words, then as a displayed formula generated from the Lean statement, then as
the Lean declaration printed from the compiled library, then as a link to its
line in the repository at the commit that was built.

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
