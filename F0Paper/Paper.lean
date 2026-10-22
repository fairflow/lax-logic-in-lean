import Verso
import VersoManual
import F0Paper.Sections.Introduction
import F0Paper.Sections.Preliminaries
import F0Paper.Sections.Downsets
import F0Paper.Sections.Independence
import F0Paper.Sections.Rationals
import F0Paper.Sections.Holes
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
independent, that the rationals order-embed in it, and that the gaps have no
greatest lower bound in it.

Every result is PROVED in Lean, sorry-free, with the axioms it depends on
stated at the end of its section.  Each is stated in words, then as a
displayed formula generated from the Lean statement, then as the Lean
declaration printed from the compiled library, then as a link to its line in
the repository at the commit that was built.

{include 0 F0Paper.Sections.Introduction}
{include 0 F0Paper.Sections.Preliminaries}
{include 0 F0Paper.Sections.Downsets}
{include 0 F0Paper.Sections.Independence}
{include 0 F0Paper.Sections.Rationals}
{include 0 F0Paper.Sections.Holes}
{include 0 F0Paper.Sections.Open}
{include 0 F0Paper.Sections.References}
