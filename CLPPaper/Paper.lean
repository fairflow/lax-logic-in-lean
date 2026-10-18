import Verso
import VersoManual
import CLPPaper.Sections.Introduction
import CLPPaper.Sections.CLP
import CLPPaper.Sections.Logic
import CLPPaper.Sections.Programs
import CLPPaper.Sections.Trees
import CLPPaper.Sections.Abstraction
import CLPPaper.Sections.Machine
import CLPPaper.Sections.Solving
import CLPPaper.Sections.Examples
import CLPPaper.Sections.Modality
import CLPPaper.Sections.Pruning
import CLPPaper.Sections.Compare
import CLPPaper.Sections.Status
import CLPPaper.Sections.References
import CLPPaper.Src
import CLPPaper.Layout

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper

#doc (Manual) "Lax Logic as a Framework for Constraint Logic Programming, Mechanised" =>

{buildStamp}`CLPPaper/VERSION`

{texSetup}

This document is a mechanisation in Lean 4 of a 1997 report of Fairtlough,
Mendler and Walton on first-order lax logic as a framework for constraint
logic programming (the reference is in Section 1), together with what the
mechanisation added to it: a constraint solver whose verdicts are certified,
one operational semantics for both passes of the report's method, and a study
of where the lax modality may be placed in a program and what each placement
buys.

Every result is machine-checked, or labelled as refuted or open.  Each is
stated in words, then as a displayed formula generated from the Lean
statement, then as the Lean declaration that carries it, printed from the
compiled library.  Numbered results are those of the 1997 report.

{include 0 CLPPaper.Sections.Introduction}
{include 0 CLPPaper.Sections.CLP}
{include 0 CLPPaper.Sections.Logic}
{include 0 CLPPaper.Sections.Programs}
{include 0 CLPPaper.Sections.Trees}
{include 0 CLPPaper.Sections.Abstraction}
{include 0 CLPPaper.Sections.Machine}
{include 0 CLPPaper.Sections.Solving}
{include 0 CLPPaper.Sections.Examples}
{include 0 CLPPaper.Sections.Modality}
{include 0 CLPPaper.Sections.Pruning}
{include 0 CLPPaper.Sections.Compare}
{include 0 CLPPaper.Sections.Status}
{include 0 CLPPaper.Sections.References}
