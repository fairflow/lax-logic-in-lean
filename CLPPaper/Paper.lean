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
import CLPPaper.Sections.Status

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Lax Logic as a Framework for Constraint Logic Programming, Mechanised" =>

A Lean 4 mechanisation of

> M. Fairtlough, M. Mendler and M. Walton.
> *First-order Lax Logic as a framework for Constraint Logic Programming.*
> Draft of 10 September 1997.

together with what the mechanisation added: a certified constraint solver, an
operational semantics in one format for both passes of the method, and a
study of where the lax modality may be placed in a program and what each
placement buys.  Every claim is machine-checked with pinned axioms, or labelled
otherwise; each result is followed by the Lean declaration that carries it,
printed from the compiled library, so its statement is read off the compiler,
not asserted here.  Numbered results refer
to the draft.

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
{include 0 CLPPaper.Sections.Status}

