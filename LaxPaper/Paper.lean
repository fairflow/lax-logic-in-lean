import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LaxPaper.Sections.Introduction
import LaxPaper.Sections.Machinery
import LaxPaper.Sections.Modularity
import LaxPaper.Sections.Solving
import LaxPaper.Sections.Models
import LaxPaper.Sections.Latch
import LaxPaper.Sections.Adders
import LaxPaper.Sections.Pipeline
import LaxPaper.Sections.Conclusion

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Synthesising Constraints in Lean" =>

A Lean 4 library for abstraction and refinement with synthesised constraints,
after

> M. Fairtlough, M. Mendler and X. Cheng.
> *Abstraction and refinement in higher order logic.*
> In R. J. Boulton and P. B. Jackson (eds), Theorem Proving in Higher Order
> Logic (TPHOLs 2001), pp. 201–216, Springer LNCS 2152, 2001.

together with the tactics and commands that let the method run without a person
supplying the answers.  Every claim below is machine-checked with pinned axioms;
each node carries the declaration it names, so its status is read off the
compiler rather than asserted here.

{include 0 LaxPaper.Sections.Introduction}
{include 0 LaxPaper.Sections.Machinery}
{include 0 LaxPaper.Sections.Modularity}
{include 0 LaxPaper.Sections.Solving}
{include 0 LaxPaper.Sections.Models}
{include 0 LaxPaper.Sections.Latch}
{include 0 LaxPaper.Sections.Adders}
{include 0 LaxPaper.Sections.Pipeline}
{include 0 LaxPaper.Sections.Conclusion}

{blueprint_graph}
{blueprint_summary}
