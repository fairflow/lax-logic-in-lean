import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LaxBlueprint.Chapters.Overview
import LaxBlueprint.Chapters.Development
import LaxBlueprint.Chapters.Notation
import LaxBlueprint.Chapters.Terms
import LaxBlueprint.Chapters.Normalisation
import LaxBlueprint.Chapters.StrongNorm
import LaxBlueprint.Chapters.FRJW
import LaxBlueprint.Chapters.UI
import LaxBlueprint.Chapters.RN
import LaxBlueprint.Chapters.Tools

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Propositional Lax Logic: Blueprint" =>

A blueprint for `lax-logic-in-lean`, the Lean 4 mechanisation of
Propositional Lax Logic (Fairtlough and Mendler 1997).  This first cut covers
the two-sided architecture and the live FRJW campaign; it is deliberately
partial, and the open nodes are open in the project, not merely unwritten
here.

Papers, published on this site beside the Blueprint:

* [Lax Logic as a Framework for Constraint Logic Programming, Mechanised](https://fairflow.github.io/lax-logic-in-lean/clp-paper/)
  ([one page](https://fairflow.github.io/lax-logic-in-lean/clp-paper/single/))
* [Synthesising Constraints in Lean](https://fairflow.github.io/lax-logic-in-lean/lax-paper/)
  ([one page](https://fairflow.github.io/lax-logic-in-lean/lax-paper/single/))

Explorers and guides, self-contained pages (each states its own version and
date):

* [The RN(◯,{}) catalogue](https://fairflow.github.io/lax-logic-in-lean/tools/rn-catalogue.html)
  (v27, 2026-08-26): the lattice explorer for the closed fragment: the ρ-catalogue R, its order
  as a Hasse diagram, the operation tables and the hypercubes.
* [The R operation tables](https://fairflow.github.io/lax-logic-in-lean/tools/rho-optables.html)
  (2026-08-25; the catalogue above carries the later tables).
* [The PLL calculus ledger](https://fairflow.github.io/lax-logic-in-lean/tools/pll-calculus-ledger.html):
  every proof system in the development and the soundness, completeness and
  equivalence results relating them, each with its Lean statement and
  observed axiom pin (2026-08-31).
* [Interpolation, plainly](https://fairflow.github.io/lax-logic-in-lean/tools/interpolation-guide.html):
  a teaching guide to Craig and uniform interpolation; its claims are checked
  by hand or cited, not machine-checked.
* [Principal proof states](https://fairflow.github.io/lax-logic-in-lean/tools/principal-proof-states.html):
  annotated proof states of the strong-normalisation proof.

{include 0 LaxBlueprint.Chapters.Overview}
{include 0 LaxBlueprint.Chapters.Development}
{include 0 LaxBlueprint.Chapters.Notation}
{include 0 LaxBlueprint.Chapters.Terms}
{include 0 LaxBlueprint.Chapters.Normalisation}
{include 0 LaxBlueprint.Chapters.StrongNorm}
{include 0 LaxBlueprint.Chapters.FRJW}
{include 0 LaxBlueprint.Chapters.UI}
{include 0 LaxBlueprint.Chapters.RN}
{include 0 LaxBlueprint.Chapters.Tools}

{blueprint_graph}
{blueprint_summary}
