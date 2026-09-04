import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LaxBlueprint.Chapters.Overview
import LaxBlueprint.Chapters.Development
import LaxBlueprint.Chapters.FRJW


open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Propositional Lax Logic: Blueprint" =>

A blueprint for `lax-logic-in-lean`, the Lean 4 mechanisation of
Propositional Lax Logic (Fairtlough and Mendler 1997).  This first cut covers
the two-sided architecture and the live FRJW campaign; it is deliberately
partial, and the open nodes are open in the project, not merely unwritten
here.

{include 0 LaxBlueprint.Chapters.Overview}
{include 0 LaxBlueprint.Chapters.FRJW}
{include 0 LaxBlueprint.Chapters.Development}

{blueprint_graph}
{blueprint_summary}
