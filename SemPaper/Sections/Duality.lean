import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import SemPaper.Math
import SemPaper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks

#doc (Manual) "Duality: planned" =>

Nothing in this section is built.  Esakia duality represents a Heyting
algebra by its space of prime filters {pcite}`Esakia1974 Esakia2019`, and
under it the nuclei on a Heyting algebra correspond to certain closed subsets
of the dual space {pcite}`BezhanishviliGhilardi2007`.  The planned results,
each OPEN in the sense of this paper (no Lean statement yet):

* Esakia duality for Heyting algebras with a nucleus, as a dual equivalence
  of categories in Lean;
* the subframe models of Section 4 placed in the dual: a finite subframe model
  $`(W, \le, S, V)` as the dual of a finite Heyting algebra with a nucleus,
  the nucleus given by $`S`.

The statements will be fixed, and tested for refutation, before any proof is
built.
