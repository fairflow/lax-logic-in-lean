import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import SemPaper.Math
import SemPaper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI

set_option paperkit.notation "sem"

#doc (Manual) "Other certified deciders" =>

Two further calculi decide PLL in the library.  This section records them
from the repository's provenance record (`docs/calculus-map.md`) and its
tool register (`TOOLS.md`).

_G4c._  Iemhoff's calculus G4iLL {pcite}`Iemhoff2024`, the lax extension of
Dyckhoff's contraction-free calculus {pcite}`Dyckhoff1992`, is incomplete for
PLL: the sequent $`\bigcirc Ga,\ Fa \Rightarrow r`, where
$`Fa = \bigcirc p \twoheadrightarrow r` and $`Ga = Fa \twoheadrightarrow \bigcirc p`, is derivable in the cut-free sequent calculus of Fairtlough and Mendler and
not in G4iLL (`sc_but_not_G4`, PROVED; tabled below).  The
library's repair, G4c, has cut and contraction admissible and is equivalent
to natural deduction.  PROVED.

{stmt}`G4c.equiv_nd`

{leanStmt G4c.equiv_nd}

Backward search in G4c with a loop check gives a decision procedure
(`decidablePLL`, Theorem 2.8 of {cite}`FairtloughMendler1997`), within
`propext` and `Quot.sound`; its fuel bounds are infeasible, and it is never
run as a search.  The practical G4c search, the `pll_g4c` tactic, runs an
unverified search and has the kernel check the derivation it finds; a failed
search is a report, not a refutation.

_FRJW and $`\mathrm{Gbu}\bigcirc`._  Fiorentini and Ferrari pair a provability
calculus $`\mathrm{Gbu}` with a forward refutation calculus $`\mathrm{FRJ}`
for intuitionistic logic {pcite}`FiorentiniFerrari2018`; the
$`\bigcirc`-extensions $`\mathrm{Gbu}\bigcirc` and FRJW are the library's.  An
FRJW derivation is a disproof.  Every goal has a $`\mathrm{Gbu}\bigcirc`
derivation or an FRJW disproof, with no choice.  PROVED.

{stmt}`FRJ.Gbu.W.decideGbuW`

{leanStmt FRJ.Gbu.W.decideGbuW}

With the translation of $`\mathrm{Gbu}\bigcirc` into `LaxND`, this decides
provability.  PROVED.  The decision is a proof object, not a practical
algorithm.

{stmt}`FRJ.Gbu.W.decideLaxND`

{leanStmt FRJ.Gbu.W.decideLaxND}

_Invocation._  The lean-certify library separates an untrusted producer from
a certifier proved sound.  A decider is a set of settings, checked when it is
compiled (`#certify_decider`), that name a prover and a disprover, each a
producer paired with a certifier.  The `subtabdecide` tool
(`tools/SubTab/Settings.lean`) names the subframe tableau, judged by `yes`,
as prover, and the finite-model enumeration on at most six worlds, judged by
`no`, as disprover, run as a race; every answer is checked by the compiled
checker of a certifier proved sound.  The `pllfast` tool runs the tableau
first and falls back to the FRJW engine.  The routing between these tools is
interim, until a pre-registered comparison orders the decider settings.

# Supporting declarations

{lemmaTable PLLG4Gap.sc_but_not_G4 G4c decidablePLL FRJ.Gbu.W.PLL_iff_laxND FRJ.Gbu.W.finite_poset_model_property FRJ.Gbu.W.frjw_complete FRJ.Gbu.W.gbuw_complete FRJ.Gbu.W.provableGbuC_iff_pll FRJ.Gbu.W.disprovableW_iff_not_pll}

Pins (`collectAxioms`):
{axiomsOf}`PLLG4Gap.sc_but_not_G4 G4c.equiv_nd decidablePLL FRJ.Gbu.W.decideGbuW FRJ.Gbu.W.decideLaxND FRJ.Gbu.W.PLL_iff_laxND FRJ.Gbu.W.finite_poset_model_property FRJ.Gbu.W.frjw_complete FRJ.Gbu.W.gbuw_complete FRJ.Gbu.W.provableGbuC_iff_pll FRJ.Gbu.W.disprovableW_iff_not_pll`
for all.  `FRJ.PLL` is validity in the finite rooted posets that are
constraint models; it meets `LaxND` provability through `PLL_iff_laxND`.
