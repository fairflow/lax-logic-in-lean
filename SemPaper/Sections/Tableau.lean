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

#doc (Manual) "The subframe tableau" =>

A node of the tableau is a signed sequent $`\Gamma \Rightarrow \Delta` at one
world of a subframe model: the formulas of $`\Gamma` hold there and those of
$`\Delta` fail; at an $`S`-point it is written $`\Gamma \Rightarrow_{S} \Delta`.
The rules, one constructor each of the certificate type `TCert`:

* a branch closes on $`\bot \in \Gamma`, or on a formula in both $`\Gamma`
  and $`\Delta`;
* $`\land`, $`\lor`, $`\twoheadrightarrow` are decomposed in $`\Gamma`, and
  $`\land`, $`\lor` in $`\Delta`, at the same world;
* at the same world, $`B` joins $`\Delta` when $`A \twoheadrightarrow B \in \Delta`
  and $`A \in \Gamma`; at an $`S`-point, $`A` joins $`\Gamma` when
  $`\bigcirc A \in \Gamma`, and $`\Delta` when $`\bigcirc A \in \Delta`;
* two rules open a world above, keeping $`\Gamma` and not $`\Delta`:
  $`A \twoheadrightarrow B \in \Delta` gives $`\Gamma, A \Rightarrow B`, and
  $`\bigcirc A \in \Delta` gives $`\Gamma \Rightarrow_{S} A`.

The $`\bigcirc`-free rules are those of a multi-succedent signed tableau for
intuitionistic logic; the $`S`-marking and the three $`\bigcirc` rules are
designed for subframe models (the repository's provenance record,
`docs/calculus-map.md`).

_Certificates._  A closed tableau is a term of `TCert`, checked by the
structural function `check`; an open tableau is read off as a `SubCM`, a
finite subframe model given by tables, checked by `refutes`.  Each checker,
with its soundness proof, is a certifier of the lean-certify library: `yes`
and `yes'` for closed tableaux, `no` for countermodels.  A countermodel
certificate refutes its formula.  PROVED.

{stmt}`SubTab.SubCM.refutes_sound`

{leanStmt SubTab.SubCM.refutes_sound}

A closed tableau is a natural-deduction derivation.  Under the reading

$$`\lceil \Gamma \Rightarrow \Delta \rceil = \textstyle\bigvee \Delta, \qquad \lceil \Gamma \Rightarrow_{S} \Delta \rceil = \bigcirc \textstyle\bigvee \Delta, \qquad \textstyle\bigvee [\,] = \bot,`

each rule is a derived rule of `LaxND`, and `deriveOf` turns a checked
tableau for $`\Gamma \Rightarrow \Delta` into a derivation of
$`\Gamma \vdash \lceil \Gamma \Rightarrow \Delta \rceil`; at the root it is
`termOf`.  PROVED, as a definition: the derivation is data, and the
`pllfast` tool prints it as a proof term.

{stmt}`SubTab.termOf`

{leanStmt SubTab.termOf}

The tableau is complete: every formula has a closed tableau or a finite
subframe countermodel.  The proof works over the subformulas of the root, by
strong induction on a measure, and reads the countermodel off an open
saturated tree.  PROVED.  With the soundness of the certifiers this decides
PLL with a certificate on either side, without `Classical.choice`.

{stmt}`SubTab.dichotomy`

{leanStmt SubTab.dichotomy}

Completeness for the finite decidable subframe models follows from the
dichotomy and `termOf`, without choice and without the FRJW calculus that
the proof of Section 4 uses.  PROVED.

{stmt}`SubTab.completeness_fin`

{leanStmt SubTab.completeness_fin}

:::f0Figure "countermodel" (dir := "docs/sem-paper-figures")
The countermodel the tableau engine produced for
$`\bigcirc(p \lor q) \twoheadrightarrow \bigcirc p \lor \bigcirc q`, minimised from
four worlds to three, as checked by the kernel in `fact_24`: the root
$`w_0` and two $`S`-points above it (in blue), with their atoms.  At each world
the $`\bigcirc`-subformulas it forces ($`\Vdash`) and does not force ($`\nVdash`)
are those computed by `SubCM.forceB`, the evaluator the kernel check runs.
Lines are the covering pairs of the order.
:::

The compiled producer `SubTab.solve` is partial and unverified: its
termination is a pen argument, and every answer it gives is judged by `yes`
or `no`.  Each checker rejects a corrupted certificate (`bad_yes_rejected`,
`bad_no_rejected`, by `decide +kernel`).

# Supporting declarations

{lemmaTable SubTab.SSeq SubTab.TCert SubTab.check SubTab.check_sound SubTab.Holds SubTab.holds_of_check SubTab.SubCM SubTab.SubCM.refutes SubTab.yes SubTab.yes' SubTab.no SubTab.complete SubTab.deriveOf SubTab.derive_of_check SubTab.holds_of_check' SubTab.engine fact_24}

Pins (`collectAxioms`):
{axiomsOf}`SubTab.check SubTab.check_sound SubTab.deriveOf SubTab.termOf SubTab.derive_of_check SubTab.holds_of_check' SubTab.yes'`
for the checker, its soundness and the translation;
{axiomsOf}`SubTab.dichotomy SubTab.completeness_fin SubTab.SubCM.refutes_sound SubTab.yes SubTab.no SubTab.complete SubTab.engine fact_24`
for the rest.  The library's sweep of 2026-10-22 found all 795 declarations
of `LaxLogic/PLL/SubTab` within `propext`, `Quot.sound`.  The certifier `yes`
reaches FRJW through `CF.completeness`, and so does `complete`, which names
it; `yes'`, `deriveOf`, `derive_of_check` and `completeness_fin` reach no FRJ
constant (the walk of 2026-10-22 over the constants they use, recorded in
`docs/calculus-map.md`).
