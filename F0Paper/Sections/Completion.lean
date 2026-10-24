import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math
import F0Paper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI PLLND.F0 PLLND.RNEmbed
open PLLND.LaxInfinite (atomFree)
open F0Nuclear MacNeille MacNeille.JoinDenseHeytingEmbedding

#doc (Manual) "The completion" =>

The nucleus $`\bigcirc` extends to the Dedekind–MacNeille completion
$`\mathrm{DM}(F_0)`, which fills the cuts of Sections 6 and 7.  Files:
`wip/f0Nuclear.lean`, `wip/f0MacNeille.lean`, `wip/f0MacNeilleNonUnique.lean`.

In the library $`F_0` is a Heyting algebra with the nucleus $`\bigcirc`
(`instHeyting`, `circNucleus`, choice-free).  For a Heyting algebra $`H`,
$`\mathrm{DM}(H)` is a frame, with implication
$`X \Rightarrow Y = \bigwedge \{ {\downarrow}(h \Rightarrow k) : h \in \mathrm{L}(X),\ k \in \mathrm{U}(Y) \}`,
and the principal embedding preserves the Heyting operations and is dense from
both sides {pcite}`HardingBezhanishvili2004`.  PROVED.

For $`E : H \to L` an order-reflecting Heyting homomorphism into a frame, dense
from below, and $`j` a nucleus on $`H`, the upper extension

$$`\overline{j}^{E}(x) = \bigwedge \{ E(j(a)) : a \in H,\ x \le E(a) \}`

is a nucleus extending $`j`: at $`L = \mathrm{DM}(H)` this is Goldblatt's theorem
{pcite}`Goldblatt2010`, §2.  The meet law needs inflation and that
$`h \Rightarrow j(b)` is a fixed point; upper extensions need not preserve meets
in general {pcite}`TheunissenVenema2007` (Example 3.8; closure operations,
Example 6.8; see also {cite}`GehrkeHardingVenema2006`).  New here: it is the
greatest monotone extension, and the nuclear extensions are exactly an
interval.  PROVED (the nearest statement found is Proposition 5.9 of
{cite}`TheunissenVenema2007`).

{stmt}`exists_nucleus_extension`

{leanStmt exists_nucleus_extension}

{stmt}`extends_iff_mem_Icc`

{leanStmt extends_iff_mem_Icc}

For $`F_0`: $`\bigcirc` extends to $`\mathrm{DM}(F_0)` as a nucleus, and
$`\overline{\bigcirc}` is the greatest monotone extension.  PROVED.

{stmt}`circ_extends_to_DM`

{leanStmt circ_extends_to_DM}

Uniqueness fails in general: REFUTED on the chain
$`\mathbb{N} \oplus_{\mathrm{lex}} \mathbb{N}^{\mathrm{op}}`, with the nucleus
fixing the lower copy of $`\mathbb{N}` and sending the upper copy to $`\top`; the
new cut $`m` between the copies is sent to $`m` by one extension and to $`\top` by
another ({cite}`TheunissenVenema2007`, Example 3.11).  At $`F_0` it is OPEN.

{stmt}`MacNeilleNonUnique.nucleus_extension_not_unique`

{leanStmt MacNeilleNonUnique.nucleus_extension_not_unique}

_Remark (pen, not mechanised)._  $`\mathrm{DM}(F_0)` with $`\overline{\bigcirc}` is a
complete algebraic model of PLL of the cardinality of the continuum, with
$`\aleph_0` mutually incomparable copies of $`\mathbb{R}` completing the threads
of Section 7; as mechanised statements these are OPEN.

# Supporting declarations

{lemmaTable instHeyting le_himp_iff_rn circNucleus box_inf MacNeille.instFrame cutHimp principalHom principal_himp sSup_principal_left sInf_principal_right extNucleus extNucleus_apply extNucleus_comm le_extNucleus dmNucleus dmNucleus_principal le_dmNucleus}

Pins (`#axioms_within`, confirmed by `#print axioms`): `propext`, `Quot.sound`
for `instHeyting`, `le_himp_iff_rn`, `circNucleus`, `box_inf` (no
`Classical.choice`, checked with `#choice_path`); `propext`,
`Classical.choice`, `Quot.sound` for the rest, through Mathlib's `Nucleus` API
and the order on cuts.
