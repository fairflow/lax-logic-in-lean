import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite F0Paper.Math
open PLLND PLLND.SemUI PLLND.F0 PLLND.RNEmbed
open PLLND.LaxInfinite (atomFree)
open F0Nuclear MacNeille MacNeille.JoinDenseHeytingEmbedding

#doc (Manual) "The completion" =>

This section fills the cuts of Sections 6 and 7 from outside: it extends the
nucleus $`\bigcirc` of $`F_0` to the Dedekind–MacNeille completion
$`\mathrm{DM}(F_0)`.  The extension theorem is Goldblatt's; what is added here
is its mechanisation, the statement that the extension is the greatest one and
that the extensions form an interval, and a counterexample to uniqueness.  The
results are in `wip/f0Nuclear.lean`, `wip/f0MacNeille.lean` and
`wip/f0MacNeilleNonUnique.lean`.

# The algebra with its nucleus, packaged

In the library $`F_0` is the quotient of the variable-free formulas by
interderivability, ordered by semantic entailment, which coincides with
derivability by completeness.  It is a Heyting algebra, with implication lifted
from $`\twoheadrightarrow`, and $`\bigcirc` lifted from the modality is a nucleus
on it.  Both PROVED, by the forcing clauses of constraint models, without
`Classical.choice`.

{stmt}`instHeyting`

{docstring instHeyting +allowMissing}

{srcLink}`instHeyting`

{stmt}`le_himp_iff_rn`

{docstring le_himp_iff_rn +allowMissing}

{srcLink}`le_himp_iff_rn`

{stmt}`circNucleus`

{docstring circNucleus +allowMissing}

{srcLink}`circNucleus`

{stmt}`box_inf`

{docstring box_inf +allowMissing}

{srcLink}`box_inf`

# The completion of a Heyting algebra

The Dedekind–MacNeille completion $`\mathrm{DM}(H)` of a poset $`H` is the
complete lattice of its cuts, with $`a \mapsto {\downarrow}a` the embedding by
principal cuts; Mathlib provides it.  For a Heyting algebra $`H` it is a frame,
a complete Heyting algebra, with implication

$$`X \Rightarrow Y = \bigwedge \{ {\downarrow}(h \Rightarrow k) : h \in \mathrm{L}(X),\ k \in \mathrm{U}(Y) \},`

$`\mathrm{L}(X)` and $`\mathrm{U}(X)` being the lower and the upper set of the
cut $`X`, and the principal embedding preserves the Heyting operations and is
dense from below and from above {pcite}`HardingBezhanishvili2004`.  PROVED.

{stmt}`MacNeille.instFrame`

{docstring MacNeille.instFrame +allowMissing}

{srcLink}`MacNeille.instFrame`

{stmt}`cutHimp`

{docstring cutHimp +allowMissing}

{srcLink}`cutHimp`

{stmt}`principalHom`

{docstring principalHom +allowMissing}

{srcLink}`principalHom`

{stmt}`principal_himp`

{docstring principal_himp +allowMissing}

{srcLink}`principal_himp`

{stmt}`sSup_principal_left`

{docstring sSup_principal_left +allowMissing}

{srcLink}`sSup_principal_left`

{stmt}`sInf_principal_right`

{docstring sInf_principal_right +allowMissing}

{srcLink}`sInf_principal_right`

# Extending a nucleus

Let $`L` be a frame, $`E : H \to L` a Heyting algebra homomorphism that reflects
the order and is dense from below, and $`j` a nucleus on $`H`.  The _upper
extension_ of $`j`,

$$`\overline{j}^{E}(x) = \bigwedge \{ E(j(a)) : a \in H,\ x \le E(a) \},`

is a nucleus on $`L` that extends $`j`.  At $`L = \mathrm{DM}(H)` this is
Goldblatt's theorem {pcite}`Goldblatt2010`, §2: the upper extension of a
nucleus on a Heyting algebra to its MacNeille completion is a nucleus; he
applies it to the Lindenbaum algebra of quantified lax logic.  The one law that
needs work is $`\overline{j}^{E}(x) \sqcap \overline{j}^{E}(y) \le \overline{j}^{E}(x \sqcap y)`:
the upper extension of a meet-preserving operation need not preserve meets in
general {pcite}`TheunissenVenema2007` (their Example 3.8), and here it uses
inflation and the fact that $`h \Rightarrow j(b)` is a fixed point of $`j`.
Closure operations are their Example 6.8.  For MacNeille completions of
lattice expansions in general see also {cite}`GehrkeHardingVenema2006`.
PROVED.

{stmt}`extNucleus`

{docstring extNucleus +allowMissing}

{srcLink}`extNucleus`

{stmt}`extNucleus_apply`

{docstring extNucleus_apply +allowMissing}

{srcLink}`extNucleus_apply`

{stmt}`extNucleus_comm`

{docstring extNucleus_comm +allowMissing}

{srcLink}`extNucleus_comm`

What is added to Goldblatt's theorem: the upper extension is the greatest
monotone map extending $`j`, and the nuclei that extend $`j` are exactly the
interval from the least of them, the meet $`\underline{j}^{E}` of all nuclear
extensions, to $`\overline{j}^{E}`.  PROVED.  In the sources consulted the
nearest statement is Proposition 5.9 of {cite}`TheunissenVenema2007`, which
characterises the upper extension as the smallest extension continuous for a
pair of topologies.

{stmt}`le_extNucleus`

{docstring le_extNucleus +allowMissing}

{srcLink}`le_extNucleus`

{stmt}`exists_nucleus_extension`

{docstring exists_nucleus_extension +allowMissing}

{srcLink}`exists_nucleus_extension`

{stmt}`extends_iff_mem_Icc`

{docstring extends_iff_mem_Icc +allowMissing}

{srcLink}`extends_iff_mem_Icc`

At the completion itself, with the principal embedding for $`E`, the extension
is written $`\overline{j}`.

{stmt}`dmNucleus`

{docstring dmNucleus +allowMissing}

{srcLink}`dmNucleus`

{stmt}`dmNucleus_principal`

{docstring dmNucleus_principal +allowMissing}

{srcLink}`dmNucleus_principal`

{stmt}`le_dmNucleus`

{docstring le_dmNucleus +allowMissing}

{srcLink}`le_dmNucleus`

# The corollary for the variable-free algebra

$`\bigcirc` extends to $`\mathrm{DM}(F_0)` as a nucleus, and
$`\overline{\bigcirc}` is the greatest monotone extension.  PROVED.

{stmt}`circ_extends_to_DM`

{docstring circ_extends_to_DM +allowMissing}

{srcLink}`circ_extends_to_DM`

# Uniqueness

The nuclear extension is not unique in general: REFUTED.  The witness is the
chain $`G = \mathbb{N} \oplus_{\mathrm{lex}} \mathbb{N}^{\mathrm{op}}`, that is
$`0 < 1 < 2 < \cdots < \cdots < 2' < 1' < 0'`, a bounded chain and so a
Heyting algebra, with the nucleus $`j` that fixes the lower copy of $`\mathbb{N}`
and sends the upper copy to $`\top`.  $`\mathrm{DM}(G)` has one new point, the
cut $`m` between the two copies, and the maps sending $`X` to $`X` when
$`X \le m` (respectively $`X < m`) and to $`\top` otherwise are two nuclei that
extend $`j` and differ at $`m`.  The chain is Example 3.11 of
{cite}`TheunissenVenema2007`.

{stmt}`MacNeilleNonUnique.nucleus_extension_not_unique`

{docstring MacNeilleNonUnique.nucleus_extension_not_unique +allowMissing}

{srcLink}`MacNeilleNonUnique.nucleus_extension_not_unique`

At $`F_0` the question is OPEN.  The counterexample turns on a cut whose lower
part has no greatest element and whose upper part has no least element.  $`F_0`
has cuts whose lower part has no greatest element (Sections 6 and 7); whether
their upper parts have least elements has not been examined.

_Remark (not mechanised)._  $`\mathrm{DM}(F_0)` with $`\overline{\bigcirc}` is a
complete Heyting algebra with a nucleus, so it is a complete algebraic model of
PLL.  It has the cardinality of the continuum and contains $`\aleph_0` mutually
incomparable order-embedded copies of $`\mathbb{R}`, completing the threads of
Section 7.  Only the extension is mechanised; the soundness of PLL for Heyting
algebras with a nucleus, the cardinality and the copies of $`\mathbb{R}` are a
pen argument here, and as mechanised statements they are OPEN.

# Axioms

As recorded in the files (`#axioms_within`), and confirmed by `#print axioms`
on the build:

* `propext`, `Quot.sound`: `instHeyting`, `le_himp_iff_rn`, `circNucleus`,
  `box_inf`: the packaging of $`F_0` is choice-free (checked with
  `#choice_path` in the file);
* `propext`, `Classical.choice`, `Quot.sound`: everything else in this
  section.  The choice comes from Mathlib by two routes recorded in the file:
  the `Nucleus` API (its monotonicity goes through a proof that uses
  `Classical.propDecidable`) and the order on cuts (through the complete
  atomic Boolean algebra of sets).
