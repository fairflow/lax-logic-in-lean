import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math
import F0Paper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI PLLND.F0 PLLND.RNEmbed PLLND.F0.FilterIso
open PLLND.LaxInfinite (atomFree)

#doc (Manual) "Filters isomorphic to F0" =>

Is a proper filter $`[p, \top]`, $`p \ne \bot`, order-isomorphic to $`F_0`?
Section 9 refuted it at $`p = t_3`.  Here the question is reduced to the
filters above $`t_3`, refuted at further designed cells, and an arbitrary
isomorphism is shown to force one of four shapes on $`\bigcirc p`.  The
question itself is OPEN.  Every declaration here is choice-free;
`wip/f0FilterIso.lean`.

{stmt}`FilterIsoQ`

{leanDef FilterIsoQ}

In the $`\bigcirc`-free instance the answer is yes: in the Rieger–Nishimura
lattice, with $`\bigcirc\bot` read as the generator, $`[t_1, \top]` is
isomorphic to the whole lattice by the shift $`t_n \mapsto t_{n+2}` (pen
argument).  So the question is one on which PLL must differ from
intuitionistic logic.

# The reduction to the filters above t3

Every element of $`F_0` other than $`\bot`, $`t_1`, $`t_2`, $`t_4` lies above
$`t_3`.  PROVED, from `low_trichotomy` and the tables of Section 3.

{stmt}`classify_low`

{leanStmt classify_low}

The filter $`{\uparrow}t_3` is the kernel of the nucleus $`\lnot\lnot`: the
negations of $`\bot`, $`t_1`, $`t_2`, $`t_4` are $`\top`, $`t_2`, $`t_4`,
$`t_2`, none of them $`\bot`, and $`\lnot t_3 = \bot`.  So
$`t_3 \le p \iff \lnot p = \bot \iff \lnot\lnot p = \top`.  PROVED.

{stmt}`above_t3_iff_compl_compl_eq_top`

{leanStmt above_t3_iff_compl_compl_eq_top}

The three proper filters not above $`t_3` are not isomorphic to $`F_0`, each
by an order invariant that isomorphisms carry.  Call two elements above the
bottom a _disjoint pair_ when their only common lower bound is the bottom.
$`[t_2, \top] = \{t_2\} \cup {\uparrow}t_3` and
$`[t_4, \top] = \{t_4\} \cup {\uparrow}t_5` have no disjoint pair, while
$`F_0` has $`(t_1, t_2)`.  Call an atom $`a` _big_ when the order is
$`\{\bot, d\} \cup {\uparrow}a` for some $`d`: $`F_0` has exactly one, $`t_1`,
and in $`[t_1, \top] = \{t_1, t_4\} \cup {\uparrow}t_3` the big atom is $`t_3`,
so an isomorphism $`[t_1, \top] \cong F_0` would restrict to
$`[t_3, \top] \cong [t_1, \top] \cong F_0`, against `t3_filter_not_iso`
(Section 9).  So the question is the residue above $`t_3`.  PROVED.

{stmt}`AboveResidue`

{leanDef AboveResidue}

{stmt}`filterIsoQ_iff_aboveResidue_t3`

{leanStmt filterIsoQ_iff_aboveResidue_t3}

# Refuted filters

Each cell is a designed witness with its reason, and each is PROVED without
choice.  A _core_ is a member of every disjoint pair (Section 9); $`F_0` has
one, $`t_2`, and an isomorphism carries it, so a filter with two disjoint pairs
that share no member, or with three pairwise disjoint elements, is not
isomorphic to $`F_0`.

:::f0table (widths := "0.27 0.43 0.26")
* * $`p`
  * What $`[p, \top]` has or lacks
  * Declaration
* * $`t_2`, $`t_4`
  * no disjoint pair
  * `ne_filter_not_iso`, `t4_filter_not_iso`
* * $`t_1`
  * its big atom is $`t_3`: descent to Section 9
  * `e_filter_not_iso`
* * $`\sigma^{n}(t_3) = \sigma^{n+1}(\bot)`, every $`n`
  * two disjoint pairs $`\sigma^{n}(c_1, g_1)`, $`\sigma^{n}(t_5, t_6)` with no common member
  * `sigN_filter_not_iso`
* * $`c_1 = \bigcirc t_3 = \sigma(t_1)`
  * three pairwise disjoint elements
  * `c1_filter_not_iso`
* * $`\sigma^{n}(c_1)`, every $`n`
  * three pairwise disjoint elements
  * `C1n_filter_not_iso`
* * $`t_5`
  * three pairwise disjoint elements
  * `t5_filter_not_iso`
:::

The bases $`\sigma^{n+1}(\bot)` of the nested copies of Section 9 are the
candidates that self-similarity suggests.  $`\sigma` preserves $`\land` and
derivability, and it reflects refutation on constraint models whose
fallibility is decidable (`refutes_sig`: add the two tops of Section 9 and a
fallible world above one of them), so the countermodels behind
`two_disjoint_pairs_above_t3` (Section 9) serve for every $`n`, with no
completeness theorem.  PROVED.

{stmt}`sigN_filter_not_iso`

{leanStmt sigN_filter_not_iso}

$`\sigma^{n}(c_1)` lies above $`t_3` and is $`\bigcirc`-fixed (`C1n_box`), like
$`t_1`; its three disjoint elements are the images under $`\sigma^{n}` of three
built by hand for $`n = 0`, with three countermodels.  PROVED.

{stmt}`C1n_filter_not_iso`

{leanStmt C1n_filter_not_iso}

# Any isomorphism

Fix an order isomorphism $`f : F_0 \cong [p, \top]` and write
$`a = f(t_1)`, $`d = f(t_2)`, $`d_4 = f(t_4)`, $`a_3 = f(t_3)`.  The bottom
and the implication are defined by the order, so $`f` carries them
(`iso_himp`), and the bottom of $`F_0` (Section 3) is transported:

$$`[p, \top] = \{p, d\} \cup {\uparrow}a, \qquad {\uparrow}a = \{a, d_4\} \cup {\uparrow}a_3, \qquad d_4 = d \Rightarrow p, \qquad d = d_4 \Rightarrow p,`

so $`d` covers $`p` and is meet-prime.  PROVED (`iso_split`, `iso_split_a`,
`iso_cover`, `iso_prime`, `Di_himp`, `D4i_himp`).

_Obstruction A._  If $`d` covers $`p` and is meet-prime, then
$`\bigcirc d \vdash d` or $`\bigcirc(d \twoheadrightarrow p) \vdash d \twoheadrightarrow p`.
PROVED, by one model construction: below a world that forces $`d`, a new root
whose only $`R_m`-successor is itself.  In $`F_0` itself ($`p = \bot`,
$`d = t_2`) the second alternative holds, as it must
(`obstructionA_F0_case`).

{stmt}`ObstructionA`

{leanStmt obstructionA}

{leanDef ObstructionA}

_The case analysis._  For every $`p` and every order isomorphism
$`f : F_0 \cong [p, \top]`, one of four things holds of $`\bigcirc p`; the
remaining possibility, $`a_3 \le \bigcirc p`, is excluded by Obstruction A.
$`F_0` itself ($`p = \bot`, $`\bigcirc\bot = t_1`, $`\bigcirc t_4 = t_4`) is in
the last case.  PROVED.

{stmt}`iso_cases`

{leanStmt iso_cases}

So a counterexample $`p` has one of four shapes (`case_d_shape`,
`case_d4_shape`, `case_a_shape`):

* (i) $`\bigcirc p = p`;
* (ii) $`\bigcirc p = d`: $`\bigcirc p` covers $`p` and is meet-prime;
* (iii) $`\bigcirc p = d_4`: the gap $`\bigcirc p \Rightarrow p`, which is
  $`d`, covers $`p`;
* (iv) $`\bigcirc p = a` and $`\bigcirc d_4 = d_4`: $`\bigcirc p` is a big atom
  of $`[p, \top]`.

The cells: (i) is realised above $`t_3` by the $`\bigcirc`-fixed
$`\sigma^{n}(c_1)`, every $`n`, each refuted all the same; (ii) fails at
$`t_3` ($`\bigcirc t_3` is not meet-prime) and at $`t_5` ($`\bigcirc t_5` does
not cover $`t_5`); (iii) fails at $`t_3` (the gap $`g_1` does not cover
$`t_3`); (iv) fails at $`t_3` and $`t_5`.  PROVED.  Whether some $`p` above
$`t_3` realises a shape and is isomorphic all the same, that is
$`\mathit{AboveResidue}(t_3)`, is OPEN in each of the four cases
(Section 13).

# Supporting declarations

{lemmaTable HasDisjPair BigAtom MeetPrime CoversC hasDisjPair_of_iso bigAtom_of_iso bigAtom_rn rn_hasDisjPair not_above_t3_filter_not_iso ne_filter_not_iso t4_filter_not_iso e_filter_not_iso refutes_sig c1_filter_not_iso t5_filter_not_iso C1n_box C1n_above_t3 iso_split iso_split_a iso_himp iso_cover iso_prime Di_himp D4i_himp obstructionA_F0_case case_d_shape case_d4_shape case_a_shape box_t3_not_meetPrime box_t5_not_cover gap_t3_not_cover box_t3_not_bigAtom box_t5_not_bigAtom t3_compl above_t3_iff_compl_eq_bot subBot_le}

Pins: every declaration here within `propext`, `Quot.sound`
(`#axioms_within`, each watched failing at a tighter set), and within
`propext` alone for `obstructionA`, `refutes_sig`, `subBot_le`.
