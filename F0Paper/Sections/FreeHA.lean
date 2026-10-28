import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math
import F0Paper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI PLLND.F0 PLLND.RNEmbed PLLND.F0.FreeHAn PLLND.F0.Base3
open PLLND.LaxInfinite (atomFree)

#doc (Manual) "Free Heyting algebras in F0" =>

The free Heyting algebra $`H_n` on $`n` generators, and $`H_\omega` on
countably many, lie inside $`F_0` as Heyting subalgebras of one interval,
$`[\sigma^{3}\bot, \top]`, where $`\sigma^{m}\bot` is the $`m`-th base of the
nested copies of Section 9; so does the free PLL-algebra on countably many
generators.  The result comes first, then why it is
unexpected, where the free structure stops, the generators, the construction,
and the formal statement with the reasons for trusting it.  Every declaration
here is choice-free; `wip/f0FreeIPL.lean`, `wip/f0FreeHAn.lean`,
`wip/f0FreePair.lean`, `wip/f0MeetCount.lean`, `wip/f0FreeBase3.lean`,
`wip/f0FreeAnyFamily.lean`, `wip/f0EmbedForms.lean`, and `wip/f0FreePLL.lean`
(PR #106).

# Summary

*IPC embeds faithfully into the closed fragment $`F_0` of PLL.*  There are
variable-free formulas $`x_0, x_1, x_2, \ldots` such that replacing each
variable $`p_i` by $`x_i` and $`\bot` by $`\sigma^{3}\bot` preserves and
reflects derivability between $`\bigcirc`-free formulas:

$$`A \vdash B \iff h(A) \vdash h(B), \qquad h(A) = A[p_i := x_i,\ \bot := \sigma^{3}\bot].`

PROVED (`freeHAnAbove_base3`, `freeHAωAbove_base3`; the formal statement is
displayed below).  So intuitionistic propositional logic in countably many
variables lives among the formulas built from $`\bot` alone.

*More holds: PLL itself embeds faithfully into* $`F_0`.  Take as generators
the readers alone, $`x^{r}(a) = x_{\mathrm{code}(a)+1}` for every variable
$`a`, with no $`x_0` (`xr`; $`\mathrm{code}` is an injection of the variables
into $`\mathbb{N}`, below), and send $`\bot` to $`\sigma^{3}\bot` and
$`\bigcirc` to $`\bigcirc`.  Then for all formulas $`A`, $`B`, $`\bigcirc`
included,

$$`A \vdash B \iff A[a := x^{r}(a),\ \bot := \sigma^{3}\bot] \vdash B[a := x^{r}(a),\ \bot := \sigma^{3}\bot].`

PROVED (`freeReaders`, `freePLLAbove_base3`; `wip/f0FreePLL.lean`, public
PR #106, pins $`\mathsf{propext}`, $`\mathsf{Quot.sound}`; not on main when
this version was built, so not printed here).  Algebraically: the free
PLL-algebra on $`\omega` generators embeds into $`[\sigma^{3}\bot, \top]`,
with the nucleus of $`F_0` restricted to the interval, while $`F_0` itself is
the free PLL-algebra on no generators (pen reading, as for IPC below).

* Algebraically, $`H_\omega` embeds as a Heyting subalgebra of the interval
  $`[\sigma^{3}\bot, \top]` of $`F_0`, and so does every $`H_n`; one family of
  generators serves for every $`n`.  This reading of the PROVED statement goes
  through conservativity of PLL over IPC (mechanised) and the identification
  of $`H_n` with the Lindenbaum algebra of IPC (textbook); see point (c) of
  the formal statement.
* Every countable Heyting algebra is a quotient of $`H_\omega`, hence a quotient
  of a Heyting subalgebra of an interval of $`F_0` (pen argument).
* $`F_0` is the free PLL-algebra, a Heyting algebra with a nucleus, on no
  generators (Section 2, pen argument).  So the free nucleated Heyting algebra
  on no generators contains the free Heyting algebra on $`\omega` generators,
  and in an interval, with its nucleus restricted, the free nucleated Heyting
  algebra on $`\omega` generators.
* Corollary: the conjecture
  $`\forall n\, \exists m.\ H_n \hookrightarrow [\sigma^{m}\bot, \top]` holds,
  with $`m = 3` for every $`n`.  PROVED (`conjecture`).
* Every base above serves as well: $`H_\omega` and every $`H_n` lie in
  $`[\sigma^{m}\bot, \top]` for every $`m \ge 3`, by the $`\sigma`-shift of a
  free copy.  PROVED (`allAbove3`, `allAbove3ω`, `sigShift`).

# Why this is surprising

Closed fragments are usually small.  The variable-free formulas of IPC are
$`\bot` and $`\top` up to $`\dashv\vdash`; those of the provability logic GL form
the Boolean algebra of finite and cofinite sets of natural numbers
{pcite}`Boolos1993`.  $`F_0` is infinite and its order is rich (Sections 3
to 9), but that one interval of it holds the free Heyting algebra on countably
many generators says more: the closed fragment of PLL contains a faithful copy
of the whole of IPC, and of PLL itself.

_The mechanism._  In a subframe model (Section 9: an intuitionistic Kripke model
with a set $`S` of worlds, $`\bigcirc A` holding at $`w` when $`A` holds at
every world of $`S` above $`w`) each world carries one free bit, its membership
of $`S`.  A variable-free formula reads that bit and the types of the worlds
above, the _type_ of a world being the set of variable-free formulas it forces.
Write $`k(a)` for the number of types of the $`a`-maximal worlds, those
maximal among the worlds refuting $`a`, over all finite subframe models.  Then
$`k(\sigma^{2}\bot) = \infty` (`not_typeBound_base2`), and these infinitely
many types are independent things for a formula to read.  In effect
$`\bigcirc` is a source of variables.

# Where the free structure begins

For the bases $`\sigma^{m}\bot`, $`m = 1`, $`m = 2` and $`m \ge 3`, and $`n`
generators: does
$`[\sigma^{m}\bot, \top]` contain $`H_n` in the sense of the formal statement
below ($`H_n \hookrightarrow [b, \top]`, `FreeHAnAbove`)?

:::f0table (widths := "0.17 0.2 0.33 0.28")
* * Base
  * $`n = 1`
  * $`n = 2`
  * $`n \ge 3`
* * $`t_3 = \sigma^{1}\bot`
  * yes, `freeIPL1`
  * no: `noFreeHA2`; for $`\omega`, `not_FreeIPLInAboveT3`
  * no
* * $`\sigma^{2}\bot`
  * yes
  * yes, `freePair`, `freeHAnAbove_base2_two`
  * OPEN
* * $`\sigma^{m}\bot`, $`m \ge 3`
  * yes
  * yes
  * yes, and $`\omega`: `freeHAnAbove_base3`, `freeHAωAbove_base3`, `conjecture` ($`m = 3`); `allAbove3`, `allAbove3ω` ($`m \ge 3`)
:::

A yes for $`n` generators gives a yes for fewer, by restriction to the first
variables, and a no gives a no for more (pen, one line each).  `freeIPL1`
states the one-generator case at $`t_3` for the map
$`h_1(A) = \sigma(A[p := \bigcirc\bot])`, which sends $`p` to
$`\bigcirc t_3`; `noFreeHA2` shows that for every pair of variable-free
formulas some signed conjunction lies below $`t_3`.

_The obstruction._  A copy of $`H_n` that is one-to-one and preserves
$`\land`, with bottom $`a`, needs $`k(a) \ge 2^{n}`: the $`2^{n}` signed
conjunctions of $`p_0, \ldots, p_{n-1}` are pairwise disjoint and non-zero, and
their images are realised at $`a`-maximal worlds of pairwise different types.
PROVED.

{stmt}`MeetCount.meet_counting`

{leanStmt MeetCount.meet_counting}

Here $`f` is a meet-embedding of $`H_n` (`MeetEmb`) when it sends the
$`\bigcirc`-free formulas in $`p_0, \ldots, p_{n-1}` to variable-free
formulas, $`A \dashv\vdash B` iff $`f(A) \dashv\vdash f(B)`, and
$`f(A \land B) \dashv\vdash f(A) \land f(B)`; nothing is assumed about
$`\lor`, $`\twoheadrightarrow` or $`\bot`.  And $`k(b) \le K` is `TypeBound`: one of $`K` valuations of the variable-free
formulas is assigned to every world of every finite subframe model, and every
$`b`-maximal world forces exactly the formulas its valuation makes true.
$`k(\bot) = 2` and $`k(t_3) = 3`: the upper bounds are PROVED
(`typeBound_bot`, `typeBound_t3`), the lower bounds are the evident witnesses
(pen).  So $`H_2` has no $`\land`-preserving copy with bottom $`\bot` or
$`t_3` (`noMeetCopyH2_bot`, `noMeetCopyH2_t3`), and the no entries for
$`n \ge 2` at $`t_3` also follow from the count, since $`2^{n} \le 3` fails
(`countingCriterion` with `typeBound_t3`; one line, not stated as a theorem).
At $`\sigma^{2}\bot` the count does not obstruct: $`k(\sigma^{2}\bot) = \infty`.
PROVED.

{stmt}`not_typeBound_base2`

{leanStmt not_typeBound_base2}

# The generators

The rungs $`r_n` of Section 2 before substitution are the Rieger–Nishimura
formulas in one variable $`p` (`rn`, `rnP`, `wip/rnEmbed.lean`):

$$`r_0 = \bot,\quad r_1 = p,\quad r_2 = \lnot p,\quad r_{2k+3} = r_{2k+1} \lor r_{2k+2},\quad r_{2k+4} = r_{2k+3} \twoheadrightarrow r_{2k+1}.`

With $`t_4 = t_3 \twoheadrightarrow \bigcirc\bot \dashv\vdash \lnot\lnot\bigcirc\bot`,
the formula $`Y` fails exactly at the worlds that see both a world forcing
$`\bigcirc\bot` and one forcing $`\lnot\bigcirc\bot`:

{stmt}`Yf`

The relativised odd rungs, with $`\bigcirc Y` for the variable and $`t_3` for
the bottom:

{stmt}`phiK`

The separators:

{stmt}`sepC`

The generators, $`x_0` reading $`S` and $`x_r`, $`r \ge 1`, reading the $`r`-th
cell of the construction below:

{stmt}`gen`

The bases are $`\sigma^{0}\bot = \bot` and
$`\sigma^{m+1}\bot = \bigcirc\sigma^{m}\bot \lor (\bigcirc\sigma^{m}\bot \twoheadrightarrow \sigma^{m}\bot)`
(`base`, by computation; so $`\sigma^{1}\bot = t_3`).  For $`m = 2` by `rfl`:

{stmt}`base_three`

{leanStmt base_three}

Each $`x_r` is variable-free and lies above $`\sigma^{3}\bot`, and the variable
$`p_i` is sent to $`x_i` (`x3_vf`, `b3_le_x3`, `x3_pvar`).

# The construction

The argument is carried out in one semantics, subframe models (Section 9).
Soundness for all subframe models and completeness for the finite ones with
decidable $`S` are choice-free (`SubframeModel.CF.soundness₁`,
`SubframeModel.CF.completeness_imp`).  A Kripke model for IPC is the subframe
model with the same worlds and $`S = \emptyset`; on $`\bigcirc`-free formulas
the two agree.  The multi-edge constraint models `cmM` of
`wip/f0Indep.lean` serve the independence results of Section 4 only and are
not used here: no constant of them occurs among the dependencies of the
results of this section printed here (a trace of their constants,
2026-10-28; the results of PR #106 were not traced).  Constraint models occur
in those dependencies at one place only, inside the library's
completeness theorem for finite subframe models, which reaches the soundness
of constraint models through Kripke frames (`FRJ.valid_of_derivable`); and the
one-generator case at $`t_3` (`freeIPL1`) also uses the constraint model
lifted from the ladder below (`not_deriv_of_sep`).

_Preservation_ ($`\Longrightarrow`).  $`h` is a substitution of $`x_i` for
$`p_i` together with $`\bot := \sigma^{3}\bot`, and every $`x_i` lies above
$`\sigma^{3}\bot`, so every image lies above $`\sigma^{3}\bot` and ex falso
translates.  The proof in Lean is semantic (`relB_preserves`, through the
relativisation lemma (iv) below).

_Reflection_ ($`\Longleftarrow`).  Suppose $`A \nvdash B`.  Completeness gives a
finite Kripke model $`K` and a node $`k` with $`k \Vdash A` and
$`k \nVdash B`.  The gadget $`\mathcal{M}(K)` (`Gad.MK`) is built from cells.

_The cells._  For each $`r`, the cell $`Z_r` (`ZL.M`, `wip/f0FreeHAn.lean`) has
two top worlds, one outside $`S`, where $`\bigcirc\bot` holds, and one in $`S`,
where $`\lnot\bigcirc\bot` holds; a Rieger–Nishimura ladder of $`r + 1` worlds
in $`S`, on which $`\bigcirc Y` plays the variable and $`t_3` the bottom; a
world $`f` outside $`S` below both tops; and a bottom $`m_r \in S` below
everything.  $`m_r` is the only world of $`Z_r` refuting $`\sigma^{2}\bot`, so
it is $`\sigma^{2}\bot`-maximal (`ZL.bmax_m`), and it reads the odd rungs.
The reading goes through the Rieger–Nishimura ladder (`ladder`,
`wip/rnEmbed.lean`): worlds $`0, 1, 2, \ldots`, each seeing itself and every
world at least two below it, with $`p` true exactly at $`0`.  It is a
one-variable Kripke model, here the subframe model with $`S = \emptyset`, and
only $`\bigcirc`-free formulas are evaluated on it; $`r_{2k+1}` holds at
$`w` iff $`w \le k` (`sat_rn_odd_cf`, choice-free).  The ladder worlds,
$`f` and $`m_r` of $`Z_r` are mapped onto it by a p-morphism under which the
relativisation $`A[p := \bigcirc Y,\ \bot := t_3]` of a one-variable
$`\bigcirc`-free $`A` holds iff $`A` holds at the image (`ZL.transfer`).
PROVED:

{stmt}`Cell.phi_bot`

{leanStmt Cell.phi_bot}

So $`c_r = \varphi_{r+1} \lor (\varphi_{r+2} \twoheadrightarrow \sigma^{2}\bot)`
fails at $`m_r` and holds at $`m_n` for $`n \ne r` (`Cell.sep_bot`): the first
disjunct holds when $`n + 2 \le r + 1`, the second when $`n + 2 > r + 2`.

_The gadget_ $`\mathcal{M}(K)`:

* a copy $`w_k` of each node $`k` of $`K`, with $`w_j \le w_k` iff
  $`j \le k`, and $`w_k \in S` iff $`k \nVdash p_0`;
* above every copy, the cell $`Z_0`, whose bottom $`m_0 \in S` is the first
  _killer_, and the second killer $`m'_0 \notin S`, the world $`m_0` taken out
  of $`S` (below the other worlds of $`Z_0`); both are
  $`\sigma^{2}\bot`-maximal;
* for each $`r \ge 1`, the cell $`Z_r`, whose bottom $`m_r` is the _reader_ of
  $`p_r`: it lies above $`w_k` iff $`k \nVdash p_r`.

The facts:

* (i) Every $`\sigma^{2}\bot`-maximal world forces $`\sigma^{3}\bot`.  If it is
  outside $`S`, every world of $`S` above it is a proper successor and forces
  $`\sigma^{2}\bot`, so it forces $`\bigcirc\sigma^{2}\bot`; if it is in $`S`,
  no world above it forces $`\bigcirc\sigma^{2}\bot` and refutes
  $`\sigma^{2}\bot`, so it forces
  $`\bigcirc\sigma^{2}\bot \twoheadrightarrow \sigma^{2}\bot` (pen argument; in
  $`\mathcal{M}(K)` every world other than a copy forces $`\sigma^{3}\bot`,
  PROVED world by world: `Cell.b3_all`, `Gad.z_b3`, `Gad.kn_b3`).  Every copy
  refutes $`\sigma^{3}\bot`: $`\bigcirc\sigma^{2}\bot` fails by $`m_0`, and
  $`\bigcirc\sigma^{2}\bot \twoheadrightarrow \sigma^{2}\bot` by $`m'_0`, which
  forces $`\bigcirc\sigma^{2}\bot` (`Gad.w_not_b3`).
* (ii) $`x_0 = \bigcirc\sigma^{3}\bot` reads $`S`: it holds at $`w_k` iff no
  copy above $`w_k` is in $`S`, iff $`k \Vdash p_0` (`Gad.w_gen0`).
* (iii) $`x_r`, $`r \ge 1`, reads $`p_r`.  Among the readers and killers,
  $`c_r` fails exactly at $`m_r`: $`m_0` forces $`\varphi_{r+1}`, and $`m'_0`
  forces $`\bigcirc Y`, hence every $`\varphi_k`.  So
  $`(c_r \twoheadrightarrow \sigma^{2}\bot) \twoheadrightarrow \sigma^{2}\bot`
  holds at $`w_k` iff $`m_r` is not above $`w_k`, iff $`k \Vdash p_r`
  (`Gad.w_gen_succ`).
* (iv) The relativisation lemma (`relB_transfer`, `wip/f0FreePair.lean`): a
  map $`\varphi` from a Kripke model $`K` into a subframe model $`M` that sends
  every node to a world refuting $`b`, is monotone, satisfies the back
  condition relative to $`b` (every successor of $`\varphi(k)` forces $`b` or
  is $`\varphi(j)` for some $`j \ge k`) and reads the variables, carries every
  $`\bigcirc`-free formula to its relativisation.  PROVED:

{stmt}`Pair.relB_transfer`

{leanStmt Pair.relB_transfer}

With $`\varphi(k) = w_k` and $`b = \sigma^{3}\bot`, (i) to (iii) are the
hypotheses.  PROVED:

{stmt}`Gad.transfer`

{leanStmt Gad.transfer}

Reflection follows: $`k \Vdash A` gives $`w_k \Vdash h(A)`; if
$`h(A) \vdash h(B)`, soundness gives $`w_k \Vdash h(B)`, so $`k \Vdash B`,
against the choice of $`K` (`free3_reflects`).  The gadget is infinite, with one
cell for every generator; soundness holds in every subframe model, and only
$`K` needs to be finite.  For $`H_\omega` the same gadget reads every variable
$`q` through an injection $`\mathrm{code}` of the variables into $`\mathbb{N}`
by their UTF-8 bytes (`code_inj`, choice-free), with the generator
$`x_{\mathrm{code}(q)}` (`xω`, `freeOmega3`).

Before the general proof, three designed cells were shown to have images that
are no theorems: $`(p_1 \twoheadrightarrow p_2) \lor (p_2 \twoheadrightarrow p_1)`,
$`\lnot\lnot p_2 \twoheadrightarrow p_2` and
$`(p_0 \twoheadrightarrow p_2) \lor (p_2 \twoheadrightarrow p_0)`
(`cell_Ca`, `cell_Cb`, `cell_Cc`; kernel-checked gadget countermodels of 12
and 13 worlds).

The case $`n = 2` over $`\sigma^{2}\bot` (`freePair`) is the same design one
level down: base $`\sigma^{2}\bot`, threshold $`t_3`, the three
$`t_3`-maximal worlds $`f`, $`g`, $`h` above the copies, one of each of the three
types, and the generators $`y_0 = \bigcirc\sigma^{2}\bot`, reading $`S`, and
$`y_1 = \sigma^{2}\bot \lor ((\bigcirc Y \twoheadrightarrow t_3) \twoheadrightarrow t_3)`,
reading whether $`h` lies above.  PROVED:

{stmt}`Pair.FreePair`

{leanDef Pair.FreePair}

{leanStmt Pair.freePair}

_PLL itself_ (`wip/f0FreePLL.lean`, PR #106).  Drop $`x_0`: the variable $`a`
is read by the reader $`m_{\mathrm{code}(a)+1}` alone, and the copy keeps the
$`S` of $`K`, now any finite subframe model: $`w_k \in S` iff $`k \in S`.  The
killer $`m_0` lies above every copy as before.  The relativisation lemma gains
a $`\bigcirc` case (`relB_transferO`), under the condition that
$`\varphi(k) \in S` iff $`k \in S`: a world of $`S` above $`\varphi(k)` either
forces $`b`, and with it every relativised formula, or is $`\varphi(j)` for
some $`j \ge k` in $`S`.  Preservation is semantic again, on the worlds
refuting $`\sigma^{3}\bot` with $`S` restricted to them.  Before the proof,
three designed cells, $`\bigcirc p \twoheadrightarrow p`,
$`\bigcirc p \lor \lnot\bigcirc p` and
$`\bigcirc(p \lor q) \twoheadrightarrow \bigcirc p \lor \bigcirc q`, were shown
to have images that are no theorems (`cell_O1`, `cell_O2`, `cell_O3`), and a
gadget whose copies read $`S` as in the $`x_0` design was watched failing on
the second.  PROVED (`freeReaders`, `freePLLAbove_base3`; pins
$`\mathsf{propext}`, $`\mathsf{Quot.sound}`).

# Any family, and every base above

The choice of readers and killers does not matter.  Any $`n + 1`
$`\sigma^{2}\bot`-maximal worlds of pairwise different types, in finite
subframe models, give a copy of $`H_n` in $`[\sigma^{3}\bot, \top]`.  A given
world refuting $`\bigcirc\sigma^{2}\bot` serves as the killer that refutes it,
a given world forcing it as the other killer, and where there is none, $`m_0`
or $`m'_0` is added; $`n - 1` of the remaining worlds are the readers, each
with a separator that is a disjunction of one formula for each other
distinguished world; the gadget is built over the disjoint sum of their models
(`GadU`, `transferF`, `fromCells3`).  PROVED:

{stmt}`AnyFamily.freeHAnAbove_base3_of_distinct`

{leanStmt AnyFamily.freeHAnAbove_base3_of_distinct}

With $`k(\sigma^{2}\bot) = \infty` (`base2_unbounded`) this gives
`freeHAnAbove_base3` again (`freeHAnAbove_base3'`).

_The_ $`\sigma`_-shift._  For a variable-free base $`b`, a free copy over $`b`
gives one over $`\sigma^{k}(b)`, with the generators $`\sigma^{k}(x(q))`:
$`\sigma^{k}` is faithful (Section 9) and commutes with the relativisation
(`sigN_relB`).  PROVED:

{stmt}`AnyFamily.SigShift`

{leanDef AnyFamily.SigShift}

{leanStmt AnyFamily.sigShift}

Since $`\sigma^{k}(\sigma^{3}\bot) = \sigma^{3+k}\bot` (`sigN_base`), every base
above $`\sigma^{3}\bot` in the sequence carries every $`H_n` and
$`H_\omega`.  PROVED:

{stmt}`AnyFamily.AllAbove3`

{leanDef AnyFamily.AllAbove3}

{leanStmt AnyFamily.allAbove3}

{stmt}`AnyFamily.AllAbove3ω`

{leanDef AnyFamily.AllAbove3ω}

{leanStmt AnyFamily.allAbove3ω}

# The formal statement

$`[b, \top]` contains the free Heyting algebra on $`n` generators:

{stmt}`FreeHAnAbove`

{leanDef FreeHAnAbove}

The conjecture:

{stmt}`Conjecture`

{leanDef Conjecture}

One family of generators for every $`n`:

{stmt}`FreeFamily3`

{leanDef FreeFamily3}

PROVED, with the family $`x(p_i) = x_i`:

{leanStmt freeFamily3}

So every $`H_n`, and $`H_\omega`, lies in $`[\sigma^{3}\bot, \top]`.  PROVED:

{stmt}`freeHAnAbove_base3`

{leanStmt freeHAnAbove_base3}

{stmt}`freeHAωAbove_base3`

{leanStmt freeHAωAbove_base3}

The conjecture, with $`m = 3`.  PROVED:

{leanStmt conjecture}

For PLL the statement is `FreePLLAbove b`: `FreeHAωAbove b` with the side
condition `boxFree` dropped, so that $`A` and $`B` range over all formulas
(`wip/f0FreePLL.lean`, PR #106; PROVED for $`b = \sigma^{3}\bot`).

Why the statement says what the summary claims:

* (a) _Clause by clause._  `atomFree (x a)`: every generator is variable-free,
  so the copy lies in $`F_0`.  `Deriv [b] (x a)`: every generator lies in
  $`[b, \top]`.  `boxFree`: $`A` and $`B` are $`\bigcirc`-free, formulas of
  IPC.  `varsBelow n`: their variables are among $`p_0, \ldots, p_{n-1}`.  The
  biconditional: the relativisation $`h` preserves ($`\Longrightarrow`) and
  reflects ($`\Longleftarrow`) derivability.
* (b) _The calculus._  `Deriv Γ φ` is `Nonempty (LaxND Γ φ)`, the reference
  natural deduction of {cite}`FairtloughMendler1997` (Section 2;
  `docs/calculus-map.md`).  The semantics appears only inside the proofs.
* (c) _From the Lean statement to a Heyting embedding of_ $`H_n`.
  `conservativity_IPL` (mechanised, axioms {axiomsOf}`conservativity_IPL`)
  makes $`\bigcirc`-free PLL derivability IPC derivability, and the Lindenbaum
  algebra of IPC on $`p_0, \ldots, p_{n-1}` is $`H_n` (textbook, not
  mechanised).  $`h` is a substitution, so it commutes with $`\land`, $`\lor`,
  $`\twoheadrightarrow` and sends $`\bot` to $`\sigma^{3}\bot`, the bottom of
  $`[\sigma^{3}\bot, \top]`, a Heyting algebra with the $`\land`, $`\lor`,
  $`\twoheadrightarrow` of $`F_0` since $`b \vdash a \twoheadrightarrow b`.  It is
  well defined on classes by ($`\Longrightarrow`) and one-to-one by
  ($`\Longleftarrow`): a Heyting embedding (pen, three lines).
* (d) _Trust base._  The Lean kernel; the axioms $`\mathsf{propext}` and
  $`\mathsf{Quot.sound}` (computed in Section 13); no `Classical.choice`, no
  `sorry`, no `native_decide`.  The pins are enforced at build time by
  `#axioms_within` and were watched failing at tighter bounds.
* (e) _Teeth._  The generators are explicit formulas; the same statement is
  REFUTED at $`t_3` (`not_FreeIPLInAboveT3`, and `noFreeHA2` for every pair);
  the designed cells were shown unprovable before the general proof.
* (f) _Not mechanised:_ the identification of $`H_n` with the Lindenbaum
  algebra of IPC, and the homomorphism remark of (c).

# Three forms of a copy

A copy of a Heyting algebra $`H` in $`F_0` is a map $`e : H \to F_0` of one of
three strengths (`wip/f0EmbedForms.lean`): (H) a Heyting embedding into
$`[b, \top]`, preserving the $`\land`, $`\lor`, $`\twoheadrightarrow` of
$`F_0`, sending $`\bot` to $`b`, reflecting the order; (L) a lattice embedding,
preserving $`\land`, $`\lor`, reflecting the order, with $`\twoheadrightarrow`
computed in the image; (O) an order embedding, all operations computed in the
image.  `FreeHAnAbove` is (H).  By the pairwise lemma (`pairwiseHimp`) an
(L)-copy has $`e(a \Rightarrow c) \le e(a) \Rightarrow e(c)`, with equality
exactly when $`e(a) \Rightarrow e(c)` lies in the image, so (L) and (H) agree
pair by pair; by the shift (`shift`) the image of the bottom can be lowered to
any $`b' \le e(\bot)` without losing (O).  Applied to `freePair`, the shift
gives an (O)-copy of $`H_2` with bottom $`\bot` (`shiftH2`, `shift2_orderEmb`)
that does not preserve $`\land`: $`h(p) \land h(\lnot p) \dashv\vdash \sigma^{2}\bot`
and $`\sigma^{2}\bot \nvdash \bot` (`shiftMeetFails`), as `noMeetCopyH2_bot`
requires.  All PROVED.  Applied to `freeHAnAbove_base3`, it gives an (O)-copy of
every $`H_n` with bottom $`\bot` (pen; not stated as a theorem).

$$`\text{(H)} \Longrightarrow \text{(L)} \Longrightarrow \text{(O)}, \qquad \text{(H) with bottom } b \Longrightarrow \text{(O) with any bottom } b' \le b.`

# The complement of the range

$`h` is one-to-one, not onto $`[\sigma^{3}\bot, \top]`.

* (1) _$`\bigcirc x_1` is not in the range._  PROVED (`not_image_circ_x1`,
  `sep_circ_x1`; `wip/f0FreePLL.lean`, PR #106).  In every gadget
  $`\bigcirc x_1` holds at $`w_k` iff $`k \Vdash p_0 \lor p_1`, because $`x_0`
  and $`\bigcirc` both read $`S`: the worlds of $`S` above $`w_k` are the copies
  $`w_j`, $`j \ge k`, with $`j \nVdash p_0`, and worlds forcing
  $`\sigma^{3}\bot`, hence $`x_1`.  If $`\bigcirc x_1 \dashv\vdash h(A)`, the
  transfer gives $`k \Vdash A` iff $`k \Vdash p_0 \lor p_1` in every finite
  $`K`, so $`A \dashv\vdash p_0 \lor p_1` and
  $`\bigcirc x_1 \dashv\vdash x_0 \lor x_1`.  A small subframe model separates
  them: a world $`w \notin S` below a world $`s \in S`, both below the
  killers, with the reader $`m_1` above $`w` but not above $`s`.  Then
  $`s \nVdash x_0` and $`s \Vdash x_1`, so $`w \Vdash \bigcirc x_1`, while
  $`w \nVdash x_0` and $`w \nVdash x_1` (a 12-world model, kernel-checked).
  So the range is not closed under $`\bigcirc`; only the direction from
  $`\bigcirc x_1` to $`p_0 \lor p_1` is used.  The copy of PLL of the summary,
  with the readers alone and $`\bigcirc \mapsto \bigcirc`, is closed under
  $`\bigcirc` by construction.
* (2) _The scaffolding._  The elements outside the range depend on the choice
  of readers and killers, and that choice is free: any $`n + 1`
  $`\sigma^{2}\bot`-maximal worlds of pairwise different types give a copy
  of $`H_n` in $`[\sigma^{3}\bot, \top]`, PROVED (`anyFamily3`,
  `freeHAnAbove_base3_of_distinct`, above).  So the copy, and with it the
  complement of its range, rests on a choice, and no single complement is
  canonical (remark).
* (3) Below $`\sigma^{3}\bot` the free structure thins out, as the table of
  bases shows.

# Supporting declarations

{lemmaTable relB pvar varsBelow FreeHAωAbove MeetCount.MeetEmb TypeBound Distinct ZL.relX ZL.bmax_m ladder sat_rn_odd_cf ZL.transfer ZL.cell_force base2_unbounded not_typeBound_base2 FreeIPL.FreeIPLInAboveT3 FreeIPL.FreeIPL1InAboveT3 FreeIPL.freeIPL1 FreeIPL.noFreeHA2 FreeIPL.not_FreeIPLInAboveT3 Pair.FreePair Pair.freeHAnAbove_base2_two Pair.relB_preserves MeetCount.typeBound_bot MeetCount.typeBound_t3 MeetCount.NoMeetCopyH2 MeetCount.noMeetCopyH2_bot MeetCount.noMeetCopyH2_t3 MeetCount.countingCriterion x3 x3_pvar x3_vf b3_le_x3 Free3 free3_preserves free3_reflects free3 freeFamily3_of_free3 freeHAnAbove_of_family conjecture_of_base3 Cell.b3_all Cell.sep_bot Cell.sepimp_bot Gad.Dp Gad.w_not_b3 Gad.w_gen0 Gad.w_gen_succ Gad.w_read Base3.code Base3.code_inj Base3.xω Base3.FreeOmega3 Base3.freeOmega3 Base3.cell_Ca Base3.cell_Cb Base3.cell_Cc EmbedForms.PairwiseHimp EmbedForms.pairwiseHimp EmbedForms.Shift EmbedForms.shift EmbedForms.ShiftH2 EmbedForms.shiftH2 EmbedForms.ShiftOrderEmb EmbedForms.shift2_orderEmb EmbedForms.ShiftMeetFails EmbedForms.shiftMeetFails AnyFamily.AnyFamily3 AnyFamily.anyFamily3 AnyFamily.freeHAnAbove_base3' AnyFamily.sigN_relB AnyFamily.sigN_base AnyFamily.SigShiftω AnyFamily.sigShiftω}

Pins: every declaration of `wip/f0FreeIPL.lean`, `wip/f0FreeHAn.lean`,
`wip/f0FreePair.lean`, `wip/f0MeetCount.lean`, `wip/f0FreeBase3.lean` and
`wip/f0FreeAnyFamily.lean` here within `propext`, `Quot.sound`
(`#axioms_within`); in
`wip/f0EmbedForms.lean`, `pairwiseHimp` and `shift` within no axioms, the rest
within `propext`, `Quot.sound`.
