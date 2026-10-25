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

#doc (Manual) "The Dedekind–MacNeille completion" =>

$`F_0` has holes: the gaps $`g_k`, $`k \ge 1`, have lower bounds but no greatest
one (Section 6), and so do the halves $`f(1/2^{n})` (Section 7).  The
Dedekind–MacNeille completion $`F^{*}` fills every such hole, as Dedekind's cuts
fill the holes of $`\mathbb{Q}` {pcite}`Dedekind1872 MacNeille1937`.  This
section gives the construction, what is proved about it and where
`Classical.choice` enters, the extension of $`\bigcirc`, and what the points of
$`F^{*}` are.  Files: `wip/f0MacNeille.lean`, `wip/f0Nuclear.lean`,
`wip/f0MacNeilleNonUnique.lean`, `wip/f0MacNeillePoints.lean`.

# Cuts

For $`S \subseteq F_0` write $`S^{u}` for the set of upper bounds of $`S` and
$`S^{l}` for its set of lower bounds.  A _cut_ is a pair $`(L, U)` of subsets of
$`F_0` with

$$`U = L^{u} \qquad\text{and}\qquad L = U^{l},`

so that each of the two sets determines the other, and $`F^{*}` is the set of
cuts, ordered by

$$`(L, U) \le (L', U') \iff L \subseteq L' \iff U' \subseteq U.`

Each $`a \in F_0` gives the _principal_ cut
$`{\downarrow}a = (\{x : x \le a\},\ \{y : a \le y\})`, and
$`{\downarrow}a \le {\downarrow}b` exactly when $`a \le b`, so $`F_0` is a
suborder of $`F^{*}`.  In Lean $`F^{*}` is Mathlib's `DedekindCut RNClass`, the
concept lattice of $`\le` on $`F_0`, with $`\mathrm{L}(x)` and $`\mathrm{U}(x)`
the two sets of a cut $`x` and `DedekindCut.principal` the embedding.

_The analogy with Dedekind's reals._  Applied to $`\mathbb{Q}`, the same
construction gives the real line with $`-\infty` and $`+\infty` added (the cuts
$`(\emptyset, \mathbb{Q})` and $`(\mathbb{Q}, \emptyset)`); $`F_0` has a least
and a greatest element, so $`F^{*}` adds no new end points.  Point by point:

:::f0table (widths := "0.17 0.38 0.41")
* * Feature
  * $`\mathbb{Q}` in $`\mathbb{R}`
  * $`F_0` in $`F^{*}`
* * A cut
  * $`(A, B)` with $`A \cup B = \mathbb{Q}` and $`A` below $`B`: a split point
  * $`(L, U)` with $`U = L^{u}`, $`L = U^{l}`: a pair of sets, $`L \cup U \ne F_0` in general
* * Old points
  * the rationals
  * the principal cuts $`{\downarrow}a`: $`L` has a greatest element
* * New points
  * the irrationals: $`A` has no greatest element, $`B` no least
  * the limit points: $`L` has no greatest element, equivalently $`U` no least
* * Density
  * every real is the supremum of the rationals below it, and the infimum of those above
  * every cut is the join of the principal cuts below it, and the meet of those above (PROVED)
* * Completeness
  * every bounded set of reals has a supremum
  * every set of cuts has a join and a meet (PROVED)
* * Operations
  * $`+`, $`\times` extend
  * $`\land`, $`\lor`, $`\Rightarrow` extend, and $`\bigcirc` extends as a nucleus, not uniquely in general (PROVED, REFUTED)
* * Size
  * $`2^{\aleph_0}`
  * $`2^{\aleph_0}` (PROVED)
:::

_Where the analogy fails._  $`\mathbb{Q}` is a chain, so every rational lies
in $`A` or in $`B`, and a cut is fixed by a single position.  $`F_0` is not a
chain (from $`g_2` on the gaps are pairwise incomparable, Section 2), and an
element may lie in neither set of a cut.  For the principal cut of
$`t_1 = \bigcirc\bot`, $`L = \{\bot, t_1\}` and $`U = {\uparrow}t_1`, and
$`t_2 = \lnot\bigcirc\bot` lies in neither, as $`t_1` and $`t_2` are
incomparable.  So a cut of $`F_0` is a pair of sets, not a split point, and
$`F^{*}` is not a chain.  What survives is the order-theoretic content:
cuts as pairs of polars, density from both sides, completeness.

# A complete Heyting algebra

$`F^{*}` is a complete lattice: the meet of a family of cuts
$`(L_i, U_i)` has left set $`\bigcap_i L_i`, and the join has right set
$`\bigcap_i U_i` (Mathlib's concept lattice).  $`F_0` sits inside it
join-densely and meet-densely: every cut is the join of the principal cuts of
its left set and the meet of the principal cuts of its right set,

$$`x = \bigvee \{{\downarrow}a : a \in \mathrm{L}(x)\} = \bigwedge \{{\downarrow}b : b \in \mathrm{U}(x)\}.`

PROVED, for every Heyting algebra $`H` in place of $`F_0` (in the displays,
$`{\downarrow}[S]` is the image of $`S` under $`{\downarrow}`).

{stmt}`MacNeille.sSup_principal_left`

{leanStmt MacNeille.sSup_principal_left}

{stmt}`MacNeille.sInf_principal_right`

{leanStmt MacNeille.sInf_principal_right}

For a Heyting algebra $`H`, the cuts of $`H` carry an implication,

$$`X \Rightarrow Y = \bigwedge \{ {\downarrow}(h \Rightarrow k) : h \in \mathrm{L}(X),\ k \in \mathrm{U}(Y) \},`

right adjoint to $`\land`, so $`\mathrm{DM}(H)` is a complete Heyting algebra
(a frame) {pcite}`HardingBezhanishvili2004` (Theorem 2.3, with the implication
of Proposition 2.4).  PROVED.

{stmt}`MacNeille.le_cutHimp_iff`

{leanStmt MacNeille.le_cutHimp_iff}

The principal embedding is a homomorphism of Heyting algebras: it preserves
$`\land`, $`\lor`, $`\bot`, $`\top` (`principalHom`) and $`\Rightarrow`.
PROVED.

{stmt}`MacNeille.principal_himp`

{leanStmt MacNeille.principal_himp}

$`F_0` is a Heyting algebra with the nucleus $`\bigcirc` without
`Classical.choice` (`instHeyting`, `circNucleus`), so all of this holds at
$`H = F_0`: $`F^{*}` is a complete Heyting algebra, and $`F_0` a join- and
meet-dense Heyting subalgebra of it.  $`F_0` itself is not complete: the gaps
have no greatest lower bound (`gap_no_glb`, Section 6), and their meet in
$`F^{*}` is a new point (below).

# Where choice enters

Everything about cuts carries `Classical.choice`.  `#axiom_path`
(`Meta/Audit.lean`) traces it, for every declaration about cuts in this
section, to one of two places in Mathlib, neither of them part of the
mathematics.

* _The order on cuts._  Mathlib orders concepts by lifting the inclusion order
  of `Set RNClass` along the left set (`Concept.instPartialOrder`), and reads
  that order off the complete atomic Boolean algebra of sets,
  `Set.instCompleteAtomicBooleanAlgebra`.  Its law of complete distributivity
  (an intersection of unions is a union of intersections) is proved with
  `Classical.skolem`.  Inclusion itself, the polars $`S^{u}`, $`S^{l}` and the
  meets and joins of cuts need none of it, yet even `DedekindCut.principal`
  reaches choice this way, through Mathlib's lemmas on polars.
* _The nucleus API._  `Nucleus.monotone` and `Nucleus.le_apply` pass through
  `InfHomClass.toOrderHomClass`, whose proof uses `Classical.propDecidable`.  A
  map that preserves $`\land` is monotone without it: $`a \le b` gives
  $`j(a) = j(a \land b) = j(a) \land j(b) \le j(b)`.

Two uses are of another kind.  The refutation of uniqueness below defines its
nuclei by cases on $`X \le m`, a decision that needs excluded middle, so there
choice is used by the counterexample itself.  And the points of $`F^{*}` below
reach choice also through `L_no_greatest` (excluded middle in
`plain_trace_dichotomy`, `wip/floor.lean`), through the completeness theorem
that reads $`\le` on $`F_0` as $`\vdash`, and, for the cardinality, through
$`\mathbb{R}`.  That completeness theorem, for constraint models
(`consequence_iff_derivable`, behind `le_iff_nonempty`), carries
`Classical.choice`, and so does the transfer from subframe to constraint models,
`SubframeModel.toConstraint_force` (a case split on membership of $`S`).  The
non-normal filter $`F_7` below avoids all three: it goes through completeness
for finite subframe models with decidable $`S` (`SubframeModel.CF.completeness`,
proved through the FRJW calculus), which is choice-free, and a transfer
re-proved for decidable $`S`.

_A choice-free $`F^{*}`:_ OPEN.  Cuts as pairs of predicates on $`F_0`, with
the order $`L \subseteq L'`, the meets and joins above and the implication
$`X \Rightarrow Y` written out by hand, and a nucleus given by its three laws.
Plausible: each proof in `wip/f0MacNeille.lean` is reasoning about elements
with upper and lower bounds and the adjunction of $`\Rightarrow`, and the trace
finds choice only inside the two Mathlib instances.  Not attempted.

# The extension of ◯

For $`E : H \to L` an order-reflecting Heyting homomorphism into a frame,
join-dense, and $`j` a nucleus on $`H`, the _upper extension_

$$`\overline{j}^{E}(x) = \bigwedge \{ E(j(a)) : a \in H,\ x \le E(a) \}`

is a nucleus extending $`j`.  At $`L = \mathrm{DM}(H)` this is Goldblatt's
theorem {pcite}`Goldblatt2010`, §2, which has priority.  The meet law needs
inflation and that $`h \Rightarrow j(b)` is a fixed point; upper extensions need
not preserve meets in general {pcite}`TheunissenVenema2007` (Example 3.8;
closure operations, Example 6.8; see also {cite}`GehrkeHardingVenema2006`).
New here: it is the greatest monotone extension, and the nuclear extensions of
$`j` are exactly the interval from the least of them, $`\underline{j}^{E}`, to
$`\overline{j}^{E}`.  PROVED (the nearest statement found is Proposition 5.9 of
{cite}`TheunissenVenema2007`).

{stmt}`exists_nucleus_extension`

{leanStmt exists_nucleus_extension}

{stmt}`extends_iff_mem_Icc`

{leanStmt extends_iff_mem_Icc}

At $`F_0`: $`\bigcirc` extends to $`F^{*}` as the nucleus
$`\overline{\bigcirc}`, the greatest monotone extension.  PROVED.

{stmt}`circ_extends_to_DM`

{leanStmt circ_extends_to_DM}

Uniqueness fails in general: REFUTED on the chain
$`\mathbb{N} \oplus_{\mathrm{lex}} \mathbb{N}^{\mathrm{op}}`, with the nucleus
fixing the lower copy of $`\mathbb{N}` and sending the upper copy to $`\top`;
the new cut $`m` between the copies is sent to $`m` by one extension and to
$`\top` by another ({cite}`TheunissenVenema2007`, Example 3.11).  The witness
is a gap like those of $`F_0`: a down-set without greatest element under an
up-set without least element.  Whether the interval of extensions is a single
point at $`F_0` is OPEN (Section 13).

{stmt}`MacNeilleNonUnique.nucleus_extension_not_unique`

{leanStmt MacNeilleNonUnique.nucleus_extension_not_unique}

# The points of the completion

_Principal and limit points._  A point $`x` is principal exactly when
$`\mathrm{L}(x)` has a greatest element $`a`, and then $`x = {\downarrow}a`;
equivalently, when $`\mathrm{U}(x)` has a least element.  The others are the
_limit points_.  Pen argument, from the definitions.  As $`\mathbb{R}` is
reached from $`\mathbb{Q}` by monotone sequences, every limit point is the join
of a strictly increasing sequence $`a_0 < a_1 < \cdots` in $`F_0` with no join
in $`F_0`, and the meet of a strictly decreasing one with no meet in $`F_0`;
conversely, the join in $`F^{*}` of such a sequence is a limit point.  Pen
argument: $`\mathrm{L}(x)` contains $`\bot` and is closed under $`\lor`, and it
is countable, as $`F_0` is (PROVED, the `Countable` instance in
`wip/f0MacNeillePoints.lean`); the partial joins of an enumeration are cofinal
in it, and not eventually constant when it has no greatest element, so a
subsequence increases strictly and has join $`x` by join-density; had it a join
$`c` in $`F_0`, then $`x = {\downarrow}c`, as $`{\downarrow}` preserves the
joins that exist.  Conversely, if the join in $`F^{*}` were $`{\downarrow}c`,
then $`c` would be the join in $`F_0`.

_Two limit points._  The meet of the gaps,
$`x_{\mathrm{gap}} = \bigwedge \{{\downarrow}g_k : k \ge 1\}`, is not principal:
were it $`{\downarrow}a`, then $`a` would be a greatest lower bound of the gaps
in $`F_0`, against `L_no_greatest` (Section 6).  PROVED.  It is also the meet of
the decreasing partial meets $`{\downarrow}(g_1 \land \cdots \land g_n)`.

{stmt}`PLLND.F0.Points.gapCut_ne_principal`

{leanStmt PLLND.F0.Points.gapCut_ne_principal}

{leanDef PLLND.F0.Points.gapCut}

The meet of the halves, $`\bigwedge_n {\downarrow}f(1/2^{n})`, is a second limit
point, by the same argument from `halves_no_glb_vf` (Section 7).  Pen argument.

_The size of $`F^{*}`._  $`|F^{*}| = 2^{\aleph_0}`.  PROVED.  Above: a cut is
determined by its left set, and $`F_0` is countable (onto it from a countable
syntax of the variable-free formulas).  Below: with $`f'` the choice-free
embedding of $`\mathbb{Q}` (`rat_embedding_cf`, Section 5), put

$$`X_r = \bigvee \{ {\downarrow}f'(q) : q \in \mathbb{Q},\ q < r \} \qquad (r \in \mathbb{R}).`

For $`r < r'` take rationals $`r < q_1 < q_2 < r'`; then
$`X_r \le {\downarrow}f'(q_1) < {\downarrow}f'(q_2) \le X_{r'}`, so
$`r \mapsto X_r` is one-to-one (`X_injective`).  It is also monotone (pen,
immediate), so it embeds $`\mathbb{R}` in $`F^{*}`: every cut of the thread
$`f'[\mathbb{Q}]` has its point in $`F^{*}`, as every cut of $`\mathbb{Q}` has
its real.

{stmt}`PLLND.F0.Points.card_eq_continuum`

{leanStmt PLLND.F0.Points.card_eq_continuum}

_Filters._  A _filter_ of $`F_0` is a nonempty up-set closed under $`\land`
($`F_0` itself included).  The right set $`\mathrm{U}(x)` of every point is a
filter, and a filter $`F` is _normal_ when $`F = F^{lu}`.  The rest of this
section is pen argument, on the definitions, except where marked.

* _The normal filters are exactly the points._  $`x \mapsto \mathrm{U}(x)` and
  $`F \mapsto (F^{l}, F)` are inverse, between $`F^{*}` and the normal filters,
  and reverse the order: $`x \le y` iff $`\mathrm{U}(y) \subseteq \mathrm{U}(x)`.
  For a cut, $`\mathrm{U}(x) = \mathrm{L}(x)^{u}` is a filter (the upper bounds
  of any set are), and normal, as $`\mathrm{U}(x) = \mathrm{U}(x)^{lu}`.
  Principal filters are normal: $`({\uparrow}a)^{l} = {\downarrow}a` and
  $`({\downarrow}a)^{u} = {\uparrow}a`.
* _Every filter lies over a point._  For a filter $`F`, its meet in $`F^{*}`
  is $`\mu(F) = \bigwedge \{{\downarrow}a : a \in F\} = (F^{l}, F^{lu})`, and
  $`F \subseteq F^{lu} = \mathrm{U}(\mu(F))`, with equality exactly when $`F`
  is normal.  The filters over a point $`x` (its _fibre_) are those with
  $`F^{l} = \mathrm{L}(x)`; the greatest is $`\mathrm{U}(x)`.
* _A non-principal filter whose meet exists in $`F_0` is not normal._  If
  $`F^{l} = {\downarrow}m` then $`F^{lu} = {\uparrow}m \ni m`, and $`m \notin F`,
  or $`F` would be $`{\uparrow}m`.
* _Some fibres._  Over the least point, $`{\downarrow}\bot`, the fibre is
  $`\{F_0\}`: every proper filter has $`t_1` or $`t_2` as a lower bound (from
  `dichotomy` and $`{\downarrow}t_2 = \{\bot, t_2\}`).  Over $`{\downarrow}t_1`,
  $`{\downarrow}t_2`, $`{\downarrow}t_4` the fibre is the principal filter alone:
  a non-principal filter contains none of $`\bot`, $`t_1`, $`t_2`, $`t_4` (each
  would be its least element), so by `classify_low` (Section 10) it lies in
  $`{\uparrow}t_3` and has $`t_3` as a lower bound.  Over a principal point
  $`{\downarrow}a` in general, the fibre has a second member exactly when $`a`
  is the meet in $`F_0` of a strictly decreasing sequence that avoids it.
  Over $`{\downarrow}t_7` there are at least two, $`{\uparrow}t_7` and
  $`F_7` (PROVED, below).  Over $`{\downarrow}t_3` and $`{\downarrow}t_5`: OPEN
  (Section 13).

_Not every filter is normal._  Write
$`\rho_k = \mathrm{rel}(r_{2k+1})` for the relativised odd rungs of Section 8
($`p` read as $`u = \bigcirc\lnot\bigcirc\bot`, $`\bot` as $`t_3`), increasing
in $`k`, and $`t_7 = t_5 \lor t_6`.  Put

$$`d_k = \rho_k \twoheadrightarrow t_7, \qquad F_7 = \bigcup_{k \ge 2} {\uparrow}d_k.`

Then $`F_7` is a non-principal filter with meet $`t_7` in $`F_0`, so it is not
normal: it lies over the principal point $`{\downarrow}t_7` and
$`F_7 \subsetneq {\uparrow}t_7`.  PROVED, without `Classical.choice`
(`wip/f0Normal.lean`, where $`F_7 = \{y : \exists k.\ d_{k+2} \le y\}`).

{stmt}`PLLND.F0.Normal.NotAllNormal`

{leanStmt PLLND.F0.Normal.notAllNormal}

{leanDef PLLND.F0.Normal.NotAllNormal}

The proof, in five steps, each PROVED.

1. _Descending:_ $`\rho_k \le \rho_{k+1}`, and $`\twoheadrightarrow` is
   antitone in its first argument.

   {stmt}`PLLND.F0.Normal.Descending`

   {leanStmt PLLND.F0.Normal.descending}

2. _Strictly, from_ $`k = 2` _on:_ the countermodel of Section 8 (the
   Rieger–Nishimura ladder under three top worlds) with two worlds added: $`z`,
   below the two tops where $`\bigcirc\bot` holds, and $`x`, below $`z`, the
   ladder worlds $`0, \ldots, k-1` and the three tops, with no new modal steps.
   There $`x` forces $`\rho_{k+1}`, and every successor of $`x` that forces
   $`\rho_k` forces $`t_7`, so $`x \Vdash d_k`, while $`x` does not force
   $`t_7`.  At $`k = 1` the same model fails ($`x` forces $`\rho_3` but not
   $`\rho_2`), as was watched.

   {stmt}`PLLND.F0.Normal.StrictlyDescending`

   {leanStmt PLLND.F0.Normal.strictlyDescending}

3. _Lower bound:_ $`b \le a \twoheadrightarrow b`.

   {stmt}`PLLND.F0.Normal.LowerBound`

   {leanStmt PLLND.F0.Normal.lowerBound}

4. _Greatest lower bound._  In every finite subframe model with decidable
   $`S` every world forces some $`\rho_k`, by induction on the number of proper
   successors: if all proper successors of $`w` force $`\rho_J`, then $`w`
   forces $`\rho_{J+2} = \rho_{J+1} \lor (\rho_{J+1} \twoheadrightarrow \rho_J)`,
   since either $`w \Vdash \rho_{J+1}`, or every successor forcing
   $`\rho_{J+1}` is proper and so forces $`\rho_J`.  The same induction, with
   $`\bigcirc\bot` for $`u`, gives it for the odd rungs.

   {stmt}`PLLND.F0.Normal.Star`

   {leanStmt PLLND.F0.Normal.star}

   {stmt}`PLLND.F0.Normal.StarOdd`

   {leanStmt PLLND.F0.Normal.starOdd}

   Now if $`y \le d_{k+2}` for all $`k`, then at a world forcing $`y` some
   $`\rho_k` holds, hence $`\rho_{k+2}`, and $`y \le d_{k+2}` puts $`t_7` there;
   completeness for these models turns this into $`y \le t_7`.

   {stmt}`PLLND.F0.Normal.GreatestLowerBound`

   {leanStmt PLLND.F0.Normal.greatestLowerBound}

   The same argument shows that the only upper bound of all $`\rho_k`, or of
   all odd rungs, is $`\top`, so $`\bigwedge_k (\rho_k \twoheadrightarrow t_7) = (\bigvee_k \rho_k) \twoheadrightarrow t_7 = t_7`.

   {stmt}`PLLND.F0.Normal.SupRho`

   {leanStmt PLLND.F0.Normal.supRho}

   {stmt}`PLLND.F0.Normal.SupOddRungs`

   {leanStmt PLLND.F0.Normal.supOddRungs}

   In infinite models the induction fails: a world above the whole ladder of
   the $`\rho_k` forces every $`d_k` and not $`t_7`, so the meet is reached in
   the algebra only.

5. _Conclusion:_ $`F_7` is a union of a chain of principal filters, so a
   filter, with meet $`t_7` by 3 and 4, not principal by 2, and
   $`t_7 \notin F_7`, else $`d_k = t_7 = d_{k+1}`; so
   $`F_7^{lu} = {\uparrow}t_7 \ne F_7`.

   {stmt}`PLLND.F0.Normal.F7Meet`

   {leanStmt PLLND.F0.Normal.F7_meet}

   {stmt}`PLLND.F0.Normal.F7NonPrincipal`

   {leanStmt PLLND.F0.Normal.F7_nonPrincipal}

   {stmt}`PLLND.F0.Normal.F7NotNormal`

   {leanStmt PLLND.F0.Normal.F7_not_normal}

The construction needs an infinite principal downset, which $`F_0` has from
$`t_6` on (Section 8).  In the $`\bigcirc`-free analogue, the Rieger–Nishimura
lattice, every $`{\downarrow}t_n` is finite, so every filter is principal and
normal (pen): the phenomenon is modal.  Whether a non-normal filter lies over a
limit point (the gap filter is the candidate) is OPEN (Section 13).

# Supporting declarations

{lemmaTable instHeyting le_himp_iff_rn circNucleus box_inf MacNeille.instFrame cutHimp mem_left_cutHimp principalHom extNucleus extNucleus_apply extNucleus_comm le_extNucleus leastExt dmNucleus dmNucleus_principal le_dmNucleus PLLND.F0.Points.gaps PLLND.F0.Points.exists_nonprincipal PLLND.F0.Points.CF PLLND.F0.Points.CF.onto PLLND.F0.Points.fq_lt PLLND.F0.Points.X PLLND.F0.Points.X_injective PLLND.F0.Normal.ρF PLLND.F0.Normal.dF PLLND.F0.Normal.F7 PLLND.F0.Normal.IsFilter PLLND.F0.Normal.F7_isFilter PLLND.F0.Normal.lowerBounds_F7 PLLND.F0.Normal.upperBounds_lowerBounds_F7 PLLND.F0.Normal.t7_not_mem_F7 PLLND.F0.Normal.bot_not_mem_F7 PLLND.F0.Normal.force_d_x PLLND.F0.Normal.force_ρ_succ_x PLLND.F0.Normal.exists_force_chain PLLND.F0.Normal.toConstraint_force_fd PLLND.SubframeModel.CF.completeness}

Pins (`#axioms_within`, each watched failing at a tighter set): `propext`,
`Quot.sound` for `instHeyting`, `le_himp_iff_rn`, `circNucleus`, `box_inf` and
every declaration of `wip/f0Normal.lean`; `propext`, `Classical.choice`,
`Quot.sound` for the rest, by the routes traced above.
