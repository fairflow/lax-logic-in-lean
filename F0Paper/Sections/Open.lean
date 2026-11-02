import Verso
import VersoManual

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Open problems" =>

Each problem is OPEN unless marked as a pen argument awaiting Lean; a short
proof sketch is given where one exists.

# Open

* _The residue above $`t_3`_: is some filter $`[p, \top]` with $`t_3 \le p`
  order-isomorphic to $`F_0`?  OPEN, in each of the four cases of
  Section 11: (i) $`\bigcirc p = p`; (ii) $`\bigcirc p` covers $`p` and is
  meet-prime; (iii) the gap $`\bigcirc p \Rightarrow p` covers $`p`;
  (iv) $`\bigcirc p` is a big atom of $`[p, \top]`.  Case (i) is realised by
  every $`\sigma^{n}(c_1)`, each refuted; (ii) to (iv) fail at the cells
  $`t_3`, $`t_5`.  No sketch.  Every filter above $`t_3` refuted so far lacks a
  core, so one route is to show that no $`[p, \top]` with $`t_3 \le p` has one.
* _Is there a non-normal filter over a limit point?  Is the gap filter normal?_
  $`F_7` lies over a principal point.  The candidate over a limit point is
  $`G = \bigcup_n {\uparrow}(g_1 \land \cdots \land g_n)`, which
  lies over the limit point $`x_{\mathrm{gap}}` (Section 12), and is normal
  exactly when every upper bound of the common lower bounds of the gaps lies
  above a finite meet of gaps.  OPEN, with no witness either way.  The
  Rieger–Nishimura ladder with one world added above all its worlds forces
  every such upper bound, so it does not separate them from $`G`; a witness of
  non-normality needs a prime filter containing every gap, no common lower
  bound of them, and not some upper bound of those; a proof of normality needs
  a trace argument of the kind of `L_bounded`.
* _The fibres over $`{\downarrow}t_3` and $`{\downarrow}t_5`_: is $`t_3`
  (or $`t_5`) the meet in $`F_0` of a strictly decreasing sequence, so that a
  non-principal filter lies over it (Section 12)?  OPEN.  The construction of
  $`F_7` does not adapt: at $`t_6` the added world $`z` of its step 2 fails the
  bound, and $`t_5` already fails on the ladder.  Over $`{\downarrow}t_7` there
  are at least two filters ($`F_7`, PROVED); how many is OPEN.
* _Uniqueness of the extension of $`\bigcirc` at $`F_0`_: is the interval of
  nuclear extensions a single point?  OPEN (REFUTED for a chain with a gap,
  Section 12).  The natural test point is $`x_{\mathrm{gap}}`, where
  $`\overline{\bigcirc}(x_{\mathrm{gap}}) = \bigwedge \{{\downarrow}\bigcirc a : a \in \mathrm{U}(x_{\mathrm{gap}})\}`.
  No sketch.
* _A choice-free $`F^{*}`_, with cuts as pairs of predicates and the order,
  lattice operations, implication and nucleus written by hand.  OPEN, and
  plausible: the trace of Section 12 finds choice only in Mathlib's instances.
* _Is $`{\downarrow}t_8` finite?_  OPEN.  $`t_6 \nvdash t_8`, so the infinite
  chain below $`t_6` (Section 8) does not lie below $`t_8`, and $`t_8` fails on
  that countermodel's ladder.  No sketch.
* _How many filters are not normal?_  At least one ($`F_7`, PROVED);
  $`2^{\aleph_0}` is plausible, by varying $`F_7` with independent gaps.  OPEN.
* _Which intervals sit at which level_ (Section 2)?  Known: covers and
  $`[\bot, t_n]`, $`n \le 5`, are at level 1; pairs in the odd-gap lattice have
  $`\aleph_0` pairwise $`\parallel` threads; $`[\sigma^{n}(\bot), \top]` is at
  level 4.  The level of the infinite $`[\bot, t_6]` is unknown, as is whether
  every infinite interval has a thread, and whether the levels are distinct (an
  interval at level 2 but not 3, or at level 3 but not 4).  OPEN.
* _Is some interval free of covers?_  A candidate is $`[g_i \land g_j, g_i]`,
  $`i < j`.  OPEN.
* _Choice in Sections 6 and 7_: the trace reaches excluded middle in
  `plain_trace_dichotomy` (`wip/floor.lean`); whether it is needed has not been
  examined.  OPEN.
* _$`H_3` in $`[\sigma^{2}\bot, \top]`_: does `FreeHAnAbove (σ²⊥) 3` hold?
  OPEN.  The count does not obstruct, as $`k(\sigma^{2}\bot) = \infty`;
  $`H_2` is there (`freePair`), and every $`H_n` one level up, in
  $`[\sigma^{3}\bot, \top]` (Section 10).  No sketch.
* _Does $`\tau = \tau_{t_3,t_6}` have a fixed point in $`F_0`?_
  (`TauFixedPoint`.)  OPEN; the conjecture is that it has none
  (`NoTauFixedPoint`).  By Section 12 a fixed point would be the one element of
  $`F_0` in every interval of the $`t_6` tower; $`\top`, $`t_6` and $`U_2` are
  not fixed points.  Sketch: a fixed point $`x` satisfies
  $`x \dashv\vdash \sigma^{d}(x) \land U_d` for every $`d`, so in a finite model
  it agrees with “$`\sigma^{d}(t_6)` for every $`d`”, that is, with “$`t_6`
  holds at every stage of removing the worlds that force $`t_3`”, and the number
  of stages is unbounded over finite models.  A proof needs a depth measure on
  variable-free formulas with invariance under depth-bounded bisimulation of
  subframe models, without choice, and for each depth $`k` a pair of finite
  models, $`k`-bisimilar at their roots, one with $`U_D` and not
  $`\sigma^{D}(t_6)`, one with every $`\sigma^{d}(t_6)`.  The repository has
  neither: its layered bisimulation is for constraint models and carries
  choice.  The obvious pair, the $`D`-fold extensions by two top worlds of a
  three-world chain and of a one-world model in $`S`, fails: the roots differ in membership of $`S`,
  which a formula of depth 1 detects.
* _Does a copy of $`F_0` in $`[a, b]` give a copy of PLL in $`[a, b]` by the
  A-translation?_  (`CopySelf`: for variable-free $`a \vdash b`,
  $`\mathit{CopyStep}(a, b)` implies $`\mathit{SelfStep}(a, b)`.)  PROVED at
  $`b = \top`, from the base criterion (`copySelf_top`, Section 9); OPEN for
  other tops.  Eighteen designed cells pass, at $`(t_3, t_6)`, $`(t_3, \top)`
  and $`(\sigma^{2}\bot, \top)` (`k4_…`, `wip/f0Endpoints.lean`).  No sketch.
* _Nested intervals for PLL_ (`NestPLL`): the nesting of Section 10 for all
  formulas, $`\bigcirc` included, with the $`\bigcirc` clause of the interval
  translation.  OPEN.  The design is ready for it: the glued copy keeps the
  set $`S` of the countermodel, no generator reads $`S`, and the composition of
  interval translations holds for every formula (`rel_comp`).  Missing: the
  collapse and the transfer with the $`\bigcirc` clause, and preservation
  through `relB_preservesO`.

# Pen arguments awaiting Lean

* _The normal filters are exactly the points of $`F^{*}`_, and every filter lies
  over the point $`(F^{l}, F^{lu})` (Section 12); on the definitions.
* _The limit points are exactly the joins of strictly increasing sequences of
  $`F_0` with no join in $`F_0`_ (Section 12).
* _The fibres over $`{\downarrow}\bot`, $`{\downarrow}t_1`,
  $`{\downarrow}t_2`, $`{\downarrow}t_4` are single filters_ (Section 12).
* _The meet of the halves is a limit point_, from `halves_no_glb_vf` as for the
  gaps (Section 12).
* _$`F^{*}` with $`\overline{\bigcirc}` is a complete algebraic model of PLL_,
  by the usual soundness of PLL for Heyting algebras with a nucleus, with
  $`\aleph_0` mutually incomparable copies of $`\mathbb{R}` completing the
  threads of Section 7; one copy, through $`r \mapsto X_r`, is one-to-one by a
  PROVED theorem and monotone by a pen argument.
* In the $`\bigcirc`-free instance, $`[t_1, \top]` is isomorphic to the
  Rieger–Nishimura lattice (the shift $`t_n \mapsto t_{n+2}`), and every filter
  of it is principal and normal.
* _An order copy of every $`H_n` with bottom $`\bot`_: the (O)-form, by the
  shift of the bottom (`shift`) applied to `freeHAnAbove_base3` (Section 10);
  not stated as a theorem.
* _The Heyting-embedding reading of `FreeHAnAbove`_: the Lindenbaum algebra of
  IPC is $`H_n` (textbook) and the relativisation is a one-to-one Heyting
  homomorphism (Section 10, point (c)).
* _$`F_0 \setminus \{\top\}` is the disjoint union of the shells $`L_n`_
  (Section 9), from `lim_eq_top` and the definitions.
* _The readings in $`F^{*}` of Section 12_: the join of the bases is $`\top`,
  from `basesOnlyTop`; the intervals of the $`t_6` tower close on one point,
  from `closing`, and it lies in $`F_0` iff $`\tau` has a fixed point there,
  from `fixedIffInAll`.

# Closed since v0.7

_Which bases $`a` give a faithful copy $`\varphi \mapsto \varphi[\bot := a]`?_
Those with $`\nvdash \bigcirc a \twoheadrightarrow a` and
$`\nvdash (\bigcirc a \twoheadrightarrow a) \twoheadrightarrow a`, and for them
PLL embeds in $`[a, \top]` by the A-translation (`baseCriterion`, Section 9).
_The upper bounds of the bases $`\sigma^{n}(\bot)` in $`F^{*}`_: their join is
$`\top` (`basesOnlyTop`, Section 12).  v0.7 said that the join is $`\top`
exactly when the bases are cofinal in $`F_0`; that is false, since the bases
are not cofinal (`notCofinal`).

# Closed since v0.5

The conjecture $`\forall n\, \exists m.\ H_n \hookrightarrow [\sigma^{m}\bot, \top]`,
OPEN in the repository when it was stated (`wip/f0FreeHAn.lean`), is PROVED
with $`m = 3` for every $`n`, and $`H_\omega` lies in
$`[\sigma^{3}\bot, \top]` as well; so do they in every
$`[\sigma^{m}\bot, \top]`, $`m \ge 3`, and any $`n + 1`
$`\sigma^{2}\bot`-maximal worlds of pairwise different types give $`H_n`
(Section 10).  PLL itself embeds faithfully into $`F_0`, with the readers as
generators and $`\bigcirc \mapsto \bigcirc`, and $`\bigcirc x_1` is not in
the range of the copy of IPC: both PROVED in `wip/f0FreePLL.lean`
(Section 10).

# Closed since v0.4.1

$`|F^{*}| = 2^{\aleph_0}` and the existence of a point of $`F^{*}` that is not
principal are PROVED (`wip/f0MacNeillePoints.lean`), and so are the non-normal
filter $`F_7` and the joins $`\bigvee_k \rho_k = \bigvee_k t_{2k+1} = \top`
(`wip/f0Normal.lean`).  Question 1 of v0.4.1 is
reduced to the residue above $`t_3` and refuted at the cells of Section 11,
with Obstruction A and the four cases PROVED.
