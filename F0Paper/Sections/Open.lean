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
  Section 10: (i) $`\bigcirc p = p`; (ii) $`\bigcirc p` covers $`p` and is
  meet-prime; (iii) the gap $`\bigcirc p \Rightarrow p` covers $`p`;
  (iv) $`\bigcirc p` is a big atom of $`[p, \top]`.  Case (i) is realised by
  every $`\sigma^{n}(c_1)`, each refuted; (ii) to (iv) fail at the cells
  $`t_3`, $`t_5`.  No sketch.  Every filter above $`t_3` refuted so far lacks a
  core, so one route is to show that no $`[p, \top]` with $`t_3 \le p` has one.
* _Is the gap filter normal?_  $`G = \bigcup_n {\uparrow}(g_1 \land \cdots \land g_n)`
  lies over the limit point $`x_{\mathrm{gap}}` (Section 11), and is normal
  exactly when every upper bound of the common lower bounds of the gaps lies
  above a finite meet of gaps.  OPEN, with no witness either way.  The model
  "Rieger–Nishimura ladder with one world above all its worlds" forces every
  such upper bound, so it does not separate them from $`G`; a witness of
  non-normality needs a prime filter containing every gap, no common lower
  bound of them, and not some upper bound of those; a proof of normality needs
  a trace argument of the kind of `L_bounded`.
* _The fibres over $`{\downarrow}t_3` and $`{\downarrow}t_5`_: is $`t_3`
  (or $`t_5`) the meet in $`F_0` of a strictly decreasing sequence, so that a
  non-principal filter lies over it (Section 11)?  OPEN.  The construction of
  $`F_7` does not adapt: at $`t_6` the added world $`z` of its step 2 fails the
  bound, and $`t_5` already fails on the ladder.
* _Uniqueness of the extension of $`\bigcirc` at $`F_0`_: is the interval of
  nuclear extensions a single point?  OPEN (REFUTED for a chain with a gap,
  Section 11).  The natural test point is $`x_{\mathrm{gap}}`, where
  $`\overline{\bigcirc}(x_{\mathrm{gap}}) = \bigwedge \{{\downarrow}\bigcirc a : a \in \mathrm{U}(x_{\mathrm{gap}})\}`.
  No sketch.
* _A choice-free $`F^{*}`_, with cuts as pairs of predicates and the order,
  lattice operations, implication and nucleus written by hand.  OPEN, and
  plausible: the trace of Section 11 finds choice only in Mathlib's instances.
* _Is $`{\downarrow}t_8` finite?_  OPEN.  $`t_6 \nvdash t_8`, so the infinite
  chain below $`t_6` (Section 8) does not lie below $`t_8`, and $`t_8` fails on
  that countermodel's ladder.  No sketch.
* _The upper bounds of the bases $`\sigma^{n}(\bot)` in $`F^{*}`._  The bases
  increase strictly (`sigN_bot_strict`); their join in $`F^{*}` is $`\top`, a
  principal point $`{\downarrow}c < \top`, or a limit point, and it is $`\top`
  exactly when the bases are cofinal in $`F_0`.  OPEN.  A possible route to
  $`\top`, not checked: as for $`\bigvee_k \rho_k = \top` (Section 11, step 4),
  show that every world of a finite subframe model forces some
  $`\sigma^{n}(\bot)`.  At a maximal world $`t_3 = \sigma(\bot)` holds, and
  $`\sigma^{n+1}(\bot) = \sigma^{n}(\bot)[\bot := t_3]` should hold one level
  further down; an upper bound of every base is then $`\top`, by the subframe
  tableau.
* _How many filters are not normal?_  At least one ($`F_7`, pen argument);
  $`2^{\aleph_0}` is plausible, by varying $`F_7` with independent gaps.  OPEN.
* _Which bases $`a` give a faithful copy $`\varphi \mapsto \varphi[\bot := a]`?_
  $`\bigcirc a \ne a` is necessary, and $`a = t_3` works (Section 9).  OPEN.
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

# Pen arguments awaiting Lean

* _$`F_7` is a non-normal filter_ (Section 11, steps 1 to 5).  Its
  certification in Lean is in progress.
* _The normal filters are exactly the points of $`F^{*}`_, and every filter lies
  over the point $`(F^{l}, F^{lu})` (Section 11); on the definitions.
* _The limit points are exactly the joins of strictly increasing sequences of
  $`F_0` with no join in $`F_0`_ (Section 11).
* _The fibres over $`{\downarrow}\bot`, $`{\downarrow}t_1`,
  $`{\downarrow}t_2`, $`{\downarrow}t_4` are single filters_ (Section 11).
* _The meet of the halves is a limit point_, from `halves_no_glb_vf` as for the
  gaps (Section 11).
* _$`\bigvee_k \rho_k = \top` and $`\bigvee_k t_{2k+1} = \top` in $`F_0`_, by the
  induction of Section 11, step 4 (for the plain rungs with $`\bigcirc\bot` in
  place of $`u`).
* _$`F^{*}` with $`\overline{\bigcirc}` is a complete algebraic model of PLL_,
  by the usual soundness of PLL for Heyting algebras with a nucleus, with
  $`\aleph_0` mutually incomparable copies of $`\mathbb{R}` completing the
  threads of Section 7; one copy, through $`r \mapsto X_r`, is one-to-one by a
  PROVED theorem and monotone by a pen argument.
* In the $`\bigcirc`-free instance, $`[t_1, \top]` is isomorphic to the
  Rieger–Nishimura lattice (the shift $`t_n \mapsto t_{n+2}`), and every filter
  of it is principal and normal.

# Closed since v0.4.1

$`|F^{*}| = 2^{\aleph_0}` and the existence of a point of $`F^{*}` that is not
principal are PROVED (`wip/f0MacNeillePoints.lean`).  Question 1 of v0.4.1 is
reduced to the residue above $`t_3` and refuted at the cells of Section 10,
with Obstruction A and the four cases PROVED.
