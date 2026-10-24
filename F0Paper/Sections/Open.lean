import Verso
import VersoManual

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Open questions" =>

Each question below is OPEN.

* _Is $`[t_3, \top]` order-isomorphic to $`F_0`?_  Not by $`\sigma`, which misses
  $`t_5` (Section 10), and not by any isomorphism of Heyting algebras with a
  nucleus (pen remark, Section 10).
* _Are the bases $`\sigma^{n}(\bot)` cofinal in $`F_0`, or do they stop below an
  unfilled cut?_
* _Which bases $`a` give a faithful copy?_  $`\bigcirc a \ne a` is necessary;
  $`a = t_3` works.
* _Is $`{\downarrow}t_8` finite?_
* _Is the nuclear extension of $`\bigcirc` to $`\mathrm{DM}(F_0)` unique?_  It is
  not in general (REFUTED, Section 8).
* _Which intervals sit at which level_ (Section 2)?  Known: covers and
  $`[\bot, t_n]`, $`n \le 5`, are at level 1; pairs in the odd-gap lattice have
  $`\aleph_0` pairwise $`\parallel` threads; $`[\sigma^{n}(\bot), \top]` is at
  level 4.  The level of the infinite $`[\bot, t_6]` is unknown, and so is
  whether every infinite interval has a thread.
* _Are the levels distinct?_  Is there an interval at level 2 but not 3, or at
  level 3 but not 4?
* _Is some interval dense, that is, free of covers?_  A candidate is
  $`[g_i \land g_j, g_i]` with $`i < j`.
* _$`\mathrm{DM}(F_0)` as a model_: the pen remark of Section 8, unmechanised.
* _Choice_: whether the results of Sections 6 and 7 that use `Classical.choice`
  need it has not been examined.
