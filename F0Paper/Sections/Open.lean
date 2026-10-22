import Verso
import VersoManual

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Open questions" =>

This section lists what remains open about $`F_0`, with the status of each
question and the evidence there is.  PROVED, REFUTED and OPEN are used in the
sense of the rest of the document; evidence that is not a proof is reported as
evidence.

# The questions answered

* _Is $`F_0` dense?_  No: PROVED, seven covers at the bottom (Section 3).
* _Does every interval $`[u, v]` with $`u < v` contain an order-embedded copy
  of $`\mathbb{Q}`?_  No: PROVED, an interval given by a cover has two elements
  (Section 3).
* _Does $`\mathbb{Q}` order-embed in $`F_0`?_  Yes: PROVED, explicitly and
  without `Classical.choice` (Section 5).
* _Does $`\bigcirc` extend to $`\mathrm{DM}(F_0)` as a nucleus?_  Yes: PROVED,
  and the extension is the greatest one (Section 8).

# Open

* _Which intervals contain a copy of $`\mathbb{Q}`?_  Every interval between
  two lattice polynomials in the odd gaps, one strictly below the other,
  contains $`\aleph_0` copies of the dyadic rationals in $`[0, 1]`, mutually
  incomparable on $`(0, 1)`: PROVED (Section 7).  Composed with the embedding
  of Section 5 they give copies of $`\mathbb{Q}`; that composition is not
  stated separately in the library.  For an
  arbitrary interval $`[u, v]` of $`F_0` with $`u < v` that is not a cover: OPEN.
* _Is the downset $`{\downarrow}t_n` finite for every $`n`?_  OPEN, with evidence
  against.  Finite downsets are PROVED only for $`t_1, \ldots, t_5`
  (Section 3).  An untrusted generator saturating $`{\downarrow}t_6` and
  $`{\downarrow}t_7` under the operations of Section 3 found at least 45 and at
  least 41 classes respectively before its time budget ran out, with no
  closure; the numbers of new classes per pass were 2, 3, 4, 6, 7, 10, 14, 24,
  roughly doubling.  This is evidence, not a result.
* _Is the nuclear extension of $`\bigcirc` to $`\mathrm{DM}(F_0)` unique?_
  OPEN.  Uniqueness fails for some Heyting algebras: REFUTED in general
  (Section 8).
* _$`\mathrm{DM}(F_0)` as a model._  That it is a complete algebraic model of
  PLL of the cardinality of the continuum, with $`\aleph_0` mutually
  incomparable copies of $`\mathbb{R}`, is a pen argument (Section 8); as
  mechanised statements these are OPEN.
* _Choice._  The rung truth sets, the single-edge lifts and the holes of
  Sections 6 and 7 carry `Classical.choice` in their proofs; whether those
  results can be proved without it has not been examined, except for the odd
  truth sets (re-proved without it in Section 4).
