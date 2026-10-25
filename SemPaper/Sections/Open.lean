import Verso
import VersoManual

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Open questions" =>

Each question below is OPEN.

* _Constructive proofs of R3a and R3b_ (Section 8): the proofs of R3a,
  direction $`\Rightarrow`, and of R3b use excluded middle; R1, R3c and R4 provably cannot be proved without it.
* _Removing the extra uses of excluded middle_ in the general case of
  Section 8: those beyond the prime filter theorem and Alexander's subbasis
  theorem, the choice of the value $`j_N(a)`, and Mathlib's
  `IsCompact.elim_finite_subcover`.
* _Does the compiled producer of the tableau terminate on every formula?_  The
  argument is a pen argument (along a branch the set of true formulas grows at
  least every second step); the proof of the dichotomy is about a different,
  verified search, and the producer's answers are trusted only through the
  certifiers.
* _Which decider setting is fastest?_  The pre-registered comparison that is
  to order the lean-certify decider settings has not been run; the routing of
  Section 6 is interim.
* _Complexity_: no complexity bound is mechanised for any decider of this
  paper.
* _The universal property of $`F_0`_ as the free Heyting algebra with a nucleus
  on no generators (the pen remark of Section 7), and the Lindenbaum algebra on
  variables.
