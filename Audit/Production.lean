/-
# The production estate: `lake build Production`

Everything imported here must stay free of `sorryAx`.  That is the whole
policy: membership in this module IS the claim, and the sweep below is
what checks it, for every declaration, whether or not anyone wrote a
bound.

`lake build` alone is not this check.  It covers only the two
`defaultTargets` (`LaxLogic`, `FRJGbu`) and it type-checks; it says
nothing about axioms.  The gap is not hypothetical: five `wip/` modules
sat broken for weeks in 2026 because nothing built them, and two of those
breaks were stale axiom pins.

**Promotion is mechanical.**  A module joins the production estate by
being imported here and surviving the sweep.  A result that needs a
`sorry` cannot be imported here, and no directory it happens to live in
changes that.  Its home is `Audit/Experimental.lean` until the `sorry`
is discharged.

`Classical.choice` and `Quot.sound` are ALLOWED here.  They are innocuous
for these claims; the axiom this estate exists to exclude is `sorryAx`.
A subsystem wanting a tighter bound states it per declaration with
`#axioms_within`, which composes with this sweep rather than replacing it.
-/
import Meta.Sweep

import LaxLogic
import FRJ
import Rewrite

import FRJ.Gbu.Base
import FRJ.Gbu.DB
import FRJ.Gbu.Search
import FRJ.Gbu.Measure
import FRJ.Gbu.Circ
import FRJ.Gbu.Transport
import FRJ.Gbu.LaxND
import FRJ.Gbu.W.Dichotomy
import FRJ.Gbu.W.DB
import FRJ.Gbu.W.CircDB
import FRJ.Gbu.W.Corner
import FRJ.Gbu.W.Search
import FRJ.Gbu.W.Closure
import FRJ.Gbu.W.Exclusion
import FRJ.Gbu.W.Saturate
import FRJ.Gbu.W.LaxND

-- The LJF◯ uniform-interpolation route (B) chain: `interpP`, its
-- soundness, the cofinality family and the two cofinality statements.
-- Promoted 2026-09-05, when the family became unconditional.
import LJF.OFuelPCofinal

/-! ## Held out, 2026-09-04 — recorded debt, not exemptions

The first run of this sweep found 7 violations in 10,947 declarations.
None had a pin; none was detectable by `lake build`.  They are held out
BY MODULE so that every other declaration in `LaxLogic/` stays swept —
widening `allowing` to admit `sorryAx` would have disabled the check for
the whole estate, which is how a gate stops meaning anything.

* `LaxLogic.Belief.Examples` — `chain4_card` and `boolean22_card` depend
  on `native_decide`'s generated axiom.  `native_decide` taints, and the
  mandate does not accept it as a proof: these two cardinality claims are
  not machine-checked in the sense the rest of the estate is.  Either
  re-prove by `decide`, or move them out of the library.

* `LaxLogic.PLL.SemUI.SemUILayered` — RELEASED 2026-10-27, and swept again.
  It held ONE sorried declaration, `SemUI.amalgamation`, from the semantic
  uniform-interpolation development shelved on 2026-08-07.  A `sorry` ASSERTS,
  so as written it stated the amalgamation lemma as though it held.

  The other four went to `wip/` on 2026-10-05, acting on this list's own
  sentence that shelved work belongs in the experimental estate and not in
  `LaxLogic/`: `SemUIChar` -> `wip/semui_char.lean` and `SemUIHenkin` ->
  `wip/semui_henkin.lean` carried `SemUI.layered_of_frag_agree_W`,
  `SemUI.wit_force`, `SemUI.wit_pbisim` and `SemUI.amalgamation_assembled`
  out of every library.  Both were LEAVES — only `LaxLogic.lean` and three
  `wip/` files imported them.

  `SemUILayered` could not follow them, and the reason is worth recording:
  `SemUIFrag` imports it, and `LaxLogic/Focusing/LJFComplete.lean` imports
  `SemUIFrag`, so the module is upstream of a live completeness result (and,
  since 2026-10-22, of the subframe tableau, through `SubframeLayered`).  So
  the DECLARATION moved, not the file.  On 2026-10-27 (F0 plan, decision D6,
  Matthew) `SemUI.amalgamation` went to `wip/semUILayeredAmalgamation.lean`
  with its name, statement and docstring unchanged, pinned there at
  `[propext, Classical.choice, Quot.sound, sorryAx]`.  No Lean declaration
  used it (the `wip/` files that name it do so in prose only), so no import
  changed.  Watched: `#axiom_sweep [LaxLogic.PLL.SemUI.SemUILayered] allowing
  [propext, Classical.choice, Quot.sound]` failed on `amalgamation` (1 of 84
  declarations) before the move and passed (83) after.

* `LaxLogic.Obligation.Examples` — `sorried` and `downstream` (2026-09-16).
  Unlike the entries above, these are not shelved work: the module's §5 exists
  to SHOW what a `sorry` does to everything downstream, and both carry pins
  asserting `[sorryAx]` deliberately.  The sweep and the demonstration arrived
  in `main` from different branches on 2026-09-16 and had never met — a
  cross-branch collision of the same family as the four in
  `docs/branch-map-2026-09-16.md` §6, in a target nothing built.  Held out by
  module, not by widening the allowance; if the demonstration ever moves to
  `wip/`, delete this line.

Each line here is a claim that something is not meeting the bar.  The
list should get shorter. -/

#axiom_sweep [LaxLogic, FRJ, Rewrite, LJF]
  except [LaxLogic.Belief.Examples, LaxLogic.Obligation.Examples]
  allowing [propext, Classical.choice, Quot.sound]
