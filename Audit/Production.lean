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

/-! ## Held out, 2026-09-04 — recorded debt, not exemptions

The first run of this sweep found 7 violations in 10,947 declarations.
None had a pin; none was detectable by `lake build`.  They are held out
BY MODULE so that every other declaration in `LaxLogic/` stays swept —
widening `allowing` to admit `sorryAx` would have disabled the check for
the whole estate, which is how a gate stops meaning anything.

* `LaxLogic.BeliefExamples` — `chain4_card` and `boolean22_card` depend
  on `native_decide`'s generated axiom.  `native_decide` taints, and the
  mandate does not accept it as a proof: these two cardinality claims are
  not machine-checked in the sense the rest of the estate is.  Either
  re-prove by `decide`, or move them out of the library.

* `LaxLogic.PLLSemUILayered`, `LaxLogic.PLLSemUIChar`,
  `LaxLogic.PLLSemUIHenkin` — five sorried declarations from the semantic
  uniform-interpolation development shelved on 2026-08-07:
  `SemUI.amalgamation`, `SemUI.layered_of_frag_agree_W`,
  `SemUI.wit_force`, `SemUI.wit_pbisim`, `SemUI.amalgamation_assembled`.
  A `sorry` ASSERTS, so as written these state the amalgamation lemma and
  its supports as though they held.  Shelved work belongs in the
  experimental estate, not in `LaxLogic/`.

Each line here is a claim that something is not meeting the bar.  The
list should get shorter. -/

#axiom_sweep [LaxLogic, FRJ, Rewrite]
  except [LaxLogic.BeliefExamples, LaxLogic.PLLSemUILayered,
          LaxLogic.PLLSemUIChar, LaxLogic.PLLSemUIHenkin]
  allowing [propext, Classical.choice, Quot.sound]
