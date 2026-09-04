/-
# The experimental estate: `lake build Experimental`

Where `sorryAx` is legitimate.  The ax-prover harness needs files that
carry sorries while a proof is being developed, and forbidding that
outright would stop the work; what must not happen is a sorry travelling
into the production estate unnoticed.

So the allowance here includes `sorryAx`, and the sweep still runs.  It
is not a check that nothing is sorried — it is a check that nothing
carries an axiom NOBODY DECLARED, which for this estate means: no
surprises beyond the four listed.  A deliberate sorry additionally earns
an `#axioms_within f [propext, sorryAx]` at its own site, which is how
intentional and incidental are told apart later.

**Coverage is partial, and deliberately says so.**  The `wipshared`
library declares about 170 modules; this audit imports a working subset.
Extending it to the whole library is blocked on two modules that do not
compile at all (2026-09-04):

  * `wip/coverfail.lean`  — `M4_swap` pins `[propext]`, measures
    `[propext, Quot.sound]`; the `Fin 4` axiom leak, same shape as the
    `Fin 2` one repaired in `wip/postui.lean`
  * `wip/coverprobe.lean` — `Unknown identifier Std.HashMap`; the import
    stopped arriving transitively, as in `wip/schemeext.lean`

Neither is an axiom problem, and neither can be swept until it builds.
That is the honest state: this module audits what it imports, and the
list is short.
-/
import Meta.Sweep

import wip.G4conf
import wip.cascadeBox
import wip.check_closed
import wip.postui
import wip.b1b2_cells
import wip.gbu_search_circ
import wip.schemeext

#axiom_sweep [wip]
  allowing [propext, Classical.choice, Quot.sound, sorryAx]
