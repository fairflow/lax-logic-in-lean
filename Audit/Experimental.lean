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
Extending it further is a matter of importing more and repairing what
breaks — which is the point of having the target at all.

The `cover*` pair is here because it carries a result, not a run.
`wip/coverfail.lean` REFUTES `CoverConj`, the substitution-cover method,
at `φ★ = ((◯⊥ ⊃ p) ⊃ (◯⊥ ∧ p)) ∧ ¬¬p`, by a four-world countermodel
whose valuation of `p` is undefinable (`M4_swap`: worlds 1 and 2 satisfy
the same variable-free formulas).  With `wip/postui.lean` refuting the
`∀`-side at `p ∨ ¬p`, the cover method is incomplete on BOTH sides —
uniform interpolation itself untouched and OPEN.  That result had stopped
being checked at all: `coverfail` did not build, because `postui` above it
did not build, so a refutation on the UI line was silently unverified
from some point before 2026-09-04 until it was repaired that day.
`wip/coverprobe.lean` is the exhaustive product-subalgebra search that
FOUND `φ★` (n ≤ 3 none, n = 4 four hits, n = 5 generic); it is discovery
tooling, kept for reproducibility rather than content.
-/
import Meta.Sweep

import wip.G4conf
import wip.cascadeBox
import wip.check_closed
import wip.postui
import wip.b1b2_cells
import wip.gbu_search_circ
import wip.schemeext
import wip.coverfail
-- NOT `wip.coverprobe`, and not for any reason to do with axioms: it
-- declares `main`, as several `wip/` probes do, and two `main`s cannot
-- share one environment —
--   "import wip.coverprobe failed, environment already contains 'main'
--    from wip.rnc_probe"
-- This is a limit of auditing an estate by IMPORTING it: every
-- executable-shaped module is unreachable this way, and there are
-- several.  Reaching them needs the sweep driven as an executable over
-- `importModules`, one module (or one compatible group) at a time,
-- rather than as a command inside one module that imports everything.
-- `wip.coverprobe` builds on its own; it is simply unswept.

#axiom_sweep [wip]
  allowing [propext, Classical.choice, Quot.sound, sorryAx]
