/-
LJF◯ — the axiom audit, batched out of the build path (round 3, 2026-08-13).

All seven `#print axioms` pins of the LJF◯ development, in one module that
nothing imports.  They used to sit at the foot of `LJFOCore.lean` (five) and
`LJFO.lean` (two), so every build of either file paid for them.

**Why they moved** (Matthew's direction, 2026-08-13): **by design this
development uses no `sorry` outside `wip/`** unless Matthew authorises one,
so the pins are a periodic check, not a per-edit one.

A *second* reason was offered — a large build-time saving, since the round-3
trace profile showed `#print axioms LJFO.satE2` at ~223 s of the tail's
~1160 s build.  **That reason was measured and is withdrawn** (2026-08-13,
after the move): the tail still takes 27:50 against 26:03 with the pins in
place — no saving — and `lake build LJF.OAudit` then completes in
1.8 s.  The ~223 s was never separable audit cost: it is the kernel checking
`satE2`, which the build pays when it writes `LJFO.olean` regardless, and
`#print axioms` merely AWAITED that asynchronous task, which is why the
profiler attributed the time to the pin.  It is proof cost.

Matthew's design reason is untouched by that, and the same measurement makes
it a better bargain than expected: **the full audit costs 1.8 s**, so there
is never a reason to skip it.

**What this costs you.**  `lake build LJF.O` no longer re-checks the
axiom profile of anything.  A regression that introduced `sorryAx` into a
pinned result would not be caught by the default build; it is caught here.
So:

    lake build LJF.OAudit

**must be run before any commit that changes a proof**, and it is the only
sound oracle (`collectAxioms`; `native_decide` taints and is not used here).
Green output is silence — `#guard_msgs` compares against the docstring above
each pin, so a changed axiom set is an error, not a diff to eyeball.

The five core pins are unchanged in content and are reproduced verbatim; the
two tail pins likewise.  Nothing else moved, and `LJFOCore.lean`'s
statements, definitions and rules are untouched.
-/
import LJF.O
import LJF.OFuelHeight
import Meta.Audit

/-! ## Part 4 results (from `LJF.OCore`)

The G4iLL-blocker standing test, identity expansion, `p`-freeness of the
interpolant, and soundness of both modes — **E1 and A1, proved outright**. -/

/-- info: 'LJFO.BlockerTest.blocker' does not depend on any axioms -/
#guard_msgs in
#print axioms LJFO.BlockerTest.blocker

/-- info: 'LJFO.idNeg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.idNeg

/-- info: 'LJFO.interp_pfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.interp_pfree

/-- info: 'LJFO.eSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.eSound

/-- info: 'LJFO.aSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.aSound

/-! ## Part 5–8 results (from `LJF.O`)

Minimality of both modes — **E2 and A2**.  Both are `sorryAx`-free:
*conditional* here means parameterised by the typed obligation `CimpAnt`,
never assumed.  `satE2` is the expensive one, and the reason this module
exists. -/

/-- info: 'LJFO.satE2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.satE2

/-- info: 'LJFO.satA2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.satA2

/-! ## Route (B), node N0h — the two release transformers of
`LJF/OFuelHeight.lean` (2026-09-05).  Their size lemmas `szI_laxReleaseUp`
and `szI_laxReleaseCirc` are pinned in that file; the transformers
themselves were not, which the blueprint's UI chapter recorded as a
check outstanding.  Measured with `#axioms_within_pin`. -/

#axioms_within LJFO.laxReleaseUp [propext, Quot.sound]
#axioms_within LJFO.laxReleaseCirc [propext, Quot.sound]
