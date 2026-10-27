# F0 plan, step 3 and decision D6: status

Branch `worktree-agent-aba8c3302dbcd8742` (local only, not pushed).  Plan:
`docs/f0-reimplementation-plan.md` §6 step 3 and §8 D6, both approved by
Matthew on 2026-10-27.

## 2026-10-27 09:04 GMT: started

* Merged `origin/method-f0` (clean: four added files, no conflicts) so the
  plan is on this branch.
* Found on arrival: commit `9c478e2` (2026-10-22) already moved the engine,
  the producer and the enumeration into the library `SubTab`, and removed the
  derived `Repr TCert` instance.  The static import closure of the twelve
  `SubTab` library modules is 100 in-repo modules, none of them `tools.*` or
  `wip.*` (re-checked today).  What remains of step 3 is in the decider
  front end: `subtabdecide` and `tools/SubTab/Source.lean` import
  `tools.Decide`, whose closure reaches 17 `wip/` modules.
* D6: no Lean declaration anywhere uses `PLLND.SemUI.amalgamation` as a term
  (a scan of code with comments and strings stripped); the `wip/` files
  name it in prose only.

Next: the `sorryAx` check, watched failing; then the move.
