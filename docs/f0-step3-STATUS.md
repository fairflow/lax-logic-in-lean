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

## 2026-10-27 09:13 GMT: D6 done

**The check** (scratch, `_out/f0step3/SorryCheck.lean`, not tracked): a
command that runs `collectAxioms` over every declaration of the twelve
`LaxLogic.PLL.SubTab.*` modules and of `LaxLogic.PLL.SemUI.SemUILayered`, and
fails naming each one that depends on `sorryAx`.

* Before the move (watched failing):

      sorry check: 1 of 879 declarations in 13 modules depend on sorryAx:
        PLLND.SemUI.amalgamation  [LaxLogic.PLL.SemUI.SemUILayered]
      axiom sweep: 1 of 84 declarations escape the allowance
        [propext, Classical.choice, Quot.sound]:
        PLLND.SemUI.amalgamation  [LaxLogic.PLL.SemUI.SemUILayered]  → sorryAx
      axiom sweep: 795 declarations, all within [propext, Quot.sound]

* After the move:

      sorry check: 878 declarations in 13 modules [...]: none depends on sorryAx
      axiom sweep: 83 declarations, all within [propext, Classical.choice, Quot.sound]
      axiom sweep: 795 declarations, all within [propext, Quot.sound]

* Closure-wide, after (`_out/f0step3/ClosureSorryCheck.lean`, the same
  command over every module of the SubTab library's import closure, prefixes
  `LaxLogic`, `FRJ`, `Meta`, `LeanCertify`):

      sorry check: 7961 declarations in 106 modules: none depends on sorryAx

**The move.**
* `PLLND.SemUI.amalgamation`, with its docstring, verbatim from
  `LaxLogic/PLL/SemUI/SemUILayered.lean` to the new
  `wip/semUILayeredAmalgamation.lean` (imports `SemUILayered` and
  `Meta.Audit`).  A one-paragraph pointer stands where it was.
* The deliberate sorry is pinned at its site:
  `#axioms_within amalgamation [propext, Classical.choice, Quot.sound, sorryAx]`.
  Watched failing first without `sorryAx` ("depends on sorryAx, which the
  bound does not allow").
* No declaration used it (code scan, comments and strings stripped, every
  tracked `.lean` file outside `Archive/`), so no `wip/` import changed.
  `wip/semui_amalg_probe.lean`: its prose pointer to `SemUILayered.lean:821`
  now names the new file.
* `lakefile.toml`: `wip.semUILayeredAmalgamation` joins `wipshared`, beside
  `wip.semui_amalg_probe`, so it can be built by name.
* `Audit/Production.lean`: the held-out note records the move, and
  `LaxLogic.PLL.SemUI.SemUILayered` leaves the sweep's `except` list.  The
  same sweep restricted to that module was watched failing and passing
  (above).  `lake build Production` itself was NOT run here: it imports the
  whole library.
* Built by name, green: `LaxLogic.PLL.SemUI.SemUILayered`,
  `wip.semUILayeredAmalgamation`, `wip.semui_amalg_probe`, and the `SubTab`
  library (which rebuilt `SemUIFrag`, `SubframeLayered` and the twelve SubTab
  modules).
