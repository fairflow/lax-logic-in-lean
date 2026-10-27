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

## 2026-10-27 09:33 GMT: step 3 done

**`tools.`/`wip.` imports.**  `git grep` over `LaxLogic/PLL/SubTab` and
`tools/SubTab` on arrival:

| module | `tools.`/`wip.` import | what it needed | now |
|---|---|---|---|
| the twelve `LaxLogic/PLL/SubTab/*` | none (since `9c478e2`) | — | none |
| `tools/SubTab/Settings.lean` | none | — | none |
| `tools/SubTab/SubTabDecide.lean` | `tools.Decide` (closure: 17 `wip/` modules, `Rewrite`) | `PLLTools.parseFormula` | `LaxLogic.PLL.Syntax.Parse`; closure: library + `tools.SubTab.Settings` only |
| `tools/SubTab/Source.lean` | `tools.Decide` | `PLLTools.srcOfP` | moved to the library, `LaxLogic/PLL/SubTab/Source.lean` (git mv), importing `Parse` and `Sound` |
| `tools/SubTab/PllFast.lean` | `tools.Decide` | `pll`'s output layer and the W-engine fallback (`wip.check_closed`) | unchanged: by design (plan §4, `checkClosed` is a producer in `wip/`) |
| `tools/SubTab/RefBench.lean` | `wip.two_sided`, `tools.SubTab.Source` | the other engines it times (`g4c`, `trees`, `frjw`) | `wip.two_sided` and an explicit `tools.Decide` (which it had through the old `Source`) kept by design; `Source` from the library |

**The parser.**  `Tok`, `tokenize`, `pImp`/`pDisj`/`pConj`/`pUn`,
`parseFormula` and `srcOfP` moved from `tools/Decide.lean` to the new
`LaxLogic/PLL/Syntax/Parse.lean` (namespace `PLLTools`, names unchanged;
`tools/Decide.lean` imports it).  One change: the parser builds `PLLFormula`
directly instead of FRJ's `Form` read back by `toPLL` (the two are isomorphic
constructor for constructor), so the module needs only
`LaxLogic.PLL.Syntax.Formula`.  Checked against the old block, verbatim, on 8
well-formed strings (every token in both spellings, precedence, right
associativity, tab) and 6 malformed ones (every error message), plus a
non-vacuity guard: all agree (`_out/f0step3/ParseEquiv.lean`).

It is NOT in the `SubTab` library: `parseFormula` reaches `Classical.choice`
through Lean core's `String.toList`, as do `String.foldl`, `String.foldr`, the
iterator and `String.Pos.Raw.get`.  Pins, watched failing first:

    #axioms_within srcOfP [propext]                                  (failed at [])
    #axioms_within parseFormula [propext, Classical.choice, Quot.sound]  (failed at [propext, Quot.sound])

**`Repr TCert`.**  On arrival there was no instance (removed in `9c478e2`).
Before, reproduced by `deriving instance Repr for TCert` in
`_out/f0step3/ReprBefore.lean`:

    'PLLND.SubTab.reprProbe' reaches 'Classical.choice' by:
      0. PLLND.SubTab.reprProbe                         [this file]
      1. PLLND.SubTab.instReprTCert__out                [this file]
      2.–3. …instReprTCert__out.repr, .repr._f          [this file]
      4. PLLFormula.instRepr                            [LaxLogic.PLL.Syntax.Formula]
      5. PLLFormula.toString                            [LaxLogic.PLL.Syntax.Formula]
      6. stripParens                                    [LaxLogic.Util.FormattingUtils]
      7. String.Slice.toString                          [Init.Data.String.Slice]
      8. String.Slice.copy  9. String.extract           [Init.Data.String.Basic]
      10. String.Pos.isValidUTF8_extract                [Init.Data.String.Basic]
      11.–12. ByteArray.extract_eq_empty_iff (+ proof)  [Init.Data.ByteArray.Lemmas]
      13. Classical.propDecidable  14. Classical.choice
    'PLLND.SubTab.reprProbe' depends on axioms: [propext, Classical.choice, Quot.sound]

After: `SubTab.instReprTCert` in `LaxLogic/PLL/SubTab/Source.lean`, by hand,
`reprPrec c _ := .text (tcertSrc c)` (`_out/f0step3/ReprAfter.lean`):

    'PLLND.SubTab.reprProbe' does not depend on 'Classical.choice'
    'PLLND.SubTab.reprProbe' depends on axioms: [propext]
    'SubTab.instReprTCert' depends on axioms: [propext]

`#eval SubTab.solve (◯p ∧ ◯q ⊃ ◯(p ∧ q))` now prints the closed tableau as
Lean source, identical to the certificate of that cell in `Facts.lean` (l. 161).

**Sweeps after step 3** (`_out/f0step3/SorryCheck.lean`, with `Source`):

    sorry check: 882 declarations in 14 modules: none depends on sorryAx
    axiom sweep: 83 declarations, all within [propext, Classical.choice, Quot.sound]   (SemUILayered)
    axiom sweep: 799 declarations, all within [propext, Quot.sound]                    (SubTab, 13 modules)
    closure: 8030 declarations in 108 modules: none depends on sorryAx

No `#axioms_within` pin changed except the two new ones in `Parse.lean` and
the new one in `wip/semUILayeredAmalgamation.lean`.

**Builds, green, by name:** `SubTab`, `SubTabTools`, `subtabdecide`, `pllfast`,
`refbench`, `pll`, `DecideTools`, `pllbench`,
`LaxLogic.PLL.Syntax.Parse`.  `refbench` failed once, watched: it had used
`FRJ.Arity.decideDataByEngine` and `PLLTools.Args` through the old
`tools.SubTab.Source → tools.Decide`; it now imports `tools.Decide` itself.

**Runs** (built binaries under `gtimeout`):
`subtabdecide`: `◯p ∧ ◯q ⊃ ◯(p ∧ q)` YES (subtab), `◯p ⊃ p` NO (enum, exit 1),
`p &` parse error (exit 2).  `pllfast`: the same two cells PROVED (tableau,
`termOf`) and REFUTED (2 worlds + fallible top).  `pll`: `◯p ⊃ p` REFUTED.
`refbench fact` on both cells: the two printed facts kernel-check, within
`[propext, Quot.sound]` (`_out/f0step3/FactCheck.lean`).

**Not done here.**  `lake build Production` (imports the whole library) and
the 33-cell port benchmark were not run.  `docs/next-session.md` item 62
("whether `SemUILayered.amalgamation` becomes a `Prop`") is left for the
manager.

## 2026-10-27 09:36 GMT: closed

* Commits on this branch: the merge of `origin/method-f0`, `094785e` (this
  note), `7ed3889` (D6), `4bbb33b` (step 3), `2d257a1` (TOOLS.md version
  cells from `tools/tools-register.sh`), and this closing note.  Not pushed;
  no upstream.
* `PaperKit` built green after both parts.  `python3 scripts/check-imports.py`:
  3252 imports in 1279 modules, every one resolves.
* Disk: 129 135 MB free on `/System/Volumes/Data` at the last check.
* Skips, for the manager:
  - `lake build Production` (the whole library), so the `except` change in
    `Audit/Production.lean` is checked only by the same sweep on the one
    module.
  - The ~200 `wip/` modules downstream of `SemUILayered` that nothing here
    needed were not rebuilt; none names `amalgamation` in code.
  - `LaxLogic.PLL.Syntax.Parse` is not imported by `LaxLogic.lean`, so the
    Production sweep does not see it; its two pins do.
  - `wip/semUILayeredAmalgamation.lean` is not imported by
    `Audit/Experimental.lean`.
  - The 33-cell port benchmark of `pllfast`/`subtabdecide` was not re-run:
    three designed cells each, above.
  - `pllfast`'s closure still holds the sorried `wip.semui_char` and
    `wip.semui_henkin` (through `tools.Decide` → `wip.check_closed`); the
    tableau's library closure and `subtabdecide`'s do not.
