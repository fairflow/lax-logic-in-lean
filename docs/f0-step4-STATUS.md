# F0 plan, step 4 (`fincm` and `ljfo` as engines; one settings file): status

Branch `f0-step4` (local only, not pushed, no upstream), cut from
`origin/main` 70b977a (#96 and #97 merged).  Plan:
`docs/f0-reimplementation-plan.md` §6 step 4; method: `METHOD-F0.md` §3
(gate decisions of 2026-10-27) and §6; engine statements:
`docs/engine-adoption-statements.md`, written on 2026-10-22 on the local
branch `engine-adoption` and merged here.

Scope: `fincm` (a disprover, `FinCM` countermodels from
`CounterEmit.emit`) and `ljfo` (a prover, LJF◯ `DerivTree`s from
`emitTree`, checked by `checkDeriv`), invoked through one project-wide
settings file.  Out of scope, waiting for Matthew: `g4c` (M2), `frjw`
(M4, M8), `reject` (M3, M8).

## 2026-10-27 12:32 GMT: started; the document refreshed

* `git merge engine-adoption`: clean, adds the document only.
* Build cache seeded by APFS clone from the step-3 worktree
  (`agent-aba8c3302dbcd8742`, the builds at #96's head).
* `docs/engine-adoption-statements.md` §9 (new, dated; nothing above it
  rewritten): what steps 1–3 settled, M1–M10 marked, and which parts of
  §3's layout are done.  In short: M1, M5, M9 settled; M10 partly settled
  (`ljfoProve` still cites `searchProves`); M2, M3, M4, M6, M7, M8 live.
* Disk: 126 835 MB free on `/System/Volumes/Data` at the start.

## 2026-10-27 12:37 GMT: the statements, before any proof

`Harness/Statements.lean` (namespace `PLLDecider`), each statement a
`Prop` (the `def … : Prop` pattern), so nothing is sorried; the proofs come
in `Harness/Tools.lean`.  Formula-level, against the existing constant
`PLLND.SubTab.Holds φ := Nonempty ([] ⊢ φ)`:

    FincmNoSound :  ∀ φ M w,  FinCM.checkB M w [] φ = true  →  Holds φ → False
    LjfoYesSound :  ∀ φ t,    checkDeriv (decideSeq [] φ) t = true  →  Holds φ
    HoldsImpIff  :  ∀ φ ψ,    Nonempty ([φ] ⊢ ψ)  ↔  Holds (φ ↠ ψ)

The expected proofs are instances at `Γ := []` of existing lemmas, so no
NEW lemma is needed:

    FinCM.not_provable_of_check   LaxLogic/PLL/Semantics/CountermodelEmit.lean
    LJFO.laxND_of_checkDeriv      LJF/OCheckDeriv.lean, [propext, Quot.sound]
    PLLND.deduction_iff           LaxLogic/PLL/ND/Theorems.lean

`HoldsImpIff` is the one-hypothesis case of §1.1 of the engine document
(the F0 store's base facts are `[φ] ⊢ ψ` and `[φ] ⊬ ψ`); `curry_iff`, for
several hypotheses, is not built.

`lakefile.toml`: a new `lean_lib Harness`, outside `defaultTargets`,
explicit globs (`Harness.Statements` for now).  Built by name, green
(`lake build Harness.Statements`, 34 s, nothing else rebuilt).

## 2026-10-27 12:47 GMT: the adapters, PROVED, with their gates

**`Harness/Tools.lean`** (namespace `PLLDecider`):

    theorem fincmNo_sound : FincmNoSound := fun _ _ _ h => FinCM.not_provable_of_check h
    theorem ljfoYes_sound : LjfoYesSound := fun _ _ h => LJFO.laxND_of_checkDeriv h
    theorem holds_imp_iff : HoldsImpIff  := fun _ _ => deduction_iff

    fincmNo : Certifier PLLFormula (FinCM × Nat) (fun φ => SubTab.Holds φ → False)
      check φ c := FinCM.checkB c.1 c.2 [] φ
    ljfoYes : Certifier PLLFormula LJFO.DerivTree SubTab.Holds
      check φ t := LJFO.checkDeriv (LJFO.decideSeq [] φ) t

    fincmDisprover : Disprover PLLFormula SubTab.Holds   name "fincm", produce := fincmProduce
    ljfoProver     : Prover PLLFormula SubTab.Holds      name "ljfo",  produce := ljfoProduce
    enumDisprover  : Disprover PLLFormula SubTab.Holds   name "enum"   (copy, below)

No new lemma: each proof is one line, an instance of an existing lemma.

**Producers and budgets** (stated in the docstrings):
* `fincmProduce φ b`: `CounterEmit.emit [] (Search.nf φ) (budget := some
  (200 * b))`, then `CounterEmit.simplify … [] φ`.  `b` is the node budget of
  `emit`'s G4c pre-check (200 000 at `b = 1000`); a proof or a cut-off gives
  `none`.  **The budget does not bound the model construction**
  (`CounterEmit.build`, exponential in the subformula closure): only the
  fixed closure cap `fincmClosureCap = 12` does, at every budget.
* `ljfoProduce φ b`: `emitTree (b / 25) (decideSeq [] φ)`, the depth bound of
  the iterative deepening (40 at `b = 1000`, then 160 and 640).  Exponential
  in the depth on failing branches.
* Both watched meaning their budgets (pinned in `Regression.lean`): on
  `◯p ↠ p` and `p ↠ ◯p` respectively, a certificate accepted by the
  certifier at budget 1000, none at budget 0.

**`enum`.**  `tools/SubTab/Settings.lean` declares `Harness.tools` and
`Harness.decider`, as the new settings file must, so the two cannot share an
environment and the new file cannot import the old one.  Its
`enumDisprover` (five lines) is therefore copied verbatim into
`Harness/Tools.lean` as `PLLDecider.enumDisprover`.  The old file and
`subtabdecide` are unchanged (gate G5).

**`Harness.config`.**  Not moved.  The only declaration is in
`CertifyAdoption.lean`; `Harness/Tools.lean` imports it through
`CertifyAdoption.CheckDeriv` (for `emitTree`), so the new modules' lints read
the project's configuration and no environment holds two.  `emitTree` was not
moved out of `CertifyAdoption/CheckDeriv.lean` (§2.4 of the engine document
suggests it); the cost is that the decider imports the exemplar module.

**Axiom pins** (`#axioms_within`), each watched failing at a smaller list
(`_out/step4/PinWatch.lean`, `PinWatch2.lean`, not tracked):

| declaration | pin | watched failing at | message |
|---|---|---|---|
| `fincmNo_sound` | `[propext, Quot.sound]` | `[propext]` | depends on `Quot.sound` |
| `ljfoYes_sound` | `[propext, Quot.sound]` | `[propext]` | depends on `Quot.sound` |
| `holds_imp_iff` | `[propext]` | `[]` | depends on `propext` (first in the build itself: the pin was first written `[]`) |
| `fincmNo`, `ljfoYes` | `[propext, Quot.sound]` | `[propext]` | depends on `Quot.sound` |
| `fincmDisprover`, `ljfoProver`, `enumDisprover` | `[propext, Quot.sound]` | `[propext]` | depends on `Quot.sound` |
| `Gates.not_peirce`, `not_somehowP`, `unit_p`, `gap` | `[propext, Quot.sound]` | `[propext]` | depends on `Quot.sound` |

The producers are `partial` underneath, yet the prover and disprovers are
within `[propext, Quot.sound]`: no `Classical.choice`.

**Lean certify lints**, pinned with `#guard_msgs`: R3 (`#certify_structural`)
and R2 (`#certify_statement`) pass on `fincmNo` and `ljfoYes` (in
`Tools.lean`); R1 and R4 on both, and R3, R1, R4 on the exemplar theorems (in
`CertifyAdoption/Regression.lean`).  The automatic R4 linter passed on both
certifiers at their declarations.

**Exemplars** (`Harness/Gates.lean`): the producers' own output at budget
1000 on four smoke cells, kernel-checked through `verdict`:

    not_peirce   : Holds (((p ↠ q) ↠ p) ↠ p) → False            fincm, 2 worlds
    not_somehowP : Holds (◯p ↠ p) → False                       fincm, 2 worlds
    unit_p       : Holds (p ↠ ◯p)                               ljfo, 6 nodes
    gap          : Holds (◯((◯p ↠ r) ↠ ◯p) ↠ (◯p ↠ r) ↠ r)      ljfo, 49 nodes

**Negative tests** (in `Gates.lean`, pinned): a tampered certificate of each
kind is rejected
* by the checker in the kernel (`decide +kernel` proves `check … = false`):
  `cmSomehowBad` (`p` made true at the root) for `fincm`; `badIndex`,
  `swapKids` (on the 49-node tree) and `badArity` (on the 6-node tree) for
  `ljfo`;
* by `verdict`, whose error is pinned with `#guard_msgs`;
* by the decider's run-time gate: `fincmDisprover.gate` and
  `ljfoProver.gate` return "certificate REJECTED by its certifier (a tool
  defect)" (pinned), and accept the untampered certificates.
Watched failing: each `check … = false` test, run on the untampered
certificate, fails ("`decide` proved that the proposition … = false is
false"), so no test is vacuous.

**`CertifyAdoption/Regression.lean`**: imports `Harness.Gates`; a new
section pins R1, R4 on both certifiers, R3 on the four exemplars, R1 on two,
R4 on four, one accepted and one rejected certificate per certifier, and the
budget behaviour of both producers.

Builds by name, green: `Harness.Tools`, `Harness.Gates`,
`CertifyAdoption.Regression` (which rebuilt `CertifyAdoption` and
`CertifyAdoption.CheckDeriv`: their `.olean`s in the seeded cache were
stale).

## 2026-10-27 12:52 GMT: one settings file, and `plldecide`

**`Harness/Settings.lean`** (the registry and the decider; docstring omitted
here):

```lean
open PLLND.SubTab PLLDecider

def Harness.tools : Harness.Registry PLLFormula Holds :=
  [ .pair "subtab" (Certify.Prover.ofEngine engine "subtab")
      (Certify.Disprover.ofEngine engine "subtab"),
    .disprover "enum" enumDisprover,
    .disprover "fincm" fincmDisprover,
    .prover "ljfo" ljfoProver ]
  -- "g4c" (M2), "frjw" (M4, M8) and "reject" (M3, M8) wait for Matthew;
  -- "f0db", the F0 database engine, is step 6 of the plan.

def Harness.decider : Harness.DeciderConfig where
  prover    := "subtab"                                   -- EDIT
  disprover := "enum"                                     -- EDIT
  fallback  := [("subtab", "subtab"), ("ljfo", "fincm")]  -- EDIT: pairs, tried in order
  run       := { mode := .race,                           -- EDIT: .race | .sequential
                 budget := 1000,
                 flagReruns := 0,
                 budgetFactor := 4,
                 deadlineSec := 120 }

#certify_decider Harness.decider           -- checks every name against Harness.tools
```

The order is PROVISIONAL until G4, and the file says so.  The first two
pairs and the run settings are exactly `subtabdecide`'s
(`tools/SubTab/Settings.lean`), so on every formula the tableau decides
within the deadline, `plldecide` answers as `subtabdecide` does; the pair
(`ljfo`, `fincm`) is appended.  Since the tableau's producer never flags,
that pair is reached only after a REJECTED certificate (§3 fact 1 of the
engine document; M6).  `flagReruns := 0` is kept from the old settings: with
the doc's 2, the first pair would re-run the enumeration at 4 and 16 times
the model cap on every formula it cannot refute in 6 worlds.

**Names.**  `Harness.tools` and `Harness.decider` are also declared by
`tools/SubTab/Settings.lean` (library `SubTabTools`), so the two settings
modules cannot share an environment; nothing imports both, and neither is
imported by any `Audit` estate module (checked with `git grep`).  Nothing
was renamed or moved.  `Harness.config`: see the previous entry.

**`Harness/Main.lean`**, outside the library (it declares `main`):

```lean
def main (args : List String) : IO UInt32 :=
  Certify.Cli.main Harness.tools PLLTools.parseFormula Harness.decider args
```

**`lakefile.toml`**: `Harness.Settings` joins the `Harness` globs; new
`lean_exe plldecide`, root `Harness.Main`, not in `defaultTargets`.
**`tools/tools-register.sh`** lists `Harness`.  **`TOOLS.md`**: a new §3 row
for `plldecide`, marked as the lean-certify decider to use, version cell
`branch f0-step4 · 2026-10-27`; the `subtabdecide` row is marked superseded
for use and preserved (G5); the routing bullet of §2 says the same.

**Checks.**
* Build by name, green: `lake build Harness.Settings plldecide`;
  `#certify_decider` printed "decider ok: prover subtab, disprover enum, 2
  fallback pair(s)".
* `#certify_decider` watched failing (`_out/step4/DeciderWatch.lean`, a
  registry of `fincm` and `ljfo` with the disprover misspelt `fincmm`):
  "error: #certify_decider: unknown disprover 'fincmm'".
* `plldecide --json` prints the settings above; `plldecide "p &"`: "parse
  error: expected a formula", exit 2.

## 2026-10-27 12:59 GMT: smoke cells; the deadline did not bound the process

Smoke cells (CLAUDE.md rule 8: ◯-free first), not the G4 comparison set.

**Forced alone.**  A temporary settings variant, `_out/alone/PllAlone.lean`
(not tracked), built as `pllalone` through a lakefile entry that was added
for the build and reverted at once (`git checkout -- lakefile.toml`; never
committed).  Its registry is `fincm`, `ljfo` and two sentinels `none` that
produce nothing; `pllalone fincm` runs the one pair (`none`, `fincm`),
`pllalone ljfo` the pair (`ljfo`, `none`).  Run settings: race mode, budget
1000, two raises by 4 (so `fincm` pre-checks at 200 000, 800 000 and 3 200 000
nodes, `ljfo` searches to depth 40, 160 and 640), deadline 50 s.

**A defect found and fixed in `plldecide`.**  The first run of `ljfo` alone
on Peirce's law ended in `gtimeout`'s kill at 60 s (exit 124) with no output,
although the deadline was 50 s.  On a pseudo-terminal
(`_out/step4/run_pty.py`), with `--deadline=5` under `gtimeout 30`:

    before:  [ 5.04 s] FLAG budget 1000: none: no certificate …; budget 1000: ljfo: no certificate …;
                       budget 4000: none: …; budget 4000: deadline reached inside the pair; deadline reached
             exit 124 after 30.02 s
    after:   [ 5.82 s] FLAG … (the same report)
             exit 3 after 5.82 s

In race mode lean-certify v0.3's `Decider.run` returns at the deadline (or
at the first certified answer), but the other producer's dedicated thread
runs on, and the Lean runtime waits for running tasks before the process
ends; standard output, a pipe, was lost when the process was killed.  The
fix is in the project's entry point only: `Harness/Main.lean` (and the
variant) flush standard output and call `IO.Process.exit` with the
decider's code.  Not changed: lean-certify (Matthew's library; a fix there,
for example in `Certify.Cli.main`, is a question beside M7), and
`subtabdecide` (G5), which has the same behaviour: after `subtab` answers,
its process lives until the `enum` thread finishes its enumeration.  In
sequential mode the deadline is checked only between attempts, so a
producer can still run past it.

**Results** (after the fix; built binaries under `gtimeout 60`, run one at a
time by `_out/step4/run_cells.py`; wall-clock time of the whole process):

| run | cell | expected | output | exit | time |
|---|---|---|---|--:|--:|
| `fincm` alone | `⊢ p ↠ p` | yes | FLAG: no certificate at budgets 1000, 4000, 16000 | 3 | 0.05 s |
| `fincm` alone | `⊢ ((p ↠ q) ↠ p) ↠ p` | no | **NO** (certified by `fincm`) | 1 | 0.29 s |
| `fincm` alone | `⊢ p ↠ ◯p` | yes | FLAG: no certificate at budgets 1000, 4000, 16000 | 3 | 0.05 s |
| `fincm` alone | `⊢ ◯p ↠ p` | no | **NO** (certified by `fincm`) | 1 | 0.04 s |
| `fincm` alone | `⊢ ◯((◯p ↠ r) ↠ ◯p) ↠ (◯p ↠ r) ↠ r` | yes | FLAG: no certificate at budgets 1000, 4000, 16000 | 3 | 0.05 s |
| `ljfo` alone | `⊢ p ↠ p` | yes | **YES** (certified by `ljfo`) | 0 | 0.04 s |
| `ljfo` alone | `⊢ ((p ↠ q) ↠ p) ↠ p` | no | FLAG: no tree at budget 1000 (depth 40); deadline reached at budget 4000 (depth 160) | 3 | 50.04 s |
| `ljfo` alone | `⊢ p ↠ ◯p` | yes | **YES** (certified by `ljfo`) | 0 | 0.04 s |
| `ljfo` alone | `⊢ ◯p ↠ p` | no | FLAG: no tree at depths 40, 160, 640 | 3 | 0.05 s |
| `ljfo` alone | `⊢ ◯((◯p ↠ r) ↠ ◯p) ↠ (◯p ↠ r) ↠ r` | yes | **YES** (certified by `ljfo`) | 0 | 0.07 s |
| `plldecide` | `⊢ p ↠ p` | yes | **YES** (certified by `subtab`) | 0 | 0.81 s (first run after the build) |
| `plldecide` | `⊢ ((p ↠ q) ↠ p) ↠ p` | no | **NO** (certified by `enum`) | 1 | 0.04 s |
| `plldecide` | `⊢ p ↠ ◯p` | yes | **YES** (certified by `subtab`) | 0 | 0.04 s |
| `plldecide` | `⊢ ◯p ↠ p` | no | **NO** (certified by `enum`) | 1 | 0.04 s |
| `plldecide` | `⊢ ◯((◯p ↠ r) ↠ ◯p) ↠ (◯p ↠ r) ↠ r` | yes | **YES** (certified by `subtab`) | 0 | 0.04 s |

Every verdict given agrees with the expected one; no certificate was
REJECTED; every FLAG is on a cell the engine cannot answer alone (a prover
on a non-theorem, a disprover on a theorem), and a FLAG is never a verdict.
The provisional decider answered every cell by its first pair, so
`fincm` and `ljfo` were not reached there (M6).  Before the fix the
`plldecide` and `fincm` rows had the same verdicts and exit codes; the
`ljfo` row on Peirce's law was exit 124 at 60.02 s with no output.

The certificates of four of these answers are kernel-checked in
`Harness/Gates.lean` (the producers' output at budget 1000):
`not_peirce`, `not_somehowP` (`fincm`), `unit_p`, `gap` (`ljfo`).

## 2026-10-27 13:02 GMT: closed

* `python3 scripts/check-imports.py`: "3236 imports in 1283 modules, every
  one resolves".
* **Ledger: not updated, not required.**  CI's gate
  (`scripts/check-ledger.sh --built-only`) reads the `.olean`s of the
  default targets (`LaxLogic`, `FRJGbu`, `SubTab`); no module of those
  changed on this branch (`git diff --stat origin/main`: `Harness/`,
  `CertifyAdoption/Regression.lean`, `lakefile.toml`, `TOOLS.md`,
  `tools/tools-register.sh`, two documents), and `docs/status-ledger.jsonl`
  holds no row from a `CertifyAdoption` or `Harness` module.  The ledger
  check itself was not run locally.
* `TOOLS.md`: the `plldecide` version cell set from `tools/tools-register.sh`
  (after the squash below: `Harness e339b75 · 2026-10-27`).  `docs/engine-adoption-statements.md`
  §9.4: step 4 as built.
* Disk: 126 488 MB free on `/System/Volumes/Data` at the close.

**Commits.**  Branch `f0-step4`, local, not pushed, no upstream (the
automatic upstream that `git checkout -b … origin/main` set was
removed).  The branch was squashed into `e339b75` to keep the history
free of references to the old location of the tableau, and the version
cells were then updated in the following commit.

**Skips and caps, for the manager.**
* Not built: `g4c`, `frjw`, `reject` (out of scope); `curry_iff`; the
  move of `emitTree` out of `CertifyAdoption/CheckDeriv.lean`.
* Not run: `lake build Production` or any full build; the local ledger
  check; the weekly CI step that builds `CertifyAdoption.Regression` (it
  was built here by name, green).
* `fincm`'s producer: the budget does not bound the model construction;
  the closure cap 12 is fixed.  `ljfo`'s producer: the depth grows with the
  budget, its cost exponentially (Peirce's law: depth 40 in under 5 s,
  depth 160 not within 50 s).
* The forced-alone runs used an untracked variant (`_out/alone/`), built
  through a lakefile entry that was reverted after each of its two builds.
* `subtabdecide` keeps the exit behaviour fixed in `plldecide` (G5:
  unchanged).
* One rule slip: a `cp` of an untracked scratch file inside `_out/` was run
  by mistake and the copy deleted at once; no tracked file was involved.
