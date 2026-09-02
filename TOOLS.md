# TOOLS.md — the tool register

The register of the **latest recommended versions** of the working tools:
tactics/normalisation, proof search, countermodel search, database
extension and maintenance. `CLAUDE.md` points here and carries no tool
detail of its own; this file is allowed to be very specific **because it
is kept current**.

**Update rule.** Any commit that changes a registered tool's behaviour
updates that tool's version cell in the same commit. Version cells are
`branch @ hash · date` of the last commit touching the tool's path —
**regenerated, never hand-edited**: run

    tools/tools-register.sh

and paste its output over the cells. A row whose printed hash differs
from the cell here is stale; fix it before relying on the row.

Register head: branch `frjw-dev`, regenerated
2026-09-02 @ `f2cfb83`.

## 1 · Tactics and normalisation

| tool | use | version |
|---|---|---|
| `Rewrite.simplifyWith Rewrite.fullSetC fuel φ` (`Rewrite/`) | **Normalise before you search** — every fresh probe pipes its cells through this certified simpset first. Use `simplifyWith` against `fullSetC` (the canonicalised set), never `simplify`/`norm` or `fullSet`. Correctness is unconditional (`simplifyWith_interd`); the choice is effectiveness only. Measured by `lake exe rwscreen`. Pins: `#print axioms rndSet`/`fullSet` are `#guard_msgs`-guarded in `Rewrite/Catalogue.lean` — keep them pinned. **Pegged to R** (standing, 2026-08-26): when R grows, the new class's kernel-proved `Interd` cells join the set; the set never shrinks; promotion runs through `lake exe rcellsgen` (G4c-certificate route); queue as of 2026-08-26: the two ρ20/ρ21 forward cells. | `f1c6576` · 2026-08-26 |

## 2 · Proof search

| tool | use | version |
|---|---|---|
| Two-sided engine: `lake exe twosided`; certified layer `wip/ljfo_link.lean` | **The default for PLL sequent questions.** `TwoSidedLink.searchProves` proves via LJF◯ focused search — sound AND complete for PLL, choice-free; `Reject.certifies` refutes via Built-tree countermodels; certificates are kernel-`decide`-checkable; `two_sided_disjoint` guards the pair. ~10³× cheaper than the G4c oracle on the closed corpus. An LJF◯ *failure* certifies nothing at any fuel. | `3884eeb` · 2026-08-24 |
| G4c engines: `PLLND.Search.prove?Bounded` / `refute?` (`LaxLogic/PLLSearch.lean`) | Premise-loaded (PCLL/`DerivU`) work, and `Config.findBudget` for grind-prone cells. Certificate-carrying, untrusted-but-safe, discover-then-pin. | `b0f4ca3` · 2026-08-19 |
| **NEVER** the decidability theorem (`decideFuel`) | Its fuel bounds are infeasible; it will hang. Not a search tool at any budget. | — standing |

## 3 · Countermodel search

| tool | use | version |
|---|---|---|
| FRJ◯/FRJV: `lake exe frjvrun` (`FRJ/`, certified consequences in `Certified/RhoFRJV.lean`) | **The constructive refutation finder**: builds its countermodel from the refutation derivation (`FRJ.V.modR`); verdicts rest on `soundnessV` (PROVED, re-cleared for calculus round 3). Completeness of FRJV is OPEN — a miss is `not-found-within-bound`, never a verdict. Paper-FRJ◯ completeness is REFUTED (#80/#81); use the V calculus. Calculus round 3 (barren (J2) → RefAt) was PROPOSED AND REVERTED 2026-08-27 — unwitnessed (conservativity screening; V5 in docs/refat-plan.md); the engine is back on strict (J2). Partial completeness: `completenessV_of_circAnteFree` (goal-guarded, frame-free), `completenessV_of_endpoints` (frame-conditioned). | `89ba5cc` · 2026-08-25 |
| FRJW engine: `FRJ.Search.W.wOps` (`FRJ/Search/OpsW.lean`; register entry `Engines.frjwRefute`) | **The W-family refutation finder** — `vOps` with `⊃∉` deleted and `Lift` added (maximal retained zone, in the `stepNotIn` slot; shared `Core` loop untouched). Rows carry `FRJWr`/`FRJWi` derivations: a hit IS a `DisprovableW` witness (`disprovableW_of_hit`), sound by `soundnessW`. Smoke 2026-08-31: on the duality-gap cell `◯(◯p⊃p)` it produces the irregular row the V-engine provably lacks; ◯-free agreement with `vOps`; no false hits on valid cells. Completeness of the calculus PROVED 2026-09-01 (`decideGbuW`, FRJ/Gbu/W/Closure.lean); the engine is UNTRUSTED (bounded arity `jmax`/`pmax`, no completeness claim): a miss is `not-found-within-bound`, never a verdict, and its store is certified by `checkClosed` (row below). 2026-09-02 (A3 repair): `⋈^◯` now also fires under the RefAt-relaxed (J2) of the calculus and the closedness contract (`mkJoinCircRelaxedW`, only when the strict `A ∈ Υ` guard fails), so a closed engine store is not missing rows `DBClosed.joinCirc` demands; `⋈At`/`⋈∨` stay strict, matching their clauses. Screening runner: `lake exe wscreen` (`tools/WScreen.lean`) — per cell, W-engine beside the G4c oracle; PASS/FLAG/ALARM (a hit on a valid cell is a soundness alarm); 18/18 PASS 2026-09-01 incl. all three searchO killer cells. | `f2cfb83` · 2026-09-02 |
| A2 arity probe: `lake exe a2probe <cell> [--K= --M= --budget= --nopromise= --dropjoins=]` (`tools/A2Probe.lean`) | **Is the k-bounded join saturation closed under all arities?**  One cell per invocation, run the binary `.lake/build/bin/a2probe` under a real alarm.  Saturates with the core non-join emitters plus verbatim copies of the eight join emitters at families ≤ k (rows keep their `FRJW` derivations), fires exact-arity k+1..M families over that store and reports rows no stored row subsumes (`wsubB`, the Boolean mirror of `WSubsumes`); full all-arity check within `--budget` (2^b families), SKIPPED otherwise, never silent; `--nopromise=1` drops promise joins (exact for ◯-free `G`); `--dropjoins=1` is the gate watch (must FAIL where joins fired).  Also prints whether the root disproof is stored at bound k and compares the engine store at `jmax=pmax=k` both ways under subsumption.  Designed cells 19–21 = `Gₙ`; verdict A2 REFUTED (`docs/a2-arity.md`).  Use for DESIGNED cells only, never for corpus sweeps (Matthew, 2026-09-02). | `ed88144` · 2026-09-02 |
| The verified store certificate: `FRJ.Arity.checkClosed G db : Bool` with `checkClosed_sound`, `dbClosed_of_check`, `decideGbuW_of_check`, `decideByEngine` (`wip/check_closed.lean`, halves in `wip/check_scan.lean` + `wip/check_join.lean`; contract `wip/dbclosed_dg.lean`) | **The practical decider** (discover-then-pin): any row list `db : List (WRow G)` — the engine's, the verified saturation's, a file's — passes `checkClosed` only if it is closed under the 21 clauses at the B1/B2′-reduced arities (`DBClosedDG`), whence `DBClosed G db` (`dbClosed_of_check`) and the decision `ProvableGbuC G ⊕' DisprovableW G` (`decideGbuW_of_check`), pins `[propext, Quot.sound]`.  `decideByEngine G cfg` runs the untrusted W-engine and certifies its store: `none` = `not-closed-within-bound` (raise `jmax`/`pmax`/rounds), never a verdict.  `rowsOfDBO` carries a `DBO (wOps G)` into rows.  Cost: store-polynomial × G-exponential (`impInI` 2^\|Θ\|, `axIC` 2^\|gAt\|, intrinsic); sub-millisecond on the 20 probe stores.  Gate watched failing 2026-09-02 (`checkprobe`: join rows deleted → `false` 14/14, first row deleted → `false` 20/20). | `f2cfb83` · 2026-09-02 |
| `lake exe checkprobe` (`tools/CheckProbe.lean`) | **Engine + checker + oracle screen with the gate watch**: per cell, W-engine store → `rowsOfDBO` → `checkClosed` → `decideGbuW_of_check`, beside the G4c oracle (`PLLND.Search.settle`); PASS/ALARM/FLAG (ALARM = certified store whose decision disagrees with the oracle — escalate; FLAG = store not certified at this budget); then deletes the join-built rows and the first row and requires `false` each time.  Exit 1 on any ALARM or un-failed gate.  20/20 PASS, 0 gate failures, 2026-09-02 (`wip/checkprobe_out.txt`).  Cells are the `wscreen` set plus the designed `G₂`, `G₃`; add designed cells, not corpus sweeps. | `f2cfb83` · 2026-09-02 |
| FRJV completeness sweep: `lake exe frjvrun sweep <rounds> <lamCap>` then `tools/frjv-sweep-check.py <out>` | **The incompleteness miner.** The sweep runs the V-engine BLIND on all 462 directed ρ-cells; the checker joins its HIT/MISS against the RNDB banked `⊬` cells (`sepEntry`/`nleEntry`/`frjCertEntry`/`escEntry`, each a kernel-checked `¬ Deriv [ρi] ρj`, PLL-level). A **MISS on a banked ⊬ cell is a candidate FRJV incompleteness witness**; a HIT on a banked ⊢ cell is a soundness alarm. A MISS on an unbanked cell is not a verdict. Closes the "compare externally" gap in `sweepMain`'s docstring. Costly: ~50s on the hard cells. | `dd870c7` · 2026-08-30 |
| FinCM certificates: `FinCM.not_provable_of_check` (`LaxLogic/PLLCountermodelEmit.lean`) | Kernel-`decide` escalation of any found model: pin the frame, the theorem does the rest. Repo pin convention: witness world `w`, fallible worlds listed explicitly. | `b0f4ca3` · 2026-08-19 |
| Confluent battery: `RNC.not_derivU_of_checkConf` (`LaxLogic/PLLSearchConf.lean`) | Sweep a *known* frame battery as a check; sound, not complete (confluent models are a proper subclass). **Battery enumeration is not a discovery method** — it survives only as an independent check on a model an engine constructed. | `267fc1d` · 2026-07-27 |

## 4 · Database (RNDB): extension and maintenance

| tool | use | version |
|---|---|---|
| `RNDB` library (`RNDB/DB.lean`, `Types.lean`, `Order.lean`, `SepEntries.lean`) | The banked evidence: every entry carries its certificate (`ok` cannot be sorried); OPEN claims get **no entry** — the frontier lists are the record of what is unsettled. Census 2026-08-25: 1874 entries; the 462-cell ρ-order matrix is TOTAL (`frontierOrder = []`). Pins `#guard_msgs`-guarded per file. New 2026-08-26: `RNDB/Diamond.lean` (the covers bridge + bottom diamond). | `b16da79` · 2026-08-26 |
| `lake exe rhocover` (`tools/Cover.lean`) | The R-catalogue workbench, DB-overlaid (banked entries beat engine verdicts; conflicts abort). Modes: `sweep` (order matrix + Hasse, with control), `emit` (generate separation certificates + DB entries), `probe` (new-class candidates, lattice-laws-first), `rtable` (the R operation tables), `jcell k i j fuel` (single directed cell ρk ⊢? ρi∨ρj), `matrix` (machine-readable settled-matrix dump). | `710cb33` · 2026-08-26 |
| Hasse drawer: `tools/rho-hasse.sh` → `tools/rho-hasse-svg.py` | Re-runs the sweep and redraws `docs/rho-hasse-pll.svg`; refuses a failed-control or incomplete run. Run whenever the order changes. | `23401ae` · 2026-08-26 |
| Certificate emit/pin: `lake exe frjcert` (`tools/Cert.lean`), `lake exe rnpin` (`tools/Pin.lean`) | Emit a kernel-checkable certificate file for a settled cell and pin it. Every emitted `#print axioms` gets a `#guard_msgs` guard. | `3884eeb` · 2026-08-24 |
| The catalogue page: `docs/rn-catalogue.html` (Artifact, v26) | The presented reference: R representatives, operation tables, order matrix, structure, ladders and families. Republish to the SAME artifact URL; bump the visible version number every publish. | `e629a64` · 2026-08-26 |

**Banking loop** (unchanged in spirit): a new certified result is banked
into the DB/`Rewrite/` with its pin; banking is finished only when the
affected measurements are re-run, anything newly closed is promoted to a
kernel-pinned theorem, and the catalogue page is updated.

## 5 · Axiom hygiene (`Meta/Audit.lean`)

| tool | use | version |
|---|---|---|
| `#cf_search "pat" ["pat2" …]`, with `#choice_path` / `#choice_sources` / `#axiom_path` / `#axiom_pin` | Axiom hygiene at REACH time, not just pin time. `#cf_search` lists every environment constant whose name contains all the patterns and whose axiom closure is `Classical.choice`-free, with module of origin; tainted matches are counted in the header, never silently dropped. Use it before adopting a library lemma inside an extraction-bound proof — the 2026-09-01 instance: `List.eq_nil_iff_forall_not_mem` is tainted and leaked choice into three closure defs; `#cf_search "List.eq_nil"` shows 11 clean alternatives. The path/sources commands localise any leak that still lands; `#axiom_pin` generates the `#guard_msgs` block so pins are never retyped. | `79bc324 · 2026-09-01` |

## Superseded / dormant (pointers, not deletions)

- The D₁₅/D₁₆ representative dictionary and its open-cell lists — the
  ρ-catalogue **R** (open-ended; 22 classes as of 2026-08-25) is the only
  reference set; write **∉R**, never ∉D. `rnextend`/`rnDictGen` belong to
  the dictionary era.
- `wip/rho_engines_out.txt` engine comparison — superseded by
  `docs/two-sided-engine.md` (same corpus, later measurement).
- `FRJO/` — dormant by decision; its `def … : Prop` pattern for OPEN
  claims is the live inheritance.
- `lake exe enginecmp` — deferred 2026-08-21, must be revisited; until it
  runs, "FRJ◯ is the most efficient refutation engine" is UNVERIFIED.
