# Next session — 2026-08-29

Standalone brief for the FRJV completeness campaign, superseding the
tail of `docs/next-session.md` (the long rolling file remains as
history; THIS file is the entry point).  Branch:
`claude/frj-redevelopment-69005f`, pushed at `d7a37c6`
(2026-08-29 12:49 BST).  Everything below is on that branch at origin.

## Session bootstrap (fresh worktree)

A fresh Claude worktree is cut from the CLONE's HEAD, not this branch
(standing trap, memory `worktree-branch-base`).  First:

```bash
git fetch origin claude/frj-redevelopment-69005f
git merge --ff-only FETCH_HEAD
cp -Rc <repo-root>/.lake .lake
```

Then `LEAN_NUM_THREADS=1 lake build wipshared` should be green
(~8813 jobs, most cached).

## Where the campaign stands

Two completeness theorems for FRJV (the RefAt-repaired calculus,
strict round-2 form), both sorry-free, choice-free, pins
`[propext, Quot.sound]` under `#guard_msgs`:

1. **`completenessV`** (wip/minmodv_assembly.lean, commit 166e7ac):

       hloc → K.Infallible → ¬ K.valid G → ProvableV G

   where `hloc : ∀ b, circPart (Λ*_b) = []` (world-wise ◯-free Λ*).

2. **`completenessV_lift`** (wip/minmodv_liftmain.lean, commit
   807858a — THE hloc-LIFT):

       TagLeafV K G → K.Infallible → ¬ K.valid G → ProvableV G

   `hloc` is GONE from the statement.  `TagLeafV K G` is the ONE named
   residual interface: a tagged (`RegWitV`, i.e. barren-or-chain with
   `Covers`) prime/or witness at a world `w` with `circPart (Λ*_w) ≠ []`
   where the goal is refuted at `w` but FORCED at some proper
   Rm-successor (i.e. not cone-refuted).  `tagLeafV_of_hloc` makes it
   vacuous under `hloc`; `completenessV_of_hloc` re-derives theorem 1
   through the lift (the supersession gate), and the two instance
   cells (residue GR, Peirce GP) are re-validated through it
   (`provableV_residue_lifted`, `provableV_circ_peirce_lifted`).

### The file chain (all in `wip/`, wipshared globs)

| file | contents |
|---|---|
| `minmodv.lean` | round 1: `IrrWitV`/`RegWitV`, barren join lemmas `regPrimeV_ax/join`, `regOrV_join`, `minModV` + `CircSupplyV` |
| `minmodv_flight.lean` | brick 2: `CornerSupply`, `corner_coverage` (the (F)/(R) size induction), `corner_lamStar_clo` |
| `minmodv_assembly.lean` | THE ASSEMBLY: corner machinery (`CornerCtx`, `cc_*`, `atLeaf/orLeaf/circLeaf`, `rowFor`, `cornerIrrWit`), `minModF`, `completenessV` |
| `minmodv_lift.lean` | `corner_lamStar_mem` (Λ*-membership at cone-trivial worlds), `circRegWit` (hloc-free regular ◯Z-wit via minZeta ∘ maxRmAbove + one barren ⋈^◯, no Z-row) |
| `minmodv_port.lean` | free grade: `FreeWitV`, fallible joins `regPrimeF_join`/`regOrF_join` (Λ*-thick premises, modal zone via `joinCtxCircF`, family `C :: upsPrime` with `axIWitV` head); pledged joins `tagPrimeP_join`/`tagOrP_join` (cone-refuted goals; family = one tagged row per proper Rm-successor pledging the goal; (J5) via each Λ*-circ's own Rm-witness); `properSucc` |
| `minmodv_liftmain.lean` | `TagLeafV`, `ht_le`/`ht_lt_of_le`, `MinModStmtL` (grades 0=irregular / 1=tagged / ≥2=free), `minModL` on measure `(ht, grade, size)`, `completenessV_lift`, `completenessV_of_hloc` |
| `minmodv_test.lean` / `minmodv_residue.lean` | instance validations incl. the `_lifted` pair |
| `frjv_probe.lean` (`lake exe frjvprobe`) | the refute-first battery (below) |

`FRJ/RefAt.lean` (library) holds brick 1: `keptOf_saturated` plus the
sf-bounded lemmas.  Superseded-in-effect but not yet retired:
`minmodv_seen.lean` (guard route) — run `/constraint-supersession-check`
before touching.

### Key structural facts (earned, reusable)

* Refuted implications have refuted consequents; refuted `◯`s have
  refuted bodies — no irregular ◯-cell is demanded at corners.
* Cone-trivial worlds are Λ*-circ-free, and there `Λ*` sits in the
  barren base ++ kept chain as LITERAL membership (`corner_lamStar_mem`).
* Cone-refutation transports along Rm; pledging a cone-refuted `C` is
  SAFE (`◯C ∈ Λ*` is impossible there) — the peer's
  `not_pledgeFam_of_circ_mem` killed only the universal supply form.
* A circ-carrying world always has a proper Rm-successor
  (`properSucc_ne_of_circ`) — the carried ◯Y's own forcing witnesses it.
* Closed formulas are CONSTANT across infallible models (`◯⊥ ≡ ⊥`
  there) ⟹ the ρ-matrix cannot test any `Infallible`-conditioned
  statement; the 6-cell engine residue is irrelevant to the lift.
* Measure `(ht, grade, size)`: the §9 wall stays dodged because the
  (0,◯Z)-cell re-anchors via minZeta/maxRmAbove (ht drops) or the
  corner serves in place; `ht_le` (antitonicity) + `ht_lt` order every
  float.
* Hygiene traps re-confirmed: `push_neg` and `by_cases` on a bounded ∀
  both pull `Classical.choice` — use the constructive filter-match
  device; `omega` on conjunction goals likewise (split first).

### The probe evidence (wip/frjv_probe.lean, `lake exe frjvprobe`)

Battery of 6–9 small infallible circ-carrying models (wf-gated with a
watched-failing negative control) × exhaustive goals over {p,q,⊥} ×
the typed V-engine (`vOps` — a HIT is a real `FRJVr` derivation;
promise/fallible joins included).  Modes: `frjvprobe <size> <rounds>
<lamCap>`, `frjvprobe replay`, `frjvprobe inspect <name>`.

| stratum | refuted | circ-carrying targets | target misses |
|---|---|---|---|
| size ≤ 5 | 608 | 19 | 0 |
| size ≤ 6 | 2 702 | 236 | 0 |
| size ≤ 7 | 16 696 | 1 027 | 0 |
| size ≤ 8 | 86 957 | 9 277 | 0 |

(size-8 output banked: `wip/frjv_probe8_out.txt`; control misses also
zero everywhere; corpus replay of residue/flight/witness shapes
all-HIT.)  **(LIFT) — the unconditional statement — is unrefuted
through four strata.**  Caveat: engine budgets (rounds=10, lamCap=16,
jmax/pmax defaults) bind in principle; a miss would have been
`not-found-within-bound`, but there were none, so nothing was capped
away silently.

## OPEN (rigidly)

1. **`TagLeafV`-freeness** — the full unconditional lift
   `Infallible → ¬valid → ProvableV`.  Either (a) prove reached
   interface instances always constructible (probe evidence points
   this way — note the engine's winning rows are often barren with the
   Λ*-circ only in irregular Θ-zones, i.e. provability routes around
   retention), or (b) find a kernel-checked separating cell — which
   per the V5 licence rule (docs/refat-plan.md) is the ONLY admissible
   trigger for a calculus round.
2. **Root-only infallibility** — weaken `K.Infallible` to the root
   (per-wit `wfal` + fallible joins), needed before fallible ρ-cell
   countermodels can feed the recursion.  This is what the ρ-matrix
   actually needs (see the closed-formula constancy fact).
3. **A hand end-to-end instance on a circ-carrying model** (M2-style:
   2 worlds, Rm-edge up, ◯p carried at the root) with `tl` supplied —
   the missing validation stratum for the lift.
4. Curation, pending Matthew's review: hoist the six-file chain to
   library level; register `frjvprobe` in TOOLS.md; retire the
   seen/guard route (supersession check first).

## Records

HANDOFF.md §§2026-08-26i → 2026-08-28d (the campaign arc, incl. the
round-3 revert and its licence lesson); docs/refat-plan.md (V5
licence discipline); docs/calculus-map.md for provenance before
asserting anything.
