# `Tools/` — the FRJ(◯) certificate-and-search toolchain

Created 2026-08-21 on Matthew's instruction: *aggregate the tools that
have been shown to work and that are the latest versions.*

## Every file here is a COPY, not a move

The `wip/` originals are left in place, **unchanged**, so that any other
branch still compiles. This directory is the **maintained** side; the
`wip/` twins are stale by construction and are due to be marked as such.
Do not edit a `wip/` twin, and do not "reconcile" the two.

| here | copied from | exe | what it does |
|---|---|---|---|
| `Tools/Cert.lean` | `wip/frj_cert.lean` | `frjcert` | sequent → FRJ(◯) search → minimised countermodel → emits `.lean` + `.svg` → runs Lean on the emitted file and reports its exit code and `#print axioms` |
| `Tools/Pin.lean` | `wip/rnpin.lean` | `rnpin` | route A: search, keep the model, pin it as a `Search.Tab` |
| `Tools/Search.lean` | `wip/rnfrj.lean` | `rnfrj` | the FRJ(◯) search driver over a bank |
| `Tools/Derive.lean` | `wip/frj_derive.lean` | `frjderive` | route B: keeps the *derivation*. **Partial** — the emitter is deliberately unbuilt |
| `Tools/Bank.lean` | `wip/rnBank.lean` | — | the corpus the drivers run over |

The four `lean_exe` targets keep their existing names and now root here,
so every command in the docs still works.

## What is NOT here, and why

- **`wip/frj_sat.lean` stays in `wip/`.** It is the FROZEN reference
  implementation and the differential oracle for `FRJ/Search/Engine.lean`.
  A second copy would defeat the point of having an oracle.
- **The probes** (`frjprobe`, `rejscreen`, `closedfrag`, `rncprobe`,
  `clscreen`) stay in `wip/`. They are one-off experiments, not tools.
- **`wip/rnDict.lean`, `wip/rnDict2.lean`, `wip/rnDictGen.lean`** stay in
  `wip/`. The dictionary is withdrawn — see below.

## The dictionary status tags in `Tools/Bank.lean` are WITHDRAWN

`Bank.lean` tags every cell `proved` / `refuted` / `open`. Those tags were
generated from `wip/rnDict.lean`, whose bookkeeping is withdrawn: a
`sorry`ed cell theorem typechecks, can be applied, and is indistinguishable
*by name* from a proved one, so "still to be determined" and "asserted
without proof" became the same object. No tally derived from that record
survives. **Treat every tag as UNKNOWN** until regenerated.

Two things do survive, and they are worth being precise about:

- the **mechanism** — status as three-valued *data* rather than as
  theorems is exactly the right shape, and a rebuild should keep it;
- the **individual countermodels** in `wip/rnFRJCerts.lean`, because a
  countermodel is self-certifying and stands whatever happens to the
  surrounding table.

What is withdrawn is the tags and the tallies, not the engine.

## Provenance of "shown to work"

- all targets build clean (`lake build Tools frjcert rnpin rnfrj frjderive`);
- `frjcert` demonstrated end-to-end on `q10 ⊢ q10 ∧ q13`: search, minimise
  to 5 worlds, emit, and Lean's own check of the emitted file returning
  exit 0 with `[propext, Quot.sound]` on both theorems;
- `rnpin` / `rnfrj` produced `wip/rnFRJCerts.lean` — 35 theorems, 107
  `by decide`, 0 sorries.
