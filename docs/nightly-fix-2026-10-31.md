# Nightly integrity repairs, 2026-10-31

Branch `nightly-fixes-2026-10-31`, cut from origin/main `d5dcf0e`, `.lake`
seeded by an APFS clone of the nightly checkout's v4.31.0 build of the same
commit. The nightly (`scripts/nightly-integrity.sh`) failed on 2026-10-30 and
2026-10-31 with the same four failures (logs
`~/Lean/nightly/logs/lax-logic-in-lean-2026-10-30.log` and `-10-31.log`).
They were the first full builds, and all four are old breakage, not
regressions of `d5dcf0e`.

Items 1 and 4 were fixed in the first commit. Items 2 and 3 were reported
unchanged, then fixed in a second commit after Matthew approved (2026-10-31)
option (b) for item 2 and the pin update for item 3. The four pins of
the same kind in item 3's dependants were updated in a third commit,
approved by Matthew 2026-11-01.

| # | failure | cause | action | result |
|---|---|---|---|---|
| 1 | `F0/Bridge.lean`: type mismatch at 19:71, `cases` at 19:9, pin at 25:0 | semantic merge conflict (`rn` became data) | fixed | builds; pin `[propext, Quot.sound]` passes unchanged; both dependants build |
| 2 | `wip/frjw_gcc.lean`: unknown `V.WCounter.no_irregular_circ_imp_self` (44:28), `#guard_msgs` (60:0) | the lemma was withdrawn when `(Lift)` joined `FRJVi`; the conjunct it proved is REFUTED for the current `FRJVi` | fixed, option (b), approved | `duality_closed` withdrawn; first conjunct and the refutation of the second are pinned theorems; builds |
| 3 | `wipx/frjx_screen.lean`: `#guard_msgs` at 75:0 and 236:0 | axiom sets shrank upstream (the 2026-09-03 import diet) | fixed, approved: six pins ratcheted to the generated `[propext]` (two in the file 2026-10-31, four in its dependants 2026-11-01) | `frjx_screen`, `frjx_plan`, `frjx_ports` all build (exit 0) |
| 4 | `wipshared: some modules have bad imports` | five `wipshared` globs name files moved to `FRJ/Gbu/` | fixed | `lake query wipshared:modules` watched failing, now passes |

## 1. `F0/Bridge.lean`: FIXED

Cause. `F0.holds_trans` was written on `explorer-data` (`ffe3403a`,
2026-10-22) against `PLLND.SubTab.rn` as a `Nonempty`-valued theorem,

    theorem rn (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ') (d : Nonempty (Γ ⊢ φ)) : Nonempty (Γ' ⊢ φ)

while main's `ff0b9bd9` (the same day, "the tableau-to-derivation
translation as data") made it a definition on derivations,

    def rn (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ') (d : Γ ⊢ φ) : Γ' ⊢ φ

The merge `a9b25571` joined the two without a textual conflict. Since
`Holds φ := Nonempty ([] ⊢ φ)`, the old proof passed a `Prop` where `rn`
wants a derivation, and `obtain ⟨d₁⟩ := rn …` then tried to `cases` a
`LaxND` term. `F0` is not a default target, so nothing built it before the
nightly.

Fix. Destructure the two `Nonempty` hypotheses first, then call `rn` on the
derivations. The statement and the pin are unchanged:

    theorem holds_trans {A B C : PLLFormula} (h₁ : Holds (A ↠ B)) (h₂ : Holds (B ↠ C)) :
        Holds (A ↠ C)
    #axioms_within F0.holds_trans [propext, Quot.sound]

The pin was watched failing in the nightly (it reported `sorryAx`).

Dependants. The reverse import closure of `F0.Bridge` over every `.lean`
file of the repository is `F0.Named.Part0` (direct) and `F0.Named`
(through it). Lake skipped both in the nightly, and neither can have built
on main since `a9b25571`. Both build now, and `F0.Named.Part0`'s 22
`#axioms_within … [propext, Quot.sound]` pins pass.

| command | exit |
|---|---|
| `gtimeout 3600 lake build F0.Bridge` | 0 (8660 jobs; upstream replayed, `F0.Bridge` built, 34 s) |
| `gtimeout 3600 lake build F0.Named.Part0 F0.Named` | 0 (8690 jobs; `F0.Named.Part0` 9.9 s, `F0.Named` 9.7 s) |

## 2. `wip/frjw_gcc.lean`: FIXED (option (b), approved 2026-10-31)

Cause. `FRJ.W.duality_closed` (stage W4, `6ca588e7`, 2026-08-31, FRJW line)
stated

    Nonempty (FRJWi Gcc [] [] Gcc) ∧ (FRJVi Gcc [] [] Gcc → False)

and proved the second conjunct from `FRJ.V.WCounter.no_irregular_circ_imp_self`
(`d898fb3b`, 2026-08-31),

    theorem no_irregular_circ_imp_self {G Z : Form} {St Th : List Form}
        (d : FRJVi G St Th (.circ (.imp (.circ Z) Z))) : False

On the FRJX line, `993ea740` (2026-09-01) added `(Lift)` to `FRJVi` as the
constructor `liftI` and withdrew that lemma, replacing it in
`wip/gbu_weakening.lean` by

    theorem irregular_circ_imp_self_lifts {G Z : Form} {St Th : List Form}
        (d : FRJVi G St Th (.circ (.imp (.circ Z) Z))) :
        ∃ (t : Tag) (Γ : List Form), Nonempty (FRJVr G t Γ (.circ (.imp (.circ Z) Z)))

The two lines met in the merge `5b895074` (2026-09-16); since then
`frjw_gcc` named a declaration that exists nowhere (known since then:
`docs/ledger-campaign-2026-09-16.md`, `docs/dangling-triage-2026-09-18.md`).
The `#guard_msgs` failure at 60:0 was a consequence: elaboration recovers
with `sorryAx`, so the pin read `[propext, sorryAx, Quot.sound]`.

The statement could not be kept. The superseding theorem concludes an
existential, not `False`, and the second conjunct is false of the current
calculus: `liftI` applied to the regular disproof `GccWitness`, with the
retained context empty, is an irregular FRJV disproof of `Gcc`. This was
first kernel-checked in a scratch file (`gtimeout 600 lake env lean
_out/frjw_gcc_conj2.lean`, exit 0, `[propext, Quot.sound]`).

Fix (option (b)). `duality_closed` is withdrawn, not reused. In its place:

    theorem FRJ.W.gccIrregular_nonempty : Nonempty (FRJWi Gbu.Gcc [] [] Gbu.Gcc)
      -- PROVED, pinned [propext, Quot.sound]

    theorem FRJ.W.not_frjvi_Gcc_impossible : ¬ (FRJVi Gbu.Gcc [] [] Gbu.Gcc → False)
      -- PROVED, pinned [propext, Quot.sound]; it REFUTES the old second conjunct

The first is the old first conjunct, statement unchanged (proof
`⟨gccIrregular⟩`); the second is proved by
`fun h => h (.liftI Gbu.GccWitness.2 (fun _ hX => absurd hX List.not_mem_nil))`.
Each is pinned twice: an exact `#guard_msgs in #print axioms` pin (the
file's convention; the old 60:0 pin now guards `gccIrregular_nonempty`) and
`#axioms_within … [propext, Quot.sound]` (hence `import Meta.Audit`, which
imports only `Lean`). The existing `gccIrregular` and its pin are
unchanged. The module docstring and the `gccIrregular` docstring now say
that the second conjunct held before `liftI` (993ea740, 2026-09-01), is
REFUTED for the current `FRJVi`, and that
`FRJ.V.WCounter.irregular_circ_imp_self_lifts` is the superseding positive
result.

Order of work: the file was first built with the two new `#print axioms`
unguarded (exit 0, no errors; they printed `[propext, Quot.sound]`), and
only then were the `#guard_msgs` docstrings written from that output.

| command | exit |
|---|---|
| `gtimeout 3600 lake build wip.frjw_gcc` (new prints unguarded) | 0 (976 jobs; the two `#axioms_within` pins pass) |
| `gtimeout 3600 lake build wip.frjw_gcc` (guards added) | 0 (976 jobs; no message from the file) |

`wip.frjw_gcc` has no dependants.

Follow-ups, not edited here (each still names the withdrawn lemma or the
old reading):

* `LaxBlueprint/Chapters/FRJW.lean` (about line 70, the theorem "duality_hole",
  and line 93, "proved 2026-08-31");
* `docs/claims.tsv:335` and `docs/claim-reconciliation.md:51` (the
  blueprint citation);
* `docs/pll-calculus-ledger.html:469` (entry with a stale location
  `wip/gbu_weakening.lean:211`; its "refuted" badge is that page's badge
  for negative results);
* `docs/frjw-plan.md:52` and `:89`, `docs/frjw-explainer.md:2279`,
  `docs/frjw-complexity-comparison.md:725`, `docs/frj-fidelity.md:557`,
  `docs/frjx-progress-2026-09-01.md:21`;
* `wip/gbu_search_circ.lean:1250`, `wip/rbar.lean:6`, `wipx/frjx_plan.lean:18`
  (prose);
* `wipa/`…`wipd/frjx_screen.lean:69` use the lemma in code; these are the
  frozen arms, outside every build target;
* `HANDOFF.md:3278`, `:3327`, `docs/ledger-campaign-2026-09-16.md:141`,
  `docs/dangling-triage-2026-09-18.md:164`, `:276` are dated records (a new
  dated § rather than an edit, if any).

## 3. `wipx/frjx_screen.lean` and its dependants: FIXED (approved 2026-10-31 and 2026-11-01)

| line | declaration | pinned (old docstring) | generated (new docstring) |
|---|---|---|---|
| 75 | `FRJ.Gbu.X.saturated_and_liftClosed` | `[propext, Quot.sound]` | `[propext]` |
| 236 | `FRJ.Gbu.X.evalI_omegaX_goal` | `[propext, Quot.sound]` | `[propext]` |

Classified SUBSTANTIVE (an axiom list) and first left unchanged. Both changes
remove an axiom; neither adds one. Cause: the import diet `e89f0035`
(2026-09-03; `FRJ/Basic.lean` from `import Mathlib` to `import Batteries`)
shrank upstream axiom sets, and its pin ratchet ("a pin may lose axioms,
never gain them") weakened 36 pins from `[propext, Quot.sound]` to
`[propext]`, among them `FRJ.Gbu.saturated_fderivable`
(`FRJ/Gbu/Search.lean`), on which `saturated_and_liftClosed` rests.
`frjx_screen.lean` was on the FRJX line (`993ea740` is not an ancestor of
`e89f0035`), so its pins were not ratcheted; the two lines met in
`5b895074`.

Fix, on Matthew's approval: the two docstrings now read `[propext]`; nothing
else in the file changed.

First build, `gtimeout 3600 lake build wipx.frjx_screen wipx.frjx_plan
wipx.frjx_ports` (2026-10-31): exit 1.

* `wipx.frjx_screen`: built (7.4 s), no errors.
* `wipx.frjx_plan`: FAIL, one pin of the same kind; 13 `declaration uses
  sorry` warnings (lines 78, 172, 186, 223, 232, 240, 249, 259, 285, 295,
  305, 313, 321).
* `wipx.frjx_ports`: FAIL, three pins of the same kind; 5 `declaration uses
  sorry` warnings (lines 272, 279, 289, 328, 339).

The four failing pins (left unchanged on 2026-10-31):

| file:line | declaration | pinned | generated |
|---|---|---|---|
| `wipx/frjx_plan.lean:143` | `FRJ.Gbu.X.liftClosure_irr` | `[propext, Quot.sound]` | `[propext]` |
| `wipx/frjx_ports.lean:427` | `FRJ.Gbu.X.gbuInv8'` | `[propext, Quot.sound]` | `[propext]` |
| `wipx/frjx_ports.lean:431` | `FRJ.Gbu.X.gbuInv14'` | `[propext, Quot.sound]` | `[propext]` |
| `wipx/frjx_ports.lean:435` | `FRJ.Gbu.X.unrefutedBelow_step'` | `[propext, Quot.sound]` | `[propext]` |

Each removes `Quot.sound` and adds nothing, the same ratchet situation as
the two `frjx_screen` pins.

Fix, approved by Matthew 2026-11-01: these four docstrings now read
`[propext]`; nothing else in `frjx_plan.lean` or `frjx_ports.lean`
changed (the pin of `FRJ.Gbu.X.regSoundWorld_liftClosure`,
`frjx_plan.lean:109`, which passes at `[propext, Quot.sound]`, is
untouched).

| command | exit |
|---|---|
| `gtimeout 3600 lake build wipx.frjx_screen wipx.frjx_plan wipx.frjx_ports` (2026-11-01) | 0 (973 jobs) |

Warnings in that build, per file: `frjx_screen.lean` none (up to date
from the 2026-10-31 build, which printed none); `frjx_plan.lean` 13
`declaration uses sorry` (the lines listed above); `frjx_ports.lean` 5
`declaration uses sorry` (the lines listed above) and 1 unused-variable
lint (353:17). The `sorry`s are the blueprint obligations of these
`wipx/` campaign files, unchanged by this repair.

## 4. `wipshared: some modules have bad imports`: FIXED

Cause. Lake (`LeanLib.recCollectLocalModules`, v4.31.0) logs this when it
cannot read the header of a module in the library's collection. Five
`wipshared` globs name modules with no file:
`wip.gbu`, `wip.gbu_db`, `wip.gbu_search`, `wip.gbu_measure`,
`wip.gbu_circ`. `bc355109` (2026-09-02) moved them to `FRJ/Gbu/Base`, `DB`,
`Search`, `Measure`, `Circ` (all in the `FRJGbu` library) and cut them from
the list; the merge `5b895074` (2026-09-16) resolved its `wipshared`
conflict as a union and put them back. Found by a read-only audit,
`python3 -I _out/imports_audit.py <root> …`: no other library glob in the
lakefile names a missing file.

Fix. The five stale entries are deleted from the `wipshared` list. They
are not replaced by their new names, which `FRJGbu` already builds.

| command | lakefile | exit |
|---|---|---|
| `gtimeout 600 lake query wipshared:modules -o _out/…` | fixed | 0 |
| same | `d5dcf0e` (restored with `git restore`) | 1: `error: wipshared: some modules have bad imports` |
| same | fixed (re-applied) | 0 |

`lake query wipshared:modules` computes exactly the collection that emits
the error and builds no module. A side observation, not re-tested:
`bc355109` recorded that `globs = ["FRJ.Gbu.*"]` gave the same error,
"recorded rather than diagnosed". A `X.*` glob includes `X` itself, and
there is no `FRJ/Gbu.lean` (nor `FRJ/Search.lean`, the other failing
probe), while `Meta.lean` exists for the passing `Meta.*`. That is
consistent with the same cause.

## Not done

* No `wipshared` build. Every module that failed or was skipped in the
  2026-10-30/31 nightlies has now built on this branch; the next nightly
  after merge is the whole-library check.
* The follow-up documents of item 2 are not edited.
* Nothing pushed; no upstream set.
