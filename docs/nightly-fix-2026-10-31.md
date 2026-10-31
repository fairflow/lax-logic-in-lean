# Nightly integrity repairs, 2026-10-31

Branch `nightly-fixes-2026-10-31`, cut from origin/main `d5dcf0e`, `.lake`
seeded by an APFS clone of the nightly checkout's v4.31.0 build of the same
commit. The nightly (`scripts/nightly-integrity.sh`) failed on 2026-10-30 and
2026-10-31 with the same four failures (logs
`~/Lean/nightly/logs/lax-logic-in-lean-2026-10-30.log` and `-10-31.log`).
They were the first full builds, and all four are old breakage, not
regressions of `d5dcf0e`.

| # | failure | cause | action | result |
|---|---|---|---|---|
| 1 | `F0/Bridge.lean`: type mismatch at 19:71, `cases` at 19:9, pin at 25:0 | semantic merge conflict (`rn` became data) | fixed | builds; pin `[propext, Quot.sound]` passes unchanged; both dependants build |
| 2 | `wip/frjw_gcc.lean`: unknown `V.WCounter.no_irregular_circ_imp_self` (44:28), `#guard_msgs` (60:0) | the lemma was withdrawn when `(Lift)` joined `FRJVi`; the statement it served is now REFUTED | none | open for Matthew; options below |
| 3 | `wipx/frjx_screen.lean`: `#guard_msgs` at 75:0 and 236:0 | axiom sets shrank upstream (the 2026-09-03 import diet) | none | SUBSTANTIVE (an axiom list); old/new below |
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

## 2. `wip/frjw_gcc.lean`: NOT FIXED (needs Matthew)

Cause. `FRJ.W.duality_closed` (stage W4, `6ca588e7`, 2026-08-31, FRJW line)
states

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
`frjw_gcc` names a declaration that exists nowhere (known since then:
`docs/ledger-campaign-2026-09-16.md`, `docs/dangling-triage-2026-09-18.md`).
The `#guard_msgs` failure at 60:0 is a consequence: elaboration recovers
with `sorryAx`, so the pin reads `[propext, sorryAx, Quot.sound]`.

Can the use be restated against the superseding result with the statement
intact? No. The superseding theorem concludes an existential, not `False`,
and the second conjunct is false of the current calculus. One designed
witness, `(Lift)` applied to the regular disproof `GccWitness` with the
retained context empty, kernel-checked in a scratch file (not committed)
with `gtimeout 600 lake env lean _out/frjw_gcc_conj2.lean`, exit 0:

    theorem frjvi_Gcc_irregular : Nonempty (FRJVi Gbu.Gcc [] [] Gbu.Gcc) :=
      ⟨.liftI Gbu.GccWitness.2 (fun _ hX => absurd hX List.not_mem_nil)⟩
    theorem duality_closed_conj2_refuted : ¬ (FRJVi Gbu.Gcc [] [] Gbu.Gcc → False)
    -- 'duality_closed_conj2_refuted' depends on axioms: [propext, Quot.sound]

So the conjunction `duality_closed` is REFUTED as stated, for the present
`FRJVi`; its first conjunct (`gccIrregular`, pinned `[propext, Quot.sound]`,
that pin passes) is untouched. This is the inversion that
`wipx/frjx_ports.lean` (§ before `gbuInv10'`) and the docstring of
`irregular_circ_imp_self_lifts` already record. (The "refuted" badge on the
lemma in `docs/pll-calculus-ledger.html` is that page's badge for negative
results, the same one `not_gbuIC_Gcc` carries; its location cell
`wip/gbu_weakening.lean:211` is stale.)

Nothing in `wip/frjw_gcc.lean` was changed. Options, each Matthew's call:

* (a) Restate `duality_closed` over what the current calculi prove, e.g.
  replace the second conjunct by the lifting characterisation

      ∀ d : FRJVi Gcc [] [] Gcc, ∃ t Γ, Nonempty (FRJVr Gcc t Γ Gcc)

  (from `irregular_circ_imp_self_lifts`), and rewrite the W4 prose, which
  presents FRJW's disproof as one "FRJV provably lacks". A statement change.
* (b) Keep the first conjunct only (`gccIrregular`) and record the second as
  REFUTED with the witness above. Also a statement change.
* (c) Remove `wip.frjw_gcc` from the `wipshared` globs, leaving the file as
  a historical record. Changes the nightly's build target.
* (d) Leave it red; the nightly then reports it every night.

## 3. `wipx/frjx_screen.lean`: NOT CHANGED (SUBSTANTIVE)

| line | declaration | pinned (docstring) | generated | class |
|---|---|---|---|---|
| 75 | `FRJ.Gbu.X.saturated_and_liftClosed` | `[propext, Quot.sound]` | `[propext]` | SUBSTANTIVE (axiom list) |
| 236 | `FRJ.Gbu.X.evalI_omegaX_goal` | `[propext, Quot.sound]` | `[propext]` | SUBSTANTIVE (axiom list) |

Both changes remove an axiom; neither adds one. Cause: the import diet
`e89f0035` (2026-09-03; `FRJ/Basic.lean` from `import Mathlib` to
`import Batteries`) shrank upstream axiom sets, and its "pin ratchet"
weakened 36 pins from `[propext, Quot.sound]` to `[propext]`, among them
`FRJ.Gbu.saturated_fderivable` (`FRJ/Gbu/Search.lean`), on which
`saturated_and_liftClosed` rests. `frjx_screen.lean` was on the FRJX line
(`993ea740` is not an ancestor of `e89f0035`), so its pins were not
ratcheted; the two lines met in `5b895074`. Nothing changed, by the
classification rule of this repair. Updating the two docstrings to
`[propext]` is what that ratchet's rule ("a pin may lose axioms, never gain
them") would do; that is for Matthew to approve.

Dependants `wipx.frjx_plan` and `wipx.frjx_ports` were skipped by Lake in
the nightly and remain UNCHECKED. `wip.frjw_gcc` has no dependants.

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

* No `wipshared` build: it would fail at items 2 and 3 regardless.
* `wipx.frjx_plan`, `wipx.frjx_ports`: UNCHECKED (item 3).
* Nothing pushed; no upstream set.
