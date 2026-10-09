# Tactic extraction, repo-wide: candidate 6 surveyed

*2026-09-19. A read-only census of `LaxLogic/`, `FRJ/`, `LJF/`, `FRJO/`,
`BiLax/`, `Meta/`, `Reject/`, `Rewrite/`, `Certified/`, `tools/`, `Audit/`,
`RNDB/` — 382 `.lean` files. `wip/`, `wipa`–`wipx`, `Archive/` and `paper/`
excluded, per the campaign's scope rule. No build was run; every number below is
a count over source text, and every projection is labelled as an estimate.*

Companion documents: `docs/proof-simplification-plan-2026-09-16.md` (the
campaign and its ten-candidate table — this is candidate 6),
`docs/ljf-simp-round1.md` and `docs/ljf-round-d-2026-09-18.md` (the method and
its recorded refusals).

---

> ## READ THIS FIRST — the plan below has been executed, and is no longer advice
>
> **Status as of 2026-10-09.** Everything from "## The one structural fact" down
> to "## 4. Ranking" is the survey **as written on 2026-09-19**, kept unrewritten
> because it is the record of what was predicted. It is not a to-do list, and
> three of its four steps are settled:
>
> | step | | outcome |
> |---|---|---|
> | 1 | `fin_sub`, 135 Finset sites in the three UI files | **DONE** — 389 lines, gated clean (`01ba085`) |
> | 2 | the `Sub.cons`/`Sub.grow` inlining reversal, ~110 lines | **NOT DONE** — Matthew's reading, 2026-10-09: no clear benefit. It was the weakest of the four |
> | 3 | six `Sub` facts for the zero-import island | **DONE** — 209 lines, 51 sites, gated clean (`e7698b1`) |
> | 4 | `mem_sub` across the Mathlib island, 93 sites | **REFUTED** — see §"Step 4, REFUTED 2026-10-09" below |
>
> **Outturn: 598 lines of the ~1,159 estimated**, and the whole gap is step 4.
>
> **Two of this document's own measurements did not survive execution**, and both
> argue for distrusting a token-level census:
>
> * §2 records step 1's sites as a **three**-line block. They are four: the
>   closing paren sits on the `tauto` line, so the block folds onto its `(by`
>   line and the saving is three lines per site, not two. The outturn beat the
>   estimate for this reason.
> * §1 and §3c describe step 4's leaves as `List.mem_cons_self` /
>   `List.mem_cons_of_mem`. In `Craig.lean` they are `List.Mem` **constructors**
>   (`.head _`, `.tail _ (…)`) — the counted text is not there — and the blocks
>   are nested in a way that defeats bulk conversion, some sharing closing parens
>   with siblings.
>
> **And the refusal that matters is not in the ranking.** §4's watched failure for
> step 4 is a *timing* test, and §"What was not measured" says the axiom question
> "is **not** answered here". It is answered now, and it is the reason step 4 is
> dead: five `tauto` calls move `PLLND.craig_interpolation'` from
> `[propext, Quot.sound]` to `[propext, Classical.choice, Quot.sound]`. Read the
> ranking table with that in mind — it costs its own step 4 row.

## The one structural fact that decides the whole candidate

**The repository is two islands, and `tauto` is only on one of them.**

`LaxLogic/Focusing/LJF.lean` and `LJF/OCore.lean` have **zero imports** —
deliberately, and it is written down in both files: *"Zero imports: no mathlib,
no other calculus carries any of the proof"* (`LJF/OCore.lean:4`), and the IPC
control's own statement of the same policy at
`LaxLogic/Focusing/LJF.lean:3`. Every `LJF/*` module roots at `LJF.OCore`; the
whole chain `ORows → O → OFuel → OFuelSound → OFuelP → OFuelPCof → OFuelPFam →
OFuelPSound → OFuelMin → OFuelPMin` has a Mathlib-free import closure, as does
`LJF/OUniverse.lean` and (Batteries-only) `FRJ/Basic.lean`. Measured by
computing the transitive import closure of every module and testing for any
`Mathlib*` member.

`Meta/Portable.lean:8` and `Meta/Tactics.lean:4` record why this is
load-bearing: *"ANY Mathlib import except `Mathlib.Tactic.Lemma` drags the same
~1307-module foundation, so the cost is all-or-nothing"*, and a cold clone of
`lake exe pll` built `Mathlib.CategoryTheory`, `MeasureTheory` and
`NumberTheory` before printing a verdict.

`tauto` is `Mathlib.Tactic.Tauto`. So the `simp only [mem…] ; tauto` shape —
which is *already the repository's own solution*, 170 times over — **cannot be
used in the island that holds 550 of the 856 collapsible structural lines.**
That island needs named lemmas instead. This split is the single most important
output of the survey, and it is why "one `mem_bash` tactic, repo-wide" is not
the right artefact.

## 1. The census

Method, stated so the numbers can be re-derived:

* **`simp` census.** Every `simp` / `simp only` / `simp_all` / `dsimp` with a
  bracketed lemma list (3,397 invocations), lists extracted by bracket
  balancing. "Membership-dominated" = at least one entry matching `List.mem_*`,
  `List.not_mem_*`, `Finset.mem_*`, `Multiset.mem_*`, `mem_ite_list`,
  `ite_none_eq_some`, and those entries at least half the list.
* **Block census.** A *bookkeeping block* is a maximal run of consecutive tactic
  lines each of which is `intro x hx`,
  `rcases (List|Finset).mem_(cons|append|insert|union).mp h with …`,
  `exact/refine/apply` of a membership **constructor** (`List.mem_cons_self`,
  `mem_cons_of_mem`, `mem_append_left/right`, `Finset.mem_insert_self/of_mem`,
  `.head`/`.tail`), `simp only [… mem_ …] at …`, or `tauto`, with continuation
  lines absorbed by paren balance. Blocks of one tactic are excluded throughout
  (a one-line block replaced by a one-line tactic saves nothing).
* **Purity.** A block is **pure** if no token in its body is a foreign
  identifier — nothing but the membership constructors, the split lemmas,
  `rfl`, and hypothesis/variable names. A block is **mixed** if a leaf applies
  anything else (`splits_sub`, `mem_filter`, `.mpr`, a context hypothesis at a
  non-membership goal).
* **Saving.** Measured per block, not modelled: if the line *before* the block
  ends in `(by` / `by` / `=> by` / `(fun`, a one-line replacement absorbs the
  whole block, so the saving is its physical line count; otherwise the saving is
  that count minus one. Physical lines throughout, comments stripped.

| # | idiom | occ. | files | median lines/occ. | lines a one-line replacement removes | how estimated |
|---|---|--:|--:|--:|--:|---|
| S1 | `simp`/`simp only` whose lemma list is membership-dominated | **639** | **77** | **1** | **0** | Measured, not estimated: 608 of 639 occupy exactly one physical line, 31 occupy two. A macro replaces one line with one line. |
| S1a | — of those, list lies inside a fixed membership bundle | 306 | — | 1 | 0 | |
| S1b | — of those, list carries a project-local definition (`gHat` 50, `sf` 40, `invertPos` 32, `joinCtxAt` 18, `joinCtxOr` 16, `hyps` 9, `splits` 8 …) | **333** | — | 1 | 0 | A fixed bundle cannot reproduce these; `mem_bash [gHat]` is not shorter than `simp only [gHat, List.mem_append]`. |
| S2 | membership `simp … at h` with `rcases`/`obtain` on the *next* line | **211** | **35** | 2 | **211** (est., upper bound) | 2 lines → 1. 17 distinct destructuring patterns: 68 × `h \| h`, 59 × `(h\|h) \| h`, 26 × `h \| h \| h`, 12 × `⟨⟨⟨·,·⟩,·⟩,·⟩`, 11 × `((h\|h)\|h) \| h`. |
| A | structural membership walk (`rcases mem_cons.mp` cascade with constructor leaves) | **293** | **64** | 4 | **1,036** | Per-block measurement above. |
| A-pure/ML | — pure leaves, Mathlib in the import closure | **93** | **35** | 3 | **236** | |
| A-pure/Z | — pure leaves, **zero-Mathlib island** | **116** | **11** | 4 | **528** | `LJF.lean` 165, `OCore` 103, `O` 74, `OFuelPFam` 61, `OFuelSound` 68, `OFuelPSound` 39, `OFuelMin`/`OFuelPMin` 6+6, three strays 6. |
| A-mixed | — a leaf applies a foreign lemma or hypothesis | **84** | **36** | 4 | (272 — refused, §2) | ML 59 blocks / 194; Z 25 blocks / 78. |
| B | `intro y hy` / `simp only [Finset.mem_insert] at hy ⊢` / `tauto` | **170** | **13** | 3 | **452** | 132 blocks (396 lines, saving **395**) have *exactly* `Finset.mem_insert`; 138 exact-string matches of `simp only [Finset.mem_insert] at hy ⊢` — `G4UIAdq` 54, `G4UI` 45, `G4UITrunc` 39. |
| C | `rw [interp]; split` / `all_goals rename_i heq` / `· rw [hsat] at heq; cases heq` | **39** | **5** | 3 | **~78** (est.) | 3-line prefix → 1. `Focusing/LJF` 9, `ORows` 9, `OFuelMin` 10, `OFuelPMin` 10, `OCore` 1. All zero-Mathlib. |
| D | `obtain ⟨⟨⟨X,rest⟩,hXr⟩,hmem,hEq⟩ := memMapWitness …` / `subst hEq` / `cases X with` | **45** | **9** | 10+ | (refused, §2) | `memMapWitness` occurrences: `OCore` 14, `Focusing/LJF` 10, `OFuelPSound` 5, `OFuelSound` 5, `OFuelPFam` 3, `O` 3, `OFuelMin`/`OFuelPMin` 2+2, `OSearch` 1. |
| E | `split at h` outside the three UI files | **18** | **6** | — | — | 100 repo-wide; 82 are in `G4UITrunc`/`G4UI`/`G4UIStab`, i.e. the candidate-7 floor of 96. Too thin to carry a tactic. |
| F | `constructor` / `· intro h` (iff split) | **69** | **33** | 2 | 0–69 | Already two tokens; a macro would hide the iff. Named for completeness, not proposed. |

**Total collapsible population, measured: 1,488 lines** (A 1,036 + B 452). The
candidate's "≥1,500 lines" is very nearly right as a *population* figure; §2
shows 1,216 of it survives the mechanism test and 272 does not.

One correction to the candidate's wording. It names "a `mem_bash`-style tactic
**+ ~6 named lemmas**". The survey inverts the emphasis: **the simp-bundle half
of `mem_bash` saves zero lines** (row S1, measured), and the named-lemma half is
worth more than the tactic half (528 against 236 for idiom A). The plan already
half-said this at its line 89 — *"explicit `simp` lemma lists are a weak
signal"* — and the 333 sites at S1b are the mechanism.

## 2. Mechanism test: PROPOSED / REFUSED

### PROPOSED — idiom B, `fin_sub` in the three UI files (395 lines)

*The repeated part is a fixed three-tactic sequence with no case split at all.*
The 132 like-for-like sites run, character for character, `intro y hy` /
`simp only [Finset.mem_insert] at hy ⊢` / `tauto`, always as the argument of
`weaken_subset (by …)` (e.g. `G4UI.lean:291`, `:1223`, `G4UIAdq.lean:381`,
`:793`, `G4UITrunc.lean:2110`). A macro whose expansion is that exact text
changes nothing the elaborator sees; the only risk is hygiene, and it is the
same risk `mem_tbl` already survived in the same files. The over-reduction
constraint that shaped `mem_tbl` does **not** bite: these blocks close their
goal, so no guard proposition has to survive to a downstream `rw [if_neg …]`.

### PROPOSED — idiom A-pure, Mathlib island, `mem_sub` (236 lines)

*The repeated part is a case split, and here the arms ARE uniform — provably,
because the repository has already replaced this exact split by `simp;tauto` 170
times.* Every block is a cascade of `rcases List.mem_cons.mp hZ with rfl | hZ`
whose every leaf is a membership constructor; after
`simp only [List.mem_cons, List.mem_append, List.mem_singleton,
List.not_mem_nil] at hZ ⊢` the hypothesis and the goal are propositional
combinations of the *same* atoms (`Z = X`, `Z ∈ Γ`), which is precisely what
`tauto` decides. Idiom B is the same goal shape over `Finset.mem_insert` and is
discharged that way today at 170 sites: **idiom B is the existence proof for
idiom A's arms being uniform.** The blocks are closed sub-proofs, so nothing
downstream reads their intermediate state and the over-reduction hazard is
inert.

### PROPOSED — idiom A-pure, zero-Mathlib island, six `Sub` lemmas (528 lines)

*Not a tactic — the doubled thing here is a small set of FUNCTIONS on
inclusions, and the campaign's own rule says a function abstracts for free.* The
116 blocks classify into 22 canonical shapes, and five of them carry 74 blocks /
390 lines. Each shape is one named fact about `Sub` (`LJF/OCore.lean:122`,
`LaxLogic/Focusing/LJF.lean:107`, both
`def Sub (Γ Γ' : List Neg) : Prop := ∀ N, N ∈ Γ → N ∈ Γ'`):

| shape | blocks | lines | the fact | needs new code? |
|---|--:|--:|---|---|
| `⟨1s, 0s, 2h⟩` | **26** | 132 | `Sub (X :: Y :: Γ) (Y :: X :: Γ)` — exchange | **yes**, `Sub.swap` |
| `⟨0s, 1?⟩` | 16 | 61 | `Sub.cons _ ((Sub.grow _).trans hsub)` | **no** |
| `⟨0s, 2h⟩` | 15 | 57 | `Sub.cons X (Sub.grow Y)` | **no** |
| `⟨1s, 0s, 3h⟩` | 10 | 70 | `(Sub.swap _ _).trans (Sub.cons _ (Sub.cons _ (Sub.grow _)))` | via `swap` |
| `⟨2s, 0s, 1s, 3h⟩` | 7 | 70 | `Sub (X :: Y :: Z :: Γ) (Y :: Z :: X :: Γ)` — rotate | **yes**, `Sub.rot3` |
| append shapes | ~22 | ~90 | `Sub.app`, `Sub.appL`, `Sub.appR` | **yes**, three lemmas |

Exemplars, read and confirmed by hand: `LaxLogic/Focusing/LJF.lean:1678` and
`:3613` (exchange, five lines each), `:3901` (`Sub.cons X (Sub.grow Y)`, four
lines), `:3534` (the `hsub` composition, four lines), `:2187` (the rotate, ten
lines), `LJF/OFuelPSound.lean:231`. **31 blocks / 118 lines need no new code at
all** — they are `Sub.cons`/`Sub.grow` inlined by hand, the same inlining
reversal that candidate 8's Family B performed, and the same "compositions" that
candidate 8 explicitly set aside as not fitting `rowHyp`/`rowSub`. They fit
`Sub.cons` and `Sub.trans`, which exist today.

Two safety notes for this island, both checked: (a) `Sub` is a `Prop`, so proof
irrelevance makes the replacement invisible to reduction — the `LaxND` iota
mechanism is inert here, exactly as candidate 8 recorded for the same reason;
(b) 54 of the 116 blocks open with `intro Z hZ` and 62 sit inside an
already-bound `fun Z hZ => by`, so the latter become bare terms
(`(Sub.swap _ _)` in place of `(fun Z hZ => by …)`), which is where the "inline"
saving comes from.

### REFUSED — the `mem_bash` simp bundle as a line-saving measure

*The thing that is doubled is a NAME LIST, and a name list is already one line.*
Row S1 is the measurement: 608 of 639 membership-dominated `simp only` calls
occupy exactly one physical line, so `mem_bash at h` in place of
`simp only [List.mem_cons, List.mem_append] at h` saves zero lines. Worse,
**333 of the 639 carry a project-local definition in the same list** (`gHat` 50,
`sf` 40, `invertPos` 32, `joinCtxAt` 18, `joinCtxOr` 16 …) and a fixed bundle
cannot reproduce them. A bundle would also silently widen the simp set at 306
sites, which is the over-reduction failure mode candidate 7 was designed around.
The lever the plan already identified — marking those five definitions `@[simp]`
or giving each a named equation set — is a different piece of work and dominates
this one.

### REFUSED — idiom A-mixed (84 blocks, 272 lines)

*The bodies do different mathematics — the `TRF`/`URF` lesson at the leaf.*
These blocks look identical to A-pure at the level of the cascade, but a leaf
applies something the propositional closure cannot see: `.mpr` of a
characterisation (46), `List.mem_filter` (19), `splits_sub` (11),
`mem_unionAll` (9), `mem_sdiff` (7), `subParkInv`, `rm_subset`, `joinCtxAt`.
After `simp only [List.mem_cons …]` the hypothesis atom and the goal atom are
*different propositions* related by a lemma, so `tauto` cannot close them; the
honest tactic is `solve_by_elim`/`aesop` with those lemmas in scope, which is the
outcome the plan predicted for candidate 6 in advance — *"a
`solve_by_elim`-backed tactic that is slower than the explicit terms it
replaces"*. The 272 lines are real but they are not one fact, and buying them
costs a search at every site. **Not proposed.** If ever revisited, the plan's own
rule applies: adopt only where the explicit term exceeds three lines, which here
is 41 of the 84.

### REFUSED — idiom D, the `memMapWitness` station rows (45 sites)

*The repeated part includes a `cases` on an inductive, and this one is the
campaign's fifth-refusal shape.*
`obtain … := memMapWitness _ _ x hx2` / `subst hEq` /
`cases X with | up P0 => … | imp Q0 N => cases Q0 with …` splits on the
*negative-formula constructor*, and the arms below the split carry the goal of
the particular station, which differs per site. This is the same object the plan
already handled correctly: the fuel files got
`stationCircF`/`stationUpF`/`stationCircP`/`stationUpP` (1,077 lines) and
`OCore` was refused because a recursive call under a lambda loses the variables
`ljf_dec_sound`'s `assumption` farm reads. A macro could emit the three-line
preamble, but the preamble is three lines against ten-plus lines of per-site
arms, and it would sit immediately above a `cases` whose arms are not uniform.
**No further extraction here.**

### REFUSED — idiom E, `mem_tbl` beyond the three UI files (18 sites, 6 files)

The 2026-09-18 entry already established that the 96 remaining `split at` sites
in the UI trio are bounded by a matcher (`match b with`, `match C with`) and
that `mem_ite_list` does not reach a matcher. Outside those three files there
are 18 `split at` sites in six files, no two of which share a table. Below every
threshold.

### NOTED, NOT PROPOSED — S2 (211 lines) and idiom C (~78 lines)

S2 fuses `simp only [… mem …] at h` with the `rcases` on the next line into one
`mem_cases [extra] h with pat`. It is mechanically sound — 17 patterns, all
uniform — but it is **211 lines spread over 35 files at ~6 sites each**, 149 of
them needing an extra-lemma argument, and it touches the largest number of
modules of anything in this survey for the smallest per-file gain. Ranked last,
and it is below the line.

Idiom C is the `rw [interp]; split; all_goals rename_i heq` dance named in
`docs/ljf-simp-round1.md` ("The surprise of round C"). 39 sites, 5 files, all
zero-Mathlib, ~78 lines. A macro is possible but must reproduce a *bullet
structure under a variable goal count*, which is the fragile part; the recorded
`rename_i` hygiene escape (`set_option hygiene false`) would probably be needed,
as it was for `ljf_dec_*`. Worth doing only after the three proposed steps land.

## 3. The artefacts

### 3a. `Meta/Tactics.lean` — the home for both macros

**Checked before proposing.** `Meta/Tactics.lean` is *already* the designated
home and says so: *"the tactics the PROOFS in this repository actually use, in
one auditable list … Add a line here when a proof needs a new tactic"*
(`Meta/Tactics.lean:16`). It imports only `Aesop` and eighteen
`Mathlib.Tactic.*` modules — including `Mathlib.Tactic.Tauto` — and **no project
module**, so it is a leaf of the project import graph and cannot create a cycle
with anything. Its own docstring carries the one constraint to respect:
*"Definitions, engines and executables should NOT import this: the runtime
closure of `lake exe pll` is meant to stay Mathlib-free."* Every file in §3c
already has Mathlib in its closure, so none of them is in that runtime closure
and none gains a dependency it did not have.

```lean
/-- Close a purely structural LIST inclusion: the goal is `∀ z ∈ s, z ∈ t`
with `s` and `t` explicit `cons`/`append` towers over the same tail
variables, so that after unfolding membership the fact is propositional.
Refuses (leaves the goal) when a leaf needs a lemma — that case is the
`A-mixed` population of `docs/tactic-extraction-survey-2026-09-19.md` and is
deliberately out of scope. -/
macro "mem_sub" : tactic =>
  `(tactic| (intro _z _hz
             simp only [List.mem_cons, List.mem_append, List.mem_singleton,
               List.not_mem_nil] at _hz ⊢
             tauto))

/-- `mem_sub` where the binder and the membership hypothesis are already in
scope (62 of the surveyed sites sit inside `fun Z hZ => by …`). -/
macro "mem_sub" " at " h:ident : tactic =>
  `(tactic| (simp only [List.mem_cons, List.mem_append, List.mem_singleton,
               List.not_mem_nil] at $h:ident ⊢
             tauto))

/-- Close a `Finset` insert-tower inclusion.  The expansion is character for
character the three lines it replaces at 132 sites, so the elaborator sees
nothing new; the lemma list is deliberately NOT widened past
`Finset.mem_insert`. -/
macro "fin_sub" : tactic =>
  `(tactic| (intro _y _hy
             simp only [Finset.mem_insert] at _hy ⊢
             tauto))
```

The `Finset.mem_union` / `Finset.mem_singleton` lemmas are deliberately
**absent** from `fin_sub`: 132 of the 170 idiom-B sites use `Finset.mem_insert`
alone, and adding lemmas is the over-reduction move that `mem_tbl`'s docstring
warns against. The other 38 keep their explicit `simp only`.

### 3b. `LJF/OCore.lean` and `LaxLogic/Focusing/LJF.lean` — six `Sub` lemmas, in each file

Two copies, because these are the two zero-import islands and the whole point of
both files is that nothing carries their proofs. Place immediately after
`Sub.grow` (`LJF/OCore.lean:141`, `LaxLogic/Focusing/LJF.lean` the analogous
line). Statements only; proofs are four lines each, the body already written out
at the sites.

```lean
/-- Peel one hypothesis off the SOURCE.  Every walk over an explicit cons
tower is a chain of these ending in `Sub.grow` or `Sub.refl`. -/
theorem peel {Γ Γ' : List Neg} {X : Neg} (hX : X ∈ Γ') (h : Sub Γ Γ') :
    Sub (X :: Γ) Γ'

/-- Exchange at the head.  26 sites, 132 lines — the commonest shape in the
zero-import island. -/
theorem swap {Γ : List Neg} (X Y : Neg) : Sub (X :: Y :: Γ) (Y :: X :: Γ)

/-- Rotate the first three.  7 sites, 70 lines. -/
theorem rot3 {Γ : List Neg} (X Y Z : Neg) :
    Sub (X :: Y :: Z :: Γ) (Y :: Z :: X :: Γ)

/-- Both halves of an append land in one target. -/
theorem app {Γ₁ Γ₂ Δ : List Neg} (h₁ : Sub Γ₁ Δ) (h₂ : Sub Γ₂ Δ) :
    Sub (Γ₁ ++ Γ₂) Δ

/-- Grow the target on the right. -/
theorem appL {Γ Δ : List Neg} (Δ' : List Neg) (h : Sub Γ Δ) : Sub Γ (Δ ++ Δ')

/-- Grow the target on the left. -/
theorem appR {Γ Δ' : List Neg} (Δ : List Neg) (h : Sub Γ Δ') : Sub Γ (Δ ++ Δ')
```

`peel` rather than `head`, so that `Sub.head` does not collide with
`List.Mem.head` in dot-notation position.

### 3c. Files edited, and sites per file

**Step 1, `fin_sub` — 3 files, 132 sites** (exact-string
`simp only [Finset.mem_insert] at hy ⊢`: 54 / 45 / 39):
`LaxLogic/PLL/UI/G4UIAdq.lean` (1,113 ln), `LaxLogic/PLL/UI/G4UI.lean` (1,846),
`LaxLogic/PLL/UI/G4UITrunc.lean` (3,126). Plus one import line each, and the
`Meta/Tactics.lean` addition.

**Step 2, no new code — 6 files, 31 sites**: `LaxLogic/Focusing/LJF.lean` and
the LJF chain, the `⟨0s,2h⟩` and `⟨0s,1?⟩` shapes → `Sub.cons X (Sub.grow Y)`
and `Sub.cons _ ((Sub.grow _).trans hsub)`.

**Step 3, the `Sub` lemmas — 8 files, 85 sites**:
`LaxLogic/Focusing/LJF.lean` 33 blocks / 169 lines (4,485 ln file),
`LJF/OCore.lean` 21 / 104 (4,041), `LJF/O.lean` 17 / 78 (2,094),
`LJF/OFuelPFam.lean` 17 / 66 (1,958), `LJF/OFuelSound.lean` 13 / 69 (1,111),
`LJF/OFuelPSound.lean` 8 / 39 (1,239), `LJF/OFuelMin.lean` 2 / 8,
`LJF/OFuelPMin.lean` 2 / 8. (Steps 2 and 3 overlap in file set; 116 blocks in
total.)

**Step 4, `mem_sub` — 35 files, 93 sites**, the head being
`LaxLogic/PLL/Sequent/Craig.lean` 14 / 56, `LJF/OBridge.lean` 8 / 28,
`LJF/OPolInv.lean` 7 / 25, `LaxLogic/PLL/UI/CandOr.lean` 6 / 13,
`LaxLogic/PLL/Sequent/Sequent.lean` 5 / 11, `LaxLogic/PLL/ND/Judgmental.lean`
4 / 12, `FRJ/Gbu/W/Search.lean` 4 / 14, `Rewrite/Core.lean` 4 / 8,
`LaxLogic/PLL/G4/G4P.lean` 3 / 13, `FRJ/Gbu/W/Closure.lean` 3 / 10,
`FRJ/Gbu/Circ.lean` 3 / 6, and 24 files with one or two.

## Step 1, EXECUTED 2026-09-19 03:29 — `fin_sub`, 135 sites, 389 lines

Carried out exactly as ranked below, watched failure first.

**The watched failure came back clean.** One site rewritten
(`LaxLogic/PLL/UI/G4UI.lean`, the `h.weaken_subset (by …)` inside the `andAll`
cons arm) and that file compiled alone, exit 0 in 15 s. Hygiene was the only
thing that could fail — whether the `_y`/`_hy` that `intro` introduces inside
the quotation are visible to the `simp only … at _hy` in the same quotation —
and it does not.

**One correction to the census, found by doing it.** The document above reports
"138 exact-string matches" of the middle line and treats the block as three
lines. The block is **four**: 128 of the 138 sites are

```lean
        h.weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
```

with the closing paren on the `tauto` line, so the whole thing folds onto the
`(by` line as `h.weaken_subset (by fin_sub)` and the saving is **three** lines
per site, not two. That is why the outturn beats the estimate.

| file | before | after | sites |
|---|--:|--:|--:|
| `LaxLogic/PLL/UI/G4UI.lean` | 1,846 | 1,726 | 45 |
| `LaxLogic/PLL/UI/G4UIAdq.lean` | 1,113 | 961 | 51 |
| `LaxLogic/PLL/UI/G4UITrunc.lean` | 3,126 | 3,009 | 39 |
| total | 6,085 | 5,696 | **135** |

**−389 lines net**, of which 15 are the macro itself, so 404 lines of
bookkeeping are gone. Estimate was 395; outturn 389 net / 404 gross.

**Three sites left alone**, all in `G4UIAdq`: their fourth line is
`rcases hy with rfl | hy`, not `tauto`, so the block does not close its goal and
`fin_sub` is the wrong tactic for it. Three sites is below every threshold this
campaign uses.

**Home.** `G4UI.lean`, immediately after `mem_tbl`, not `Meta/Tactics.lean`. The
three files form an import chain (`G4UITrunc → G4UIStab → G4UIAdq → G4UI`), so
one definition reaches all of them, and `mem_tbl` set the precedent in the same
place for the same reason. Nothing gains an import.

**The axiom question, answered.** `tauto` is classical-capable and this was the
step that could have moved a pin. It cannot have: the macro's expansion is
character for character the three lines it replaced, so the elaborator sees what
it saw before. Confirmed rather than argued —
`#guard_msgs in #print axioms inter_adequate` (`G4UIAdq.lean:958`) passes
untouched, and `lake build` is green at 8,748 jobs.

## Step 4, REFUTED 2026-10-09 — `mem_sub` would make Craig interpolation classical

The designed watched failure was a timing test. It fired for a better reason
than timing, and the refusal is a certificate rather than a judgement.

**What was done.** `mem_sub` as specified in §3a, defined locally in
`LaxLogic/PLL/Sequent/Craig.lean` (the densest single file, 14 sites by the
census), applied to **five** sites whose shape is unambiguous — the `rcases
List.mem_cons.mp` walk with `List.Mem` constructor leaves, inside
`X.rename (by …)`. The proofs all went through: there is no correctness problem
with the tactic.

**What broke is the axiom profile.** Four of the file's own
`#guard_msgs`-guarded `#print axioms` pins failed, and this is the diff:

```
- 'PLLND.SCh.maehara'          depends on axioms: [propext, Quot.sound]
+ 'PLLND.SCh.maehara'          depends on axioms: [propext, Classical.choice, Quot.sound]
- 'PLLND.SC.maehara''          depends on axioms: [propext, Quot.sound]
+ 'PLLND.SC.maehara''          depends on axioms: [propext, Classical.choice, Quot.sound]
- 'PLLND.craig_interpolation'' depends on axioms: [propext, Quot.sound]
+ 'PLLND.craig_interpolation'' depends on axioms: [propext, Classical.choice, Quot.sound]
- 'PLLND.craig_implication''   depends on axioms: [propext, Quot.sound]
+ 'PLLND.craig_implication''   depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Five `tauto` calls are enough to make Craig interpolation classical.** And the
primed names are not incidental: the file maintains BOTH variants on purpose —
`craig_interpolation` at `[propext, Classical.choice, Quot.sound]` and
`craig_interpolation'` at `[propext, Quot.sound]` — so the choice-free halves
are a deliberate, pinned result. Twenty-six lines is not a price worth paying
for them, and no amount of care at other sites changes the mechanism: `tauto`
has no choice-free discipline, which is precisely why `mem_ite_list` was written
with `cases inst` rather than `by_cases` back in candidate 7.

**So step 4 is REFUSED**, and with it the 236-line estimate. The underlying
population is real; the tactic that was proposed to take it is not admissible
here.

**Two corrections to §1's census, found by doing it.** Both are reasons to trust
a token-level census less:

* **The leaf shape is wrong.** In `Craig.lean` the leaves are `List.Mem`
  *constructors* — `.head _`, `.tail _ (.tail _ h)` — not the
  `List.mem_cons_self` / `List.mem_cons_of_mem` lemmas the census matched on.
  `mem_sub` still handles them (`simp only [List.mem_cons]` covers both), but
  the count was arrived at by matching text that is not there.
* **The nesting is wrong, and it defeats bulk conversion.** Of the 13 blocks in
  the file, 2 apply a context hypothesis `H` at a leaf and so belong to the
  refused A-mixed class, and several are *pairs* of blocks in which one block's
  final line also carries the closing parens of a sibling's enclosing `(by`. A
  converter keyed on tokens and paren balance, ignoring bullet indentation,
  flattens genuinely nested case splits into one block and loses arms; mine did,
  producing `unexpected token '·'` at `:324`. Each site wants reading.

**On the timing half**: not reportable. Two builds of byte-identical reverted
source measured 5.33 s and 15.93 s wall clock, so wall clock on this machine is
too noisy at this scale to carry a conclusion, and `user` time (3.15 s against
5.74 s) is a single pair. The axiom result needs no help from it.

**What survives of the plan.** Step 1 (`fin_sub`, 389 lines) and step 3 (the six
`Sub` facts, 209 lines) are done and gated. Step 2 is unbuilt by Matthew's
reading, and I agree it was the weakest. Step 4 is refused above. So the plan's
outturn is **598 lines of its ~1,159 estimate**, and the gap is almost entirely
step 4 — which was the step whose saving depended on a tactic the repository's
axiom discipline does not permit.

## 4. Ranking, cheapest first, each with its designed watched failure

Measured savings unless marked *(est.)*. The order is by risk and by blast
radius, as the campaign's own §"Order of work" requires — one file before three,
three before thirty-five.

| # | step | files | sites | saving | the single cheapest thing that refutes it |
|---|---|--:|--:|--:|---|
| 1 | `fin_sub` in the three UI files | 3 (+`Meta/Tactics`) | 132 | **395** | **Rewrite ONE site in `G4UI.lean` and compile that file alone.** The macro's expansion is byte-identical to the three lines it replaces, so the only thing that can fail is hygiene — whether `_y`/`_hy` introduced inside the quotation are visible to the `simp only … at _hy` in the same quotation. If that one site compiles, all 132 do. (Second, cheap watch: `#print axioms` on one `G4s.weaken_subset` consumer must stay unchanged — `tauto` is classical-capable and this is the step that could quietly add `Classical.choice`, which is the reason `mem_ite_list` used `cases inst`.) |
| 2 | `Sub.cons`/`Sub.grow` inlining reversal, no new code | 6 | 31 | **~110** *(est.; 118 lines measured, one line of slack per standalone block)* | **Rewrite the four-line block at `LaxLogic/Focusing/LJF.lean:3901` as `Sub.cons _ (Sub.grow _)` and compile `LaxLogic.Focusing.LJF` alone.** If the implicit arguments do not solve at that site they will not solve at the other thirty. |
| 3 | `Sub.swap` / `rot3` / `app` / `appL` / `appR` / `peel`, both zero-import files | 8 | 85 | **~418** *(est.; 528 measured maximum less step 2's 110)* | **Add `Sub.swap` to `LJF/OCore.lean`, rewrite the block at `LaxLogic/Focusing/LJF.lean:1678`, compile.** The two files need *independent* copies — if the `LJF.lean` copy is forgotten, the build fails loudly, which is the good failure. The real watch: the 62 sites that sit inside `fun Z hZ => by …` must become **terms**, and a term in an argument position is elaborated against an expected type that the tactic block was previously hiding. Take one of those (`LaxLogic/Focusing/LJF.lean:3613`) as the probe, *not* one of the 54 `intro` sites. |
| 4 | `mem_sub` across the Mathlib island | 35 (+`Meta/Tactics`) | 93 | **236** | **Compile-time, not correctness.** Rewrite the 14 sites in `LaxLogic/PLL/Sequent/Craig.lean` (612 lines, the densest single file) and time `lake build LaxLogic.PLL.Sequent.Craig` against the same build before the change. Fourteen `tauto` invocations replacing fourteen `rcases` walks is the whole question; if that file gets slower, the step is refuted and the remaining 79 sites are not worth 178 lines. The campaign made compile time a first-class metric in round 1 and Round D spent 23 lines to buy 1 min 45 s — this is the same trade running the other way. |
| — | *(below the line)* S2 fusion | 35 | 211 | 211 *(est.)* | Not proposed. 35 files for 6 lines each, 149 sites needing an extra-lemma argument. |
| — | *(below the line)* idiom C, the `interp` dance | 5 | 39 | ~78 *(est.)* | Not proposed before steps 1–4. Its watched failure, when taken: write the macro and apply it at `LJF/ORows.lean`'s first site — a macro containing `all_goals rename_i` followed by bullets has a *variable goal count*, and if the bullet structure does not survive the quotation, the design is refuted at that one site. |

**Total proposed: ~1,159 lines** across steps 1–4 (395 measured + ~110 est. +
~418 est. + 236 measured), against 37 lines of new code — six `Sub` lemma
statements twice over, and three macros. **Refused, with mechanisms: 272 lines**
(A-mixed), **zero lines** (the simp bundle), and the D and E populations.

## What was not measured

* No build was run, so no compile-time figure is quoted anywhere and step 4's
  watched failure is precisely the missing measurement.
* The savings for steps 2 and 3 are labelled estimates because they assume a
  one-line replacement fits. The supporting measurement: the zero-import blocks'
  first-line indentation is median 12 columns, maximum 28 (79 of 127 at ≤12), so
  the candidate-7 wrapping shortfall — which cost that step its point estimate —
  is unlikely to repeat here. That is a reason, not a guarantee.
* The `A-mixed` refusal is a judgement on 84 blocks classified by a token test,
  not by reading all 84. Twelve were read; all twelve had a genuine foreign leaf.
* The axiom question is live for every `tauto` introduced and is **not** answered
  here. `mem_ite_list` used `cases inst` rather than `by_cases` specifically to
  keep `Classical.choice` out of the pins; `tauto` has no such discipline. The
  170 existing `tauto` sites mean the three UI files already carry whatever
  `tauto` brings, so step 1 cannot make them worse — but steps 3 and 4 introduce
  it where it was not, and the ledger gate is what must say so.
