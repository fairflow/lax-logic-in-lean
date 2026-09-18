# Simplifying the proofs that go through — a tactic-extraction plan

2026-09-16. Written after the four-line merge, from a mechanical survey of
every proof body in `LaxLogic/`, `FRJ/` and `LJF/`: 2,618 proofs, 50,489 proof
lines. The evidence tables are in the session scratchpad (`proof-clusters.tsv`,
`prefixes.tsv`, `simpsets.tsv`, `families.tsv`, `subblocks.tsv`); the numbers
quoted below come from them.

The rule this plan obeys: **a simplification must not change what is proved.**
Every step is a refactor of a proof whose statement stays byte-identical, and
each step is finished only when the module builds and
`scripts/check-ledger.sh` reports no regression — the ledger names any
declaration that gained an axiom or a `sorryAx`, which is exactly the failure
mode a proof refactor can hide.

## Scoreboard

Every row is gated: `lake build` green and `scripts/check-ledger.sh` reporting
the new lemmas as additions and **zero regressions** — no declaration anywhere
in the estate gained an axiom, a `sorryAx` or a `native_decide` taint, and none
vanished.

| done | what | lines |
|---|---|--:|
| 2026-09-16 | `Enum.f_mem`; one `Clo` induction, not five | ~120 |
| 2026-09-16 | `FRJ/SoundCore.lean` + `SoundCoreV.lean`: fifteen join proofs → five | 1,003 |
| 2026-09-16 | `SaturateV` said 21 things twice | 291 |
| 2026-09-16 | LJF `fireA`; station factoring in the two fuel files | 1,077 |
| 2026-09-17 | `itp_step_mono`: fuel and budget monotonicity were one proof | 547 |
| 2026-09-17 | `tools/RCells.lean`: a 445-row table written out twice | 436 |
| 2026-09-17 | candidate 7: 238 guarded-membership sites → 96 | 399 |
| 2026-09-17 | `join_closed`: one lemma for 24 `preR_closed` join arms | 235 |
| 2026-09-17 | candidate 8: the LJF weakening triple | 201 |
| 2026-09-17 | `tagConeP_core`: `tag_cone` 165 → 82 lines in each of three files | 175 |
| 2026-09-17 | the `FRJ/Gbu` W-copy hoist: seven W copies, 1,110 → 814 | 296 |

**Refused, each with a written reason and, since 2026-09-17, a designed watched
failure**: the G4/G4H/G4P triplication (eliminations cannot be abstracted over
a record, and the duplication is load-bearing for a published separation); the
LJF `aSound` triple (a duplicated recursion needs its termination argument);
station factoring in `OCore` (a recursive call under a lambda loses the
call-site variables `ljf_dec_sound`'s `assumption` entries read); the
`LaxND` congruence split (the abstraction stops something reducing that the
concrete form reduced by iota, and the repair would have to cross a
`Type`-valued index); and `gbuInv14`'s case split (an elimination again — the
V and W irregular families have different constructor sets, so only the arm
BODIES were hoisted, not the `cases`).

**The one sentence worth carrying forward**: ask what is *doubled*, not how
similar the text is — and if the doubled thing is a **function**, it abstracts
for free; if it is an inductive family, a recursion, or a termination
argument, it does not.

## What the survey found

141 proof bodies are byte-identical to another modulo whitespace and comments
(2,757 lines). Fuzzy clusters at similarity ≥ 0.85 account for 9,720 duplicated
lines. The duplication is not evenly spread: it sits in five places, and four
of them are the *same construction proved three times* — once for each of a
family of calculi that were developed in sequence.

| # | duplication | lines | shape of the fix |
|---|---|--:|---|
| 1 | `FRJ/Sound.lean` ↔ `SoundV.lean` ↔ `SoundW.lean` | 1,906 | one lemma over an abstract join, instantiated three times |
| 2 | `LJF/OCore.aSound` ↔ `OFuelSound.aSoundF` ↔ `OFuelPSound.aSoundP` | ~1,900 | parameterise over the interpretation; merge the 0.97 pair first |
| 3 | `G4UITrunc.itp_fuel_mono` ↔ `itp_budget_mono` | ~551 | one lemma over the step relation |
| 4 | `FRJ/Saturate.lean` ↔ `SaturateV.lean` | 825 | hoist the 21 shared declarations into the base module |
| 5 | G4 / G4H / G4P triplication (`inv`, `identity_mpt`, `impR_inv`, `weaken`, `toSC`) | 886 | a structure over the three calculi |
| 6 | list-membership bookkeeping, repo-wide | ≥1,500 | a `mem_bash`-style tactic + ~6 named lemmas |
| 7 | `simp only / split at / cases` in the three UI interpolation files | ~700 | characterisation lemmas, or one tactic |
| 8 | the LJF weakening-argument triple, 84 identical sites | ~700 | one packaging lemma |
| 9 | the 12-case `LaxND` congruence split, 13 proofs | ~400 | `LaxND.mapCtx`, or a tactic leaving `iden`/`laxIntro` |
| 10 | the `enumOf`/cover preamble in `FRJ/Gbu` | ~540 | a `coverOf` lemma |

Two findings are as useful as the candidates. First, the survey rejects the
obvious targets: the `nil`/`cons` and `zero`/`succ` splits (174 and 87 sites)
are generic inductions with unrelated bodies, and the `revert`-then-`induct`
opening (82 sites) is already as short as it can be. Second, explicit `simp`
lemma lists are a weak signal — only 25 lists of ≥ 3 lemmas recur at ≥ 3
sites — while five project-local definitions dominate those lists
(`Form.size` 93 sites, `gHat` 78, `ConstraintModel.force` 77,
`PLLFormula.weight` 75, `pGuard` 58). Marking those `@[simp]` (or giving each a
small named equation set) is a bigger lever than any simp-set extraction.

## Order of work, and why

The order is by *risk*, not by size: the cheapest-to-verify refactors first, so
that the ledger gate and the build loop are proved out on easy cases before
they are trusted on `aSound`.

**Stage A — lemma extraction inside one module.** Candidates 8, 10, 9.
Each is a packaging lemma next to its uses, no cross-module movement, no
statement changes. Success criterion: the module rebuilds, the ledger shows the
same axioms for every declaration in it, and the line count falls.

**Stage B — hoisting within a family.** Candidate 4 (`Saturate` ↔
`SaturateV`): `SaturateV` already imports `Saturate` and declares in `FRJ.V`,
so the 21 shared declarations move down, not sideways. This is the test case
for "does the ledger notice a hoist?" — it must show the declarations moving
module, and nothing else.

**Stage C — abstraction over a family.** Candidates 1, 5, 3. Here a proof is
stated once over an abstract parameter and instantiated. The constraint that
decides the design: the three `joinAtP` proofs never mention their calculus
except in the statement, so the abstraction takes the premodel equations as
**explicit hypotheses** rather than relying on `rfl` — the three
`FRJr/FRJVr/FRJWr.joinAtP` definitions are not definitionally equal.

**Stage D — tactics.** Candidates 7 and 6, in that order. 7 is the highest
confidence tactic in the repo (232 token-identical sites in exactly three
files); 6 is the largest but saves two lines in four, because the shapes match
while the leaf terms differ — the honest form is a `solve_by_elim`-backed
tactic that is *slower* than the explicit terms it replaces, so it is adopted
only where the explicit term is longer than three lines.

**Stage E — candidate 2**, last, alone. It is 1,900 lines of
`termination_by`/`decreasing_by` mutual recursion; the 0.88 pair genuinely
diverges. Merge the 0.97 pair (`OCore` ↔ `OFuelSound`) or nothing.

## Progress

**Stage A, done 2026-09-16.**

* `Enum.f_mem` (`FRJ/Minimal.lean`). Every proof that takes an `enumOf` needs
  "every value of the enumeration is a member", and all 25 sites wrote the same
  term out by hand. 25 sites rewritten, `FRJ/{Saturate,SaturateV}.lean` and
  `FRJ/Gbu/{Circ,DB,W/CircDB,W/Corner,W/DB}.lean`.
* **One induction over `Clo`, not five.** `clo_trans` (Cl6) is the general
  transport; `clo_mono` (Cl4) and the four `clo_*_cons` lemmas of
  `FRJ/Gbu/Base.lean` each repeated its five-case induction, differing only in
  what they do with a base member. All five now supply that map and call
  `clo_trans`, which is reordered to come first in `FRJ/Basic.lean`.

Verified: `lake build FRJGbu FRJ` 8626 jobs, `lake build` 8746 jobs, and the
ledger gate reports **one addition and no axiom change anywhere** —

```
ledger: 1 addition(s)/improvement(s)
  NEW         FRJ.Enum.f_mem  (FRJ.Minimal)
gate exit 2
```

which is the evidence the refactor changed no proof's content.

**Stage C, the FRJ soundness triple, designed.** The three `join*_case`
families are not the same lemma eight times: five (`joinAtP`, `joinAtF`,
`joinOrP`, `joinOrF`, `joinCircP`) differ across the three calculi only in type
names, while `joinAt`/`joinOr` differ by V/W's `kept` zone and `joinCirc` is
three genuinely different proofs. So the target is the five, all three
calculi — 2,523 duplicated lines down to about 1,395.

The design constraint, and it is the whole difficulty: **the abstraction cannot
quantify over the derivation `d`.** The proofs do not use `preR d` through an
interface, they use it through *reduction* — `cases w` on inhabitants of
`(preR d).W`, `none` fed where a world is expected, `join_force_comp` whose
statement mentions `PreModel.join` syntactically. A record field
`preR (joinAtP …) = PreModel.join …` is a propositional equation between
structures whose first field is a `Type`, and every such step would need a
`cast`. The escape is to state the core lemma directly about the
`PreModel.join` term, with six ordinary hypotheses in place of the definitional
facts (`preR_root_lbl`, `wfR`, `wfI`, `lhs_clo_of_steps`, and the two
closedness proofs); each wrapper then discharges the unfolding by `rfl`,
because `preR (FRJr.joinAtP …)` *is* that term.

The risk is exactly that `rfl`: it asks the elaborator to unify an
18-field `PreModel.join` literal against the `whnf` of `preR (…)`. **One
wrapper is compiled before the other fourteen are written** — that build
decides the design.

**Stage C, done 2026-09-16.** The `rfl` holds. It was tested first in
isolation, as a one-line probe (`preR (FRJr.joinAtP …) = PreModel.join … :=
rfl`), before any core lemma was written; then `joinAtP` alone, all the way
through a wrapper, before the other four were touched.

`FRJ/SoundCore.lean` now holds two pre-model constructions — `joinPModel` for a
promise join, `joinFModel` for a fallible one, the context being a parameter —
and five calculus-free lemmas: `joinAtP_core`, `joinOrP_core`, `joinAtF_core`,
`joinOrF_core`, `joinCircP_core`. It also holds the 308 lines of context and
forcing lemmas that were the first third of `FRJ/Sound.lean` and mention no
calculus at all.

Each of the fifteen proofs (five cases × `FRJr`, `FRJVr`, `FRJWr`) is now a
twelve-line wrapper. The statements of `join*_case` are untouched, in all three
files.

| | before | after |
|---|--:|--:|
| `FRJ/Sound.lean` | 1,921 | 1,079 |
| `FRJ/SoundV.lean` | 1,948 | 1,272 |
| `FRJ/SoundW.lean` | 1,963 | 1,287 |
| `FRJ/SoundCore.lean` | — | 1,191 |
| total | 5,832 | 4,829 |

Verified: `lake build FRJ FRJGbu` green, and the ledger gate reports the five
new core lemmas and the 308 moved helpers as additions and MOVES, with no axiom
change anywhere.

**The two cases V and W share, done the same day.** `joinAt` and `joinOr` are
not shared by all three: both carry the `kept` zone and a `KeptChain`, which
`FRJr` has no analogue of, so `FRJ/Sound.lean`'s versions are a different proof
and stay. Between `FRJVr` and `FRJWr` they are rename-only (`stab`/`th` against
`Ξs`/`Θs`), so they moved into `FRJ/SoundCoreV.lean` — a second core module,
because they speak of `KeptChain`, `RefAt` and `joinCtxAtVBase`, which arrive
with `FRJ.RefAt` and `FRJ.CalculusV`, modules `FRJ/Sound.lean` neither imports
nor should have to. Four proofs of 167 and 146 lines became four wrappers of
twelve: `SoundV` 1,272 → 984, `SoundW` 1,287 → 999, against 383 new lines of
core.

Two mechanical traps, both caught by the compiler and worth naming because they
will recur in any rename-driven merge: a blanket `stab → Ξs` rewrite also
rewrote **named arguments** (`stab_mem_baseAtV (th := th)` became
`(Θs := Θs)`, which is not that lemma's parameter), and the hypothesis list I
copied included an `hC` that `joinAt` never had — its `hC` is a variable the
body introduces with `intro C hC`.

Two hypotheses had to be named explicitly, and they are the interesting
residue: `hwfR` is `wfR d` composed with the context equation `hΓ`, and `hlhs`
is `lhs_clo_of_steps` applied to the single `Step.join*` of the rule. Both were
definitional in the original and are ordinary arguments now — which is what
"abstract over the calculus" costs here, and it is six lines, not a design.

**A gate improvement fell out of this.** Hoisting 308 declarations into a new
module made every one of them vanish from `FRJ.Sound` and appear in
`FRJ.SoundCore`, which the gate called a regression (a vanished declaration is
the shape of a lost proof). It now distinguishes a MOVE — same name, same
axioms, different module — from a loss, and a move whose axioms *changed* is
still a regression, reported as `MOVED*`. Both cases are in
`scripts/test-ledger-diff.py`, and both were watched failing.

**`tag_cone`, the fourth member of the mutual block, done 2026-09-17.**
`tag_cone` was proved three times at 165 lines and pairwise similarity
0.984–0.993. The distribution inside it is what decides the design: eight of
its eleven arms are one to six lines — a barren root, or a tag that cannot be
`chain` — and **`joinAtP`, `joinOrP` and `joinCircP` are 133 of the 165**
(45, 45, 43). Two similarity claims were checked by diff before anything was
written, not assumed: R↔V differ only in the `kept` zone and only inside the
SMALL arms, so the three big arms are identical across R and V modulo `FRJVr`;
V↔W is rename-only (`stab`/`th` → `Ξs`/`Θs`).

One lemma, `tagConeP_core` (`FRJ/SoundCore.lean`, 74 lines), states the shared
part about the abstract `joinPModel elems hcomplete Ψ Ms Ns`, taking as
ordinary parameters what the arms read off the derivation: the covering
certificate `hcov`, the per-component pledge `hall`, the `joinCtx?P_clo`
supplier, `hΓ`, and the two recursive calls `lemma39R (dps i)` and
`tag_cone (dps i)` as functions. The recursion is NOT moved: each file keeps
its eleven-arm skeleton and calls out, as `SoundCore` and `join_closed` do.
`joinCircP_core` was already carrying `ihP` and `ihT` with literally the
`tag_cone` statement, over abstract `Ns`, and was most of the answer.

**The probe, run alone before any core lemma was written.** The one genuine
risk was whether `hu : (modR d).Rm (modR d).root u` still ascribes to a
`PreModel.join` term when `Ms`/`Ns` are abstract — the step the concrete text
performs at `FRJ/Sound.lean:749`. A one-line `:= hu` example against the
abstract `joinPModel`, compiled alone, **passed**, so no wrapper keeps an
ascription and the design runs at full size. `joinAtP` was then taken all the
way through one wrapper, and compiled, before the other five were touched —
the same discipline as the `rfl` probe above; that build is also what showed
the mutual block accepts `fun i => tag_cone (dps i)` as an argument, which
`lemma39R` was already relying on one lemma over.

| | before | after |
|---|--:|--:|
| `FRJ/Sound.lean` | 1,079 | 996 |
| `FRJ/SoundV.lean` | 984 | 901 |
| `FRJ/SoundW.lean` | 999 | 916 |
| `FRJ/SoundCore.lean` | 1,200 | 1,274 |
| total | 4,262 | 4,087 |

175 lines, `tag_cone` itself 165 → 82 in each of the three files. Verified:
`lake build` green (8,748 jobs), and the gate reports

```
ledger: 1 addition(s)/improvement(s) — regenerate `docs/status-ledger.jsonl`
  NEW         FRJ.tagConeP_core  (FRJ.SoundCore)
```

with `FRJ.tag_cone`, `FRJ.V.tag_cone` and `FRJ.W.tag_cone` unchanged at
`[propext, Quot.sound]`.

**What was NOT done, and the reason is the estimate.** Each `joinAtP`/
`joinOrP` wrapper still opens its own tag by hand — `rcases htag`, `rcases ht`,
`injection`, `subst`, nine lines, six times. A second lemma taking `htag` and
`ht` and returning `Covers Γ' (Ds 0) Z ∧ hall` would take another 42 lines out
for 14 of its own. It is a separate fact about the tag algebra, not about the
model, and it is left for whoever next opens these files.

## Stage B, done 2026-09-16: `SaturateV` said 21 things twice

The survey called `FRJ/Saturate.lean` ↔ `FRJ/SaturateV.lean` 825 duplicated
lines. Examining it declaration by declaration gives a smaller and much more
interesting number.

The two files share **72** declaration names, 55 of them byte-identical — but
byte-identical text is not the same theorem. Five base structures (`IrrWit`,
`MRWit`, `FRWit`, `OWit`, `PledgeFam`) differ in exactly one field, `FRJr`
against `FRJVr`, and **34 of the 55 identical declarations mention one of
them**, so they are genuinely different statements that happen to be spelled
alike. Deleting those would silently retype the V layer to the paper calculus.

**21 are redundant outright**: byte-identical, and nothing in their statements
mentions a doubled name. Since `FRJ.V` is nested inside `FRJ`, every use in the
V file resolves to the original once the copy is gone; no site anywhere refers
to them as `FRJ.V.…`, and no axiom pin names one. Deleted — 291 lines — with a
note in place listing what was removed and why.

The lesson for the rest of this plan: **similarity measured on text overstates
what can be shared.** The number that matters is how many of the "identical"
declarations mention something that is itself doubled — here 34 of 55, and that
is what the 825 collapses to 291 against.

## Refused: the LJF `aSound` triple (candidate 2, ~1,900 lines)

Examined 2026-09-16 and **not attempted as stated**, for a third reason, which
completes the pattern.

`aSound` (`LJF/OCore.lean:2731`), `aSoundF` (`LJF/OFuelSound.lean:294`) and
`aSoundP` (`LJF/OFuelPSound.lean:340`) prove the same statement over
`interp`, `interpF` and `interpP`; there is no type renaming at all, and
normalising the fuel away leaves `aSound` and `aSoundF` differing in 110 of
1,290 lines. But:

* **What is duplicated is the recursion itself.** All three are two-member
  `mutual` blocks with calls both ways, so `aSound` cannot move without
  `eSound`; and their termination arguments are not one function of different
  arguments — `2 * sum3 todo + sum3 done + 3 ^ wNeg G` discharged by a
  fifty-alternative tactic farm, against `f` discharged by `omega`. An
  abstraction must carry the decrease obligations as parameters, roughly forty
  of them, and about 200 clause and row equations besides: more lines supplied
  than removed.
* **The proof depends on iota-reduction of the interpolant's rows.** After
  `cases X`, fourteen arms must reduce for `exact nBotElim _ …` to typecheck.
  Abstract the row and every one becomes an explicit hypothesis per goal shape
  — the "stuck context function" that sank the G4 attempt, reached from the
  introduction side instead of the elimination side.
* **The 110 divergent lines sit in exactly the arm the abstraction must open**
  (`interp` puts the ◯-implication's left component at `rest`, `interpF` at
  `done`), so the 0.97 similarity gives back what it offers. And `aSoundP` is
  not a near-copy: 44 `atkPark` sites against none, `atkDyk` gone, because
  retention at the full station makes the residual simulator unnecessary —
  which is the property `OFuelP` exists to exhibit.

Three cheaper moves survive, in ascending risk, and are the live plan for
`LJF/`:

1. `fireASoundF` and `fireASoundP` are byte-identical and already abstract over
   the interpolant. One `fireA` in `OCore`, with `fireASound` as its
   instance — about 50 lines, and the statements are already the same.
2. `atkPark` generalises `atkCimp`, and the file already carries the proof
   (`atkPark … = atkCimp … := rfl`, `OFuelPSound.lean:77`). Hoist it — about
   25 lines, and it records the identity that file was written to record.
### Station factoring: done for the two fuel files, refused for `OCore`

Done 2026-09-16/17. `OFuelSound` and `OFuelPSound` each had eleven station
clauses running the same case split — six identical at 89 and 114 lines, three
at 42 and 67 — differing only in which goal they proved. Each file now has two
lemmas (`stationCircF`/`stationUpF`, `stationCircP`/`stationUpP`) and nine
one-line call sites. **1,077 lines out of the two files**, no statement changed,
`lake build LJF` green.

Three things it settled, and the third is the boundary:

* **A fuel-recursive call can be passed as a parameter.** The sites hand the
  lemma `fun todo rest H => aSoundF p f todo rest H` — a recursive call under a
  lambda with variable arguments. Lean accepts it because the measure is the
  fuel, which does not mention those arguments: the decrease goal is `f < f+1`.
* **The lemma must be stated about the literal row term**, the `match X, hXr
  with …` copied from `interpF` with the goal abstracted, so `cases X` still
  reduces the fourteen arms.
* **The same move fails in `OCore`, and the failure is the measure.** There the
  termination argument is the syntactic complexity of the arguments themselves,
  discharged by the fifty-alternative `ljf_dec_sound` farm whose entries read
  call-site variables with `assumption` (hygiene deliberately off). Put the
  recursive call under a lambda and those variables are no longer at the call
  site: `Tactic 'assumption' failed`, six times over. Tried, reverted, recorded
  — the fuel files are shareable and the fuel-free one is not, for a reason that
  belongs to `decreasing_by`, not to the proof.

3. **Factor the station rows within each file.** The eleven station blocks of
   one `aSound` differ only in the goal term — the four non-◯ blocks are 39
   lines each and differ pairwise in four lines. A `stationBranches` lemma per
   file, stated about the *literal* `(splits done).attach.map (fun … => match
   X, hXr with …)` term so that `cases X` still iota-reduces, takes ≥300 lines
   out of each body: 900–1,000 across the three, at a fraction of the risk,
   with `interp` never abstracted and no `termination_by` touched. Compile one
   block first, as the FRJ work compiled one `rfl` first.

## Stage C, candidate 3, done 2026-09-17: fuel and budget monotonicity were one proof

*This closes Stage C: candidate 1 done, candidate 5 refused with reasons,
candidate 3 here. The survey's estimate for it was ~551 lines; the actual
saving is 547, which is the first candidate whose size estimate held.*

`LaxLogic/PLL/UI/G4UITrunc.lean` proved

    itp_fuel_mono   : G4c [itpE p S (fuel+1) b Γ] (itpE p S fuel b Γ)  ∧  …
    itp_budget_mono : G4c [itpE p S fuel (b+1) Γ] (itpE p S fuel b Γ)  ∧  …

by the same 574-line induction twice, at lines 1331–1903 and 1915–2488. The
two bodies differ in which of the two numerals carries the `+ 1`; everything
else — the same eleven splits, the same `itpEcls`/`itpAgoal`/`itpAenv` walk,
the same `imp_mono`/`box_mono` plumbing — is common.

The abstraction replaces the two numerals by two step *functions*:

    theorem itp_step_mono (p : String) (S : Finset PLLFormula)
        (sf sb : Nat → Nat) (hsf : ∀ f, sf (f + 1) = sf f + 1)
        (hsb : ∀ b, sb (b + 1) = sb b + 1) : ∀ (fuel : Nat),
        (∀ b Γ, G4c [itpE p S (sf fuel) (sb b) Γ] (itpE p S fuel b Γ)) ∧
        (∀ b Γ C, G4c [itpA p S fuel b Γ C] (itpA p S (sf fuel) (sb b) Γ C))

and the two theorems become five-line instances, at `sf := (· + 1), sb := id`
and `sf := id, sb := (· + 1)`, both equations `fun _ => rfl`.

**What the two hypotheses buy, precisely.** A concrete `b + 1` in the source
position reduces: `itpAgoal … (b'+1) … (somehow D)` iota-reduces to its
`succ` branch, and the tables unfold by `itpE_succ`. An abstract `sb (b'+1)`
does not, and that is the *only* thing the abstraction breaks. `hsb` restores
it exactly where the proof splits on the budget — six `rw [hsb]` at the six
`cases b with … | succ b' =>` branches, and eight `hsb b' ▸ ih… (b' + 1) …`
transports where an induction hypothesis is applied at the stepped budget —
and `hsf` at the two `rw [itpE_succ …]` / `rw [itpA_succ …]` unfoldings. The
final `itpAfull_map` argument, which in the fuel proof passes the budget
through unchanged, becomes `fun b' hb => ⟨sb b', by rw [hb, hsb], ihE b' Γ⟩`.
Nothing else in 582 lines changed.

**Why this one worked where three others were refused.** The refusals
(`aSound`, `OCore` station factoring, G4/G4H/G4P) all founder on something
*per-copy*: a separate inductive family, a separate recursion, a separate
termination argument. Here the two copies live in one file, share every
definition and every recursion, and the only doubled object is the numeral
step — which is a function, and a function is the one kind of thing that
abstracts without cost. That is the test worth carrying forward: ask what is
doubled, not how similar the text is.

**The probe, run before writing anything** (the shape the last
`itpAfull_map` argument has to take, with `sb` abstract):

```lean
example (p : String) (S : Finset PLLFormula) (sb : Nat → Nat)
    (hsb : ∀ b, sb (b + 1) = sb b + 1) (f₁ f₂ b : Nat) (Γ : List PLLFormula)
    (ihE : ∀ b', G4c [itpE p S f₂ (sb b') Γ] (itpE p S f₁ b' Γ)) :
    ∀ b₁', b = b₁' + 1 → ∃ b₂', sb b = b₂' + 1 ∧
      G4c [itpE p S f₂ b₂' Γ] (itpE p S f₁ b₁' Γ) :=
  fun b' hb => ⟨sb b', by rw [hb, hsb], ihE b'⟩
```

Verified: the file is 4,036 lines down to 3,489 — **547 lines removed**, one
582-line proof and two five-line instances in place of 1,147 lines of proof —
`lake build` green, and the gate reports the addition of `itp_step_mono` with
no axiom change to `itp_fuel_mono` or `itp_budget_mono`.

## Refused: the G4 / G4H / G4P triplication (candidate 5, 886 lines)

Examined 2026-09-16 and **not attempted**. The five families (`inv`,
`identity_mpt`, `impR_inv`, `weaken`, `toSC`) are rename-only between `G4` and
`G4p` and genuinely different for `G4h`, and the reason they cannot be shared is
the mirror image of what made `SoundCore` work.

`SoundCore` succeeded because the proofs reduced a constructor applied to an
object, so the lemma could be restated about the object. Here four of the five
families are **eliminations** — they open with `induction d` — and an
elimination cannot be abstracted over a record of operations: a record supplies
introduction forms, and the only field that would support the induction is the
recursor, a different dependent type for each of the three constructor sets.
There is no underlying object to restate the lemma about, because here the
derivation *is* the object. A single parameterised inductive type-checks on
paper and buys nothing: every goal then carries a stuck context function, and
the diverging lines are exactly the permutation arithmetic that re-exposes a
formula past `[X]`, past `[F, X]`, or past nothing — the same three proofs,
relocated.

And the duplication is load-bearing, which matters more than the line count:

* `G4` is the object of a published separation (`G4Gap.sc_but_not_G4`,
  `contraction_not_admissible`), machine-checked *about Iemhoff's Figure 2.3 as
  transcribed*. Make `G4` an instance of a parameterised family and a reader
  checking fidelity to the paper must check the instantiation too.
* `G4ipComplete.completeness_isIPL` is the rule-8 fragment result, and its point
  is to locate the defect in exactly `laxL`, `impLLax`, `impLLaxLax` — the three
  constructors an abstraction would blur.
* `G4h.inv` is height-**preserving**; `G4.inv` has no height. They are different
  theorems, not two copies of one.

One bounded exception exists and is left for Matthew: `identity_mpt` never
eliminates a derivation (it inducts on `Nat` and matches on the formula), so it
would fit a record of the 17 introduction rules — about 140 lines, with the same
"compile one instantiation first" discipline. Small, and it touches the ladder
documents; his call, not mine.

## Stage D, candidate 7, designed 2026-09-17: the guarded-membership census

The `simp only … / split at hin / next … =>` idiom in the three
uniform-interpolation files was surveyed as "~700 lines". A census of all
**238** sites gives a sharper picture. Every site is *consuming* a membership
hypothesis; they sit in eight proofs only (`itp_step_mono`, `itp_pfree`,
`itp_sound`, `itp_congr` in `G4UITrunc.lean`, three in `G4UI.lean`, one in
`G4UIStab.lean`), forming **114 maximal chains over 2,425 lines, of which 961
are scaffolding**. The *producing* idiom is separate — 82 sites of
`simp only` / `rw [if_neg h₁, if_pos h₂]` / `exact .head _`, ~214 lines — and
never uses `split`.

| group | guard shape | chains | scaffold lines |
|---|---|--:|--:|
| G1 | one guard, `[e]`/`[]`, one live leaf | 32 | 138 |
| G2 | `if c₁ then [] else if c₂ then [e] else []` | 32 | 263 |
| G3 | 2–5 guards, **two** live leaves | 22 | 263 |
| G4 | cascade over `… ++ Γ.filterMap …` | 8 | 123 |
| G5 | cascade containing `match b with \| 0 \| b'+1` | 12 | 146 |
| G6 | Option-valued (`if c then none else some e`) | 8 | 28 |

Two facts decide the design. **Every dead branch in the tables is literally
`[]`** (`itpEcls`, `itpAgoal`, `itpAenv`), except the inner pair of G3. And
**80 of about 160 live leaves bind their guard** and feed it straight to the
producing `rw [if_neg h₁, if_pos h₂]`, so the two halves are coupled: whatever
replaces the split must hand the guard proofs back *in the unnormalised form
`if_pos`/`if_neg` accept*.

So the extraction is one iff-lemma used as a simp lemma, not a family of
bespoke `mem_guard` lemmas — neither `List.mem_ite_nil_left` nor an iff form
exists in Mathlib or Batteries:

```lean
theorem mem_ite_list {α : Type} {c : Prop} [inst : Decidable c]
    {l₁ l₂ : List α} {x : α} :
    (x ∈ if c then l₁ else l₂) ↔ (c ∧ x ∈ l₁) ∨ (¬c ∧ x ∈ l₂) := by
  cases inst with | isTrue h => simp [h] | isFalse h => simp [h]
```

`cases inst`, not `by_cases`, so that `Classical.choice` stays out of the
axiom pins. Used with `List.not_mem_nil`, `List.mem_singleton`,
`List.mem_cons`, `List.mem_append`, `and_false`, `false_or`, `or_false`, one
`simp only` collapses a cascade of **any depth**, because the `[]` branches die
under `and_false`/`false_or`. The set is bundled as a `mem_tbl` macro so the
name list is written once rather than 114 times, and so it serves the
producing side too.

**The constraint that shapes the simp-set is over-reduction, not
under-reduction.** A guard such as `¬(χ ∈ Γ ∨ χ ∉ S)` must arrive at the
producing `rw [if_neg hg]` *unchanged*, so `not_or`, `not_not`, `not_and`,
`ne_eq` and `Decidable` normalisation must stay out of the set. The one thing
that provably does not collapse is `match b with | 0 => [] | b'+1 => [e]`:
simp has no lemma for a matcher on `b`, so G5 keeps its `cases b` — and that
is the designed watched failure.

Against the three refusals: (a) nothing is abstracted over a record — the
only eliminations in the eight proofs are `induction fuel` and `cases F`/
`cases C`, kept verbatim; (b) `grep` finds no `termination_by`/`decreasing_by`
anywhere in the three files; (c) nothing is passed under a lambda. The lemma
rewrites a *proposition*, forward, with every row term left concrete, which is
why none of the three mechanisms has purchase.

Estimate to be held to: **500 lines**, range 420–700. Order: G2 (the shape the
probe tests), then G1, G4, G3, then the producing side; G5 and G6 last or not
at all. The likeliest reason it comes in under is G3: its collapsed `rcases`
pattern carries four to six guard names plus two `rfl`s, and at the
indentation those sites already sit at (columns 26–34) it wraps to three lines
rather than one.

## Stage D, candidate 7, done 2026-09-17: 238 guarded-membership sites became 96

The design above survived contact. Both probes were run first, and both said
what they were designed to say. Probe 1 — `mem_tbl` at a real G2 site, guards
fed straight back to `rw [if_neg h1, if_pos h2]` — **passed**. Probe 2, the
watched failure, **failed**, one step earlier than predicted: `mem_tbl at hφ`
itself reports `simp made no progress` on `match b with | 0 => [] | b'+1 => …`,
so the budget group G5 keeps its `cases b` and the boundary of the design is
exactly where the census said it was.

`mem_ite_list`, `ite_none_eq_some` and the `mem_tbl` macro live in
`LaxLogic/PLL/UI/G4UI.lean`, the earliest of the three files, so all three see
them (37 lines).

**Result: 238 `split at` sites down to 96, 5,802 lines down to 5,403** — a net
399, or 436 lines of scaffolding against the 37 the lemmas cost.

| file | before | after | `split at` |
|---|--:|--:|--:|
| `G4UITrunc.lean` | 3,489 | 3,126 | 202 → 82 |
| `G4UI.lean` | 1,856 | 1,846 | 27 → 13 |
| `G4UIStab.lean` | 457 | 431 | 9 → 1 |

The rewrite was mechanical, in four passes, each compiled before the next: the
fixed two-guard shape (16 chains), then a general single-live-leaf cascade
parser of any depth (18, then 24 once unnamed guards were allowed to become
`_`), then the multi-live-leaf case, which emits one `rcases` with a nested
alternation pattern and `·` bullets —

```lean
mem_tbl at hin
rcases hin with ⟨hBΓ, hBS, ⟨hq, rfl⟩ | ⟨hq, hqp, rfl⟩⟩
· …
· …
```

— and finally the `Option`-valued rows, where `simp only [ite_none_eq_some] at
heq` + `obtain ⟨hg, rfl⟩ := heq` replaces `split`/`injection`/`subst` (8
sites). The parser composes with itself: each pass collapses inner cascades
into `mem_tbl`/`obtain` pairs, which the next pass reads as leaves and absorbs
into the enclosing cascade, so a three-deep nest ends as one `rcases`. Run to a
fixpoint.

**Against the 500-line estimate: 436 lines of scaffolding, inside the stated
420–700 range but under the point estimate**, and not for the reason predicted.
G3's `rcases` patterns did not wrap badly.

What is left is 96 sites, and the attempt to take the largest remaining group
**failed and was reverted**, which is the more useful result. The census had
counted 22 sites "written with `·` bullets rather than `next`" as a parser
limitation worth another ~60 lines. Extending the parser to read bullets
matched them, and the build then failed at nine sites with

```
Dependent elimination failed: Failed to solve equation
  (match C with
    | ◯a => [◯(interE p fuel (χ :: Γ) ↠ interA p fuel (χ :: Γ) C)]
    | x => []) = φ :: as✝
```

**The bullet form is not a style; it is a tell.** These `split`s are on a
*matcher* — `match C with …` — not on an `if`, which is exactly why they were
written with bullets in the first place: splitting a matcher produces goals
with no guard proposition to name, so there is nothing for `next h =>` to
bind. And a matcher is precisely what `mem_ite_list` does not reach. The
bullet group is the same boundary as G5, in disguise: **one `if`, one
collapse; one matcher, one `cases`.** Reverted in all three files; 96 is the
floor this design reaches, not a parser deficiency.

The one group that is still mechanically open is the **8 cascades whose live
leaf is a `List.mem_append` alternation**, which needs a second alternation
level in the pattern builder — worth perhaps 30 lines, and genuinely a parser
limitation rather than a boundary of the design.

## Done 2026-09-17: a 445-row table written out twice

`tools/RCFuel.lean` and `tools/RCellsGen.lean` each carried the classed
R-increment cells `(op, i, j, k)` — 445 rows, 446 byte-identical lines — as a
private root-level `def cells`. It is now `tools/RCells.lean`, importing
nothing so that neither generator drags the other's dependencies in, in
namespace `RCells` because eight other modules in this tree declare a
root-level `cells` of a different type. RCFuel 477 → 31 lines, RCellsGen
620 → 174; `tools.RCells` added to the `Tools` library glob, without which the
exe roots cannot see it (`lake` builds an exe root's imports only from declared
libraries).

The check that matters here is not the build. `.lake/build/bin/rcellsgen`
reproduces the committed `wip/rcells.lean` **byte-for-byte**, 2,247 lines — so
the generated content is provably unchanged, which a compile alone would not
show. This is data, not proof, and it is listed because it is the single
largest identical block in the repository.

An incidental finding: neither generator's declarations were in the ledger
before this. The campaign built every *library*; `lean_exe` roots that belong
to no library were outside the estate, which is the same gap `FRJO` fell
through. Nineteen declarations entered the record with this change, seventeen
of them pre-existing.

## Refused 2026-09-17: the `LaxND` congruence split (candidate 9, 300 lines)

Measured, not estimated: `LaxND` has twelve constructors and **fourteen**
proofs split on all twelve, **300 lines** across `NDCore.lean` (five),
`Terms.lean` (two), `Realisability.lean` (two), and one each in `SemUICtx`,
`CtxCompleteness`, `Judgmental`, `Hilbert`, `Obligation/PLLBridge`.

The proposed `LaxND.mapCtx` reaches **three** of the fourteen — `erased`,
`substND`, `translate`, the only ones whose shape is
`LaxND Γ φ → LaxND (Γ.map f) (f φ)` — so 54 lines, and it buys them at the
price the module was built to avoid. With `f` abstract, `.impIntro` yields
`LaxND (Γ.map f) (.ifThen (f φ) (f ψ))` where the goal is
`LaxND (Γ.map f) (f (.ifThen φ ψ))`. For the concrete `erase`/`substP`/`subC`
these are `rfl` by iota; for abstract `f` they need `hImp ▸`, an `Eq.rec` on a
`Type`-valued index — a real cast, and `NDCore.lean:230` already records the
superseded version of `erased` as having needed fifteen of them. Worse,
`conservativity` proves `p.erased.isIPLProof` by `induction p` with arms
`exact ih`, which typecheck *only* because `p.erased` iota-reduces per
constructor and `isIPLProof` matches on the constructor. Cast `erased` and
those arms stop reducing.

This is the fourth refusal, and the first whose mechanism is **(d)**: the
abstraction stops something reducing that the concrete form reduced by iota.
It is the same mechanism that `itp_step_mono` survived — there, one equation
per stepped variable restored the reduction at six sites; here the equation
would have to be carried through a `Type`-valued index, which no equation
can do.

The certificate is a designed watched failure, to be pasted at the end of
`LaxLogic/PLL/ND/NDCore.lean` inside `namespace PLLND`:

```lean
example (f : PLLFormula → PLLFormula)
    (hImp : ∀ φ ψ, f (.ifThen φ ψ) = .ifThen (f φ) (f ψ))
    {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (d : LaxND (f φ :: Γ.map f) (f ψ)) :
    (hImp φ ψ ▸ LaxND.impIntro d :
        LaxND (Γ.map f) (f (.ifThen φ ψ))).isIPLProof = d.isIPLProof := rfl
```

The `Eq.rec` is stuck on the opaque `hImp φ ψ`, the match cannot reduce, and
`rfl` fails. Only if it unexpectedly passes is `mapCtx` viable. The one live
sub-item, which is Matthew's call and not Stage A: making `f` a structure
whose field matches the connectives, so that commutation is iota again. That
redefines `erase`, `substP` and `subC` across three modules and touches a
published conservativity result.

## Stage A, candidate 8, DONE 2026-09-17: the LJF weakening triple, 201 lines

| file | before | after |
|---|--:|--:|
| `LJF/OCore.lean` | 4,116 | 4,041 |
| `LJF/OFuelSound.lean` | 1,171 | 1,111 |
| `LJF/OFuelPSound.lean` | 1,305 | 1,239 |

201 lines against the ~410 estimate, and **the shortfall is a correction to the
census, not a failure of the design.** Two counts were wrong:

* **Family B: 27 sites, not 53.** A census of all 115 blocks of that shape
  found only 27 that are the bare `Sub.cons _ h`. Of the rest, 36 are
  `Sub.cons _ (Sub.grow _)` and 16 are
  `Sub.cons _ (Sub.trans (Sub.grow _) hsub)` — the *compositions* the survey
  itself set aside as genuinely different. `(Sub.cons _ hsubD)` is not what
  they are.
* **Family A: 78 of 138 argument slots**, not 138 — 48 of 69 `hX` and 30 of 69
  `hrest`. The 21 remaining `hX` and 15 `hrest` route through `hsub`, where the
  inclusion in scope is `Sub (Y :: done) Γ'`, **one cons wider** than the
  lemmas' `Sub done Γ'`; bridging it needs `Sub.trans (Sub.grow _) hsub` at
  every site, which is generalisation rather than extraction and is no shorter.
  The other 18 `hrest` are the `rest := done` instantiation, with no
  `splits_sub` in them at all.

`rowHyp` and `rowSub` are in `LJF/OCore.lean` after `splits_sub`. **No
`assumption` failure occurred**: both lemmas return a `Prop` proof and swallow
nothing, so `D₁`/`D₂` stayed direct call-site arguments and `ljf_dec_sound`'s
farm still sees them. `lake build` green (8,748 jobs) and `lake build LJF`
green (3,102 jobs) — note the bare build does **not** cover `LJF`, which is
absent from `defaultTargets`. Gate: two additions, `LJFO.rowHyp` and
`LJFO.rowSub`, and zero regressions.

**A latent gate defect came out of this, and it is worth more than the 201
lines.** `scripts/check-ledger.sh` in its default mode could not run in a fresh
worktree at all: a checkout stamps every source newer than every cloned
`.olean`, the mtime proxy fires on all 579 modules, the script asks lake to
rebuild them, and `docs/ledger-modules.txt` carried **`Tools.Engines` beside
`tools.Engines`** — a duplicate minted by the case-insensitive filesystem and
invisible on macOS. `lake build Tools.Engines` reports `unknown target`, so the
run aborted at exit 3 with no ledger generated. The 2026-09-16 `Tools`/`tools`
repair fixed the lakefile and the imports and never reached the record. The
duplicate is now removed.

### The design, as written before the work



Two families, both about `Sub` (`LJF/OCore.lean:122`), **528 identical lines**
— not the ~700 the survey quoted, because 46 further blocks (303 lines) are
`Sub.cons`/`Sub.grow`/`Sub.trans` *compositions* and genuinely differ.

*Family B, and it needs no new code at all.* `Sub.cons` (`LJF/OCore.lean:132`)
is written out by hand, byte-for-byte its own proof body, at **53 sites over
252 lines** — `OCore` 13, `OFuelSound` 12, `OFuelPSound` 12,
`LaxLogic/Focusing/LJF.lean` 6, `O` 3, `OFuelPFam` 3, `OFuelMin` 2,
`OFuelPMin` 2. Each becomes `(Sub.cons _ hsubD)`. This is a pure inlining
reversal and is the half to do first.

*Family A, two lemmas.* Every call of `atkQimp`/`atkDyk`/`atkCimp`/`atkPark`
supplies `hx, hX, hrest` in one of two shapes — **69 sites over 276 lines**:

```lean
theorem rowHyp {A X : Neg} {rest done Γ' : List Neg}
    (hsubD : Sub done Γ') (hXr : (X, rest) ∈ splits done) : X ∈ A :: Γ' :=
  List.mem_cons_of_mem _ (hsubD _ (splits_mem hXr))

theorem rowSub {A X : Neg} {rest done Γ' : List Neg}
    (hsubD : Sub done Γ') (hXr : (X, rest) ∈ splits done) : Sub rest (A :: Γ') :=
  fun Z hZ => List.mem_cons_of_mem _ (hsubD _ (splits_sub hXr Z hZ))
```

**The constraint that dictates two bare lemmas rather than one wrapper**:
`ljf_dec_sound` (`LJF/OCore.lean:2233`, `set_option hygiene false`, 37
`by assumption` entries) reads call-site variables, so the derivations `D₁`,
`D₂` must remain direct arguments at the call site. A wrapper that swallowed
them is the mechanism that reverted the `OCore` station factoring. Mechanism
(d) is inert here: `Sub` and `_ ∈ _` are `Prop`s, so proof irrelevance makes
the replacement invisible to reduction.

Estimate: **~410 lines** (range 350–480). Order: Family B in
`LJF/OFuelSound.lean` first (12 sites, fuel measure, no `ljf_dec_sound`
farm), then the rest of B, then A.

## Designed 2026-09-17: the two remaining FRJ triplications

Both are `FRJ`/`FRJV`/`FRJW` copies of one proof, and both were surveyed,
measured and probe-designed without a build. **One fact settles the two
mechanisms that killed the `OCore` station factoring**: `termination_by` and
`decreasing_by` do not occur in any of
`FRJ/{Sound,SoundV,SoundW,Extract,ExtractV,ExtractW}.lean`. There is no measure
and no `assumption` farm, both recursions are equation-compiler recursions over
the mutual inductive `FRJr`/`FRJi`, and **passing a recursive call under a
lambda already compiles in both blocks today** — `FRJ/Sound.lean:712` passes
`(fun i => tag_cone (dps i))` and `FRJ/Extract.lean:526` passes
`(fun i => preR (dps i))` inside `Sum.elim`. Neither design moves a recursion.

### `preR_closed` — DONE 2026-09-17, 235 lines

The probe was the lemma itself, and it compiled first time, as did the first
arm rewritten by hand. All **24 join arms** (eight per file, three files) are
now instances:

```lean
  | _, _, _, @FRJr.joinAtP … => by
      refine join_closed (fun x => ?_) (fun x X hX => ?_)
      · cases x with
        | inl ji => exact preI_closed (prem ji.1) ji.2
        | inr i => exact preR_closed (dps i)
      · cases x with
        | inl ji =>
            obtain ⟨s', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
            exact clo_trans (fun Y hY => .base ((hlbl Y).mpr hY))
              (lhs_clo_of_steps
                ((occI_steps hocc).tail
                  ⟨_, Step.joinAtP (F := F) (Δs := Δs) ji.1 hJ1 (CtxEq.refl _)⟩) X hX)
        | inr i =>
            exact clo_trans (fun Y hY => .base ((preR_root_lbl (dps i) Y).mpr hY))
              (joinCtxAtP_clo i X hX)
```

| file | before | after |
|---|--:|--:|
| `FRJ/Extract.lean` | 941 | 880 |
| `FRJ/ExtractV.lean` | 509 | 422 |
| `FRJ/ExtractW.lean` | 503 | 416 |

235 lines, against an estimate of 265 — the shortfall is exactly the predicted
one: the `preI_spec`/`occI_steps`/`Step.join*` prelude stays in every arm,
because the `Step` constructor differs per arm *and* per calculus. That
prelude is the only calculus-specific content left in any of the 24 arms, and
naming it as a hypothesis is what the design was for.

The V/W measurement that justified it, checked independently: **all 13
`preR_closed` arms are byte-identical between V and W**, and 10 of the 13
between R and V.

### The original estimate and design

`FRJ/Extract.lean:657`, `ExtractV.lean:282`, `ExtractW.lean:277`, 189–190 lines
each, 41% of them mentioning a doubled name. The decisive measurement is
sharper than the similarity score: **the V and W bodies are byte-identical** —
`diff` touches only the statement line and the nine constructor-pattern
headers. All 24 join arms are instances of *one* lemma over the raw
`PreModel.join`, with no `Idx`/`Sum` scaffolding and no new module:

```lean
theorem join_closed {ι : Type} [DecidableEq ι] {ιe : List ι} {ιc : ∀ i, i ∈ ιe}
    {Γ₀ : List Form} {Ms : ι → PreModel} {iP : ι → Bool}
    (hM : ∀ i, ClosedLbl (Ms i))
    (hroot : ∀ i, ∀ X ∈ Γ₀, Clo ((Ms i).lbl (Ms i).root) X) :
    ClosedLbl (PreModel.join ιe ιc Γ₀ Ms iP)
```

Mechanism (d) — does something stop reducing? — **already has a passing witness
eleven lines above where the lemma would go**: `join_le_comp`
(`FRJ/Extract.lean:246`) does `cases h with | comp hab` on `PJLe Ms` for a
fully abstract `Ms`, and the field equations the arms rely on
(`lbl none = Γ₀`, `lbl (some ⟨i,a⟩) = (Ms i).lbl a`, `Extract.lean:184`) do not
stop reducing when `Γ₀`/`Ms` are variables. The lemma above *is* the probe: if
`cases hle` were stuck, the design is refuted outright.

The likeliest reason it comes in under: the `hroot` supply keeps the five-line
`preI_spec`/`occI_steps`/`Step.join*` prelude in each arm (e.g.
`Extract.lean:675`), because the `Step` constructor differs per arm *and* per
calculus — arms would land at 13–14 lines rather than 10, costing about 70.

### `tag_cone` — second, ≈ 230 lines

`FRJ/Sound.lean:722`, `SoundV.lean:603`, `SoundW.lean:631`, 164 lines each,
45% mentioning a doubled name — and the distribution is the point:
**`joinAtP`, `joinOrP` and `joinCircP` are 133 of the 164 lines** (45, 45, 43),
while the other eight arms are one to six lines each. R↔V differ only in the
`kept` zone and only inside the three *six*-line arms; V↔W is rename-only
(`stab`/`th` → `Ξs`/`Θs`).

The `SoundCore` vocabulary is already in place: `joinCircP_core`
(`FRJ/SoundCore.lean:1014`) already carries `ihP` and `ihT` with literally the
`tag_cone` statement (`:1043`), over abstract `Ns`, and `joinCircP_case`
(`Sound.lean:618`) already discharges the
`modR d ≡ (joinPModel …).toKripke hP` defeq by `exact`. One new
`tagConeP_core` serves all nine sites.

Its probe is the one genuine risk, and it is exactly the Stage C risk one link
further along: whether `hu : (modR d).Rm (modR d).root u` still arrives at a
parameter typed by `PreModel.join` when `Ms`/`Ns` are abstract. The existing
text already ascribes this by `:= hu` at `Sound.lean:749`, so the probe is a
one-line `:= hu` against the abstract `joinPModel`. Failure costs about a third
of the saving, not the design.

## Done 2026-09-17: the `FRJ/Gbu` W-copy hoist (candidate 10)

This is candidate 10, "the `enumOf`/cover preamble in `FRJ/Gbu`, ~540 lines,
a `coverOf` lemma" — and the fix is not a `coverOf` lemma. The preamble is
not what is doubled; the whole manufacture proof is, and once the rule it
fires is a parameter the preamble travels with it for free.

`FRJ/Gbu/DB.lean` + `Circ.lean` against `FRJ/Gbu/W/DB.lean` +
`W/CircDB.lean`: seven declarations proved twice, once over FRJV and once
over FRJW. Measured, not estimated — `diff` on the seven pairs touches only
the statement line, the `EvalI`→`WEvalI` renames, and (in `_circ`) the one
`RefAt.ups` adapter. Everything else was byte-identical.

### The probe, and what it settled

The stated obstacle was the `⋈^◯` premise (J2), which is **not** alpha-equal
across the families: `A ∈ upsilon rhs` in FRJV (`FRJ/CalculusV.lean:192`),
`RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++ kept) A` in FRJW
(`FRJ/CalculusW.lean:172`). The probe asked whether one abstract rule-field
type can serve both, for all four fields used
(`axR`, `⋈^At`, `⋈^∨`, `⋈^◯`), and it **passes**:

```
$ lake env lean probe_wcopy.lean      # 3.1 s
$                                      # (exit 0, no output)
```

The probe was a scratch file (deleted); its four rule types are now the repo's
`AxRRule`/`AtRule`/`OrRule`/`CircRule` and its eight instances the
`…RuleV`/`…RuleW` definitions, so the probe survives as the code. The `⋈^◯`
line that carries the divergence read

```lean
example : CircRuleOf FRJVi FRJVr × CircRuleOf FRJWi FRJWr :=
  ⟨@fun _ _ _ _ _ _ _ p a b c d e f _ h => FRJVr.joinCirc p a b c d e f h,
   @fun _ _ _ _ _ _ _ p a b c d e f _ h =>
      FRJWr.joinCirc p a (fun A B hm => .ups (b A B hm)) c d e f h⟩
```

So `joinCirc` needs **no** premise-predicate parameter. The abstract field
carries the STRICT (FRJV) premise; FRJW's rule asks for strictly less, so the
W instance weakens it by `RefAt.ups` — the same adapter the W call site
already carried at `W/CircDB.lean:345` before the hoist. A weaker rule
instantiates a stronger abstract field for free; only a rule asking for MORE
would have needed the extra parameter.

The design is `FRJ/SoundCore.lean`'s: the rule is an explicit hypothesis, the
core mentions no calculus, no recursion moves. Two further hypotheses replace
the database layer, so `FSeq`/`WSeq` do not appear in any core either:
`irr_of_evalI` ((DB1) at an irregular row) and `evalI_of_irr` ((DB2), with the
subsuming row's zones repaired), one four- and one nine-line lemma per family.

### What was hoisted

Into `FRJ/Gbu/DB.lean`, all calculus-free: the four rule-field types
(`AxRRule`, `AtRule`, `OrRule`, `CircRule`); the three manufacture cores
(`refutedCleanly_at_core`, `_or_core`, `_circ_core`); the two zone-bookkeeping
lemmas `impZoneSplit` (clause viii) and `orZoneMerge` (Lemma 10). Into
`FRJ/Gbu/Circ.lean`, next to `clo_classForce`: `liftZoneGrow` and
`vacZoneGrow`, the three arm bodies of clause 14.

| declaration | V before → after | W before → after |
|---|--:|--:|
| `refutedCleanly_at` | 103 → 9 | 99 → 9 |
| `refutedCleanly_or` | 90 → 11 | 90 → 11 |
| `refutedCleanly_circ` | 85 → 10 | 86 → 10 |
| `gbuInv7` | 20 → 8 | 20 → 8 |
| `gbuInv8` | 47 → 10 | 47 → 10 |
| `gbuInv10` | 27 → 8 | 27 → 8 |
| `gbuInv14` | 52 → 25 | 52 → 24 |

| file | before | after |
|---|--:|--:|
| `FRJ/Gbu/DB.lean` | 724 | 964 |
| `FRJ/Gbu/Circ.lean` | 2,582 | 2,519 |
| `FRJ/Gbu/W/DB.lean` | 568 | 376 |
| `FRJ/Gbu/W/CircDB.lean` | 542 | 438 |
| total | 4,416 | 4,297 |

The number to read is **296**: the two W files fell from 1,110 lines to 814,
and what left them was duplication only — `gbuInv9`, `pledge_of_le` and the
pledged-lookup layer, which are W-specific and have no V counterpart, are
untouched. The net across all four is 119, because the V bodies
did not vanish — they BECAME the cores, and the price of naming what differs
is the 62 lines of rule-field signature plus eight one-line instances. The
gain the net line count does not show is that Lemmas 11, 12 and 13 now have
one proof each instead of two.

### Refused: `gbuInv14`'s case split

The fifth refusal, and the same mechanism as the G4 one. Clause 14 opens with
`cases d` on the irregular derivation, and the two families' constructor sets
genuinely differ: FRJVi has `impNotIn` and `liftI`, FRJWi has `lift` and no
`impNotIn`. An abstract premise family has nothing to case on, and the
watched failure says so exactly:

```lean
example {Ri : Form → List Form → List Form → Form → Type}
    {G : Form} {Ξ Θ : List Form} {Z : Form} (d : Ri G Ξ Θ (.circ Z)) : True := by
  cases d
```
```
error: Tactic `cases` failed: major premise type is not an inductive type
  Ri G Ξ Θ Z.circ
```

What the arms DO is calculus-free, and that was hoisted: `liftZoneGrow` for
the `◯∉`/`Lift` arms, `vacZoneGrow` for `Ax^I◯`, with `evalI_of_irr` supplying
the (DB2) tail. Each arm is three lines in each family now, and the 52-line
bodies are 25 and 24 — the residue is the `cases` itself, which is where the
two calculi actually differ.

## 2026-09-18: one import line was hiding thirty modules

Not a simplification — a restoration, and it belongs here because it was found
by the campaign's own machinery.

Re-running the prose-vs-record reconciliation over the merged tree gave 3,370
claims, 1,751 of them citing a declaration (51%), and **three CONTRADICTED**.
Two are the one accurate sentence already known. The third,
`docs/ui-routeB-blueprint.md:57`, marks N3 — `hasUI_of_stabilises` — **PROVED
both ways `[propext, Classical.choice, Quot.sound]`**, and the ledger said
`sorryAx`.

**The claim was true and the ledger could not see it.**
`wip/ui_routeB_n4.lean` imported `LJF.Complete`, which the 2026-09-16 merge
deleted in favour of `LaxLogic/Focusing/LJFComplete.lean`. The file has not
compiled since, so it was outside the estate, and the only declaration of that
name the ledger could find was the **blueprint stub** in
`wip/ui_routeB_blueprint.lean` — which carries a `sorry` because that is what a
blueprint file is for. One import line repaired, and:

    LJFO.hasUI_of_stabilises  def  sorry:false
      axioms [propext, Classical.choice, Quot.sound]

**The one import was holding thirty modules.** Every `wip/ui_routeB_*` module
outside the estate now builds — all thirty, in 4½ minutes: the whole halted
`interpR` line, the `n4q_*` loop-checked route, `pqequiv`, `pqmono`, `wp4`.
They had been invisible to every check since the merge. The estate goes from
598 modules and 28,249 declarations to **628 and 29,214 — 965 additions and
zero regressions.**

**They are sorry-free.** The counts are still 23 `sorryAx` and 2
`native_decide`, and not one of the 23 is in a restored module. The halted
search's working files pass their open cases as typed obligations, exactly as
CLAUDE.md rule 1 requires.

Two lessons, both already paid for once:

* **This is the `FRJO` hole a second time** — a documented PROVED result
  outside every check because nothing built its module. The difference is that
  this one was *caused* by the merge, and a sorried stub of the same name made
  an absence look like a contradiction.
* **A static sweep is cheap and should be standing.** Every `import` line in
  the tree, checked against every module that exists, finds exactly one
  unresolvable name outside `Archive/`, the Verso dependency and the
  `FrontierSampler` sub-tree: `LJF.Complete`. That sweep takes seconds and
  would have caught this on the day of the merge.

## The rules that keep this honest

1. **No statement moves.** If a refactor would change a theorem's statement, it
   is not part of this plan; it goes on the list for Matthew.
2. **The ledger is the gate.** `scripts/check-ledger.sh` after every stage; a
   REGRESSION line stops the stage. A refactor that silently routes a proof
   through `Classical.choice` is exactly what the gate is for.
3. **Watch each new tactic fail** before it is used anywhere (CLAUDE.md
   discipline): a tactic that silently closes the wrong goal is worse than the
   duplication it removes.
4. **Extraction is not generalisation.** A lemma is extracted with the weakest
   hypotheses that the existing call sites supply, never with the hypotheses
   that would make it pretty.
5. **Archive, don't delete** the superseded proof when a merge is not
   byte-exact: the old body goes in the commit message, so a bisect can read
   it.

## What this is not

It is not a speed campaign. Build time is not measured here and no step is
justified by it. It is not a re-proof: nothing is re-derived, only re-arranged.
And it does not touch `wip/`, the frozen four-arm `wipa/…/wipx` records, or
`Archive/` — those are the record of how the development happened.
