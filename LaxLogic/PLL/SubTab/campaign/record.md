# The subframe tableau: the campaign's record

Written 2026-11-19, after the fact.  The subframe tableau (`SubTab`) was
built between 2026-10-15 and 2026-10-27, before the campaign method of
[proof-tools](https://github.com/fairflow/proof-tools) (`docs/campaign.md`)
was written down.  This page sets what was done against that method: the
five questions as they turned out, the rules, the reading of a judgment,
the measure, the truth lemma, the statements, and what runs.  Nothing here
is new mathematics; every statement is in the Lean files named, and
`docs/calculus-map.md` (section `SubTab`) and `TOOLS.md` hold the detail.

The tableau was designed, not adopted from a source (Matthew, 2026-10-15:
"we do need a new refuter based on subframes").  So there is no source to be
faithful to, and in place of a table of rules against a source this record
has the rules, the reading of a signed sequent, the measure of termination
and the truth lemma.

## 1. The five questions, as they turned out

**1. What are the rules?**  Twelve, on signed sequents; §2.  No source.

**2. What is proved about it?**  Soundness of closed tableaux, soundness of
the countermodel check, the dichotomy, completeness, the translation of a
closed tableau into a natural-deduction derivation as data, and
completeness of PLL for finite subframe models from the tableau alone; §5.
All within `[propext, Quot.sound]`.  Not proved: that the compiled search
terminates (a paper argument; the proof's dichotomy terminates by the
measure).  Not attempted: complexity, interpolation.

**3. What should run, and why?**  A decision procedure for `⊢ φ` in PLL
with a certificate either way: a closed tableau, or a finite subframe
countermodel.  It was wanted as the fastest refuter for the tables of F0
(the free algebra on no generators), where every cell is a verdict that
later work relies on, so every verdict is checked by the kernel; §6.

**4. How do people use it?**  Until 2026-11-19 only whole: a formula in, a
verdict and a certificate out (`pllfast`, `plldecide`, `refbench fact`).
There was no way to make one move and look.  The explorer instance of
2026-11-19 is that way (`Explore.lean`, `ExploreTactic.lean`,
`Play/SubTab.lean`).

**5. Which calculi is it related to?**  `LaxND`, the natural deduction of
Fairtlough and Mendler (1997): a closed tableau computes its derivation
(`deriveOf`, `termOf`).  FRJW with `Gbu`, the forward refutation calculus:
the first proof that a closed tableau proves its formula went through
FRJW's completeness (`yes`); the second does not (`yes'`).  LJF◯, the
focused sequent calculus, and the finite-model enumeration, which stand
beside the tableau in the decider `plldecide`.  `docs/calculus-map.md`.

## 2. The rules

A judgment is a signed sequent at one world, `SSeq = ⟨b, Γ, Δ⟩`: the
formulas of `Γ` are true there, those of `Δ` false there, and `b` says
whether the world is an S-point.  `Γ + A` is `Γ ++ [A]`.

| rule | asks | leaves |
|---|---|---|
| `bot` | `⊥ ∈ Γ` | nothing |
| `ax A` | `A ∈ Γ`, `A ∈ Δ` | nothing |
| `andL A B` | `A ∧ B ∈ Γ` | `⟨b, Γ + A + B, Δ⟩` |
| `orL A B` | `A ∨ B ∈ Γ` | `⟨b, Γ + A, Δ⟩` and `⟨b, Γ + B, Δ⟩` |
| `impL A B` | `A ↠ B ∈ Γ` | `⟨b, Γ, Δ + A⟩` and `⟨b, Γ + B, Δ⟩` |
| `boxL A` | `b` is S, `◯A ∈ Γ` | `⟨b, Γ + A, Δ⟩` |
| `andR A B` | `A ∧ B ∈ Δ` | `⟨b, Γ, Δ + A⟩` and `⟨b, Γ, Δ + B⟩` |
| `orR A B` | `A ∨ B ∈ Δ` | `⟨b, Γ, Δ + A + B⟩` |
| `impLoc A B` | `A ↠ B ∈ Δ`, `A ∈ Γ` | `⟨b, Γ, Δ + B⟩` |
| `boxLoc A` | `b` is S, `◯A ∈ Δ` | `⟨b, Γ, Δ + A⟩` |
| `impR A B` | `A ↠ B ∈ Δ` | `⟨not S, Γ + A, [B]⟩` |
| `boxR A` | `◯A ∈ Δ` | `⟨S, Γ, [A]⟩` |

The first ten stay at the world.  `impR` and `boxR` go to a new world above,
which keeps the true formulas and drops the false ones: these are the two
rules where a choice can be lost.

In Lean the rules are the twelve cases of the checker `check : SSeq → TCert
→ Bool` (`Sound.lean`), and since 2026-11-19 also the twelve cases of
`Move.rule` (`Explore.lean`), with the same conditions and the same
premises.

## 3. The reading of a signed sequent

Semantically (`Refutes`, `Sound.lean`): a world `x` of a subframe model
refutes `⟨b, Γ, Δ⟩` when it is an S-point if `b` says so, forces every
formula of `Γ` and forces none of `Δ`.  A closed tableau shows that no
world of a finite decidable subframe model refutes its sequent.

As a statement to derive (`SSeq.goal`, `Translate.lean`):

    ⌈⟨not S, Γ, Δ⟩⌉ = ⋁Δ          ⌈⟨S, Γ, Δ⟩⌉ = ◯⋁Δ          ⋁[] = ⊥

and a closed tableau for `s` computes a derivation of `s.ant ⊢ ⌈s⌉` in
`LaxND`.

## 4. The measure, and the truth lemma

Over a list `U` closed under subformulas, with `cnt U Γ` the number of
members of `U` not in `Γ` (`Steps.lean`):

    meas U b Γ Δ = (2 · cnt U Γ + (if b then 0 else 1)) · (2 · |U| + 1) + (cnt U Γ + cnt U Δ)

Every rule applied where it adds something lowers it (`meas_ant`,
`meas_suc`, `meas_impR`, `meas_boxR`), and the dichotomy is by strong
induction on it.

An open tree (`OTree`, `Dich.lean`) is `Good` when every world is
consistent and saturated, each of its demands has a child serving it, and
its true formulas are carried to its children.  A `Good` tree is a finite
decidable subframe model, and (`Model.lean`):

    truth : (A ∈ (nodeAt t a).ant → (model t hg).force a A) ∧
            (A ∈ (nodeAt t a).suc → ¬ (model t hg).force a A)
    root_refutes : Covers t s → Refutes (model t hg) (rootW t hg) s

## 5. The statements

Each is PROVED, within `[propext, Quot.sound]`, pinned in its file.

| statement | name | file |
|---|---|---|
| `check s c = true → ∀ M [FinDec M] x, ¬ Refutes M x s` | `check_sound` | `Sound.lean` |
| `check ⟨false, [], [φ]⟩ c = true → Holds φ` | `holds_of_check` (through FRJW), `holds_of_check'` (the tableau's own rules) | `Sound.lean`, `Translate.lean` |
| `m.refutes φ = true → Holds φ → False` | `SubCM.refutes_sound` | `Sound.lean` |
| `meas U s.isS s.ant s.suc = n → s.ant ⊆ U → s.suc ⊆ U → Outcome s` | `dich` | `Dich.lean` |
| `(∃ c, yes.check φ c = true) ∨ (∃ m, no.check φ m = true)` | `complete` | `Complete.lean` |
| `deriveOf : (c : TCert) → (s : SSeq) → check s c = true → (s.ant ⊢ s.goal)` | a definition | `Translate.lean` |
| `(∀ M [FinDec M] x, M.force x φ) → Holds φ` | `completeness_fin` | `Translate.lean` |

`Holds φ` is `Nonempty ([] ⊢ φ)`; `Outcome s` is "a closed tableau, or a
`Good` tree covering `s`".  Each has its ◯-free instance, proved first.
Sweep of 2026-10-27: all 799 declarations of the thirteen modules are
within the bound.

Added 2026-11-19, by the explorer instance (`Explore.lean`, the same
bound):

| statement | name |
|---|---|
| `(m.rule s).ok = true → Checks (m.rule s).prems cs → check s (m.cert cs) = true` | `check_cert_of` |
| `STab.Sound (fun s => ∃ c, check s c = true)` | `sound` |
| `check s (cert d) = true`, for `d : Der STab s` | `check_cert` |
| `cert (ofCert c s h) = c` | `cert_ofCert` |
| `Der STab ⟨false, [], [φ]⟩ → Holds φ` | `holds_of_der` |
| `(∃ ls, yesScript.check φ ls = true) ∨ (∃ m, no.check φ m = true)` | `complete_script` |

OPEN (not attempted): `ofCert (cert d) s (check_cert d) = d`, the other
round trip; and that the compiled search `SubTab.solve` terminates.

## 6. What runs

* **The search** `SubTab.solve` (`Tableau.lean`): depth-first, with
  backtracking over the branches of each world.  Untrusted, `partial`.  It
  returns a closed tableau or an open tree as tables.
* **The two certifiers** `yes` and `no` (`Sound.lean`), and the engine
  `PLLND.SubTab.engine` (`Engine.lean`).  The engine never flags.
* **Negative tests** (`Gates.lean`): one corrupted certificate for each
  checker, rejected by the kernel.
* **Facts** (`Facts.lean`): 29, generated, each checked by the kernel.
* **The tools** (`TOOLS.md`): `pllfast`, `plldecide`, `subtabdecide`,
  `refbench`.

Measurements on record (`TOOLS.md`, 2026-10-22): on the 33 cells of the
benchmark the verdicts agree with the earlier record; the 7 proved cells
take 56 to 63 ms per process through the tableau, against 57 to 1555 ms
through the FRJW engine; the largest cell (a closed formula of 32,877
characters, with a countermodel of 10 worlds) takes 17 s.

## 7. Against the method's five stages

| stage | for the tableau |
|---|---|
| Survey | none: built on request |
| Adopt | done, as a checker of whole trees (2026-10-15); a move at a time since 2026-11-19 |
| Prove | done (§5) |
| Run | done (§6) |
| Explore | the first instance, 2026-11-19; the full exploration is not started |
