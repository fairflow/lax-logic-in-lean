# The PLL formalisation in Lean: statement-level ledger

*Generated 2026-07-16, branch `claude/belief-lax-logic-handover-f331bf`,
toolchain Lean v4.31.0 + Mathlib v4.31.0.*

**Purpose.** Lean's kernel checks the *proofs*; what remains for a human is to
check that the *statements* — the definitions and the displayed theorems — say
what they are claimed to say. This ledger is that checklist: each row names a
result, its Lean identifier and location, and its axiom audit, so the human
task reduces to reading the statement at the cited location and agreeing it
formalises the intended claim. Every audit below was **re-run on 2026-07-16**
(not copied from earlier notes); to re-verify any row, run
`lake env lean <file>` for a file containing `#print axioms <name>`.

**Axiom key.**
- **none** — fully constructive: no axioms at all.
- **[p]** = `[propext]`; **[p,Q]** = `[propext, Quot.sound]` — no choice.
- **clean** = `[propext, Classical.choice, Quot.sound]` — the ordinary axioms
  of classical Lean.
- No entry uses `sorryAx` (no `sorry` anywhere in `LaxLogic/`) and none uses
  `ofReduceBool`/`native_decide` except where explicitly flagged.

---

## 1. The systems and their equivalence (F&M I&C 1997, §2)

| result | Lean name | location | axioms |
|---|---|---|---|
| Natural deduction for PLL (membership-based contexts; weakening/exchange/contraction admissible, cast-free) | `LaxND` (+ `LaxND.rename`) | `PLLNDCore.lean:72` | (def) |
| Cut-free G3-style sequent calculus, height-indexed | `SCh` / `SC` | `PLLSequent.lean:31,58` | (def) |
| **Cut admissibility** (lexicographic induction; F&M Thm 2.6 engine) | `SC.cut` | `PLLSequent.lean:524` | clean |
| **Cut elimination** | `cutElimination` | `PLLSequent.lean:615` | clean |
| Sequent ⟶ natural deduction | `SC_to_ND` | `PLLSequent.lean:546` | clean |
| Natural deduction ⟶ sequent | `ND_to_SC` | `PLLSequent.lean:578` | clean |
| **Disjunction property** (F&M Lemma 2.7) | `disjunction_property` | `PLLSequent.lean:623` | clean |
| **`◯`-reflection**: `⊢ ◯M ⟹ ⊢ M` (F&M Lemma 2.7) | `somehow_reflection` | `PLLSequent.lean:637` | clean |
| **Hilbert ⟷ natural deduction** | `hd_iff_ND` | `PLLHilbert.lean:194` | **[p]** |
| **Conservativity over IPL** (erasure form) | `conservativity_prop` | `PLLNDCore.lean:193` | [p,Q] |
| **Conservativity over IPL** (classic form: IPL sequents) | `conservativity_IPL` | `PLLNDCore.lean:211` | **[p,Q]** — no choice |
| Strong extensionality (F&M Thm 2.5) | `strong_extensionality` | `PLLTheorems.lean:178` | clean |

## 2. Kripke constraint semantics (F&M §3–4)

| result | Lean name | location | axioms |
|---|---|---|---|
| Constraint models (F&M Def 3.1) + forcing (Def 3.2) | `ConstraintModel`, `force` | `PLLKripke.lean:28,52` | (def) |
| **Soundness** (F&M Thm 3.3, sequent form) | `soundness` | `PLLKripke.lean:97` | **[p]** |
| **Completeness** (F&M Thm 4.4, strengthened to sequents) | `completeness` | `PLLCompleteness.lean:614` | clean |

## 3. Countermodels — known non-theorems, formally refuted (F&M Fig. 3)

| non-theorem | Lean name | location | axioms |
|---|---|---|---|
| `⊬ ¬◯⊥` (no doxastic `D`) | `not_provable_not_somehow_false` | `PLLFrames.lean:88` | [p,Q] |
| `⊬ ◯(A∨B) ⊃ (◯A ∨ ◯B)` | `not_provable_somehow_or_dist` | `PLLFrames.lean:142` | clean |
| `⊬ (◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)` | `not_provable_imp_somehow_dist` | `PLLFrames.lean:205` | clean |

## 4. Proof-term calculus: strong normalisation

| result | Lean name | location | axioms |
|---|---|---|---|
| **Strong normalisation of the full reduction** (β + `let`-assoc interleaved; Lindley–Stark ⊤⊤-lifting) | `strong_normalisation` | `PLLTopTop.lean:1266` | clean |
| Certified normaliser (normal form reached) | `Tm.normalize_spec` | `PLLTopTop.lean:1296` | clean |

*(Component results — `assoc_sn`, the certified one-step reducer `Tm.step?`, and
the machine-checked failure of quasi-commutation forcing the semantic method —
live in `PLLStrongNorm.lean` / `PLLReducibility.lean`; not separately audited
here, subsumed by the above.)*

## 5. Beyond the I&C paper

| result | Lean name | location | axioms |
|---|---|---|---|
| **Craig interpolation for PLL** (Maehara over the cut-free calculus) | `craig_interpolation` | `PLLCraig.lean:401` | clean |
| Interpolation for implications | `craig_implication` | `PLLCraig.lean:411` | clean |
| **Kleene–Brouwer order on an inductively well-founded tree over a well-founded alphabet is well-founded** | `wellFounded_kb`, `wellFounded_kb'` | `KleeneBrouwer.lean:164,180` | **none — fully constructive** (in-file guard asserts it) |

*(Naming: the file and the literature say Kleene–Brouwer, also Lusin–Sierpiński;
"Kolmogorov" could not be verified as part of the standard name.)*

## 6. The Curry-paper results (F&M TYPES 2000, LNCS 2277) — `wip/context_completeness.lean`, `wip/lax_infinite.lean`

| result | Lean name | location | axioms |
|---|---|---|---|
| Constraint-context soundness (Thm 6, ⟸ direction engine) | `Ctx.thm6_soundness` | `context_completeness.lean:173` | [p,Q] |
| **Context completeness** (Thm 6): `PLL ⊢ φ ⟺ ∀ standard C, IPL ⊢ φ^C` | `Ctx.thm6` | `context_completeness.lean:651` | clean |
| Lemmas 8, 9 (escape family) | `Ctx.lemma8`, `Ctx.lemma9` | `:973,:864` | clean |
| **No finite constraint set suffices** (Cor 10) | `Ctx.corollary10` | `context_completeness.lean:981` | clean |
| **The constraint algebra `𝕊` is a Boolean algebra** (Thm 2, bundled Mathlib instance) | `Ctx.thm2_boolean_algebra`, `Ctx.CQuot.instBooleanAlgebra` | `:1588,:1667` | **[p,Q]** |
| **The closed lax fragment `RN(◯,{})` is infinite** | `LaxInfinite.closed_lax_infinite` | `lax_infinite.lean:616` | clean |

## 7. The G4iLL gap — the decidability route, machine-refuted

| result | Lean name | location | axioms |
|---|---|---|---|
| The separating sequent is PLL-derivable | `PLLG4Gap.sep_SC` | `PLLG4Gap.lean:58` | clean |
| …but not G4iLL-derivable | `PLLG4Gap.sep_not_G4` | `PLLG4Gap.lean:340` | **[p]** |
| Contraction not admissible in G4iLL | `PLLG4Gap.contraction_not_admissible` | `PLLG4Gap.lean:378` | **[p]** |
| Cut not admissible in G4iLL | `PLLG4Gap.cut_not_admissible` | `PLLG4Gap.lean:396` | **[p]** |

## 8. Open items (stated honestly)

- **Decidability of PLL (F&M Thm 2.8): NOT mechanised.** Proved on paper via
  the finite model property; the planned mechanisation route (Iemhoff's G4iLL)
  was **machine-refuted** (§7: the calculus is incomplete for PLL). A repaired
  calculus or an FMP mechanisation remains open.
- **The uniform-interpolation probe** (`wip/onevar.lean`, `wip/absorb_base.lean`,
  `wip/g4ill_ui.lean`) is a separate research thread and carries the repo's only
  open `sorry`s (5, all listed in those files' headers). No result above
  depends on them.

## 9. The belief-paper layer (2026-07-14…16)

Statement-level index for the *Belief in Lax Logic* results (Boolean collapse,
`N(B) ≃o B`, normality, introspection/omniscience, open vs closed nuclei, `◯⊥`
facts, small-algebra enumerations): `docs/belief-mechanisation-index.md`.
Route B realisability results (the two evidence clauses, heredity, the local
nucleus laws, the separation triptych, the double-negation believer, and
combinatory completeness `Poly.abs_spec` **[p,Q]**):
`wip/belief_realisability.lean`, statuses in `docs/route-b-model.md` §8.
