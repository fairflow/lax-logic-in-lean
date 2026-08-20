# Propositional Lax Logic, in Lean 4

A machine-checked development of **Propositional Lax Logic** (PLL), the
intuitionistic modal logic of Fairtlough and Mendler, *Propositional Lax
Logic*, Information and Computation **137**(1), 1997, 1–33.

Everything in the default build target is finished work: sorry-free, with the
axioms of each headline theorem pinned so that the build fails if they ever
change. Unfinished campaigns are not in the default target — §6 says what they
are and where they live. Nothing here is claimed that Lean does not check.

```bash
lake build
```

That builds [`Core.lean`](Core.lean), which imports the whole core, and
[`Core/Audit.lean`](Core/Audit.lean), which pins its axioms. A green build *is*
the claim.

---

## 1. What lax logic is

PLL is intuitionistic propositional logic (IPL) with one extra unary modality,
written `◯`. Read `◯φ` as

> φ holds *under some constraint* — up to some admissible qualification.

The constraint is not named in the syntax: `◯` quantifies over it existentially.
This is what makes the modality lax rather than a `□` or `◇` of a normal modal
logic — but see §2 for the sense in which it *is* a normal box.

Over IPL, `◯` is axiomatised by ([`LaxLogic/PLLAxiom.lean`](LaxLogic/PLLAxiom.lean)):

| | | |
|---|---|---|
| `◯R` | `φ ⊃ ◯φ` | a constraint may be trivial |
| `◯M` | `◯◯φ ⊃ ◯φ` | constraints compose |
| `◯S` | `(◯φ ∧ ◯ψ) ⊃ ◯(φ ∧ ψ)` | two constraints can be met at once |
| `◯Bind` | `(φ ⊃ ◯ψ) ⊃ (◯φ ⊃ ◯ψ)` | constraints propagate through entailment |

Algebraically these say exactly that `◯` is a **nucleus** on the Heyting algebra
of propositions: inflationary, idempotent, and meet-preserving. Categorically
they make `◯` a strong monad, which is why the logic has a well-behaved term
calculus (§3).

The reference proof system in this development is natural deduction,
`LaxND` ([`LaxLogic/PLLNDCore.lean`](LaxLogic/PLLNDCore.lean)). Its two modal
rules are introduction and a Moggi-style bind:

```
    Γ ⊢ φ                     Γ ⊢ ◯φ     Γ, φ ⊢ ◯ψ
  ──────────  laxIntro      ─────────────────────────  laxElim
   Γ ⊢ ◯φ                            Γ ⊢ ◯ψ
```

Throughout, the sequent is written `Γ ⊢ φ`, and `Γ ⊬ φ` when it fails. In Lean,
`Γ ⊢- φ` (`LaxND Γ φ`) is the *type* of derivations; `Deriv Γ φ`, its
inhabitedness, is the `Prop`-level form of `Γ ⊢ φ`; and `⊬` is notation for
`Underivable`. `hd_iff_ND` (F&M Theorem 2.3) proves the Hilbert presentation
above and this natural deduction agree.

**Semantics.** A *constraint model* ([`LaxLogic/PLLKripke.lean`](LaxLogic/PLLKripke.lean))
is a Kripke structure `(W, Rᵢ, Rₘ, F, V)` with two preorders — `Rᵢ` for
implication, `Rₘ` for the constraint — subject to `Rₘ ⊆ Rᵢ`, together with a set
`F` of *fallible* worlds at which everything holds, including `⊥`. The clauses
are the intuitionistic ones plus

```
  w ⊩ ◯φ   iff   ∀ v. Rᵢ w v → ∃ u. Rₘ v u ∧ u ⊩ φ
```

so `◯` is a `∀∃` modality: persistently, some constraint is met. Fallible worlds
are what make `◯⊥` satisfiable, and hence what distinguish PLL from its
infallible extension (§7 below).

## 2. Why any of this is worth mechanising

PLL was not invented for its own sake. Three applications are formalised here.

**Curry's problem.** Given a set of "constraints" — extra assumptions relativised
to subformulas — when does an intuitionistic tautology survive? F&M's answer
(*A Solution to Curry's Problem*, TYPES 2000, LNCS 2277) is that PLL is exactly
the logic that is sound and complete for *all* standard constraints at once:
`PLL ⊢ φ` iff `IPL ⊢ φ^C` for every standard constraint `C`. Both directions are
proved here, with the corollary that no *finite* set of constraints suffices.

**Timing analysis of circuits.** Mendler's proofs-as-delays reading (*Timing
Analysis of Combinational Circuits in Intuitionistic Propositional Logic*, Formal
Methods in System Design **17**(1), 2000) evaluates PLL proof terms in the strong
monad `T A = ℕ × A`, with `+` for sequential composition and `max` for
reconvergent fanout. A derivation of `◯a ⊃ ◯b ⊃ ◯c` *is* a stabilisation bound
for a circuit. His §7 `CIRC` example is reproduced, including the punchline: the
proof-term bound beats the topological one, because the logic notices a false
path that a purely structural analysis cannot.

**Idealised evidential belief.** Reading `◯φ` as "φ is believed on evidence"
makes `◯` a nucleus again, and the three axioms become recognisable doxastic
principles. `◯` validates the K axiom, so belief is normal; and classical belief
is degenerate — every nucleus on a Boolean algebra satisfies `j x = x ⊔ j ⊥`, so
it is either the identity or constantly `⊤`. That is an argument for
constructivism made inside the logic.

## 3. The proof systems, and how they relate

Six systems appear. [`docs/calculus-map.md`](docs/calculus-map.md) is the
authoritative map of which result belongs to which; read it before attributing
anything.

| system | what it is | file |
|---|---|---|
| `Hd` | Hilbert-style, the axioms of §1 | `PLLAxiom`, `PLLHilbert` |
| `LaxND` | natural deduction — **the** reference | `PLLNDCore` |
| `Tm` | the term calculus for `LaxND` | `PLLTerms` |
| `SC` | F&M's cut-free sequent calculus (Iemhoff's `G3iLL`) | `PLLSequent` |
| `G4` | Iemhoff's contraction-free `G4iLL`, transcribed | `PLLG4` |
| `G4c` | the repaired contraction-free calculus | `PLLG4H*` |

The equivalences are theorems, not conventions:

```
  G4c Γ C  ↔  SC Γ C  ↔  Deriv Γ C  ↔  Nonempty (Tm Γ C)
```

(`PLLND.G4c.equiv_sc`, `equiv_nd`, `equiv_tm`). Cut elimination for `SC` is F&M
Theorem 2.6; with it come the subformula property and the disjunction property.

**`G4` is the exception, and that is a result.** Iemhoff's `G4iLL` (*Proof Theory
for Lax Logic*, arXiv:2209.08976, Fig. 2.3) was claimed equivalent to `G3iLL`.
It is not. Writing `F' := ◯p ⊃ r` and `G' := F' ⊃ ◯p`,

```
  ◯G', F' ⇒ r
```

is derivable in `SC` and **not** derivable in `G4` — both halves machine-checked
in [`LaxLogic/PLLG4Gap.lean`](LaxLogic/PLLG4Gap.lean), the second by a decision
procedure whose completeness over the `G4` rules is itself a theorem. The `SC`
derivation uses `F'` twice, once inside the box-opening and once outside;
`G4iLL`'s `L◯→` rule reuses the *box* across its premises but consumes the
implication, and its first premise `G' ⇒ ◯p` is invalid. This is Howe's
duplication phenomenon one level up, with the formula needing contraction
straddling a box-opening. Consequently the modal case of Theorem 1 of
arXiv:2011.11847 fails as stated.

`G4c` is the repair. For it, cut, full cut-free contraction, completeness, and
all three equivalences above are unconditional, and decidability of PLL (F&M
Theorem 2.8) follows.

Alongside these sit the **focused** calculi: Liang–Miller's `LJF` for the
intuitionistic base and `LJF◯`, its lax-flagged extension.  Focalization is the
theorem that restricting search to maximal alternating phases of invertible and
non-invertible rules loses no derivations, so a focused search procedure is
complete without being a blind enumeration.  `LJFO.bridge_iff` proves LJF◯
derivability and PLL derivability coincide; `LJFIPC.uniform_interpolation_IPC`
gets uniform interpolation for IPC out of the same machinery.

Two refutation calculi complete the picture, both of which derive *counter*models
positively rather than searching for them: `FRJ(G)` for IPC, after Fiorentini and
Ferrari (ACM TOCL **21**(3), 2020), and `Reject` for PLL, after their JLC 2021
S4 model-generation calculus.

## 4. A reading order

Each step names the file and the theorem that step delivers. Section numbers
match [`Core.lean`](Core.lean) and [`Core/Audit.lean`](Core/Audit.lean).

1. **Syntax and `LaxND`.** [`LaxLogic/PLLNDCore.lean`](LaxLogic/PLLNDCore.lean) —
   the modal rules, then `conservativity_prop`: erasing every `◯` from a PLL
   derivation yields an IPL derivation of the erased sequent. Its classic
   corollary `conservativity_IPL` is that on `◯`-free sequents PLL proves nothing
   IPL does not. [`LaxLogic/PLLHilbert.lean`](LaxLogic/PLLHilbert.lean) —
   `hd_iff_ND` (F&M Theorem 2.3).
2. **Constraint semantics.** [`LaxLogic/PLLKripke.lean`](LaxLogic/PLLKripke.lean) —
   the models and `soundness`. [`LaxLogic/PLLCompleteness.lean`](LaxLogic/PLLCompleteness.lean) —
   `completeness`, by a finitary canonical model needing no Zorn.
   [`LaxLogic/PLLFiniteModel.lean`](LaxLogic/PLLFiniteModel.lean) —
   `finite_model_property` (F&M Theorem 4.6).
3. **The sequent calculus.** [`LaxLogic/PLLSequent.lean`](LaxLogic/PLLSequent.lean) —
   `cutElimination` (F&M Theorem 2.6) and `disjunction_property` (Lemma 2.7(i)).
4. **`G4iLL` refuted, and repaired.** [`LaxLogic/PLLG4Gap.lean`](LaxLogic/PLLG4Gap.lean) —
   `sc_but_not_G4`, and with it `cut_not_admissible` and
   `contraction_not_admissible` as explicit derivations. Then
   [`LaxLogic/PLLG4HCut.lean`](LaxLogic/PLLG4HCut.lean), [`…HCtr`](LaxLogic/PLLG4HCtr.lean),
   [`…HComp`](LaxLogic/PLLG4HComp.lean) for `G4c.cut`, `G4c.contract`,
   `G4c.completeness` and the equivalence chain, and
   [`LaxLogic/PLLG4Dec.lean`](LaxLogic/PLLG4Dec.lean) for `decidablePLL`.
5. **Terms and normalisation.** [`LaxLogic/PLLTerms.lean`](LaxLogic/PLLTerms.lean),
   then [`LaxLogic/PLLTopTop.lean`](LaxLogic/PLLTopTop.lean) —
   `strong_normalisation` for the full interleaved reduction (β for every
   connective plus `let`-association), by Lindley–Stark ⊤⊤-lifting. This is a
   result about terms, not about derivability.
6. **Curry's problem.** [`LaxLogic/PLLCtxCompleteness.lean`](LaxLogic/PLLCtxCompleteness.lean) —
   `Ctx.thm6` in both directions, and `Ctx.corollary10`.
7. **PCLL and the infallible extension.** [`LaxLogic/PLLConfluentComplete.lean`](LaxLogic/PLLConfluentComplete.lean)
   and [`LaxLogic/PLLNoFall.lean`](LaxLogic/PLLNoFall.lean) — F&M Theorem 4.7,
   both bullets: `PLL + ◯(A∨B) ⊃ (◯A∨◯B)` is complete for mutually confluent
   models, and `PLL + ¬◯⊥` for models with no fallible worlds. Ours:
   `varfree_dichotomy`, the variable-free collapse under `¬◯⊥`.
8. **The closed fragment.** [`LaxLogic/PLLLaxInfinite.lean`](LaxLogic/PLLLaxInfinite.lean) —
   `closed_lax_infinite`: the `◯`-only variable-free fragment has infinitely many
   classes, proved three independent ways. No finite operation table closes it.
9. **Craig interpolation.** [`LaxLogic/PLLCraig.lean`](LaxLogic/PLLCraig.lean),
   by Maehara's method over the cut-free calculus.
10. **Search and countermodels.** [`docs/search-manual.md`](docs/search-manual.md)
    first; then [`LaxLogic/PLLSearchDemo.lean`](LaxLogic/PLLSearchDemo.lean) as a
    file to step through. The engines are untrusted but certificate-carrying:
    discover with search, pin with the kernel. §0 of the manual names the trap —
    a countermodel refutes **PCLL** only if it is mutually confluent, so a PCLL
    claim wants `#refuteConf`, not `#refute`.
11. **Timing.** [`LaxLogic/PLLTiming.lean`](LaxLogic/PLLTiming.lean) —
    `circUp_rising` and `falsePath_beats_topological`; then the ripple, adder and
    carry-lookahead files.
12. **Belief.** [`LaxLogic/BeliefNormality.lean`](LaxLogic/BeliefNormality.lean)
    (`nucleus_himp_le`, the K axiom), [`LaxLogic/BeliefCollapse.lean`](LaxLogic/BeliefCollapse.lean)
    (`nucleus_eq_sup_bot`, the classical degeneracy),
    [`LaxLogic/BeliefRealisability.lean`](LaxLogic/BeliefRealisability.lean) for
    the uniform and strategy realisability relations and their separations, and
    [`LaxLogic/PLLRealCompleteness.lean`](LaxLogic/PLLRealCompleteness.lean) —
    `derivable_iff_no_realP_refutation`: a sequent is derivable exactly when no
    presented-strategy realisability structure refutes it.
13. **`FRJ(G)` for IPC.** [`FRJ/`](FRJ) — `soundness`, `completeness`,
    `frj_iff_not_IPL`. No modality; independent of everything above.
14. **`Reject` for PLL.** [`Reject/`](Reject) — `not_laxND_of_built` (the
    constructors are sound: a built countermodel certifies `Γ ⊬ ψ`) and
    `built_iff_of_reduced` (they are complete: if a sequent has a finite reduced
    countermodel at all, it has one assembled by `solo` and `join` alone, so the
    certificate format is a calculus).

15. **Focused search.** `LaxLogic/LJFOBridge.lean` — `LJFO.FocalizationPLL` and
    `LJFO.bridge_iff`: focalization for PLL. `LaxLogic/LJFComplete.lean` —
    `LJFIPC.focalization` and `LJFIPC.uniform_interpolation_IPC`: Pitts'
    properties for the `◯`-free fragment, i.e. uniform interpolation for IPC.
    Note what this is *not*: uniform interpolation for PLL, which is OPEN (§6).

## 5. How to check it yourself

```bash
lake build
```

Green means: every module of the core elaborated, every `#guard_msgs` matched,
and no declaration used `sorry`. Then read
[`Core/Audit.lean`](Core/Audit.lean), which pins the axioms of every terminal
theorem listed above.

`#print axioms` (Lean's `collectAxioms`) is the only sound oracle for what a
theorem rests on. What may legitimately appear is `propext`, `Quot.sound`, and
`Classical.choice`. The last is usually a property of the *statement* rather
than a weakness of the proof: passing from "not every model validates φ" to
"some model refutes φ" is not constructively valid.

What must never appear is `sorryAx` — an unproved claim — or `Lean.ofReduceBool`,
which is what `native_decide` leaves behind: it trusts the compiled evaluator
instead of the kernel. Neither occurs in the core. Because the pins are
`#guard_msgs`-checked, an axiom regression is a build failure rather than
something discovered months later.

Three verdicts are kept rigidly distinct throughout:

- **PROVED** — sorry-free in Lean with pinned axioms. Nothing else earns it.
- **REFUTED** — a kernel-checked counterexample. `G4iLL`'s incompleteness is
  a result of this kind, and is pinned on the same footing as a theorem.
- **OPEN** — anything else, including everything carrying a `sorry`.

## 6. What is deliberately not here

The repository holds parallel campaigns accumulated over months. Several are
parked mid-flight, and the criterion for this branch is *per campaign, not per
file*: if a sequence of files aims at a result that was never reached, the whole
sequence is out, including its sorry-free members. They are untouched on this
branch — `lake build LaxLogic` still builds the full working library — and
completed work can be re-admitted later as its own clean sequence.

**Uniform interpolation for PLL is OPEN and is not claimed here.** Three routes
to it are parked: the semantic route after Litak–Visser (the `PLLSemUI*`
cluster, which carries the only `sorry`s outside `wip/`), the syntactic route
through the `G4c` tower (`PLLG4UI*`), and the minimality tail of the focused
route (`LaxLogic/LJFO.lean` and `FRJO/`, where the remaining results are
conditional on a typed obligation `CimpAnt` that has not been discharged).

What those routes produced *on the way* is in the core, because it stands on its
own: focalization for PLL and uniform interpolation for IPC (§4 step 15). A
campaign failing to reach its goal does not retract the theorems it proved en
route, and the core admits any such theorem whose own import closure is
finished — which is the whole point of keeping shared definitions out of
campaign files (see `LaxLogic/Deriv.lean` and `LaxLogic/Bisim.lean`).

Also out: `BiLax/`, whose bi-lax calculus, soundness and refutation pipeline are
proved but whose duality bridge was never attempted; and `Rewrite/`, a certified
simpset whose mechanism is finished but whose rule data is not (of 323 dictionary
cells, 236 are proved, 87 carry `sorry`, and four are refuted).

`wip/` is campaign material, outside the core by construction. Its files are
probes, screens and certificate banks, not results. The standing handover is
[`HANDOFF.md`](HANDOFF.md); the live threads are
[`docs/next-session.md`](docs/next-session.md).

## Licence and provenance

Results due to others are attributed in the module docstring of the file that
formalises them — Fairtlough–Mendler for PLL itself, Curry's problem, and the
completeness theorems; Mendler for the timing reading; Iemhoff for `G3iLL` and
`G4iLL`; Fiorentini–Ferrari for the refutation calculi; Lindley–Stark for the
⊤⊤-lifting. Everything else, including the `G4iLL` refutation and the repaired
calculus, is this development's own.
