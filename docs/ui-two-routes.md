# Uniform interpolation: the two live routes, and where each one bites

*Written 2026-08-08, after `docs/lax-logic-interpolation-handoff.md` reopened
the question. Companion to `docs/next-session.md` §1 (which records why the
nine-round campaign was shelved) and `docs/calculus-map.md` (which says which
calculus each claim is about). Nothing here is mechanised unless it says so.*

---

## 0. What changed

The handoff proposes a polarised/focused route. Separately, work on 2026-08-07
identified the ∨-free fragment of PLL with the **bounded nuclear implicative
semilattices** of Bezhanishvili–Bezhanishvili–Carai–Gabelaia–Ghilardi–Jibladze
(arXiv:2001.11060), and that paper's main theorem is that the variety is
**locally finite** (their Thm 6.18 for `NIS`, Thm 7.12 for the bounded case).

Putting those together splits uniform interpolation into two halves of very
unequal difficulty. That split is the main content of this note.

---

## 1. The split: `∃p` is free, `∀p` is the whole problem

Fix a finite set of variables. Write `L` for the ∨-free fragment (formulas
built from `⊥`, `∧`, `⊃`, `◯`; no `∨`), and `L_p` for its `p`-free part.

**`∃p φ` exists for ∨-free `φ`, by local finiteness.** By the handoff's
definition, `∃p φ` is the weakest `p`-free formula that `φ` entails — the
`p`-free summary of the antecedent. Consider

> `S = { ψ ∈ L_p : φ ⊢ ψ }`, taken up to interderivability.

By local finiteness of bounded NIS, `L_p` is **finite**, so `S` is finite.
Its conjunction `χ = ⋀S` is again `p`-free and again ∨-free, `φ ⊢ χ`, and
every `p`-free consequence of `φ` follows from `χ`. So `χ` *is* `∃p φ`, and it
exists for the reason that there are only finitely many candidates. No
construction, no proof search, no interpolation machinery.

**`∀p φ` is not free, and the obstruction is exactly `∨`.** `∀p φ` is the
strongest `p`-free formula *entailing* `φ` — dually, a **join** over
`{ ψ ∈ L_p : ψ ⊢ φ }`. That set is finite too, but a finite join is not a
∨-free formula: the ∨-free fragment is an *implicative semilattice*, which has
meets and residuals but **no joins**. Erné's framework says the same thing from
the algebraic side — `𝔠a = ↑a` is a nuclear range only in lattices
(*Nuclear ranges in implicative semilattices*, Prop. 5.5).

So the ∨-free fragment is **not self-contained for uniform interpolation**: it
supplies `∃p` for free and cannot express `∀p`. That is a clean statement of
where the difficulty actually lives, and it is not where the nine-round
campaign was looking.

**Why this is more than bookkeeping.** It matches everything else found in the
closed fragment on 2026-08-07: RN(◯,{}) is infinite but its ∨-free part has
exactly eight elements; the booleanization `𝔟⊥` has exactly four; adding a
nucleus preserves local finiteness for `∧,⊃` and destroys it for `∧,∨,⊃`
already at zero generators. In every one of these, **`∨` is the source of the
infinitude**. The conjecture this suggests is that `∨` is also the source of
the interpolation difficulty, and that `◯` — long treated as the villain — is
not.

### What to do with it

1. **Check the `∃p` argument properly.** It is three lines of algebra on top of
   someone else's theorem, which is exactly the shape of claim this project has
   been burned by (`docs/llm-formalisation-case-study.md`: the failures were
   *statement* failures). Machine-check it, or find the reason it is wrong.
2. **State the residue.** If `∃p` is free, uniform interpolation for PLL
   reduces to the existence of `∀p`, i.e. to expressing certain finite joins.
   That is a much smaller target than the general problem.
3. **PCLL as the fallback is now motivated, not merely optimistic.** PCLL adds
   `◯(A∨B) ⊃ (◯A∨◯B)` and is complete for mutually confluent models
   (`derivU_iff_confluent_valid`). Since the difficulty has been localised at
   `∨`, an axiom governing `◯` *over* `∨` is aimed at the right thing.

---

## 2. The polarised route: what is settled and what is not

Verified 2026-08-08, machine-checked parts in `wip/polarity.lean`.

* `◯` is **negative** in the two-judgment Pfenning–Davies setting, as the Twelf
  `lax-logic` development declares (`circ : prop pos → prop neg`). Its `circR`
  is invertible because the premise is `P lax`, not `P true`.
* In our **single-judgment** `SC`/`LaxND` the corresponding inversion
  `Γ ⊢ ◯A ⟹ Γ ⊢ A` is **false** (`box_right_not_invertible`, `[propext,
  Quot.sound]`). So the negative assignment is bought entirely by the second
  judgment. Polarities cannot be painted onto the existing calculus; the
  two-judgment structure has to be adopted first.
* `◯`-left inversion **is** available unrestricted in the succedent, via the
  unit (`box_left_invertible`, `[propext]`). So `SC`'s `laxL` goal-restriction
  is a property of the rule, not a semantic necessity.
* The handoff's "real monster" — `◯`-left firing only when the goal is
  `◯`-shaped — becomes, in the target, `circL`'s succedent being `A lax`. A
  condition on the **shape of the succedent formula** becomes a condition on
  **which judgment we are in**, and a judgment is what a focusing phase
  tracks. This is the mechanism by which polarisation could dissolve the
  entanglement.
* `circL` **retains** `◯P` in its premise, exactly as `G4c`'s three retention
  repairs do. The "contraction by the back door" is already present, and
  already tamed, in the target.

**Caveats on the references.** Twelf proves cut admissibility in the target,
**not** focusing completeness. Simmons's *Structural focalization* covers
propositional **intuitionistic** logic only — no modality — and the part he
calls his major contribution is *identity expansion*, which is therefore the
part most likely to be the work. **None of the three references concerns
interpolation**; step 3 of the handoff's programme has no precedent in them.

---

## 3. Matthew's contraction-bound route (2026-08-08)

> Can one determine, purely by inspecting the antecedent, a bound on the number
> of contractions needed in backwards search? If so, pre-expand the antecedent
> by that many duplicates and prove uniform interpolation for the expanded
> antecedent.

This attacks the handoff's core diagnosis head-on. The diagnosis was that
contraction tracking is **proof-dependent**, which is what uniform
interpolation forbids. A bound computed from the antecedent alone is
**proof-independent** by construction, so if it exists the objection
evaporates.

**What is already known.** The separating sequent
`◯((◯p→r)→◯p), ◯p→r ⇒ r` needs exactly **2** copies of `◯p→r`
(`PLLG4Gap.lean`); the naive tower also needs only 2 (`PLLG4Tower.lean`).
Whether any sequent needs **3** is open, and is HANDOFF §7 item 5 — the
multiplicity-3 hunt, untouched since it was written.

**Why the bound should track `◯`, not size.** `G4c` is a *localization*
result: all contraction that remains lives in the `◯`-rules, absorbed by the
three retention repairs (`docs/calculus-map.md`). So the natural conjecture is

> `mult(Γ) ≤ f(number of ◯-occurrences in Γ)`,

not a function of `|Γ|`. The cheapest possible version, consistent with all
present evidence, is `mult(Γ) ≤ 2` outright.

**The stake.** If `mult` is computable from `Γ`, pre-expansion yields a
terminating analytic calculus in which no contraction is needed. That is close
to a refutation of Howe's conjecture that lax logic admits no contraction-free
calculus — a conjecture this repository has so far *supported* (HANDOFF §4;
`PLLG4Gap` shows contraction is inadmissible in Iemhoff's `G4iLL`, which is the
evidence *for* Howe). So the route is not a safe fallback: it is a bet against
a standing conjecture, and its failure would be informative in its own right.

**First move, and it is cheap.** Run the multiplicity-3 hunt. It is a decider
sweep with existing tooling and it either produces a witness (bound is not 2,
and we learn what drives it) or a documented negative sweep (evidence that 2
suffices, which would make the whole route immediate).

---

## 4. Suggested order

1. **Machine-check the `∃p`-from-local-finiteness argument** (§1). Cheapest,
   and it either halves the problem or exposes a statement error early.
2. **Multiplicity-3 hunt** (§3). Cheap, uses existing tooling, settles whether
   the contraction-bound route starts at `2`.
3. **Polarised syntax, two judgments, translation, cut admissibility** (§2) —
   the Twelf port. This is the first substantial build.
4. **Identity expansion** for the focused lax system. The risk.
5. **Interpolant by recursion on phases.** No precedent; only attempt after 3
   and 4.

Steps 1 and 2 are days; 3 is a session or two; 4 and 5 are the research.

---

## 5. Standing constraints that apply here

* The machine-checked mandate: anything in §1 or §3 that is to stand in a paper
  needs a `sorry`-free Lean proof with a pinned `#print axioms`. The arguments
  above are **prose**, and §1 in particular is exactly the kind of short
  algebraic claim that has misled this project before.
* `lake build` does **not** check `wip/`; use `lake build wipshared`
  (`docs/belief-mechanisation-index.md`).
* Do not claim Howe refuted, or PLL-UI settled either way, anywhere
  (HANDOFF §8).
