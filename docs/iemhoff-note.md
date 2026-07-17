# Notes on the uniform-interpolation development for Propositional Lax Logic

*Draft — for M. Fairtlough to review and, if he judges it useful, to send.*

This note records some findings from a machine-checked formalisation, in Lean 4,
of Propositional Lax Logic (PLL) and of the sequent calculi used in your
*Proof Theory for Lax Logic* (arXiv:2209.08976v1; the book chapter of the same
title). The formalisation covers PLL as a natural-deduction/term calculus, the
single-succedent G3-style calculus (here `SC`, your G3iLL) and the
contraction-free calculus `G4` (your G4iLL, transcribed from Fig. 2.3), together
with a verified decision procedure for `G4`-derivability. Everything referred to
below is in the public repository `github.com/fairflow/lax-logic-in-lean`; each
claim names the Lean file and theorem that establishes it, and is marked as
proved (machine-checked), refuted (with an explicit witness), or open.

The formalisation turned up two genuine problems in the G4iLL route to uniform
interpolation, plus one purely local slip in the soundness proof of the
interpolant assignment. It also confirms the positive core: Craig interpolation
for PLL goes through cleanly, and a small repair of G4iLL restores exactly the
calculus your programme needs. None of this is offered as anything other than
the ordinary business of mechanisation, which is good at finding the places
where a paper proof and a machine disagree.

Throughout, ◯ is the lax modality of Fairtlough–Mendler PLL (◯A = "A holds
subject to some constraint"), the strong monad of the logic; it is the modality
your papers write as a circle (rendered `#` in the OCR of the arXiv source,
which I have normalised to ◯ in the quotations below). All sequents are
single-succedent.

---

## 1. The headline findings

1. **G4iLL is not complete for PLL.** There is a sequent that is PLL-derivable
   (and derivable in G3iLL) but not derivable in G4iLL. Hence Corollary 1 of
   arXiv:2209.08976 — G3iLL and G4iLL are equivalent — is false as stated.
2. **Cut and contraction are not admissible in G4iLL.** Both are refuted by
   explicit witnesses. In particular Fact 3 ("G4iLL is a balanced calculus")
   fails, since balancedness requires cut-admissibility.
3. **A separate, local flaw** sits inside the soundness proof of the interpolant
   assignment: Lemma 7, case (DPN) for the L◯ rule, first subcase. The
   derivation given closes the *wrong* sequent.
4. **Craig interpolation for PLL holds** (Maehara's method over the cut-free
   calculus), machine-checked.
5. **A minimally repaired G4iLL exists** — three rules retain their principal
   formulas — and is proved complete for PLL, with cut and contraction
   admissible and equivalent to natural deduction. So the target calculus your
   argument wants does exist; uniform interpolation for PLL itself remains open
   in the formalisation (one lemma outstanding).

---

## 2. G4iLL is incomplete for PLL

Write F′ := ◯p ⊃ r and G′ := F′ ⊃ ◯p = (◯p ⊃ r) ⊃ ◯p. The separating
sequent is ◯G′, F′ ⇒ r.

Proved derivable in G3iLL (`PLLG4Gap.sep_SC`, `LaxLogic/PLLG4Gap.lean`):
bind on ◯G′; a second use of F′ inside the `laxL` box-opening turns G′
into ◯p, so ◯p holds outright, and F′ gives r as the final implication.

Refuted in G4iLL (`PLLG4Gap.sep_not_G4`): a kernel-checked proof term
(axiom audit `propext` only, no choice or quotients, no compiled
evaluation), agreeing with the decision procedure's `false` verdict. The
cause is retention: your L○→ (like R○→) consumes its principal implication, so
its first premise here, G′ ⇒ ◯p, is invalid, and no rule instance keeps
the second copy of F′ the G3 proof needs inside the box — every branch
fails. This is Howe's duplication phenomenon (MSCS 2001) one level up:
the formula needing contraction is the ◯-antecedent implication itself,
straddling a box-opening. A constant-only variant, F = ◯⊥ ⊃ ⊥,
G = F ⊃ ◯⊥, separates the calculi the same way, so this is not about the
atom p.

Packaged: `PLLG4Gap.sc_but_not_G4` proves `SC` derives ◯G′, F′ ⇒ r while
`G4` does not.

**Consequence.** Corollary 1 — "G3iLL and G4iLL are equivalent and the
structural rules are admissible in both" — is refuted: the general
theorem it invokes (Theorem 1 of *The G4i analogue of a G3i calculus*,
arXiv:2011.11847) fails in exactly its modal case, since the premises
S_i here carry an extra copy of ◯φ→ψ, so S_i ≪ S fails and the copy
cannot be dropped. Fact 3 ("G4iLL is balanced") rests on Fact 2 and
Corollary 1; Theorem 5 — the interpolation engine of *Uniform
interpolation and the existence of sequent calculi* (APAL 2019) — needs a
balanced calculus, so the Theorem 5 → 6 chain ("PLL has uniform
interpolation") is not established as given.

---

## 3. Cut and contraction are not admissible in G4iLL

Both fail on the same family, each an explicit derivation pair plus the
underivability of §2.

**Cut.** Refuted (`PLLG4Gap.cut_not_admissible`) on cut formula ◯p:
`cut_left_G4` derives ◯G′, F′ ⇒ ◯p and `cut_right_G4` derives ◯p, ◯G′,
F′ ⇒ r, both G4iLL-derivable, but cutting them gives the underivable
sequent of §2, ◯G′, F′ ⇒ r.

**Contraction.** Refuted (`PLLG4Gap.contraction_not_admissible`): two
copies of F′ make the sequent derivable — one consumed by L○→ outside the
box, the other inside it — but one copy does not: ◯G′, F′, F′ ⇒ r holds
while ◯G′, F′ ⇒ r does not.

Both witnesses have a clean axiom audit (`propext` only). Contraction
failure is what a corrected balancedness claim would need to add; cut
failure directly contradicts Fact 3.

---

## 4. A local flaw in the soundness proof: Lemma 7, (DPN)-L○, first case

Independent of §§2–3, and not fixed by restoring cut: a slip in the
induction of Lemma 7 (soundness of the interpolant assignment).

**Setup.** For the L○ rule the last inference is S_1 = (Γ, ψ ⇒ ◯φ) over
S = (Γ, ◯ψ ⇒ ◯φ). For an i-part S^i non-principal for L○, the paper
splits into two cases — S^i = (Γ^i ⇒ ◯φ), or S^i = (Γ^i ⇒) with empty
succedent — with two obligations:

> "We have to show that ⊢ Γ^r, ◯ψ, ∃p S^i ⇒ ∀p S^i in the first case,
> and ⊢ Γ^r, ◯ψ, ∃p S^i ⇒ ◯φ in the second case."

So the first case's target has succedent ∀p S^i. But the derivation given
is:

> "If S^i = (Γ^i ⇒ ◯φ), we have ⊢ Γ^r, ψ, ∃p S_1^i ⇒ ◯φ by the induction
> hypothesis. An application of L○ gives ⊢ Γ^r, ◯ψ, ∃p S_1^i ⇒ ◯φ, and
> since S_1^i = S^i, this is what we had to show."

*(Lemma 7's proof, arXiv:2209.08976v1; lax modality rendered ◯, the
derivability decoration D^p_R written ⊢.)*

That is the *second* case's sequent, not the first case's ∀p S^i, so it
closes the wrong obligation — and no L○ instance can close the right one:
L○ needs a ◯-shaped succedent, but ∀p S^i is by definition
∀^+p S^i ∨ ∀^-p S^i ∨ ∀^at p S^i, never ◯-shaped, and no disjunct
anticipates a succedent-side box — the L○/γ-disjuncts range over
antecedent-side boxes and implications (◯α→β ∈ Γ^i), while the
R○-disjunct ◯∀p(Γ^i ⇒ φ) needs an induction hypothesis at (Γ, ψ ⇒ φ)
that a derivation ending in L○ lacks.

**Status.** Refuted as a proof step, machine-locatable
(`wip/g4ill_ui.lean`, the (DPN)-L○ first case). Not an easy fix: the
natural repair — a box-goal clause recursing at the *same* sequent — is a
self-reference the Dershowitz–Manna order behind your Fact 1/2
termination forbids, so this would break termination. The flaw and the §2
completeness gap are complementary, not the same error.

The flaw looks to be in the *proof*, not the *statement*: `G4`-derivability
is decidable and both interpolants computable, so the lemma's claims are
checkable instance by instance. A sweep (`wip/g4ill_probe.lean`) decided
roughly 2,550 instances of the soundness statements — including 1,080 of
the L4→ conjunct of §5, and every decided (DPN)-L○ instance, including
the exact breaking shape — and found *no counterexample*: the required
`G4`-derivation always exists. A few large instances remain undecided, so
this is evidence, not a theorem; the natural conjecture is that Lemma 7
holds of G4iLL and only its proof needs repair. **Status.** Open, with
instance-level evidence in favour.

---

## 5. The L4→ interpolant: a second, independent deviation

A related but separate issue concerns the ∃-assignment for the L4→ rule:

```
  Γ, ψ→γ ⇒ φ→ψ    Γ, γ ⇒ Δ
  ────────────────────────── L4→
     Γ, (φ→ψ)→γ ⇒ Δ
```

for which the standard assignment (APAL 2019 §5) sets ι∃^R p S = ∃p S_1 ∧
(∀p S_1 → ∃p S_2).

Soundness of the *first conjunct*, ∃p S_1 — property (IPP), that
Γ ⊢ ∃p S_1 — is argued (APAL 2019, p. 26) from the "obvious fact that
⊢ ⋀S^a → ⋀S_1^a," replacing the context along that derivable implication.
That replacement is a composition of derivabilities — a cut — and cut is
unavailable in G4iLL (§3); nor does induction supply it, since the
premise-1 context B→D, Γ∖F is not reachable from Γ by any G4iLL rule
without changing the goal, which the L4→ instance fixes at φ→ψ.

By contrast, Pitts's guarded shape for the same conjunct —
(E(S_1)→A(S_1)) → E(D, Γ∖F) rather than bare E(S_1) — is derivable
cut-free in G4iLL (machine-checked, `wip/g4ill_ui.lean`: fire the
retained L○-style implication rule, discharge the guard by an
in-context, consumed-form modus ponens). It is the printed assignment's
deviation from this guarded shape that costs the (IPP) argument its cut —
a second, independent point where the assignment, not the calculus,
wants revisiting.

---

## 6. What survives, and the positive core

**Craig interpolation for PLL.** Proved (`LaxLogic/PLLCraig.lean`:
`craig_interpolation`, `craig_implication`), via Maehara's method over
the cut-free calculus `SC` (proved equivalent to natural deduction and
the term calculus): from a derivation of Γ_1,Γ_2 ⊢ C it yields an
interpolant I with Γ_1 ⊢ I, I,Γ_2 ⊢ C, and every atom of I shared between
Γ_1 and Γ_2,C. The construction is the textbook intuitionistic one plus
one lax-specific move: when the ◯-left rule's principal formula lies in
Γ_1, box the premise interpolant, I ↦ ◯I — forced, since Γ_1 ⊢ ◯I opens
the boxed antecedent under a now-◯-shaped goal, and ◯I, Γ_2 ⊢ ◯B (the
end-formula is necessarily of this shape for the ◯-left rule to apply)
opens ◯I under the ◯-shaped end-formula. Axiom audit: Lean's standard axioms
only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no
compiled evaluation.

**A repaired G4iLL.** Proved complete and structural: the one-token
repair from §2 lets three rules retain their principal formulas rather
than consume them — L○→'s first premise keeps its implication (compare
→SL of van der Giessen–Iemhoff's G4iSL, whose first premise likewise
retains its principal), and, as the admissibility proofs also required,
the box rules keep their box and R○→ keeps its context. The result
(`G4c`, `LaxLogic/PLLG4H*.lean`) is proved complete for PLL, slotting
into G4c = SC = natural deduction = term calculus (`PLLG4HComp.lean`:
`completeness`, `equiv_sc`, `equiv_nd`, `equiv_tm`), with cut
(`PLLG4HCut.lean`) and contraction admissible. So the calculus your
programme needs does exist: your G4iLL with these three retentions.

**Uniform interpolation for PLL.** Open in the formalisation. With the
tables transcribed faithfully, essentially all of it is machine-checked
(p-freeness, both independent interpolant properties bar the §5
conjunct, and the adequacy commutations for the axioms, all right rules,
and the box rules) except a single stabilization lemma: three systematic
finite-countermodel searches found no counterexample, but it is not yet
proved. "PLL has uniform interpolation" is thus neither established nor
refuted here; the honest status is one outstanding lemma.

---

## 7. Closing

I hope this is read in the spirit intended: mechanisation is unusually good at
locating the exact sequents where a hand proof and a proof assistant part
company, and the separating sequent of §2 is a small and, I think, genuinely
interesting one. The substantive corrections are two — the incompleteness of
G4iLL (with the attendant failure of Corollary 1, Fact 3, and the completeness
premise of the Theorem 5–6 chain) and the local L◯ slip in Lemma 7 —
and the programme's positive goal is intact: Craig interpolation holds, and a
minimally repaired calculus recovers the structural properties the argument
relies on.

Every claim above is a checkable Lean statement in
`github.com/fairflow/lax-logic-in-lean`; the file and theorem names are given
inline, and M. Fairtlough can supply any of the derivations, the decision-
procedure verdicts, or the transcribed tables in whatever form is most useful.

---

### Numbering cross-reference

| Claim | arXiv:2209.08976v1 | Book chapter† |
|---|---|---|
| G3iLL ≡ G4iLL (refuted) | Corollary 1 | Corollary 8.1 |
| G4iLL balanced (refuted) | Fact 3 | — |
| Interpolation engine (balanced ⇒ UI) | Theorem 5 | — |
| PLL has uniform interpolation | Theorem 6 | Theorem 8.6 |
| Interpolant assignment (§) | §6.3–6.8 | §8.6 |
| Soundness of assignment (local flaw) | Lemma 7, (DPN)-L◯ | — |

† Book-chapter numbers are the correspondences recorded in the repository's
transcription notes; the arXiv numbers in the left column were each checked
against the arXiv source text, the book numbers were not independently verified
against a book PDF here.
