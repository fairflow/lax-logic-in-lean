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
claim names the Lean file and theorem that establishes it, and is tagged
**PROVED** (machine-checked), **REFUTED** (with an explicit witness), or **OPEN**.

The formalisation turned up two genuine problems in the G4iLL route to uniform
interpolation, plus one purely local slip in the soundness proof of the
interpolant assignment. It also confirms the positive core: Craig interpolation
for PLL goes through cleanly, and a small repair of G4iLL restores exactly the
calculus your programme needs. None of this is offered as anything other than
the ordinary business of mechanisation, which is good at finding the places
where a paper proof and a machine disagree.

Throughout, $\bigcirc$ is the lax modality of Fairtlough–Mendler PLL
($\bigcirc A$ = "$A$ holds subject to some constraint"), the strong monad of the
logic; it is the modality your papers write as a circle (rendered `#` in the OCR
of the arXiv source, which I have normalised to $\bigcirc$ in the quotations
below). All sequents are single-succedent.

---

## 1. The headline findings

1. **G4iLL is not complete for PLL.** There is a sequent that is PLL-derivable
   (and derivable in G3iLL) but not derivable in G4iLL. Hence Corollary 1 of
   arXiv:2209.08976 — G3iLL and G4iLL are equivalent — is false as stated.
2. **Cut and contraction are not admissible in G4iLL.** Both are refuted by
   explicit witnesses. In particular Fact 3 ("G4iLL is a balanced calculus")
   fails, since balancedness requires cut-admissibility.
3. **A separate, local flaw** sits inside the soundness proof of the interpolant
   assignment: Lemma 7, case (DPN) for the $L\bigcirc$ rule, first subcase. The
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

Write
$$F' \;:=\; \bigcirc p \supset r, \qquad G' \;:=\; F' \supset \bigcirc p \;=\; (\bigcirc p \supset r)\supset \bigcirc p .$$
The separating sequent is
$$\bigcirc G',\; F' \;\Rightarrow\; r
\qquad\text{i.e.}\qquad
\bigcirc\big((\bigcirc p \supset r)\supset \bigcirc p\big),\;\; \bigcirc p \supset r \;\Rightarrow\; r .$$

**PROVED** that it is derivable in G3iLL: `PLLG4Gap.sep_SC`
(`LaxLogic/PLLG4Gap.lean`). It is PLL-valid: bind on $\bigcirc G'$; inside the
box-opening $G'$ together with a *second* use of the hypothesis $F'$ yields
$\bigcirc p$; so $\bigcirc p$ holds outright, and $F'$ then gives $r$. The G3
derivation uses $F'$ twice — once inside the `laxL` box-opening, once as the
final implication.

**REFUTED** that it is derivable in G4iLL: `PLLG4Gap.sep_not_G4`. This is a
kernel-checked explicit proof term (axiom audit: `propext` only — no choice, no
quotients, and in particular no trusted compiled evaluation), independent of the
verified decision procedure, which returns the same `false` verdict. The reason
proof search fails is exactly the retention issue. Your two $\bigcirc$-implication
rules $R\bigcirc\!\to$ and $L\bigcirc\!\to$ *consume* their principal implication:
$L\bigcirc\!\to$ reuses the box across its two premises but discards the
implication, and its first premise here is $G' \Rightarrow \bigcirc p$, which is
invalid. No G4iLL rule instance retains the copy of $F'$ that the G3 proof spends
a second time inside the box, so every branch of the search fails. (This is
Howe's duplication phenomenon, MSCS 2001, one level up: the formula needing
contraction is the $\bigcirc$-antecedent implication itself, straddling a
box-opening.) A constant-only variant with $F=\bigcirc\bot\supset\bot$,
$G=F\supset\bigcirc\bot$ separates the calculi in the same way, so the phenomenon
does not depend on the atom $p$.

Packaged statement: `PLLG4Gap.sc_but_not_G4` proves the conjunction
$\;\mathrm{SC}\,[\bigcirc G', F']\,r \,\wedge\, \neg\,\mathrm{G4}\,[\bigcirc G', F']\,r$.

**Consequence.** Corollary 1 of arXiv:2209.08976 (book Cor. 8.1) —
*"G3iLL and G4iLL are equivalent and the structural rules are admissible in
both"* — is **REFUTED**. The modal case of the general G4-analogue theorem it
invokes (Theorem 1 of *The G4i analogue of a G3i calculus*, arXiv:2011.11847)
fails at exactly the expected spot: the premises $S_i$ carry an extra copy of
$\bigcirc\varphi\to\psi$, so the order condition $S_i \ll S$ does not hold and the
copy cannot be dropped. Since Fact 3 ("G4iLL is balanced") is justified in the
paper "using Fact 2 and Corollary 1," and Theorem 5 (the interpolation engine
imported from *Uniform interpolation and the existence of sequent calculi*, APAL
2019) requires a balanced calculus, the completeness premise of the Theorem 5 →
Theorem 6 chain (book Thm 8.6, "PLL has uniform interpolation") is not
established by the argument as given.

---

## 3. Cut and contraction are not admissible in G4iLL

Both structural rules fail on the same family, and each failure is a plain pair
of explicit derivations plus the underivability of §2.

**Cut — REFUTED** (`PLLG4Gap.cut_not_admissible`). The cut formula is
$\bigcirc p$:
$$\underbrace{\bigcirc G',\,F' \;\Rightarrow\; \bigcirc p}_{\texttt{cut\_left\_G4}}
\qquad
\underbrace{\bigcirc p,\;\bigcirc G',\,F' \;\Rightarrow\; r}_{\texttt{cut\_right\_G4}}
\qquad\Longrightarrow\qquad
\bigcirc G',\,F' \;\Rightarrow\; r .$$
Both premises are G4iLL-derivable (proof terms given); the conclusion is the
underivable sequent of §2.

**Contraction — REFUTED** (`PLLG4Gap.contraction_not_admissible`). With two
copies of $F'$ the sequent becomes derivable — one copy consumed by
$L\bigcirc\!\to$ outside the box, the other inside the box-opening:
$$\bigcirc G',\,F',\,F' \;\Rightarrow\; r \quad\text{(derivable)}
\qquad\text{but}\qquad
\bigcirc G',\,F' \;\Rightarrow\; r \quad\text{(not derivable).}$$

Both witnesses have a clean axiom audit (`propext` only). Contraction-failure is,
in effect, the hypothesis that a corrected balancedness claim would have to add;
cut-failure directly contradicts Fact 3.

---

## 4. A local flaw in the soundness proof: Lemma 7, $(\mathrm{DPN})\text{-}L\bigcirc$, first case

This point is independent of §§2–3: it is a slip in the induction of Lemma 7
(soundness of the interpolant assignment for the modal and implication-modal
rules), and it would need attention even in a calculus where cut *were*
available.

Recall the setup. For the $L\bigcirc$ rule the last inference is
$S_1=(\Gamma,\psi\Rightarrow\bigcirc\varphi)$ over $S=(\Gamma,\bigcirc\psi\Rightarrow\bigcirc\varphi)$.
For a partition whose $i$-part $S^i$ is non-principal for $L\bigcirc$, the paper
splits into two cases, $S^i=(\Gamma^i\Rightarrow\bigcirc\varphi)$ and
$S^i=(\Gamma^i\Rightarrow\ )$, and states the two obligations:

> "We have to show that $\vdash \Gamma^r,\bigcirc\psi,\exists p S^i \Rightarrow \forall p S^i$
> in the first case, and $\vdash \Gamma^r,\bigcirc\psi,\exists p S^i \Rightarrow \bigcirc\varphi$
> in the second case."

The first-case target therefore has succedent $\forall p S^i$. But the derivation
supplied is:

> "If $S^i=(\Gamma^i\Rightarrow\bigcirc\varphi)$, we have
> $\vdash \Gamma^r,\psi,\exists p S_1^i \Rightarrow \bigcirc\varphi$ by the induction
> hypothesis. An application of $L\bigcirc$ gives
> $\vdash \Gamma^r,\bigcirc\psi,\exists p S_1^i \Rightarrow \bigcirc\varphi$, and since
> $S_1^i=S^i$, this is what we had to show."

*(Quoted from the proof of Lemma 7, arXiv:2209.08976v1; the lax modality is
rendered $\bigcirc$ and the derivability decoration $\mathcal{D}^p_R$ written
$\vdash$.)*

The sequent actually derived,
$$\Gamma^r,\;\bigcirc\psi,\;\exists p S^i \;\Rightarrow\; \bigcirc\varphi,$$
is the *second* case's sequent — its succedent is $\bigcirc\varphi$, not the
first case's required $\forall p S^i$:
$$\Gamma^r,\;\bigcirc\psi,\;\exists p S^i \;\Rightarrow\; \forall p S^i .$$
So the step closes the wrong obligation. The gap cannot be closed by an
$L\bigcirc$ instance: $L\bigcirc$ fires only under a $\bigcirc$-shaped succedent,
whereas $\forall p S^i$ is by definition a disjunction
$\forall^{+}pS^i \vee \forall^{-}pS^i \vee \forall^{\mathrm{at}}pS^i$, not of the
form $\bigcirc\varphi$. Nor does any disjunct of $\forall p S^i$ anticipate a
succedent-side box in this situation: the $L\bigcirc$/$\gamma$-disjuncts range
over antecedent-side boxes and implications ($\bigcirc\alpha\to\beta\in\Gamma^i$),
and the $R\bigcirc$-disjunct $\bigcirc\forall p(\Gamma^i\Rightarrow\varphi)$ would
require an induction hypothesis at $(\Gamma,\psi\Rightarrow\varphi)$, which a
derivation ending in $L\bigcirc$ does not supply.

**Status: REFUTED as a proof step**, and machine-locatable
(`wip/g4ill_ui.lean`, the `(DPN)`-$L\bigcirc$ first case, isolated with the
target and the derived sequent both displayed). One should add that this is not
obviously repaired by extending the $\forall p S$ table: the natural repairing
disjunct is a box-goal clause that recurses at the *same* sequent (a self-
reference), which the Dershowitz–Manna order underlying your Fact 1/2
termination does not permit. So a table extension at this point would break the
recursion's termination guarantee — the flaw and the completeness gap of §2 are
thus complementary rather than one and the same error.

We should stress that the flaw appears to be in the *proof*, not the
*statements*. Since `G4`-derivability is decidable and both interpolants are
computable, the lemma's claims can be checked instance by instance. A systematic
sweep (repository file `wip/g4ill_probe.lean`) decided roughly 2,550 instances
of the soundness statements — including 1,080 instances of the $L4\to$ conjunct
of §5 and every decided instance of the $(\mathrm{DPN})\text{-}L\bigcirc$ family
above, among them the exact shape on which the printed proof breaks — and found
**no counterexample**: in each decided case the required `G4`-derivation exists
(typically taking the $R\bigcirc$-disjunct *before* opening the box, i.e. in a
different order than the printed induction). A few large instances remained
undecided within the search budget, so this is evidence rather than a theorem;
but the natural conjecture is that Lemma 7's statement is true of G4iLL and
only its inductive proof needs repair. **Status: OPEN, with instance-level
evidence in favour.**

---

## 5. The $L4\!\to$ interpolant: a second, independent deviation

A related but separate observation concerns the $\exists$-assignment for the
$L4\!\to$ rule
$$\frac{\Gamma,\psi\to\gamma\Rightarrow\varphi\to\psi \qquad \Gamma,\gamma\Rightarrow\Delta}
{\Gamma,(\varphi\to\psi)\to\gamma\Rightarrow\Delta},$$
for which the assignment (standard assignment, APAL 2019 §5) sets
$$\iota\exists^R p S \;=\; \exists p S_1 \;\wedge\; (\forall p S_1 \to \exists p S_2).$$
The soundness of the *first conjunct* $\exists p S_1$ — the property (IPP) that
$\Gamma \vdash \exists p S_1$ — is argued (APAL 2019, p. 26) via the "obvious fact
that $\vdash \bigwedge S^a \to \bigwedge S_1^a$" followed by replacing the context
along that derivable implication. That replacement is a *composition of
derivabilities* — a cut — and cut is not available in G4iLL (§3). The premise-1
context $B\to D,\;\Gamma\setminus F$ is not reachable from $\Gamma$ by any G4iLL
rule without changing the goal (the governing $L4\!\to$ instance forces the goal
$\varphi\to\psi$), so no induction hypothesis supplies it either.

By contrast, Pitts's guarded shape for the corresponding rule — the conjunct in
the form $(E(S_1)\to A(S_1)) \to E(D,\Gamma\setminus F)$ rather than a bare
$E(S_1)$ — **is** derivable cut-free in G4iLL. This was machine-checked
(`wip/g4ill_ui.lean`, the $L4\!\to$ case of the soundness pass: fire the retained
$L\bigcirc$-style implication rule and discharge the guard with an in-context,
consumed-form modus ponens). **PROVED** that the guarded clause is cut-free
sound; the assignment as printed deviates from Pitts's guarded shape, and that
deviation is what costs the (IPP) argument its cut. This is therefore a second,
independent point at which the assignment (rather than the calculus) would want
revisiting.

---

## 6. What survives, and the positive core

**Craig interpolation for PLL — PROVED** (`LaxLogic/PLLCraig.lean`:
`craig_interpolation`, `craig_implication`). Maehara's method over the cut-free
complete calculus `SC` yields, from a derivation of $\Gamma_1,\Gamma_2 \vdash C$,
an interpolant $I$ with $\Gamma_1\vdash I$, $I,\Gamma_2\vdash C$, and every atom
of $I$ shared between $\Gamma_1$ and $\Gamma_2,C$. Because `SC` is proved
equivalent to natural deduction / the term calculus in the repository, this is
Craig interpolation for PLL. The construction is the textbook intuitionistic one
with exactly one lax-specific move: when the principal formula of the
$\bigcirc$-left rule lies in $\Gamma_1$, box the premise interpolant, $I \mapsto
\bigcirc I$. Boxing is forced — to derive $\Gamma_1\vdash \bigcirc I$ one opens
the boxed antecedent under a now-$\bigcirc$-shaped goal, and $\bigcirc I,
\Gamma_2 \vdash \bigcirc B$ opens $\bigcirc I$ under the $\bigcirc$-shaped
end-formula. Axiom audit: Lean's standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`); no `sorry`, no compiled evaluation.

**A repaired G4iLL — PROVED complete and structural.** The one-token repair
suggested by §2 is to let three rules retain their principal formulas rather than
consume them: the first premise of $L\bigcirc\!\to$ keeps its implication
(cf. the $\to_{SL}$ rule of van der Giessen–Iemhoff's G4iSL, whose first premise
likewise retains its principal), and — as writing the admissibility proofs
revealed was also necessary — the box rules keep their box and $R\bigcirc\!\to$
keeps its context. The resulting calculus (here `G4c`, `LaxLogic/PLLG4H*.lean`)
is proved **complete for PLL** and slots into the equivalence chain
$$\mathrm{G4c} \;=\; \mathrm{SC} \;=\; \text{natural deduction} \;=\; \text{term calculus}$$
(`PLLG4HComp.lean`: `completeness`, `equiv_sc`, `equiv_nd`, `equiv_tm`), with
**cut admissible** (`PLLG4HCut.lean`) and **contraction admissible**. So the
calculus your programme needs — a contraction-free, structurally well-behaved
G4-style presentation of PLL — does exist; it is your G4iLL with these three
retentions.

**Uniform interpolation for PLL — OPEN in the formalisation.** With the tables
transcribed faithfully and read relative to derivability, essentially all of the
construction is machine-checked (p-freeness, both independent interpolant
properties bar the §5 conjunct, and the adequacy commutations for the axioms,
all right rules, and the box rules) — except for a single stabilization lemma,
for which three systematic finite-countermodel searches turned up no
counterexample but which is not yet proved. The overall statement "PLL has
uniform interpolation" is thus neither established nor refuted here; the honest
status is one outstanding lemma.

---

## 7. Closing

I hope this is read in the spirit intended: mechanisation is unusually good at
locating the exact sequents where a hand proof and a proof assistant part
company, and the separating sequent of §2 is a small and, I think, genuinely
interesting one. The substantive corrections are two — the incompleteness of
G4iLL (with the attendant failure of Corollary 1, Fact 3, and the completeness
premise of the Theorem 5–6 chain) and the local $L\bigcirc$ slip in Lemma 7 —
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
| Soundness of assignment (local flaw) | Lemma 7, $(\mathrm{DPN})\text{-}L\bigcirc$ | — |

† Book-chapter numbers are the correspondences recorded in the repository's
transcription notes; the arXiv numbers in the left column were each checked
against the arXiv source text, the book numbers were not independently verified
against a book PDF here.
