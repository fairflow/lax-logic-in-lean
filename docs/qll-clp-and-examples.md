# QLL as a framework for constraint logic programming, and how the system works

Written 2026-09-07, alongside the first-order completeness proof.  Everything
here is literature; the Lean development is referenced only where a paper bears
on a design decision we actually took.  Verification tags follow the convention
of `docs/second-order-pll-survey.md`.

## 1. The paper

> **M. Fairtlough, M. Mendler and M. Walton, "First-Order Lax Logic as a
> Framework for Constraint Logic Programming", Technical Report MIP-9714,
> University of Passau, July 1997.**
> [Authors and title **CONFIRMED** from Mendler's own publication list at
> Bamberg (`papersMM/qllclp.html`), which carries the abstract; report number,
> institution and month **SEMI-VERIFIED**, from secondary indexing.  The PDF is
> not served at that path — only the abstract page is.]

What the abstract claims, in its own terms:

* the calculus of QLL captures not only the **extensional** side of logic
  programming (which queries succeed) but the **intensional** side (*what the
  answer constraint is, and how it is built);
* the connection is a **formulas-as-programs, proofs-as-constraints**
  principle — an *intensional extension of the Curry–Howard isomorphism*
  linking derivations to answer constraints;
* QLL is an *internal* framework: "operational semantics are not differentiated
  by different axiom systems but by different rule systems", and formulas *are*
  programs rather than statements about programs;
* the monad `◯` is instantiated by a generic notion of **constraint
  computation**, which decomposes CLP into an abstract Lax-Logic-Programming
  component plus an associated **constraint table**.

### 1.1 A provenance correction

`docs/surveys/nuclei-model-completions-monads.md` calls the CLP report a
*Fairtlough–Walton* paper from Sheffield.  That conflates two distinct 1997
technical reports, both dated July:

| report | authors | number, institution |
| :-- | :-- | :-- |
| *Quantified lax logic* | Fairtlough, Walton | CS-97-11, Sheffield |
| *First-order lax logic as a framework for CLP* | Fairtlough, **Mendler**, Walton | MIP-9714, Passau |

Mendler's own publication page lists all three authors for the CLP report, so
the three-author attribution should be treated as settled and the Sheffield
line in that survey corrected.  (Semantic Scholar indexes the CLP report under
two authors, dropping Mendler; that is the likely source of the confusion.)

## 2. How the system works — worked examples from the literature

### 2.1 The one that started it: circuits as half-open intervals

*Fairtlough & Mendler, "Propositional Lax Logic", Information and Computation
137(1):1–33, 1997, §7.*  [**VERIFIED** — preprint read at Bamberg.]

This is the example to quote, because every feature of our Kripke semantics is
visible in it concretely.

A **timing diagram** `I` assigns to each atom `A` a signal `I(A) : ℕ → 𝔹`.  Cut
the time line at the instants where some signal changes; the **Leibniz
intervals** of `I` are the half-open `[s,t)` whose endpoints are such instants
(with `t = ∞` and empty `[s,s)` allowed).  The constraint model `M(I)` is then

| component | definition |
| :-- | :-- |
| worlds | the Leibniz intervals of `I` |
| `Ri` | *subinterval* |
| `Rm` | *final* subinterval — `[s,t) Rm [s',t')` iff `t = t'` and `s ≤ s'` |
| `V(A)` | the intervals on which `I(A)` is constantly 1 |
| `F` | the **empty** intervals `[s,s)` |

and Proposition 7.1 reads the modality off the waveform:

    I ⊨ A     iff  I(A) is constant 1
    I ⊨ ◯A    iff  I(A) stabilises eventually to 1
    I ⊨ ¬A    iff  I(A) is constant 0
    I ⊨ ◯¬A   iff  I(A) stabilises eventually to 0

So `◯` is "stabilises to", and the paper's own gloss on intuitionism follows:
`I ⊨ A ∨ ¬A` iff `I(A)` is **stable**.  Excluded middle is exactly the absence
of transient behaviour.

Three things this settles for our development:

* **Fallible worlds are the empty intervals.**  Not a device — the empty
  interval is a real object of the construction, and everything holds on it
  vacuously.  This is the source Matthew remembered.
* **Two relations were there from the start.**  `Ri` (subinterval) and `Rm`
  (final subinterval) are already distinct in the propositional paper.  Our
  `RA`/`RE` split refines the *modal* relation further, and the refinement is
  forced: `CompleteTests.all_not_ex` and `ex_not_all` show one relation would
  identify `◯∀` with `◯∃`.
* **The circuit models satisfy more than PLL.**  `M(I)` is confluent, so it
  validates `◯(M ∨ N) ⊃ ◯M ∨ ◯N`, which PLL does not prove.  A reminder that
  the intended models are a proper subclass — and a natural source of extra
  axioms if a "circuit fragment" is ever wanted.

### 2.2 The other complete semantics for *quantified* lax logic

*R. Goldblatt, "Cover semantics for quantified lax logic", Journal of Logic and
Computation 21(6):1035–1063, 2011.*  [**VERIFIED** — preprint read in full.]

Goldblatt proves completeness for quantified lax logic by a route entirely
different from ours, and the contrast is the most useful thing in the
literature for us right now.

| | Goldblatt | this development |
| :-- | :-- | :-- |
| base semantics | Beth–Kripke–Joyal **cover** semantics | Kripke |
| domains | a **single** domain `U` | **increasing** domains |
| `∨` | `x ⊨ φ∨ψ` iff some cover `C ▷ x` with `C ⊆ |φ| ∪ |ψ|` | disjunct at `x` |
| `∃` | some cover `C ▷ x` with `C ⊆ ⋃_c |φ(c)|` | a witness in `Dom x` |
| `∀` | Tarskian: all `c ∈ U`, at `x` | all `v ≥ x`, all `d ∈ Dom v` |
| fallible worlds | the empty-covered points `j∅`; **exactly one** suffices | an arbitrary `Fl` |
| completeness route | nucleus lifted to the MacNeille completion; locale as a cover system | saturated Lindenbaum + canonical model |

The trade is clean and worth stating in the paper: **cover semantics buys
completeness by weakening `∨` and `∃` to hold *locally*, and can then keep a
single domain.**  We kept the strong reading — an existential needs an actual
witness — and paid for it exactly where expected: increasing domains (forced
independently by `cd_not_prv`) and an ω-construction to supply the witnesses.
Neither is more correct; they answer different questions.

Two further points of direct use:

* **A cheaper Henkin construction.**  Goldblatt's §8 gives completeness for
  first-order intuitionistic logic over cover semantics with points the
  **principal theories** `φ⊢ = {ψ : φ ⊢ ψ}`, ordered by inclusion, with
  `x ◁ C` iff `x = ⋂C`.  No primeness, no saturation, no Zorn, no ω-chain.  If
  we ever want the cover-semantics variant, that is the construction to copy —
  it would make `Saturate.lean` unnecessary for that semantics.
* **"Is `◯` a box or a diamond?"**  Goldblatt poses exactly this and answers
  *neither* — under Kripke semantics `◯` has a box-like and a partly
  diamond-like modelling, and the moral is that intuitionistic modality is not
  obtained by generalising Boolean `□`/`◇`.  QLL gives the sharper answer:
  **both, and they are different modalities in one system.**  `◯∀` is the
  box-like reading, `◯∃` the diamond-like one, and our two machine-checked
  underivabilities are the proof that the calculus keeps them apart.

## 3. Folding in Pfenning

One correction first, and it makes the connection *better*, not weaker.
**λProlog is Miller and Nadathur's language.**  Pfenning's own logic-programming
language is **Elf** (and its successor **Twelf**, with Schürmann), built on the
Edinburgh Logical Framework rather than on hereditary Harrop formulas.  But
Pfenning is a co-author of the paper that gives λProlog its proof theory, and
that paper is the one that matters here:

> **D. Miller, G. Nadathur, F. Pfenning and A. Scedrov, "Uniform proofs as a
> foundation for logic programming", Annals of Pure and Applied Logic
> 51:125–157, 1991.**  [**CONFIRMED** — volume, pages, year.]

Its thesis: a logic is a *logic programming language* when the declarative
reading (provability) coincides with the operational one (goal-directed
search), and that coincidence is made precise by **uniform proofs** —
cut-free sequent proofs in which every non-atomic goal is decomposed by the
right rule for its principal connective, so the connectives *are* the search
instructions.  A logic admitting uniform proofs for every provable sequent is
an **abstract logic programming language**.

This is precisely the frame the CLP report is working in when it says
operational semantics are differentiated "not by different axiom systems but by
different rule systems", and that formulas are programs rather than properties
of programs.  Read together:

* MNPS fix what it means for a *logic* to be a programming language;
* Fairtlough–Mendler–Walton add the **constraint** dimension by making the
  monad `◯` the carrier of the answer constraint, so that the proof term is not
  merely a witness of success but *the constraint that was computed* — the
  intensional Curry–Howard the abstract advertises.

The second Pfenning paper is the direct one:

> **F. Pfenning and R. Davies, "A judgmental reconstruction of modal logic",
> Mathematical Structures in Computer Science 11(4):511–540, 2001.**
> [**CONFIRMED** — that issue is the *Modalities in Type Theory* special issue
> edited by Fairtlough, Mendler and Moggi.]

Separating *judgments* from *propositions* after Martin-Löf, they give
introduction and elimination rules for necessity and possibility, and then
observe that **the lax modality is already expressible using possibility and
necessity** — with the computational reading yielding a new formulation of
Moggi's monadic metalanguage.

That is worth following up in Lean, and it is a concrete next step rather than
a gesture: if `◯` decomposes into `□`/`◇`, then our *two* modalities plausibly
unbundle that composite, with `◯∀` and `◯∃` landing on different halves.  The
test is cheap — state the two candidate equivalences in a constructive S4 with
our two relations and try to refute them with the machinery of
`CompleteTests.lean`, which already builds two-state countermodels to order.

## 4. Access control, for completeness of the applications picture

Already recorded in `docs/belief-applications-draft.md`: **Garg and Pfenning**'s
constructive authorisation logic, whose `says` modality is a lax modality
indexed by principals, and the PCFS file system built on it.  Deepak Garg's
*From indexed lax logic to intuitionistic logic* (CMU-CS-07-167) is the
technical bridge.  Worth keeping in view because it is the one application area
where the *first-order* case, which is what we have just proved complete, is the
one actually used: policies quantify over principals, files and times.
