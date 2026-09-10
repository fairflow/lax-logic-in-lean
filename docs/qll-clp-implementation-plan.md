# Implementing the CLP paper: scope and stages

Dated 2026-09-10.  The paper is

> **M. Fairtlough, M. Mendler, M. Walton, "First-order Lax Logic as a framework
> for Constraint Logic Programming"**, draft of 10 September 1997, 31pp.

located on this machine at `~/Backup/Sheffield/matt/public_html/mendler/temp.pdf`
(byte-identical copy under `~/TransferM4/…/Sheffield/…`).  It is the last and
fullest of a lineage: `clp.pdf` = `master-clp2.pdf` (8pp, 8 Apr 97, with Walton
on the title), `csl-97.pdf` (13pp, 18 Apr), `master-mf.pdf` (25pp, 16 Apr),
`master-mf-22-8.pdf` (28pp, 21 Aug), `temp.pdf` (31pp, 10 Sep).  Unpublished.
The PDFs and TeX stay outside the public repository; only mechanised statements
enter it.

## The correspondence this development already has

The paper's QLL has **one** modality, and its Def 3.3 clause

    α ⊨ ◯M   iff   for all β with α Ri β there is γ with β Rm γ and γ ⊨ M

is our `◯∃` clause exactly, over frames with `Rm ⊆ Ri`, increasing domains and
`Ri`-closed fallible worlds.  Its `∀`, `∃`, `⊃` clauses are ours.  So the
paper's logic is **our logic at `q = .ex`**.

| paper | here |
| :-- | :-- |
| Def 3.2 Kripke constraint model | `QFrame`/`KModel` with `RA = RE` |
| Def 3.3 forcing | `force` at `q = .ex` |
| Fig. 2 QLL-ND, the λ̄c typing rules | `Derives` (including `efq`) |
| Thm 3.6 `⊢QLL M ⟺ ⊨QLL M` | `prv_iff_consequence`, for the ND system |
| Fig. 3, two of five derived rules | `QLL/CLP.lean` (`∧◯`, `⊃◯`) |

Two consequences for how to proceed.  The paper proves Thm 3.6 by Gödel
translation into a classical bimodal `[S4,S4]` and refers the details to
`[FW97]` (the Sheffield report `CS-97-11`), which we do not have; so building on
our own completeness is not merely cheaper, it is the only route open.  And
**Thm 4.1** (QLL-ND extensionally equivalent to the Gentzen system) reduces to
Gentzen soundness plus our completeness in one direction, and the routine
simulation of ND rules in the sequent calculus in the other — no
proof-transformation argument is needed.

## Stages

**0 — pin the correspondence.**  Def 3.2/3.3 as an independent structure with
its own forcing; agreement with `force` at `.ex`; Thm 3.6 over the paper's own
models.  Also the once-and-for-all discrepancy check.

**2 — the LLP fragment, §5.**  Σ-formulas, LLP programs `πᵢ = ∀x̃. Sᵢ ⊃ Hᵢ`,
queries; all five derived rules of Fig. 3 with their λ̄c definitions.

**3 — constraint algebras and `|·|`, §4.**  The λ-calculus over `C` and `U`;
`|M|` on formulas and `|p|` on proofs; Lemma 4.3; Thm 4.4.  This translation is
**not** a variant of `Interp.lean`: the paper has `|A| = 1` and `|◯M| = C × |M|`,
putting the constraint on the modality, where `Interp.lean` follows TPHOLs 2001
and puts a witness type on atoms.  New file.

**4 — abstraction and refinement, §6.**  Def 6.2, Thm 6.3, `ind(S)`, Table 1,
Def 6.5, Prop 6.6, Thm 6.8.  Depends on stage 3.  The heart of the paper.

**5 — canonical constraint models, §7.**  The four-world frame with world 3
fallible; `Π₀` (`◯P ↦ true`), `Π₁` (`◯P ↦ P`), `Π₂ = (Δ:Π)♭`; least Herbrand
models; Def 7.1, Lemmas 7.2/7.3, Def 7.4, Thm 7.5.

**6 — embedding CLP into LLP, §§8–9.**  `active`/`latent`/`total`, Def 8.2,
Lemmas 8.3/8.4; goals, Table 2 derivation steps, answer constraints; Thm 9.4,
Lemma 9.6, Thm 9.7, Cor 9.8.

**1 — the Gentzen system, Fig. 1.**  Independent; by the semantic route above.

Order: 0 → 2 → 3 → 4 → 5 → 6, with 1 floating.

## Examples

| example | status |
| :-- | :-- |
| 6.1 + two continuations, the three-component timing program | best target; the extracted constraint `(u≤5) ⊗ (u≤9) ⊗ (z ≥ u+35) = z ≥ 44` is checkable over a small linear-arithmetic constraint domain |
| 6.4, 6.7 | small, fully implementable |
| 9.5 | implementable; the draft leaves steps k=2…6 blank, so we complete it |
| 2.1, the CLP(ℝ) mortgage program | program and abstraction easy; reproducing `P = 120000` needs a real-arithmetic solver, a project of its own — **decision needed** |

## Open decisions

1. **The `?I` rule** for leaves of partial proofs: the draft records "some
   disagreement among the authors as to whether this rule is acceptable".
   Proposal: make it a parameter so both readings are available.
2. **Thm 4.4**, "this interpretation is a model of the computational lambda
   calculus", needs a notion of λc-model; the paper declines to investigate and
   points to [Men93].  Proposal: the equational reading — verify Moggi's λc
   equations.
3. **Lemma 4.3** carries the authors' own note doubting in what sense the
   translation "induces" reductions.  Proposal: implement the equations as the
   definition of constraint extraction and prove them about `|·|`.

## Draft artefacts

Noted in passing, not hunted for.

* Def 3.3's atomic clause is `(t̄) ∈ I_α(P)`, with no fallibility disjunct,
  while the translation has `P° = □i P ∨ □i f`.  Our `force` follows the
  translation, and so does stage 0.
* Thm 3.6's detailed proof is not in this draft; it is cited to `[FW97]`.
* Lemma 8.3's remaining cases are "left as exercises for the reader".
* Example 9.5 stops after `k = 1`; steps `k = 2…6` are headings with no content.
* Two dangling references: "Definition ??" in Ex. 9.5, and a "Definition 7.2"
  cited in Thm 9.4's proof, where 7.2 is a Lemma.
