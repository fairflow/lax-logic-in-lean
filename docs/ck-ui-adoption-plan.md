# Adoption plan: G4CK and uniform interpolation for CK

*Stage 1 deliverable of the calculus-adoption method. Reviewable without
opening any code. **No Lean until Matthew has reviewed this.***
Written 2026-11-19 15:24 GMT.

## The requirement

A mechanised, **proof-theoretic** construction of uniform interpolants for a
constructive modal logic with independent `□` and `◇`, reproduced in Lean
exactly as published, so that later work can test which extensions of the
calculus keep the construction alive. Extensions are not part of this plan.

## The candidates considered

| Calculus | Source | Why it does / does not fit |
|---|---|---|
| **G4CK** (and G4WK) | van der Giessen and Shillito, arXiv:2602.16880v2 | Terminating, cut-free, single-succedent; Pitts-style `Ep`, `Ap` tables with rows for `□` and `◇`; formalised in Rocq. **Adopted.** |
| Iemhoff's G4iK | Iemhoff 2019 (the paper's reference `Iemhoff19b`) | `□` only; G4CK extends it. Subsumed. |
| Dalmonte, Grellois, Olivetti: multi-succedent calculi for CK, WK | the paper's reference `DalGreOli21` | G4CK is their calculus made single-succedent. No interpolation there. |
| Férée and van Gool: Pitts for IL in Coq | the paper's reference `Fer23` | The `◯`/modal-free base of the Rocq development (`Environments.v` is theirs). Covered by adopting G4CK. |

## The source

* I. van der Giessen and I. Shillito, *Uniform interpolation with
  constructive diamond*, arXiv:2602.16880, v2 of 27 May 2026 (LNCS class;
  no venue printed).
* **Read**: the arXiv LaTeX source, all of `preliminaries.tex`,
  `SeqCalc.tex`, `SeqProps.tex`, `PropQuantif.tex`.
* **Appendix**: none. The proofs the paper omits ("due to space
  restrictions we highlight some of the important steps") exist only in the
  Rocq development, so the Rocq source is a second primary source here.
* **Rocq development**: `github.com/ianshil/CK`, branch
  `uniform_interpolation`, commit `cd09fce` (24 January 2026); rendered at
  `ianshil.github.io/CK`. No `Axiom`, no `Admitted` in `theories/Sequent`
  or `theories/Syntax` (text search of the sources; the build has **not**
  been run here, see the last section). Sizes, CK side only:

  | File | Lines | Content |
  |---|---|---|
  | `Syntax/im_syntax.v`, `Sequent/syntax_facts.v` | 197 + 156 | formulas, weight |
  | `Sequent/Environments.v` | 929 | multisets of formulas (stdpp `gmultiset`), `⊗Γ = □⁻¹Γ` |
  | `G4CK/CKSequents.v` | 204 | the calculus |
  | `G4CK/CKSequentProps.v` | 1341 | weakening, inversions, `→L`, contraction |
  | `G4CK/CKOrder.v` | 511 | the Dershowitz–Manna order on sequents |
  | `G4CK/CKCut.v` | 567 | additive cut |
  | `G4CK/CKDecisionProcedure.v` | 525 | `Provable_dec` |
  | `G4CK/CKSoundComplete.v` | 225 | equivalence with the Hilbert calculus |
  | `G4CK/CKPropQuantifiers.v` | 2331 | `Ep`, `Ap`, `entail_correct`, `pq_correct`, `CK_uniform_interpolation` |
  | `GHC/*` | about 900 | the generalised Hilbert calculus `CKH` |

  About 7,900 lines for CK; the WK files are near-copies (about 5,500).
* The paper proves nothing twice by different routes.

## Kind of result

Four kinds, in dependency order, each with its own encoding consequence:

1. **Termination**: every premise is below its conclusion in the
   Dershowitz–Manna extension of formula weight. Consequence: contexts must
   be multisets up to permutation, and the order must be available
   choice-free (the target is a decision procedure).
2. **Structural admissibility and cut**: weakening, `Id`, `→L`,
   contraction, additive cut, by induction on weight of the cut formula and
   then on the order. Consequence: derivations need an induction principle
   over the order, not only over height.
3. **Equivalence with a Hilbert calculus**. In Rocq this needs decidability
   only because `Provable` lives in `Type` and `CKH` in `Prop`. In Lean,
   with `Prop`-valued provability, the detour is unnecessary.
4. **Interpolation by construction**: `Ep`, `Ap` are functions defined by
   mutual well-founded recursion on the order; the theorem is about those
   functions.

There is **no semantics** in the paper, so no soundness-versus-completeness
screening applies. The corresponding screen here is: every rule of G4CK
must be derivable in `CKH` (the paper's left-to-right half of Theorem 2)
**before** cut or interpolation is attempted, since an over-permissive rule
table makes both of those easier.

## The calculus (Figure 2 of the paper), as it will be transcribed

Formulas: `p | ⊥ | φ ∧ ψ | φ ∨ ψ | φ → ψ | □φ | ◇φ`. Sequents `Γ ⇒ φ`, `Γ` a
finite multiset. `□⁻¹Γ := {φ | □φ ∈ Γ}`.

    ⊥L    Γ,⊥ ⇒ φ                         IdP   Γ,p ⇒ p
    ∧L    Γ,φ,ψ ⇒ χ  /  Γ,φ∧ψ ⇒ χ         ∧R    Γ ⇒ φ   Γ ⇒ ψ  /  Γ ⇒ φ∧ψ
    ∨L    Γ,φ ⇒ χ   Γ,ψ ⇒ χ  /  Γ,φ∨ψ ⇒ χ  ∨Rᵢ   Γ ⇒ φᵢ  /  Γ ⇒ φ₁∨φ₂
    →R    Γ,φ ⇒ ψ  /  Γ ⇒ φ→ψ
    p→L   Γ,p,φ ⇒ χ  /  Γ,p,p→φ ⇒ χ
    ∧→L   Γ,φ→(ψ→χ) ⇒ δ  /  Γ,(φ∧ψ)→χ ⇒ δ
    ∨→L   Γ,φ→χ,ψ→χ ⇒ δ  /  Γ,(φ∨ψ)→χ ⇒ δ
    →→L   Γ,ψ→χ ⇒ φ→ψ   Γ,χ ⇒ δ  /  Γ,(φ→ψ)→χ ⇒ δ
    □R    □⁻¹Γ ⇒ φ  /  Γ ⇒ □φ
    □→L   □⁻¹Γ ⇒ φ   Γ,ψ ⇒ δ  /  Γ,□φ→ψ ⇒ δ
    ◇→L   □⁻¹Γ,γ ⇒ φ   Γ,◇γ,ψ ⇒ δ  /  Γ,◇γ,◇φ→ψ ⇒ δ
    ◇L    □⁻¹Γ,φ ⇒ ψ  /  Γ,◇φ ⇒ ◇ψ

Sixteen rules, matching the sixteen constructors of the Rocq `Provable`.
G4WK replaces `◇L` by `◇L_W` (`□⁻¹Γ,φ ⇒ ◇⁻¹Δ / Γ,◇φ ⇒ Δ`) and allows an
empty succedent.

## Scope

**In scope**, in this order:

1. Syntax and weight (Definition 1, `def:weight`).
2. G4CK (Figure 2), transcribed; `#rules` against the figure, `#slime` 0.
3. The Hilbert calculus `CKH` (Figure 1) and the screen: every G4CK rule
   derivable in `CKH`.
4. The sequent order and strong termination (Definition 2, the two
   unlabelled propositions); decidability of G4CK provability.
5. Lemma 1 (`lemma:weakening`), contraction, additive cut.
6. Theorem 2 (`thm:equiv`), CK half.
7. Definitions 3–5 (`def:UIP`, `def SUIP`, `def_Ap_Ep`) with the 14 + 21
   rows of Figure 3; Theorem 3 (`thm:terminating`); Lemmas 3, 4.
8. Theorem 4 (`thm:UIP_CK`) and its corollary, in the form of the Rocq
   `CK_uniform_interpolation`.

**Out of scope**, explicitly:

* G4WK and WK (Theorem `thm:UIP_WK` and corollary). Proposed as a second
  campaign templated on the CK proofs, once step 8 stands.
* Remark 2 (`remark:dual`, `∃` defined from `∀`) and the unlabelled remark.
* Any Kripke semantics, and any link to CKD's `□◇` fragment.
* Any extension of the calculus (new rules, frame conditions).
* The other project in the same Rocq repository (conservativity between CK
  and IK, LICS 2025).

## Results to be reproduced

Numbers from the compiled `.aux` (`tools/paper-skeleton`). Six items carry
no label. The label `thm:UIP_WK` is used twice in the source (theorem and
corollary), so the compiled number of the WK theorem is unreliable; it is
out of scope here.

| Paper item | Statement (short) | Rocq name | Lean name | Status |
|---|---|---|---|---|
| Definition 1 · `def:weight` | weight of a formula | `weight` | `CK.Form.weight` | transcribed |
| Figure 2 | G4CK | `Provable` | `CK.G4CK` | transcribed; `#rules` compared, `#slime` 0 |
| Figure 1 | CKH | `CKH_prv` | `CK.CKH`, `CK.Axiom` | transcribed |
| Definition 2 (no label) | sequent order `≺` | `pointed_env_order` | | OPEN |
| Proposition (no label) | G4CK strongly terminates | (in `CKOrder`) | | OPEN |
| Proposition (no label) | G4CK provability is decidable | `Provable_dec` | | OPEN |
| Lemma 1 · `lemma:weakening` | `wk`, `Id`, `→L` admissible | `generalised_weakeningR`, `generalised_axiom`, `weak_ImpL` | `CK.G4CK.weakenList` (`wk`); exchange `CK.G4CK.perm` | `wk` PROVED [propext]; `Id` PROVED [propext] (`CK.G4CK.id`, with the detachment lemma `CK.G4CK.mp`); `→L` OPEN |
| Proposition (no label) | contraction admissible | `contraction` | | OPEN |
| Theorem (no label) | additive cut admissible | `additive_cut` | | OPEN |
| Theorem 2 · `thm:equiv` | `⊢G4CK Γ ⇒ φ` iff `Γ ⊢CK φ` | `G4CK_sound_CKH`, `G4CK_compl_CKH` | `CK.G4CK.toCKH` (left to right) | left to right PROVED [propext]; right to left OPEN |
| Definition 3 · `def:UIP` | UIP of a logic | | | OPEN |
| Definition 4 · `def SUIP` | UIP of a set of sequents | | | OPEN |
| Lemma 2 (no label) | sequent UIP gives UIP of the logic | | | OPEN |
| Definition 5 · `def_Ap_Ep` | `Ep(Γ)`, `Ap(Γ ⇒ φ)`, Figure 3 | `e_rule`, `a_rule_env`, `a_rule_form`, `EA` | | OPEN |
| Theorem 3 · `thm:terminating` | the definition terminates | (the `Program`/`Equations` obligations) | | OPEN |
| Lemma 3 · `Lemma_simple1` | a member of the `Ep` set on the left, of the `Ap` set on the right | `E_left`, `A_right` | | OPEN |
| Lemma 4 · `Lemma_simple2` | `Π, □Ep(□⁻¹Γ) ⇒ φ` gives `Π, Ep(Γ) ⇒ φ` | `E9_left` | | OPEN |
| Theorem 4 · `thm:UIP_CK` | G4CK has UIP: p-freeness, implication, uniformity | `EA_vars`, `entail_correct`, `pq_correct` | | OPEN |
| Corollary (no label) | CK has UIP | `CK_uniform_interpolation` | | OPEN |

The final theorem, as Rocq states it and as it will be stated here: for
`p ∉ V` and every `φ` with variables in `p :: V`,

    vars(Ep φ) ⊆ V,    φ ⇒ Ep φ,    ∀ψ over V.  φ ⇒ ψ   gives   Ep φ ⇒ ψ,
    vars(Ap φ) ⊆ V,    Ap φ ⇒ φ,    ∀θ over V.  θ ⇒ φ   gives   θ ⇒ Ap φ.

## Existing repo results consumed read-only

| Result | Where | Why it is safe to consume |
|---|---|---|
| The convention for list contexts with a `Perm` field | `LaxLogic/PLL/G4/G4.lean` | a convention, not a theorem |
| `Meta/Audit.lean`, `Meta/Rules.lean`, `Meta/Slime.lean` | `Meta/` | tools |

No theorem of the repository is consumed. The G4 files are over
`PLLFormula` (one modality `◯`), a different language; reusing their
admissibility proofs would be an extension in the wrong direction. Whether
Mathlib's `Multiset.wellFounded_isDershowitzMannaLT` is usable depends on
its axioms (decision 3).

## Divergence log

| # | Paper item (label) | What the paper says | What is proved here | Why |
|---|---|---|---|---|
| D1 | Figure 2 | antecedents are finite multisets | antecedents are lists; each left rule has a field `Γ.Perm (principal :: Δ)` | every conclusion index stays a variable (`#slime`: 0); the repository's G4 convention |
| D2 | Figure 2 | (Rocq) `Provable : env → form → Type` | `G4CK : List Form → Form → Prop` | the theorems need no proof terms; removes the decidability detour of Theorem 2 |
| D4 | Figure 2, `(p→L)` and `(◇→L)` | `Γ,p,p→φ` and `Γ,◇γ,◇φ→ψ` in the conclusion | only the implication is exposed by `Perm`; `p ∈ Δ`, `◇γ ∈ Δ` are side conditions | the rule leaves that formula in place; this is the encoding of `G4h.impLProp` in `LaxLogic/PLL/G4/G4H.lean`, whose inversion and contraction proofs are the templates |
| D3 | Figure 1 | axioms as schemes | `Axiom` is an inductive family indexed by the instance | Rocq states each axiom with an equation `F = …`; the index form is the same set |

Opened empty on 2026-11-19; D1–D3 recorded with the transcription the same
day. Divergences foreseen and waiting on the decisions below:
`Prop`-valued provability (decision 2) makes the decidability detour in
Theorem 2 unnecessary; the representation of multisets (decision 1).

## Statement-level decisions reserved for Matthew

1. **Contexts.** The paper uses multisets. The repository's G4 files use
   `List` with a `Perm` hypothesis as a field of each left rule, which keeps
   every conclusion index a variable (slime-free). I propose the same here.
   The alternative is Mathlib `Multiset`, with conclusions of the form
   `φ ::ₘ Γ`, which is a computed index.
2. **`Prop` or `Type`.** I propose `Prop`-valued `G4CK Γ φ` for all the
   theorems, and no `Type`-valued twin until a searcher is wanted (stage 4).
3. **Choice.** The repository standard is choice-free for anything that is
   to become a procedure. `Ep`, `Ap` and the decision procedure are such.
   Mathlib's `Multiset.wellFounded_isDershowitzMannaLT` depends on
   `[propext, Classical.choice, Quot.sound]` (checked 2026-11-19 with
   `#print axioms`). So I propose a weight-indexed measure proved here
   instead (a count vector by weight, compared lexicographically), recorded
   as a divergence in the proof of termination only.
4. **Where.** A new top-level library `CK/` (as `LJF/`, `FRJ/` are), with
   `CK.lean` as its root, on a new durable branch `ck-ui-adoption`. The
   paper and its Rocq code are public, and this plan mentions no private
   result, so the public repository is the right place.
5. **Reproducing the Rocq build.** The development needs Rocq 9.0 with
   `stdpp` and `Equations`; this machine has Coq 8.20.1 without them. A new
   opam switch would cost roughly 1–2 GB and half an hour. It would confirm
   that the cited commit compiles before porting from it. Wanted, or is
   reading the source enough?
6. **WK.** Second campaign, or not at all?

## The Rocq development, reproduced (2026-11-19)

Built here in a separate opam switch `ck-rocq` (Rocq 9.0.0, `stdpp`,
`Equations`): all 63 files of commit `cd09fce` compile. `Print Assumptions`:

| Rocq theorem | Assumptions |
|---|---|
| `CK_uniform_interpolation` | `functional_extensionality_dep` |
| `additive_cut` | none |
| `Provable_dec` | none |
| `G4CK_compl_CKH` | `Extensionality_Ensembles` |

Two facts the paper does not state, read off the Rocq source:

* **The mechanised order is not Dershowitz–Manna.** `CKOrder.v` compares
  sequents by the natural number `env_weight Γ = Σ_{φ ∈ Γ} 5^{w(φ)}`. That is
  a choice-free measure and is the one to port (it settles decision 3). The
  paper's Definition 2 is the multiset order; the two agree on what the rules
  need (every premise is smaller).
* `Ef`, `Af` do not reduce inside Rocq (`vm_compute` stops at the
  accessibility proof); they do run after extraction to OCaml. Values on
  fifteen small formulas are kept outside the repository as test data for the
  Lean functions, for example `Ap(p) = ⊥ ∨ ⊥` and
  `Ap(□p) = □((⊤ ∧ ⊤) → (⊥ ∨ ⊥)) ∨ ⊥` with `⊤ = ⊥ → ⊥`.
