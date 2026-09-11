# First-order Lax Logic and Constraint Logic Programming: the mechanisation

Dated 2026-09-11.  A write-up of the Lean development of

> M. Fairtlough, M. Mendler, M. Walton, *First-order Lax Logic as a framework
> for Constraint Logic Programming*, draft of 10 September 1997 (unpublished).

Section and result numbers without a prefix refer to the draft.  Every
statement marked PROVED is kernel-checked, sorry-free, with the axiom set shown
in the table of §10; REFUTED means a kernel-checked countermodel; OPEN and
*not built* mean what they say.  Modules live in `LaxLogic/QLL/`; the branch is
`lax-obligations`.  Paragraphs headed **Remark** are my own comments, not the
draft's.

## Contents

1. The logic and its models
2. Horn clauses and least Herbrand models
3. LLP programs and the two-world model
4. CLP without `◯`: proof trees, goal reduction, answers
5. The constraint domain: linear arithmetic over ℚ with certificates
6. The `◯` pass: abstraction, extraction, refinement
7. The canonical constraint model (Theorem 7.5)
8. Execution and certification
9. Examples
10. Status, with axioms
11. Remarks on the draft

---

## 1. The logic and its models

**Syntax.**  QLL formulas `A ::= ⊤ | ⊥ | P(t̃) | A ∧ A | A ∨ A | A ⊃ A | ◯_q A |
∀x.A | ∃x.A`, locally nameless (`Syntax.lean`).  There are two lax modalities,
`q ∈ {∀, ∃}`; the draft's `◯` is `◯_∃`.  Every proof below is stated for a
general `q`, so nothing needs redoing in a setting that tells them apart.
`Prv Γ A` (written `Γ ⊢ A`) is natural deduction with cofinite binders
(`Prov.lean`); its modal rules are

    Γ ⊢ A                    Γ ⊢ ◯_q A     A, Γ ⊢ ◯_q B
    ─────────── (◯I)         ────────────────────────── (◯E)
    Γ ⊢ ◯_q A                        Γ ⊢ ◯_q B

**Kripke models** (Def 3.2, `Kripke.lean`).  A preorder `Ri` of worlds with
increasing domains, hereditary fallible worlds, and modal relations
`R_q ⊆ Ri`; the modal clause is

    w ⊨ ◯_q A   iff   for every v with w Ri v there is u with v R_q u and u ⊨ A.

Soundness is PROVED without choice:

    Γ ⊢ A  →  Γ ⊫ A                                            (Prv.sound)

(completeness, `prv_iff_consequence` in `Complete1`, uses `Classical.choice`).

**The modal relation is a parameter.**  For the Herbrand models of §§2–7 a
frame `HFrame` carries its own preorder `m ⊆ le` for both `R_∀` and `R_∃`.
Fixing `m = le` is not harmless: with no fallible worlds, `◯` is then forced
exactly where `¬¬` is, and such models validate a formula QLL does not prove:

    Rm = Ri   ⟹   ⊨ (◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)                     (circ_imp_of_rm_eq_ri)
    ⊬ (◯P ⊃ ◯Q) ⊃ ◯(P ⊃ Q)                                    (not_prv_circ_imp, REFUTED cell)

The countermodel has three worlds `r ≤ s ≤ f` with `m` the identity plus
`s → f` (`ModalRelation.lean`).

## 2. Horn clauses and least Herbrand models

**Clauses** (Def 5.1, `LLP.lean`).  Σ-formulas are `S ::= ⊤ | P(t̃) | S ∧ S |
S ∨ S | ∃x.S`.  A program clause is `∀x₁…xₘ. S ⊃ H` with `H = P(x̃)` or
`◯_q P(x̃)`, and a program `Θ` is a list of clauses; `Θ.forms` is the list of
formulas.  A **Horn clause** (`Horn.lean`) has a primitive positive body
(no `∨`) and arbitrary head arguments.

**Splitting a Σ-body.**  The draft's indices `ind(S)` select one disjunct at
every `∨`; `sel S g` is `S` at index `g`.  Then

    g ∈ ind S,  Γ ⊢ sel S g   →   Γ ⊢ S                         (Prv.of_sel)
    Γ ⊢ S   →   Γ ⊢ ⋁_{g ∈ ind S} sel S g                        (Prv.disj_sel)

so a Def 5.1 clause is provably equivalent to its Horn clauses `c.toHorn`,
one per index (`Clause.prv_toHorn`, `Clause.prv_of_toHorn`).

**The least Herbrand model** (`Herbrand.lean`).  Relative to built-in
relations `R` (the constraint predicates, later), `Holds R P φ` is the
inductive least model: atoms of `R`, `⊤`, `∧`, `∃` with a closed witness, and
clause firing.  `LHM R P` is its atomic part and `Tp R P` the immediate
consequence operator.  PROVED, for well-formed `P`:

    Tp(LHM) = LHM,     Tp(I) ⊆ I  →  LHM ⊆ I                     (Tp_LHM, LHM_least)
    LHM = ⋃ₙ Tpⁿ(∅)  =  lfp Tp                                    (LHM_iff_Tpow, LHM_eq_lfp)
    Tp(I) ⊆ I  ⟺  R ⊆ I and I ⊨ P                               (prefixpoint_iff_model)
    LHM = ⋂ { I | R ⊆ I, I ⊨ P }                                  (LHM_iff_all_models)

and Lloyd's theorems for non-modal Horn programs and closed Σ-queries `S`:

    P ⊢ S   ⟺   S true in M_P   ⟺   P ⊫ S                       (lloyd_prv_iff, lloyd_consequence_iff)
    M_P(p, ũ)   ⟺   P ⊫ p(ũ)                                     (vanEmden_Kowalski)

Two designed cells mark the limits of the least-model method: `⊬ P ∨ ¬P`,
refuted by a two-world Herbrand model (`lem_not_prv`), and a disjunction has no
least Herbrand model (`or_no_least_model`), which is why clause bodies are split
into Horn clauses first.

## 3. LLP programs and the two-world model

§7 builds models on the frame `0 ≤ 1` with the arrow modal (`HerbrandLLP.lean`).
World 0 carries the least model of `Π⁰` (modal clauses dropped, `Θ.horn0`),
world 1 that of `Π¹` (`◯` erased, `Θ.horn`).  For a well-formed program whose
modal clauses all use `q`, and a closed Σ-formula `S`:

    Θ ⊢ S      ⟺   0 ⊨ S                                        (thm_7_5_world0)
    Θ ⊢ ◯_q S  ⟺   1 ⊨ S                                        (thm_7_5_world1)

## 4. CLP without `◯`: proof trees, goal reduction, answers

This is the first of two passes: every result is proved for constraint logic
programs with built-in constraint atoms before `◯` enters.

**Proof trees** (`CLPCore.lean`).  A predicate `isC` marks the constraint
predicates.  `CProof` has constructors `top`, `cstr B t̃` (a constraint leaf),
`andI`, `orL`, `orR`, `exI t`, and `clause w t̃` (resolve with clause `w` at the
instance `t̃`); `CTyped isC Θ S p` says `p` proves `S`.  Definition 8.1 splits
the constraint leaves of `p` into the **active** ones (not under a clause
application) and the **latent** ones (under one); `total = latent ∧ active`:

    total(p) ⊣⊢ latent(p) ∧ active(p)                            (CProof.total_equiv)
    CTyped Θ S p   →   Θ ⊢ total(p) ⊃ S                          (CTyped.prv_total)

`checkC` decides `CTyped` and is proved sound (`checkC_sound`), so a tree
produced by any program can be checked at run time.

**Goal reduction** (Table 2, `CLPOper.lean`).  A goal is `c □ φ₁,…,φₙ`.  A
`Step` applies one rule of Table 2 at any position; the constraint rule is
guarded by a test `ok (c ∧ B)`, the draft's solvability condition, left as a
parameter.  `Steps` is the reflexive–transitive closure.  Writing `≈` for `⊣⊢`:

    c □ φ̃  ⇝*  c' □ ε   →   ∃ p̃. each pᵢ proves φᵢ,  c' ≈ c ∧ total(p₁) ∧ … ∧ total(pₙ)
                                                                  (steps_forest, Theorem 9.4)
    c □ φ̃  ⇝*  c' □ ε   →   Θ ⊢ c' ⊃ c ∧ φ₁ ∧ … ∧ φₙ              (steps_sound, Corollary 9.8)

Neither uses `ok`: solvability prunes the search, it plays no part in
soundness.

**World 2 without `◯`** (`HerbrandCLP.lean`).  With `R` interpreting the
constraint predicates over the Herbrand universe (supported on constraints,
closed arguments) and `Θ` non-modal and well formed, for closed Σ `S`:

    S true in LHM_R(Θ)   ⟺   ∃ p. CTyped Θ S p ∧ total(p) true in R      (world2_free)

## 5. The constraint domain: linear arithmetic over ℚ with certificates

`LinQ.lean`.  A constraint is `e ≤ 0`, `e < 0` or `e = 0` for a linear
expression `e`; constraint atoms `leq`, `lt`, `geq`, `gt`, `eq` over terms
built from variables, numerals (`n`, `n/d`), `add`, `sub`, `neg` and
multiplication by a constant are read by `consOf`.  Two certificates:

    checkWitness cs σ = true      →   σ satisfies every c ∈ cs           (checkWitness_sound)
    checkFarkas (λ̃ zip cs) = true →   no σ satisfies cs                  (checkFarkas_unsat)

The Farkas check: `λᵢ ≥ 0` off the equations, `Σ λᵢ eᵢ` has no variables, and
its constant is positive, or non-negative with some strict constraint used.
The solver, Fourier–Motzkin elimination (`fm`), is untrusted; `certifyVerdict`
keeps a verdict only with a valid certificate, whoever produced it:

    certifyVerdict cs v = sat w     →   w satisfies cs                   (certifyVerdict_sat)
    certifyVerdict cs v = unsat λ̃   →   cs is unsatisfiable              (certifyVerdict_unsat)

`solve = certifyVerdict ∘ fm`, and the same function checks Wolfram's answers
(§8).  In `CLPEngine.lean`: entailment by refutation,

    entailsLe cs e = true   →   ∀σ ⊨ cs.  e(σ) ≤ 0                   (entailsLe_sound)

and, for timing, the least value of a variable certified from both sides —
a witness attaining `z*` and multipliers refuting `cs ∧ z < z*`:

    lowerBoundCert cs z z* λ̃ = true   →   ∀σ ⊨ cs.  z* ≤ σ(z)          (lowerBoundCert_sound)
    upClosed cs z = true, σ ⊨ cs, σ(z) ≤ r   →   σ[z := r] ⊨ cs       (upClosed_sound)

The witness and multipliers for timing systems come from longest paths through
the difference constraints (Bellman–Ford, `settle`).

## 6. The `◯` pass: abstraction, extraction, refinement

`CLPAbstract.lean`.  Constraints are formulas, `⊗ = ∧`, `ε = ⊤`; every equation
of the draft holds up to `⊣⊢`.

**Abstraction** (Def 6.2, Theorem 6.3).  `S♯` replaces each constraint atom by
`⊤`; the clause `∀x̃. S ⊃ P(x̃)` becomes `∀x̃. S♯ ⊃ ◯_q P(x̃)` (`Clause.abs`,
`Program.abs`).  Abstract proof trees `AProof` use the rules of Fig. 3
(`val(⋆)`, `∧◯`, `∨◯`, `∃◯`, `⊃◯`), typed by `ATyped Θ♯ q S a`, which is sound:
`ATyped Θ♯ q S a → Θ♯ ⊢ ◯_q S` (`ATyped.prv`).  A concrete tree maps to an
abstract one (`CProof.toA`: constraint leaves become `val(⋆)`).  With no clause
head a constraint (Def 5.1's requirement, `HeadsOK`):

    CTyped Θ S p   →   ATyped Θ♯ q (S♯) (toA p)   →   Θ♯ ⊢ ◯_q S♯     (CTyped.toA, CTyped.prv_abs)

**Extraction** (§4, Lemmas 8.3, 8.4).  The writer monad `WM α = C × α` with
`val a = (⊤, a)` and `bind (c, a) f = (c ∧ π₁(f a), π₂(f a))` satisfies the
monad laws and is commutative, up to `⊣⊢` (`WM.bind_val_left`,
`WM.bind_val_right`, `WM.bind_assoc`, `WM.bind_comm`).  Witnesses `Wit` are the
values of the types `|S|` of Σ-formulas (unit, pairs, injections, packs with a
term).  A constraint table `T w t̃ z` gives the constraint of clause `w` at
instance `t̃` and witness `z` — the first component of the draft's `θ♯₁ t̃ z`.
`a.ext T` is the extracted pair `|a|`.  For the table of the concrete program
itself (`Program.table`, built from `ctable`):

    ctable S (wit p) = active(p)                                     (CTyped.ctable_wit, Lemma 8.3)
    π₂|toA p| = wit p,     π₁|toA p| ⊣⊢ latent(p)                    (CTyped.ext_toA, Lemma 8.4)
    π₁|toA p| ∧ active(p) ⊣⊢ total(p)                                (CTyped.ext_total)

**Theorem 9.7.**  For a pure query `φ` (no constraint atoms):

    ⊤ □ φ ⇝* c □ ε   →   ∃ p. CTyped Θ φ p,  ATyped Θ♯ q φ (toA p),  c ⊣⊢ π₁|toA p|     (thm_9_7)

**Refinement** (Def 6.5, Theorem 6.8, Proposition 6.6).  Def 6.5 builds the
refined clause `∀x̃. (⋁_{g ∈ ind S} ∃ỹ. ⋀Dᵢ ∧ π₁(p x̃ g)) ⊃ P`.  It is used here
through its instances: `S @ z` (`atW`) is the disjunct of `S` that the witness
`z` selects, with its existential witnesses substituted, and

    RefinedBy Δ Θ♯ T  :⟺  for every clause w, instance t̃ and witness z,
                           Δ ⊢ T w t̃ z ∧ (S_w[t̃] @ z) ⊃ P_w(t̃).

Then for **any** table:

    RefinedBy Δ Θ♯ T,  ATyped Θ♯ q S a   →   Δ ⊢ π₁|a| ⊃ S          (thm_6_8, Theorem 6.8)
    Θ non-modal   →   RefinedBy Θ Θ♯ (table Θ)                       (refinedBy_abs, Prop 6.6 first half)
    Θ non-modal,  ATyped Θ♯ q S a   →   Θ ⊢ π₁|a| ⊃ S               (cor_9_8_abs, Cor 9.8 by the draft's route)

The second half of Proposition 6.6, `(p : θ)♭ ⊢ θ` for a modal clause, is
REFUTED as stated.  Take `θ = ∀x. A(x) ⊃ ◯P(x)` and the table `λx.λz.(B(x), ⋆)`,
with `B` a constraint: the refinement is `∀x. A(x) ∧ B(x) ⊃ P(x)`, which holds
in the one-world Herbrand model where `A` holds of everything and `B`, `P` of
nothing, while `θ` fails there.  It becomes true once the constraint is
assumed lax-true:

    ∀x.(A x ∧ B x) ⊃ P x   ⊬   ∀x. A x ⊃ ◯P x                     (p66_refuted)
    ∀x.(A x ∧ B x) ⊃ P x,  ∀x. ◯B x   ⊢   ∀x. A x ⊃ ◯P x          (p66_with_lax)

## 7. The canonical constraint model (Theorem 7.5)

`HerbrandCLP.lean`.  The draft's frame, as drawn:

    0 → 1,    0 → 2 → 3,      3 fallible,   every arrow modal.

For the abstraction `Θ♯` of a well-formed non-modal program `Θ` and constraint
relations `R`, the canonical model `canonModel` puts at world 0 the least
model of `Π⁰` (empty, since every clause of `Θ♯` is modal), at world 1 that of
`Π¹` (`◯` erased), at world 2 that of `Π² = Θ` over `R`, and everything at
world 3.  The interpretations are monotone along the frame (Lemma 7.3,
`canon_hered`), and world 0 forces every clause of `Θ♯` (Lemma 7.2,
`canon_clause`).  For a closed Σ-query `S`:

    Θ♯ ⊢ S        ⟺   0 ⊨ S                                          (thm_7_5_canon0)
    Θ♯ ⊢ ◯_q S    ⟺   1 ⊨ S                                          (thm_7_5_canon1)
    (∃a. ATyped Θ♯ q S a ∧ π₁|a| true in R)   ⟺   2 ⊨ S    (S pure)  (thm_7_5_canon2)

and every `◯`-formula is forced at world 2, through the fallible world 3
(`canon_circ_w2`): the solvability information of world 2 is carried by its
atoms, as the draft says.  The draft's 2-consequence asks for a *solvable*
extracted constraint, one whose existential closure is true; the statement
here asks for a true one, which is the same once the proof's witness terms
are chosen to be the solution.

## 8. Execution and certification

**The engine** (`CLPEngine.lean`).  Depth-first resolution with leftmost
selection, in continuation-passing style (`solveK`), with the clauses indexed
by head.  Heads are `P(x̃)` (Def 5.1), so resolution is matching: all term
structure is carried by constraints.  With `eager` set, each new constraint is
tested for satisfiability by the certified solver, which prunes failing
branches.  Every answer carries its proof tree, checked by `checkC`:

    answer Θ … G = some a,   a.typed = true   →   Θ ⊢ a.constraint ⊃ G      (answer_sound)

There are four levels of trust in what follows.

| checked by | trusted base | used for |
| :-- | :-- | :-- |
| the kernel, which runs the engine itself (`runL`) | kernel | Examples 6.1, 9.5 |
| `checkC`, `certifyVerdict`, `lowerBoundCert`, run compiled | kernel + compiler, checkers proved sound | the bench |
| `certify` (the verified checker of `Certify.lean`) on λ̄c terms | kernel + compiler | abstract proofs of 6.1, 9.5 |
| Wolfram, through the bridge | none: every answer is re-checked | solver and optimiser |

**Abstract proofs as λ̄c terms** (`CLPCertify.lean`).  Fig. 3's derived terms,
read directly, nest `let` in scrutinee position; `certify` is bidirectional and
refuses them (`notInferable "ι_t(p)"`).  The let-flattened term, in which values
are combined purely and only clause applications `w t̃ v` are `let`-bound, is
equal by the commuting conversions of the monad and is accepted.  For
Example 6.1:

    let∃ u ⇐ π[s] θ₀ ⋆ in let∃ v ⇐ π[s] θ₁ ⋆ in let∃ w ⇐ π[z] θ₂ ι[s] (u, (v, ⋆)) in val∃ w

`certify` does not scale: it names each binder by concatenating the names in
scope (`Kit.freshFor`), so names double in length per nested `let`; a 3-bit
adder's term exhausted memory.  A linear fresh-name function is under way in a
separate task.

**Wolfram** (`CLPWolfram.lean`, run by `scripts/clp-wolfram.sh`).  Through the
persistent kernel of the Lean–Wolfram bridge (`~/Lean/mathematica-in-lean`,
same toolchain and mathlib commit, put on `LEAN_PATH`, not a Lake dependency),
Wolfram supplies instances (`FindInstance`), Farkas multipliers (`FindInstance`
on the dual system) and minima (`Minimize`).  Every answer is checked by
`certifyVerdict` or `lowerBoundCert`.

## 9. Examples

`CLPExamples.lean` (kernel-checked), `CLPBench.lean` and `CLPWolfram.lean` (run).

**Example 6.1.**  `θ₁ = ∀s. s ≥ 5 ⊃ A₁(s)`, `θ₂ = ∀s. s ≥ 9 ⊃ A₂(s)`,
`θ₃ = ∀t. ∃s. (A₁(s) ∧ A₂(s) ∧ t ≥ s + 35) ⊃ B(t)`; query `B(z)`.

    Θ ⊢ total(p) ⊃ B(z)                                               (prv61)
    (∃σ. σ(z) = r ∧ σ ⊨ total(p))  ⟺  44 ≤ r                         (ex61_answer)
    Θ♯ ⊢ ◯B(z),   π₁|toA p| ⊣⊢ total(p),   Θ ⊢ π₁|toA p| ⊃ B(z)       (prvAbs61, ext61, cor61)

The extracted constraint is, verbatim,
`(((⊤ ∧ s≥5) ∧ (((⊤ ∧ s≥9) ∧ (⊤ ∧ ⊤)) ∧ ⊤)) ∧ ⊤) ∧ (⊤ ∧ (⊤ ∧ z ≥ s+35))`, the
draft's `true ⊗ … ⊗` expression.

**Example 9.5.**  `∀x̃. c₁ ⊃ P₁`, `∀x̃. c₂ ⊃ P₂`, `∀x̃. (P₁ ∧ c₃) ∨ (P₂ ∧ c₄) ⊃ Q`;
query `Q`.  The draft's six Table 2 steps are a `Steps` derivation (`steps95`);
the draft leaves steps `k = 2…6` of its translation blank.

    Θ ⊢ (⊤ ∧ c₁) ∧ c₃ ⊃ ⊤ ∧ (Q ∧ ⊤)                                  (cor95)
    (⊤ ∧ c₁) ∧ c₃ ⊣⊢ π₁|a|  for an abstract proof a of ◯Q             (thm97_95)
    all answers: c₁ ∧ c₃ and c₂ ∧ c₄                                  (all95)

**The mortgage program** (Example 2.1), exact over ℚ:

| query | result |
| :-- | :-- |
| `D = 120, I = 1/100, MP = 1721.65, B = 0` | `P = 119999.9037…`, determined (both inequalities certified) |
| `D = 5, I = 1/100, B = 0` | `MP = (10510100501/51010050100)·P = 0.2060397996…·P`, certified |
| `D = 5, I = 1/10, B = 0` | `MP = (161051/610510)·P = 0.2637974808…·P`, certified |

**Scheduling** with one shared machine (a disjunctive constraint): earliest end
12, 11 under deadlines 12, 11 (the engine backtracks to the other machine
order); no answer under deadline 10.

**Ripple-carry adders**, generated: `7n + 1` clauses, gate delays xor 3, and 2,
or 2.

| n | clauses | proof tree | constraints | carry-out settles | certified |
| :-- | :-- | :-- | :-- | :-- | :-- |
| 8 | 57 | 226 | 65 | 35 | witness and lower bound |
| 32 | 225 | 898 | 257 | 131 | witness and lower bound |
| 64 | 449 | 1794 | 513 | 259 | witness and lower bound |
| 32, all 33 outputs | 225 | 15330 | 4385 | 131 (latest) | all outputs |

**Wolfram against Fourier–Motzkin**; every Wolfram answer was accepted by the
checkers.

| system | constraints | Wolfram | Fourier–Motzkin |
| :-- | :-- | :-- | :-- |
| Example 6.1 | 3 | sat; least `z = 44` | sat |
| mortgage, query 1 | 121 | sat | sat |
| schedule, deadline 10 | 10 | unsat (Farkas) | unsat |
| adder n = 32, carry-out | 257 | sat; least 131, 4.9 s | sat, under 1 ms |
| `±xᵢ ± xⱼ ≤ 1`, n = 5 | 40 | sat | unknown (row cap) |
| same with `Σxᵢ ≥ 5` | 41 | unsat (Farkas) | unknown (row cap) |

## 10. Status, with axioms

`[p]` = `propext`, `[p,Q]` adds `Quot.sound`, `[p,C,Q]` adds `Classical.choice`.

| result | Lean | axioms |
| :-- | :-- | :-- |
| soundness | `Prv.sound` | [p,Q] |
| `Rm = Ri` not harmless | `not_prv_circ_imp` (REFUTED cell) | [p,Q] |
| Σ-splitting | `Prv.of_sel`, `Prv.disj_sel`, `Clause.prv_of_toHorn` | [p,Q] |
| least model, fixpoints | `Tp_LHM`, `LHM_least`, `LHM_iff_Tpow`, `LHM_iff_all_models` | [p,Q] |
| `LHM = lfp Tp` | `LHM_eq_lfp` | [p,C,Q] |
| Lloyd, van Emden–Kowalski | `lloyd_prv_iff`, `lloyd_consequence_iff`, `vanEmden_Kowalski` | [p,Q] |
| Theorem 7.5, worlds 0, 1 (two worlds) | `thm_7_5_world0`, `thm_7_5_world1` | [p,Q] |
| answer soundness, trees | `CTyped.prv_total`, `checkC_sound` | [p,Q] |
| Theorem 9.4, Corollary 9.8 | `steps_forest`, `steps_sound` | [p], [p,Q] |
| world 2 without `◯` | `world2_free` | [p,Q] |
| certificates | `checkWitness_sound`, `checkFarkas_unsat`, `certifyVerdict_*` | [p,C,Q] |
| engine, timing | `answer_sound`, `lowerBoundCert_sound`, `upClosed_sound` | [p,C,Q] |
| Theorem 6.3 | `CTyped.toA`, `CTyped.prv_abs` | [p], [p,Q] |
| monad laws, commutativity | `WM.bind_*` | [p] |
| Lemmas 8.3, 8.4 | `CTyped.ctable_wit`, `CTyped.ext_toA` | [p] |
| Theorem 9.7 | `thm_9_7` | [p] |
| Theorem 6.8, Prop 6.6 (first half), Cor 9.8 | `thm_6_8`, `refinedBy_abs`, `cor_9_8_abs` | [p], [p,Q] |
| Prop 6.6, second half | `p66_refuted` (REFUTED), `p66_with_lax` | [p,Q], [p] |
| Lemma 7.2, Theorem 7.5 (four worlds) | `canon_clause`, `thm_7_5_canon0/1/2` | [p,Q] |
| Examples 6.1, 9.5 | `ex61_answer`, `cor61`, `cor95`, `thm97_95` | [p,C,Q], [p,Q] |

`Classical.choice` enters only through Mathlib's ℚ (the arithmetic
certificates and everything that evaluates them) and `OrderHom.lfp`; the
logical results of §§6–7 are free of it.

**Not built.**  Fig. 1's Gentzen system (stage 1); Def 6.5's refined clauses
as formulas (they are used through their instances); constraints beyond
linear arithmetic.

## 11. Remarks on the draft

These are my comments.

**Remark 1 (commutativity is what selection independence uses).**  Theorem
9.4 holds for derivations that select subgoals in any order, and its proof
reorders totals freely: that is commutativity of `⊗`, which the constraint
monoid has only up to `⊣⊢`.  The monad laws the draft asks for (Lemma 4.3,
Theorem 4.4) do not include commutativity; it is an extra property of this
monoid.  With a non-commutative monoid of constraints — sequences recording
the order in which constraints were produced, say — answers would depend on
the selection rule, and Table 2 would need an order.  I have not formalised
that alternative.

**Remark 2 (refinement through instances).**  Def 6.5 needs the prenex form of
Table 1, with the existential variables `ỹ` pulled to the front.  Carrying the
existential witnesses as terms in `Wit` removes the prenexing: the refined
clause is used at each witness, `RefinedBy`.  This is also why Theorem 6.8
comes out for every table, not only for the tables of concrete programs.

**Remark 3 (Proposition 6.6).**  The second half needs the table's constraints
to be lax-provable.  In the canonical models every constraint is `◯`-forced at
world 2 (through world 3) but not at world 0, so the assumption is a real one.

**Remark 4 (the fallible world).**  At world 2 every `◯`-formula is forced, so
world 2 separates `S` from `◯S` only through its atoms; this is the draft's own
remark after Theorem 7.5, and the statement of Theorem 7.5 at `i = 2` has to
be about `S`, not `◯S`.

**Remark 5 (proof terms and checking).**  The draft's derived terms for
Fig. 3 are not in the form a bidirectional checker infers; the commuting
conversions `let y ⇐ (let z ⇐ p in q) in r = let z ⇐ p in let y ⇐ q in r` of
the monad bring them into it.  A statement about the draft's λ̄c calculus as
a type system would have to choose one of the two forms.

**Remark 6 (what the engine checks as it goes).**  Eager solving tests, at
each step, the conjunction of the constraints met so far; in the terms of
Definition 8.1 these are the latent constraints of the partial tree plus the
active ones.  The answer constraint is the total one, and Theorem 9.7 says it
is what extraction from the abstract proof computes.

**Remark 7 (artefacts of the draft).**  Example 2.1's figures do not match its
queries: the first query gives `P = 119999.90…` (the payment is rounded to
cents); the second's coefficient `0.263797522` belongs to `I = 0.1`, not to the
printed `I = 0.01`.  Example 9.5 stops after `k = 1`; Lemma 8.3's remaining
cases are left to the reader; "Definition ??" in Example 9.5 and "Definition
7.2" (a Lemma) in the proof of Theorem 9.4 are dangling.  All of these are
completed or checked here.
