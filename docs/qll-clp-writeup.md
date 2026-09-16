# First-order Lax Logic and Constraint Logic Programming: the mechanisation

Revised 2026-09-11 (evening).  A write-up of the Lean development of

> M. Fairtlough, M. Mendler, M. Walton, *First-order Lax Logic as a framework
> for Constraint Logic Programming*, draft of 10 September 1997 (unpublished).

Section and result numbers without a prefix refer to the draft.  Every
statement marked PROVED is kernel-checked, sorry-free, with the axiom set shown
in §13; REFUTED means a kernel-checked countermodel; OPEN and *not built* mean
what they say.  Modules live in `LaxLogic/QLL/`; the branch is
`lax-obligations`.  Paragraphs headed **Remark** are my comments, not the
draft's.  The examples (§11) are given in enough detail that every number can
be recomputed by hand from what is printed here.

## Contents

1. Overview: what is computed, and what is checked
2. The logic and its models
3. Conventional CLP, and how this development maps onto it
4. How constraints are solved
5. Horn clauses and least Herbrand models
6. Why two Herbrand worlds (and then four)
7. CLP without `◯`: proof trees, goal reduction, answers
8. The `◯` pass: abstraction, extraction, refinement
9. The canonical constraint model (Theorem 7.5)
10. Execution and certification
11. Examples, grouped by constraint domain and technique
12. Why the constraints come out unsimplified, and how to simplify en route
13. Status, with axioms
14. Remarks on the draft

---

## 1. Overview: what is computed, and what is checked

A CLP program is a list of clauses `∀x̃. S ⊃ P(x̃)` whose bodies mix program
atoms with constraint atoms such as `t ≥ s + 35`.  A query `G` is answered in
four stages.

    search (Table 2)  →  proof tree p  →  answer constraint total(p)  →  solve / project
                          checked by checkC      Θ ⊢ total(p) ⊃ G         certificates

1. **Search** resolves the query against the clauses, leftmost goal first,
   backtracking on failure, and optionally testing the growing constraint store
   for satisfiability after each constraint (`CLPEngine`).
2. The search returns a **proof tree** `p` (`CProof`).  A checker proved sound
   (`checkC`) confirms that `p` proves `G` from the program.
3. The **answer constraint** is the conjunction of the tree's constraint leaves,
   `total(p)`, and `Θ ⊢ total(p) ⊃ G` holds in QLL (`answer_sound`).
4. The answer constraint is **solved** over the constraint domain — here linear
   arithmetic over ℚ — by an untrusted solver whose answers carry certificates:
   an assignment, or Farkas multipliers, or a least value with both.

The `◯` pass factors the same computation differently (§8): prove the
*abstract* program, in which each clause has become `∀x̃. S♯ ⊃ ◯P(x̃)`, with the
constraints deleted; then extract the constraint from the abstract proof with a
writer monad; then solve it.  Theorem 9.7 says the two routes produce the same
constraint.

## 2. The logic and its models

**Syntax.**  QLL formulas `A ::= ⊤ | ⊥ | P(t̃) | A ∧ A | A ∨ A | A ⊃ A | ◯_q A |
∀x.A | ∃x.A`, locally nameless (`Syntax.lean`).  There are two lax modalities,
`q ∈ {∀, ∃}`; the draft's `◯` is `◯_∃`.  Every proof below is stated for a
general `q`.  `Prv Γ A` (written `Γ ⊢ A`) is natural deduction with cofinite
binders (`Prov.lean`); its modal rules are

    Γ ⊢ A                    Γ ⊢ ◯_q A     A, Γ ⊢ ◯_q B
    ─────────── (◯I)         ────────────────────────── (◯E)
    Γ ⊢ ◯_q A                        Γ ⊢ ◯_q B

**Kripke models** (Def 3.2, `Kripke.lean`).  A preorder `Ri` of worlds with
increasing domains, hereditary fallible worlds, and modal relations
`R_q ⊆ Ri`; the modal clause is

    w ⊨ ◯_q A   iff   for every v with w Ri v there is u with v R_q u and u ⊨ A.

Soundness is PROVED without choice, `Γ ⊢ A → Γ ⊫ A` (`Prv.sound`);
completeness (`prv_iff_consequence`, `Complete1`) uses `Classical.choice`.

**The modal relation is a parameter.**  Herbrand frames (`HFrame`) carry their
own preorder `m ⊆ le` for both `R_∀` and `R_∃`.  Fixing `m = le` is not
harmless: with no fallible worlds `◯` is then forced exactly where `¬¬` is, and
such models validate a formula QLL does not prove:

    Rm = Ri   ⟹   ⊨ (◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)                     (circ_imp_of_rm_eq_ri)
    ⊬ (◯P ⊃ ◯Q) ⊃ ◯(P ⊃ Q)                                    (not_prv_circ_imp, REFUTED cell)

The countermodel has three worlds `r ≤ s ≤ f` with `m` the identity plus
`s → f` (`ModalRelation.lean`).

## 3. Conventional CLP, and how this development maps onto it

**The CLP scheme** (Jaffar–Lassez, POPL 1987) parametrises logic programming
by a constraint domain `𝒟` (a structure and a language of constraints) and a
solver.  The standard operational account is the transition system of the
Jaffar–Maher survey (J. Logic Programming 19/20, 1994, §5): states `⟨A, C, S⟩`
with `A` the goals, `C` the *active* constraints and `S` the *passive* ones;
transitions `→r` (resolve an atom `a` with a renamed rule `h ← B`, adding the
equations `a = h` to the store), `→c` (move a constraint into the store), `→i`
(`infer`: propagate from passive to active constraints) and `→s` (continue if
`consistent(C)`, fail otherwise).  `consistent` may be incomplete: it must
accept every satisfiable store but may accept some unsatisfiable ones.  A
successful derivation ends with no goals; its store is the **answer
constraint**.  The survey's Theorem 6.1 relates this to the logical semantics:
the success set coincides with the least `𝒟`-model `lm(P, 𝒟)` (item 1); an
answer constraint `c` of `G` satisfies `P, T ⊨ c → G` for the constraint
theory `T` (item 2, soundness); and if `P, T ⊨ c → G` then finitely many
answers `c₁, …, cₙ` cover `c` (item 4, completeness — in general a
disjunction of answers is needed, unlike in plain logic programming).
**Answer projection** — eliminating the local variables of the answer so that
only the query's variables remain — is a separate step, quantifier elimination
(Jaffar–Maher–Stuckey–Yap, *Projecting CLP(R) constraints*, New Generation
Computing 11, 1993).  The draft's Table 2 follows Argenius–Voronkov (LNAI 1050,
1996).

**The correspondence.**

| conventional CLP | this development |
| :-- | :-- |
| constraint domain `𝒟` | constraint predicates `isC`; over the Herbrand universe, relations `R` (§6, world 2); for computation, linear arithmetic over ℚ (`LinQ`) |
| goal `⟨A, C⟩` | `Goal = c □ φ₁,…,φₙ` (`CLPOper`), and the engine state (goals, store) |
| `→r` with equations `a = h` | Table 2 Rule 5.  Clause heads are `P(x₁,…,xₘ)` with distinct variables (Def 5.1), so `a = h` is solved by substituting the arguments: resolution is *matching*, and every other relation between terms is an explicit constraint |
| `→c` | Table 2 Rule 1 |
| `→s`, `consistent` | the guard `ok (c ∧ B)` of Rule 1 (a parameter); in the engine, `satOK`: the certified solver, run on the whole store after each constraint; conservative (nonlinear stores are accepted) |
| `infer`, passive constraints | none; nonlinear constraints are not solved (they make the store "unknown") |
| answer constraint | `c'` at the end of a `Steps` derivation; equivalently `total(p)` of the proof tree (Theorem 9.4) |
| Theorem 6.1(2), soundness | `steps_sound` (Cor 9.8), `answer_sound`: `Θ ⊢ c' ⊃ c ∧ G` — provable in intuitionistic QLL, with no constraint theory |
| Theorem 6.1(1), `lm(P, 𝒟)` | `LHM R Θ.horn` and its fixpoint characterisations (§5) |
| solutions of `G`, completeness | `world2_free`: a closed query is true in `lm(P, R)` iff it has a proof tree whose total constraint is true in `R` |
| answer projection | only for specific shapes: least value of one variable of a difference system (`settle`, `lowerBoundCert`, `upClosed`), and single equalities by two entailments (`entailsEq`) |

**What is different.**  (i) Derivations become *proof trees*, first-class
objects that are checked, extracted from, and translated.  (ii) Soundness is
proof-theoretic: the answer constraint implies the query in QLL, with the
constraint atoms uninterpreted; the domain enters only semantically (the
relations `R` of world 2) and computationally (the solver).  (iii) The solver is
outside the trusted base: every verdict carries a certificate checked in Lean.
(iv) The lax modality separates the program's logic from its constraints, which
is the abstraction/refinement reading of §8.

## 4. How constraints are solved

**4.1 From atoms to linear constraints** (`LinQ.lean`).  A term is read as a
linear expression by `linOf`: variables, numerals (`n`, `-n`, `n/d`, parsed
from the function symbol's name), `add`, `sub`, `neg`, and `mul` when one side
is constant; anything else is not linear.  An atom `leq(a, b)`, `lt(a, b)`,
`geq(a, b)`, `gt(a, b)`, `eq(a, b)` becomes `e ≤ 0`, `e < 0` or `e = 0` with
`e = a − b` (or `b − a` for `geq`, `gt`), a `LinCon`.  `consOf` reads a
conjunction of atoms as a list of `LinCon`s and fails if any atom is not
linear.

**4.2 Certificates.**  A **witness** is an assignment `σ`; `checkWitness`
evaluates every constraint.  A **Farkas certificate** is a list of multipliers
`λᵢ`, one per constraint, with `λᵢ ≥ 0` except on equations.  The combination
`Σ λᵢ eᵢ` is computed and normalised (repeated variables merged); the
certificate is valid when every variable's coefficient is `0` and the constant
is `> 0`, or `≥ 0` with a positive multiplier on some strict constraint.
Validity refutes the system: under any `σ` satisfying all constraints,
`Σ λᵢ eᵢ(σ)` would be both equal to the constant and `≤ 0` (`< 0` in the strict
case).

    checkWitness cs σ = true         →   σ satisfies every c ∈ cs          (checkWitness_sound)
    checkFarkas (λ̃ zip cs) = true    →   no σ satisfies cs                 (checkFarkas_unsat)
    certifyVerdict cs v = sat w      →   w satisfies cs                    (certifyVerdict_sat)
    certifyVerdict cs v = unsat λ̃    →   cs is unsatisfiable               (certifyVerdict_unsat)

`certifyVerdict` keeps a solver's verdict only when its certificate checks.
Any solver can therefore be used, and none has to be trusted.

**4.3 Fourier–Motzkin elimination** (`fm`, untrusted).  Each constraint
becomes a *row*: a normalised term list, a constant, a strictness flag, and its
multiplier vector — initially the unit vector of the constraint (an equation
gives two rows, with multipliers `+1` and `−1`).  While variables remain:

* choose the variable `x` minimising `p · n`, where `p` and `n` count the rows
  with positive and negative coefficient on `x`;
* if `p · n` exceeds the cap (50 000), stop with *unknown*;
* replace the rows mentioning `x` by all combinations `(−b)·P + a·N` of a
  positive row `P` (coefficient `a > 0`) and a negative row `N` (coefficient
  `b < 0`); the combination has no `x`, is strict if either parent is, and
  carries the combined multiplier vector.

When no variables remain, a row `const > 0` (or `const ≥ 0` if strict) is a
contradiction, and its multiplier vector is a Farkas certificate.  Otherwise
the eliminated variables are given values in reverse order (back-substitution):
each variable's rows bound it from below and above given the values already
chosen.  With `l` the greatest lower bound and `u` the least upper bound,
`chooseVal` picks `(l + u)/2` if both exist and `l < u` (`l` if they meet);
`l`, or `l + 1` if that bound is strict, when there is no upper bound; `u`, or
`u − 1`, when there is no lower bound; and `0` when the variable is
unconstrained.  The result is a witness.
Elimination can grow the row set doubly exponentially; §11.D shows it failing
on a designed system.

**4.4 Entailment and projection by refutation.**  `cs ⊨ e ≤ 0` is established
by refuting `cs ∧ −e < 0` (`entailsLe`); an equation by both inequalities
(`entailsEq`).  This is how the mortgage program's answer `P = …` and
`MP = k·P` are certified (§11.C).

**4.5 Difference constraints and timing.**  Timing programs produce constraints
`x ≥ y + d` and `x ≥ d` (`asDiff` recognises them).  Their least solution is
given by longest paths from the sources (`earliest`, Bellman–Ford relaxation),
and the path that attains the value of `z` (the **critical path**) gives the
certificate: multipliers `1` on the path's constraints and on `z − z* < 0`,
`0` elsewhere.  The combination telescopes: the variables cancel and the
constant is `Σd − z* = 0` with a strict constraint used, a contradiction.  So

    lowerBoundCert cs z z* λ̃ = true   →   ∀σ ⊨ cs.  z* ≤ σ(z)          (lowerBoundCert_sound)

and a witness attaining `z*` shows it is the least value.  Finally, if `z` has a
non-positive coefficient in every inequality (`upClosed`), raising `z`
preserves solutions (`upClosed_sound`), so the projection of the answer onto
`z` is exactly `z ≥ z*` — the form of the draft's answer `z ≥ 44`.

**4.6 When solving happens.**  With `eager` set, after each constraint is added
the whole store is read by `consOf` and passed to the certified solver; an
*unsat* verdict fails the branch (the `→s` transition).  Without `eager`, the
answer constraint is solved once at the end.  Failures pruned eagerly are
refuted by checked Farkas certificates, but the engine does not keep them.  If
the store contains a nonlinear atom, `consOf` fails and the branch is not
tested at all (see §12).

**4.7 Wolfram, through the Lean–Wolfram bridge** (`CLPWolfram`, run by
`scripts/clp-wolfram.sh`).  The bridge (`~/Lean/mathematica-in-lean`) keeps
one `WolframKernel` alive and exchanges strings with it.  Variables are renamed
`v0, v1, …` and three kinds of command are sent:

* **an instance**: `FindInstance[{cons}, {vars}, Reals]`, returned as a
  comma-separated list of exact rationals; for example
  `FindInstance[{((1)*v0 + (1)*v1 + (-1)) <= 0, ((1)*v0 + (-1)*v1 + (-1)) <= 0}, {v0, v1}, Reals]`;
* **Farkas multipliers**: `FindInstance` over `l0, …, l(k−1)` subject to
  `lᵢ ≥ 0` off the equations, `Σᵢ lᵢ aᵢₓ == 0` for every variable `x`, and
  `(Σ lᵢ cᵢ ≥ 1) || (Σ lᵢ cᵢ ≥ 0 && Σ_{strict} lᵢ ≥ 1)` — the Farkas
  conditions of 4.2, normalised;
* **a minimum**: `Minimize[{v_z, And @@ {cons}}, {vars}]`, followed by a
  Farkas request for `cons ∧ z < z*`, whose multipliers are divided by the one
  on the added constraint to give `lowerBoundCert`'s form.

Every answer goes through `certifyVerdict` or `lowerBoundCert`.

## 5. Horn clauses and least Herbrand models

**Clauses** (Def 5.1, `LLP.lean`).  Σ-formulas are `S ::= ⊤ | P(t̃) | S ∧ S |
S ∨ S | ∃x.S`.  A program clause is `∀x₁…xₘ. S ⊃ H` with `H = P(x̃)` or
`◯_q P(x̃)`; a program `Θ` is a list of clauses and `Θ.forms` their formulas.
A **Horn clause** (`Horn.lean`) has a primitive positive body (no `∨`).

**Splitting a Σ-body.**  The draft's indices `ind(S)` choose one disjunct at
every `∨`; `sel S g` is `S` at index `g`:

    g ∈ ind S,  Γ ⊢ sel S g   →   Γ ⊢ S                         (Prv.of_sel)
    Γ ⊢ S   →   Γ ⊢ ⋁_{g ∈ ind S} sel S g                        (Prv.disj_sel)

so a Def 5.1 clause is provably equivalent to its Horn clauses, one per index
(`Clause.prv_toHorn`, `Clause.prv_of_toHorn`).

**The least Herbrand model** (`Herbrand.lean`).  Relative to built-in
relations `R`, `Holds R P φ` is the inductive least model — atoms of `R`, `⊤`,
`∧`, `∃` with a closed witness, and clause firing — `LHM R P` its atomic part,
and `Tp R P` the immediate consequence operator.  PROVED, for well-formed `P`:

    Tp(LHM) = LHM,     Tp(I) ⊆ I  →  LHM ⊆ I                     (Tp_LHM, LHM_least)
    LHM = ⋃ₙ Tpⁿ(∅)  =  lfp Tp                                    (LHM_iff_Tpow, LHM_eq_lfp)
    Tp(I) ⊆ I  ⟺  R ⊆ I and I ⊨ P                               (prefixpoint_iff_model)
    LHM = ⋂ { I | R ⊆ I, I ⊨ P }                                  (LHM_iff_all_models)

and Lloyd's theorems for non-modal Horn programs and closed Σ-queries:

    P ⊢ S   ⟺   S true in M_P   ⟺   P ⊫ S                       (lloyd_prv_iff, lloyd_consequence_iff)
    M_P(p, ũ)   ⟺   P ⊫ p(ũ)                                     (vanEmden_Kowalski)

Two designed cells mark the limits of the method: `⊬ P ∨ ¬P`, refuted by a
two-world Herbrand model (`lem_not_prv`), and a disjunction has no least
Herbrand model (`or_no_least_model`), which is why bodies are split into Horn
clauses first.

## 6. Why two Herbrand worlds (and then four)

Lloyd's theory uses one world: a Herbrand interpretation, a set of ground
atoms.  In one world `◯` collapses — the modal clause of §2 with a single world
gives `◯A ⟺ A` (`HTrue_circ`) — so a one-world model cannot tell *"`S` holds
outright"* from *"`S` holds up to a constraint"*, which is the distinction LLP
exists to make: a clause `∀x̃. S ⊃ ◯P(x̃)` says `P` follows from `S` only up to
an unstated constraint.

The least structure that separates them has two worlds, `0 ≤ 1`, with the
arrow modal.  Then `0 ⊨ ◯S` iff `1 ⊨ S`, while `0 ⊨ S` needs `S` at world 0
itself.  Each world is a least Herbrand model of a variant of the program:

* world 0: `Π⁰`, the program with its modal clauses deleted (`Θ.horn0`) — the
  most pessimistic reading, `◯M = (false ⊃ M) = true`, under which a modal
  clause says nothing;
* world 1: `Π¹`, the program with `◯` erased (`Θ.horn`) — the most optimistic
  reading, `◯M = (true ⊃ M) = M`, all constraints assumed solvable.

`M(Π⁰) ⊆ M(Π¹)` makes the interpretation monotone, and Lloyd's theorem applies
at each world (`HerbrandLLP.lean`):

    Θ ⊢ S      ⟺   0 ⊨ S                                        (thm_7_5_world0)
    Θ ⊢ ◯_q S  ⟺   1 ⊨ S                                        (thm_7_5_world1)

**Solvability needs two more worlds.**  To say that the constraint of a proof
is *solvable*, §7 of the draft adds world 2, carrying the least model of the
concrete program over the constraint relations, and above it a fallible world
3.  World 3 is there so that `◯` imposes nothing at world 2: from 2 the modal
arrow reaches 3, where everything holds, so `2 ⊨ ◯S` always
(`canon_circ_w2`).  Without world 3, forcing `◯P` at world 0 would require `P`
at world 2, i.e. that every constraint be solvable, and world 0 would no longer
force the abstract clauses `∀x̃. S♯ ⊃ ◯P(x̃)` (Lemma 7.2 would fail).  With it, world 2 records solvability in
its atoms only, and Theorem 7.5 at `i = 2` is about `S`, not `◯S` (§9).

Both frames take every arrow as modal (`m = le`), as the draft does.  On the
two-world frame `◯` then coincides with `¬¬`, and the frame validates the
formula of §2; this does not affect Theorem 7.5, which concerns Σ-queries only
and is proved for these frames.

## 7. CLP without `◯`: proof trees, goal reduction, answers

Every result is proved first for constraint logic programs with built-in
constraint atoms, before `◯` enters (the first of two passes).

**Proof trees** (`CLPCore.lean`).  `CProof` has constructors `top`, `cstr B t̃`
(a constraint leaf), `andI`, `orL`, `orR`, `exI t`, and `clause w t̃` (resolve
with clause `w` at instance `t̃`); `CTyped isC Θ S p` says `p` proves `S`.
Definition 8.1 splits the constraint leaves into **active** ones (not under a
clause application) and **latent** ones (under one):

    total(p) ⊣⊢ latent(p) ∧ active(p)                            (CProof.total_equiv)
    CTyped Θ S p   →   Θ ⊢ total(p) ⊃ S                          (CTyped.prv_total)

`checkC` decides `CTyped` and is proved sound (`checkC_sound`).

**Goal reduction** (Table 2, `CLPOper.lean`).  A goal is `c □ φ₁,…,φₙ`; a
`Step` applies one rule at any position: Rule 1 moves a constraint into `c`
(guarded by `ok`), Rule 2 chooses a disjunct, Rule 3 splits a conjunction,
Rule 4 opens an existential with a fresh variable, Rule 5 resolves with a
clause.  Writing `≈` for `⊣⊢`:

    c □ φ̃  ⇝*  c' □ ε   →   ∃ p̃. each pᵢ proves φᵢ,  c' ≈ c ∧ total(p₁) ∧ … ∧ total(pₙ)
                                                                  (steps_forest, Theorem 9.4)
    c □ φ̃  ⇝*  c' □ ε   →   Θ ⊢ c' ⊃ c ∧ φ₁ ∧ … ∧ φₙ              (steps_sound, Corollary 9.8)

Neither uses `ok`: solvability prunes the search and plays no part in
soundness.  Rules may be applied at any position, so the answer does not
depend on the order in which subgoals are selected (up to `⊣⊢`).

**World 2 without `◯`** (`HerbrandCLP.lean`).  With `R` interpreting the
constraint predicates (supported on constraints, closed arguments) and `Θ`
non-modal and well formed, for closed Σ `S`:

    S true in LHM_R(Θ)   ⟺   ∃ p. CTyped Θ S p ∧ total(p) true in R      (world2_free)

## 8. The `◯` pass: abstraction, extraction, refinement

**Where this comes from.**  The pattern is that of Fairtlough–Mendler–Cheng,
*Abstraction and refinement in higher order logic* (TPHOLs 2001, LNCS 2152): a
specification is split into an abstract part, stated with `◯`, and a
refinement, the concrete data the abstraction forgot; soundness of refinement
says that recombining them gives back a correct concrete statement.  §6 of the
draft applies it to CLP.  Abstraction removes the constraints from the program
and records them separately in a *constraint table*; the abstract program is
pure LLP.  A CLP computation then factors as

    prove ◯G from Θ♯        (logic programming, no constraints; world 1)
      → extract π₁|a|        (run the abstract proof in the writer monad with the table)
      → solve π₁|a|          (the constraint domain; world 2)

and the theorems below say that each arrow is sound and that the composite
computes the conventional answer constraint.

**Abstraction** (Def 6.2, Theorem 6.3, `CLPAbstract.lean`).  `S♯` replaces each
constraint atom by `⊤`; the clause `∀x̃. S ⊃ P(x̃)` becomes `∀x̃. S♯ ⊃ ◯_q P(x̃)`
(`Clause.abs`).  Abstract proof trees `AProof` use Fig. 3's rules — `val(⋆)`,
`∧◯`, `∨◯`, `∃◯`, `⊃◯` — typed by `ATyped`, and `ATyped Θ♯ q S a → Θ♯ ⊢ ◯_q S`
(`ATyped.prv`).  A concrete tree maps to an abstract one, constraint leaves
becoming `val(⋆)` (`CProof.toA`).  If no clause head is a constraint
(`HeadsOK`):

    CTyped Θ S p   →   ATyped Θ♯ q (S♯) (toA p)   →   Θ♯ ⊢ ◯_q S♯     (CTyped.toA, CTyped.prv_abs)

**Extraction** (§4 of the draft, Lemmas 8.3, 8.4).  The writer monad
`WM α = C × α`, with `val a = (⊤, a)` and `bind (c, a) f = (c ∧ π₁(f a),
π₂(f a))`, satisfies the monad laws and is commutative, up to `⊣⊢`
(`WM.bind_val_left`, `WM.bind_val_right`, `WM.bind_assoc`, `WM.bind_comm`).
Witnesses `Wit` are the values of the types `|S|` of Σ-formulas (unit, pairs,
injections, packs with a term).  A constraint table `T w t̃ z` gives the
constraint of clause `w` at instance `t̃` and witness `z`: the draft's
`θ♯₁ t̃ z`.  `a.ext T` computes `|a|` clause by clause of Fig. 3:
`|val(⋆)| = (⊤, ⋆)`, `|∧◯(p, r)| = bind |p| (λy. bind |r| (λz. val (y, z)))`,
and `|⊃◯(p, w, t̃)| = bind |p| (λz. (T w t̃ z, ⋆))`.  For the table of the
concrete program (`Program.table`, built from `ctable`):

    ctable S (wit p) = active(p)                                     (CTyped.ctable_wit, Lemma 8.3)
    π₂|toA p| = wit p,     π₁|toA p| ⊣⊢ latent(p)                    (CTyped.ext_toA, Lemma 8.4)
    π₁|toA p| ∧ active(p) ⊣⊢ total(p)                                (CTyped.ext_total)

**Theorem 9.7** — the factored computation computes the answer constraint.
For a pure query `φ` (no constraint atoms):

    ⊤ □ φ ⇝* c □ ε   →   ∃ p. CTyped Θ φ p,  ATyped Θ♯ q φ (toA p),  c ⊣⊢ π₁|toA p|     (thm_9_7)

**Refinement** (Def 6.5, Theorem 6.8, Proposition 6.6).  Def 6.5 recombines a
table with an abstract clause into the concrete clause
`∀x̃. (⋁_{g ∈ ind S} ∃ỹ. ⋀Dᵢ ∧ π₁(p x̃ g)) ⊃ P`.  It is used here through its
instances: `S @ z` (`atW`) is the disjunct of `S` that the witness `z` selects,
with its existential witnesses substituted, and `RefinedBy Δ Θ♯ T` says that
`Δ` proves `T w t̃ z ∧ (S_w[t̃] @ z) ⊃ P_w(t̃)` for every clause, instance and
witness.  Then, for **any** table:

    RefinedBy Δ Θ♯ T,  ATyped Θ♯ q S a   →   Δ ⊢ π₁|a| ⊃ S          (thm_6_8, Theorem 6.8)
    Θ non-modal   →   RefinedBy Θ Θ♯ (table Θ)                       (refinedBy_abs, Prop 6.6 first half)
    Θ non-modal,  ATyped Θ♯ q S a   →   Θ ⊢ π₁|a| ⊃ S               (cor_9_8_abs)

The last line is Corollary 9.8 by the draft's route: an abstract proof of `◯S`,
refined with the concrete program's own table, yields a constraint that
implies `S` in the concrete program.  The second half of Proposition 6.6,
`(p : θ)♭ ⊢ θ` for a modal clause, is REFUTED as stated (one-world
countermodel: `A` everywhere, `B`, `P` nowhere) and holds once the table's
constraints are lax-true:

    ∀x.(A x ∧ B x) ⊃ P x   ⊬   ∀x. A x ⊃ ◯P x                     (p66_refuted)
    ∀x.(A x ∧ B x) ⊃ P x,  ∀x. ◯B x   ⊢   ∀x. A x ⊃ ◯P x          (p66_with_lax)

## 9. The canonical constraint model (Theorem 7.5)

`HerbrandCLP.lean`.  The draft's frame, as drawn:

    0 → 1,    0 → 2 → 3,      3 fallible,   every arrow modal.

For the abstraction `Θ♯` of a well-formed non-modal program `Θ` and constraint
relations `R`: world 0 carries `M(Π⁰)` (empty, since every clause of `Θ♯` is
modal), world 1 `M(Π¹)`, world 2 `M(Θ)` over `R`, world 3 everything.  The
interpretations are monotone (Lemma 7.3, `canon_hered`) and world 0 forces
every clause of `Θ♯` (Lemma 7.2, `canon_clause`).  For a closed Σ-query `S`:

    Θ♯ ⊢ S        ⟺   0 ⊨ S                                          (thm_7_5_canon0)
    Θ♯ ⊢ ◯_q S    ⟺   1 ⊨ S                                          (thm_7_5_canon1)
    (∃a. ATyped Θ♯ q S a ∧ π₁|a| true in R)   ⟺   2 ⊨ S    (S pure)  (thm_7_5_canon2)

The draft's 2-consequence asks for a *solvable* extracted constraint (its
existential closure true); the statement here asks for a true one, the same
once the proof's witness terms are chosen to be the solution.

## 10. Execution and certification

**The engine** (`CLPEngine.lean`).  Depth-first, leftmost selection, in
continuation-passing style (`solveK`): the continuation is the rest of the
conjunction, so a failure anywhere later backtracks into the most recent
choice (an `∨` or the next clause for an atom).  Clauses are indexed by head.
Existentials get fresh variables `_v0, _v1, …`.  Every answer carries its proof
tree, checked by `checkC`:

    answer Θ … G = some a,   a.typed = true   →   Θ ⊢ a.constraint ⊃ G      (answer_sound)

**Four levels of trust.**

| checked by | trusted base | used for |
| :-- | :-- | :-- |
| the kernel, which runs the engine itself (`runL`, `decide +kernel`) | kernel | Examples 6.1, 9.5 |
| `checkC`, `certifyVerdict`, `lowerBoundCert`, run compiled | kernel + compiler; checkers proved sound | the bench |
| `certify` (`Certify.lean`) on λ̄c terms | kernel + compiler | abstract proofs of 6.1, 9.5 |
| Wolfram through the bridge | none: every answer re-checked | solver, optimiser |

**Abstract proofs as λ̄c terms** (`CLPCertify.lean`).  Fig. 3's derived terms,
read directly, nest `let` in scrutinee position, and `certify`, a bidirectional
checker, refuses them (`notInferable "ι_t(p)"`).  The let-flattened term —
values combined purely, only clause applications `w t̃ v` `let`-bound — is
equal by the monad's commuting conversions and is accepted.  `certify` does not
scale: it names binders by concatenating the names in scope (`Kit.freshFor`),
so names double in length per nested `let`; a 3-bit adder's term exhausted
memory.  A linear fresh-name function is under way in a separate task.

## 11. Examples, grouped by constraint domain and technique

| group | domain | solved by | checked by |
| :-- | :-- | :-- | :-- |
| A | uninterpreted constraint atoms | nothing to solve | kernel |
| B | linear ℚ, difference constraints | Fourier–Motzkin, longest paths | kernel (6.1), compiled checkers (B.2, B.3) |
| C | linear ℚ, general coefficients | Fourier–Motzkin, entailment | compiled checkers |
| D | linear ℚ, all of the above | Wolfram through the bridge | compiled checkers |
| E | abstract proofs as λ̄c terms | — | `certify` |

Notation: `v ≥ 5` is the atom `geq(v, 5)`; the engine's fresh variables are
`_v0, _v1, …`; linear constraints are printed as `Σ aᵢxᵢ + c ≤ 0`.

### A. Uninterpreted constraints: Example 9.5 (`CLPExamples`, kernel)

Program (arity 0; the draft's `x̃` plays no role):

    θ₀ = c₁ ⊃ P₁,     θ₁ = c₂ ⊃ P₂,     θ₂ = (P₁ ∧ c₃) ∨ (P₂ ∧ c₄) ⊃ Q.

Query `Q`.  The draft's six steps, as a `Steps` derivation (`steps95`):

    ⊤ □ Q
      ⇝ ⊤ □ (P₁ ∧ c₃) ∨ (P₂ ∧ c₄)       Rule 5, θ₂
      ⇝ ⊤ □ P₁ ∧ c₃                     Rule 2a
      ⇝ ⊤ □ P₁, c₃                      Rule 3
      ⇝ ⊤ □ c₁, c₃                      Rule 5, θ₀
      ⇝ ⊤ ∧ c₁ □ c₃                     Rule 1
      ⇝ (⊤ ∧ c₁) ∧ c₃ □ ε               Rule 1

Theorem 9.4 turns this into a one-tree forest: the engine's tree is
`θ₂[](∨₁(∧I(θ₀[](?:c₁), ?:c₃)))`, with `total = c₁ ∧ c₃`, and
`(⊤ ∧ c₁) ∧ c₃ ⊣⊢ ⊤ ∧ (c₁ ∧ c₃)`.  Corollary 9.8 gives
`Θ ⊢ (⊤ ∧ c₁) ∧ c₃ ⊃ ⊤ ∧ (Q ∧ ⊤)` (`cor95`).  Asking for all answers gives the
two branches, `c₁ ∧ c₃` and `c₂ ∧ c₄` (`all95`).  In the `◯` pass the abstract
proof extracts `((((⊤ ∧ c₁) ∧ (⊤ ∧ ⊤)) ∧ ⊤) ∧ (⊤ ∧ c₃))`, which is `⊣⊢` the
answer (`thm97_95`).  Nothing is solved: the constraints stay symbolic.

### B. Linear arithmetic over ℚ with difference constraints

**B.1 Example 6.1** (`CLPExamples`, kernel).  Program:

    θ₀ = ∀s. s ≥ 5 ⊃ A₁(s),   θ₁ = ∀s. s ≥ 9 ⊃ A₂(s),
    θ₂ = ∀t. ∃s. (A₁(s) ∧ A₂(s) ∧ t ≥ s + 35) ⊃ B(t).

Query `B(z)`.  The engine's derivation, in Table 2 terms (`u` = `_v0`):

    ⊤ □ B(z)
      ⇝ ⊤ □ ∃s. A₁(s) ∧ A₂(s) ∧ z ≥ s + 35     Rule 5, θ₂, t := z
      ⇝ ⊤ □ A₁(u) ∧ A₂(u) ∧ z ≥ u + 35         Rule 4, s := u
      ⇝ ⊤ □ A₁(u), A₂(u) ∧ z ≥ u + 35          Rule 3
      ⇝ ⊤ □ u ≥ 5, A₂(u) ∧ z ≥ u + 35          Rule 5, θ₀
      ⇝ ⊤ ∧ u ≥ 5 □ A₂(u) ∧ z ≥ u + 35         Rule 1
      ⇝ … □ A₂(u), z ≥ u + 35                   Rule 3
      ⇝ … □ u ≥ 9, z ≥ u + 35                   Rule 5, θ₁
      ⇝ … ∧ u ≥ 9 □ z ≥ u + 35                  Rule 1
      ⇝ ((⊤ ∧ u ≥ 5) ∧ u ≥ 9) ∧ z ≥ u + 35 □ ε  Rule 1

The proof tree is
`θ₂[z](∃I[u](∧I(θ₀[u](?:u ≥ 5), ∧I(θ₁[u](?:u ≥ 9), ?:z ≥ u+35))))`, and the
answer constraint `total = u ≥ 5 ∧ (u ≥ 9 ∧ z ≥ u + 35)` becomes

    [0]  −u + 5 ≤ 0
    [1]  −u + 9 ≤ 0
    [2]   u − z + 35 ≤ 0

*Fourier–Motzkin.*  `z` occurs only in [2], negatively, so `p · n = 0 · 1 = 0`
and eliminating it creates nothing; then `u` occurs only negatively in [0],
[1] (0 new rows).  No contradiction arises.  Back-substitution: `u` has lower
bounds `5` and `9`, so `u = 9`; `z` has lower bound `u + 35 = 44`, so `z = 44`.
Witness `(z, u) = (44, 9)`.

*Least value.*  Longest paths give `u = 9` (via [1]) and `z = 44` (via [2]).
The critical path [2], [1] gives the multipliers `(0, 1, 1)`, and with
multiplier `1` on `z − 44 < 0`:

    (−u + 9) + (u − z + 35) + (z − 44) = 0,  with a strict constraint used: contradiction.

So every solution has `z ≥ 44` (`lower61`).  `z` has coefficient `−1` in its
only constraint, so the answer is upward closed in `z` (`up61`), and

    (∃σ. σ(z) = r ∧ σ ⊨ total(p))  ⟺  44 ≤ r                         (ex61_answer)

*`◯` pass.*  The abstract proof extracts, verbatim,
`(((⊤ ∧ u≥5) ∧ (((⊤ ∧ u≥9) ∧ (⊤ ∧ ⊤)) ∧ ⊤)) ∧ ⊤) ∧ (⊤ ∧ (⊤ ∧ z ≥ u+35))`,
the draft's `true ⊗ … ⊗` expression; it is `⊣⊢ total(p)` (`ext61`) and implies
`B(z)` in `Θ` (`cor61`).

**B.2 Scheduling with one shared machine** (`CLPBench`, compiled checkers).
Tasks `a` (duration 3), `b` (2), `c` (4, not before time 4), `d` (2); `a`
precedes `b` and `c`, both precede `d`; `b` and `c` share a machine.

    schedule(Sa,Sb,Sc,Sd,E) ⊂ Sa ≥ 0 ∧ Sb ≥ Sa+3 ∧ Sc ≥ Sa+3 ∧ Sc ≥ 4 ∧ Sd ≥ Sb+2
                               ∧ Sd ≥ Sc+4 ∧ E ≥ Sd+2 ∧ disjoint(Sc, 4, Sb, 2)
    disjoint(X,DX,Y,DY) ⊂ Y ≥ X+DX        (c before b)
    disjoint(X,DX,Y,DY) ⊂ X ≥ Y+DY        (b before c)

Query `schedule(…) ∧ E ≤ d` with `eager` on.  The first `disjoint` clause gives
`Sb ≥ Sc + 4`; its critical path `Sc ≥ 4`, `Sb ≥ Sc + 4`, `Sd ≥ Sb + 2`,
`E ≥ Sd + 2` sums to `E ≥ 12`.  The second gives `Sc ≥ Sb + 2`, with critical
path `Sa ≥ 0`, `Sb ≥ Sa + 3`, `Sc ≥ Sb + 2`, `Sd ≥ Sc + 4`, `E ≥ Sd + 2`, so
`E ≥ 11`.

| deadline | what happens | earliest end |
| :-- | :-- | :-- |
| 12 | first branch succeeds | 12, witness `Sa, Sb, Sc, Sd = 0, 8, 4, 10` |
| 11 | first branch refuted when `E ≤ 11` is added; backtrack | 11, witness `0, 3, 5, 9` |
| 10 | both branches refuted | no answer |

The refutations at deadline 10 are Farkas certificates: multipliers `1` on the
critical path and on `E − 10 ≤ 0`.  First branch:
`(−Sc + 4) + (Sb − Sd + 2) + (Sd − E + 2) + (Sc − Sb + 4) + (E − 10) = 2 > 0`.
Second branch:
`(−Sa) + (Sa − Sb + 3) + (Sc − Sd + 4) + (Sd − E + 2) + (Sb − Sc + 2) + (E − 10) = 1 > 0`.

**B.3 Ripple-carry adders** (`CLPExamples.adder`, `CLPBench`).  Bit `i` has
five gates, with delays xor 3, and 2, or 2:

    xᵢ = aᵢ ⊕ bᵢ,   sᵢ = xᵢ ⊕ cᵢ,   gᵢ = aᵢ ∧ bᵢ,   pᵢ = xᵢ ∧ cᵢ,   cᵢ₊₁ = gᵢ ∨ pᵢ.

Each gate is a clause `out(t) ⊂ ∃s. in₁(s) ∧ in₂(s) ∧ t ≥ s + d` (`gate`): the
output settles `d` after both inputs have settled, where "`in(s)`" means
"settled by time `s`" and is upward closed.  Primary inputs are
`aᵢ(t) ⊂ t ≥ 0`, `bᵢ(t) ⊂ t ≥ 0`, `c₀(t) ⊂ t ≥ 0`.  An `n`-bit adder has
`7n + 1` clauses.

*The recurrence.*  `xᵢ` settles at 3 and `gᵢ` at 2.  `p₀ = max(3, 0) + 2 = 5`,
`c₁ = max(2, 5) + 2 = 7`; for `i ≥ 1`, `pᵢ = cᵢ + 2` and `cᵢ₊₁ = cᵢ + 4`.  So
`cₙ` settles at `4n + 3`; `sᵢ = cᵢ + 3` for `i ≥ 1` and `s₀ = 6`, so the
carry-out is the latest output.

*Worked case, n = 2, query `c₂(z)`.*  The answer constraint has 17 entries
(`v0…v7` are the engine's fresh variables):

    [0] −v1 ≤ 0          [1] −v1 ≤ 0          [2]  v1 − v0 + 2 ≤ 0
    [3] −v3 ≤ 0          [4] −v3 ≤ 0          [5]  v3 − v2 + 3 ≤ 0
    [6] −v5 ≤ 0          [7] −v5 ≤ 0          [8]  v5 − v4 + 2 ≤ 0
    [9] −v7 ≤ 0          [10] −v7 ≤ 0         [11] v7 − v6 + 3 ≤ 0
    [12] −v6 ≤ 0         [13] v6 − v4 + 2 ≤ 0 [14] v4 − v2 + 2 ≤ 0
    [15] v2 − v0 + 2 ≤ 0 [16] v0 − z + 2 ≤ 0

Each `vᵢ` is the `s` of one gate clause: the time by which that gate's inputs
have settled.  Longest paths give `v7 = 0` (`a₀, b₀` into `x₀`), `v6 = 3` (`x₀`
into `p₀`), `v4 = 5` (`p₀` into `c₁`), `v2 = 7` (`c₁` into `p₁`), `v0 = 9`
(`p₁` into `c₂`), `z = 11`, and `v1 = v3 = v5 = 0`; this is the witness.  The critical path is
[16], [15], [14], [13], [11], [9], with delays `2 + 2 + 2 + 2 + 3 + 0 = 11 =
4·2 + 3`; its multipliers, `1` on those six entries and on `z − 11 < 0`, give
the lower-bound certificate.

*Sizes and results* (each carry-out certified from both sides; the last row
queries all outputs at once):

| n | clauses | proof tree | constraints | carry-out settles |
| :-- | :-- | :-- | :-- | :-- |
| 8 | 57 | 226 | 65 | 35 |
| 16 | 113 | 450 | 129 | 67 |
| 32 | 225 | 898 | 257 | 131 |
| 64 | 449 | 1 794 | 513 | 259 |
| 8, all 9 outputs | 57 | 1 146 | 329 | 35 (latest) |
| 16, all 17 outputs | 113 | 4 082 | 1 169 | 67 (latest) |
| 32, all 33 outputs | 225 | 15 330 | 4 385 | 131 (latest) |

Compiled (`CLPBench`), search with proof checking took at most 22 ms per row,
and solving with certification at most 33 ms.

### C. Linear arithmetic with general coefficients: the mortgage program

Example 2.1 (`CLPExamples.mortgage`), over ℚ, `eager` on:

    mortgage(P,D,I,MP,B) ⊂ D ≤ 1 ∧ B + MP = P·(I + 1)
    mortgage(P,D,I,MP,B) ⊂ 1 < D ∧ mortgage(P·(I + 1) − MP, D − 1, I, MP, B)

The rate is a numeral in the query, so `P·(I + 1)` is linear.  With `r = 1 + I`
and `B = 0`, the balances are `P₀ = P`, `Pₖ = Pₖ₋₁·r − MP`, and the base clause
applies at `D = 1`, where `MP = P_{D−1}·r`.  Hence

    P·r^D = MP · (1 + r + … + r^{D−1}).

*Worked case, D = 2, I = 1/100.*  The engine tries the base clause first;
`2 ≤ 1` is refuted at once, and it resolves with the recursive clause and then
the base clause.  The proof tree's constraints are `1 < 2`,
`sub(2, 1) ≤ 1` and `add(0, MP) = mul(sub(mul(P, add(1/100, 1)), MP),
add(1/100, 1))`, read as

    −1 < 0,     0 ≤ 0,     MP − (10201/10000)·P + (101/100)·MP = 0,

i.e. `(201/100)·MP = (10201/10000)·P`.  Fourier–Motzkin returns the witness
`P = MP = 0` (the system is homogeneous); the relation itself is what the
query asks for, and it is certified as an entailment in both directions
(§4.4).

*Query 1*: `D = 120, I = 1/100, MP = 1721.65, B = 0`.  The derivation makes
119 recursive steps; each first tries the base clause, whose ground `D ≤ 1`
(for instance `120 ≤ 1`) is refuted eagerly, and backtracks into the recursive
clause.  The answer has 121 constraints: 119 ground `1 < D`, one ground
`D ≤ 1`, and one equation in `P`.  Solving gives the exact rational
`P = MP · Σ_{k=1}^{120} r^{−k}`, a 246-digit numerator over a 241-digit
denominator, `= 119999.9037…`; `P` is determined (both inequalities entailed).
The whole query took 1.5 s compiled.  Wolfram agrees.

*Query 2*: `D = 5, B = 0`, rate symbolic in `P` and `MP`:

| rate | certified answer |
| :-- | :-- |
| `I = 1/100` | `MP = (10510100501/51010050100)·P = 0.2060397996…·P` |
| `I = 1/10` | `MP = (161051/610510)·P = 0.2637974808…·P` |

The draft prints `MP = 0.263797522·P` for `I = 0.01`; that figure belongs to
`I = 0.1`, and its first query's `P = 120000` is `119999.90…` rounded.

### D. Wolfram as the solver (`CLPWolfram`, compiled checkers)

The systems of B and C, plus one designed to defeat elimination, were sent to
Wolfram through the bridge (§4.7); every answer passed the Lean checks.

| system | constraints | Wolfram | Fourier–Motzkin |
| :-- | :-- | :-- | :-- |
| Example 6.1 | 3 | sat, 2 ms; least `z = 44` (both certificates), 7 ms | sat |
| mortgage, query 1 | 121 | sat, 17 ms | sat |
| schedule (c before b), `E ≤ 10` | 10 | unsat (Farkas), 10 ms | unsat (Farkas) |
| adder carry-out, n = 8, 16, 32 | 65, 129, 257 | sat, 57 / 196 / 741 ms; least 35 / 67 / 131, 0.26 / 1.0 / 4.9 s | sat |
| adder, all outputs, n = 4, 8 | 101, 329 | sat, 27 / 185 ms; least 19 / 35, 0.38 / 6.3 s | not run |
| `±xᵢ ± xⱼ ≤ 1`, `n = 5` | 40 | sat, 832 ms | unknown |
| same with `Σ xᵢ ≥ 5` | 41 | unsat (Farkas), 69 ms | unknown |

Fourier–Motzkin took under 1 ms wherever it answered.  Timings are from one
run of `scripts/clp-wolfram.sh` and include the round trip to the kernel.

*The designed system.*  All `±xᵢ ± xⱼ ≤ 1` for `0 ≤ i < j < 5`: 40 constraints,
satisfiable at `x = 0`, which is Wolfram's witness.  Elimination grows the rows
`40 → 88 → 411 → 10 211`, and the next step would combine `2 935 × 2 935 =
8 614 225` pairs, past the cap, so Fourier–Motzkin answers *unknown*.  With
`Σ xᵢ ≥ 5` added (written `−Σ xᵢ + 5 ≤ 0`) the system is infeasible, since the
pairwise bounds `xᵢ + xⱼ ≤ 1` force `Σ xᵢ ≤ 5/2`.  Wolfram's certificate puts
multipliers on five constraints:

    1/5·(x₀ + x₃ − 1) + 1/5·(x₀ + x₄ − 1) + 2/5·(x₁ + x₂ − 1) + 1/5·(x₃ + x₄ − 1)
      + 2/5·(−x₀ − x₁ − x₂ − x₃ − x₄ + 5)  =  1  >  0,

every variable's coefficient cancelling (`x₀`: `1/5 + 1/5 − 2/5`; `x₁`, `x₂`:
`2/5 − 2/5`; `x₃`, `x₄`: `1/5 + 1/5 − 2/5`).

### E. Abstract proofs as λ̄c terms (`CLPCertify`)

Example 6.1's abstract proof, let-flattened (§10), is

    let∃ u ⇐ π[s] θ₀ ⋆ in let∃ v ⇐ π[s] θ₁ ⋆ in let∃ w ⇐ π[z] θ₂ ι[s] (u, (v, ⋆)) in val∃ w

(`π[t]` instantiates a clause, `ι[t]` packs an existential witness): apply `θ₀`
and `θ₁` at `s` to `⋆`, pack their results at `s`, apply `θ₂` at `z`.
`certify` accepts it, and Example 9.5's, as derivations of `◯B(z)` and `◯Q`
from the abstract programs.

## 12. Why the constraints come out unsimplified, and how to simplify en route

The examples show several redundancies.  Each has a specific cause; each can be
removed during the computation without weakening what is certified.

| redundancy | seen in | cause | remedy | justification |
| :-- | :-- | :-- | :-- | :-- |
| `⊤` units: `(⊤ ∧ c₁) ∧ (⊤ ∧ ⊤)` | extraction (A, B.1) | `val` contributes `⊤` and every `bind` a `∧`; the monad laws hold only up to `⊣⊢`, so nothing rewrites them | extract with a normalising conjunction `c ⊗ d` that drops `⊤` operands | `c ⊗ d ⊣⊢ c ∧ d`, one lemma; every theorem is already stated up to `⊣⊢` |
| ground constraints kept: `1 < 2`, `sub(2,1) ≤ 1` | C | resolution substitutes arguments unevaluated, and the store is only tested, never rewritten | decide ground atoms on entry: drop if true, fail if false | evaluation is the certificate; in Jaffar–Maher terms this is `infer` simplifying the store |
| unevaluated arithmetic: `add(0, MP)`, nested `mul(sub(mul(P, …), MP), …)` | C | Herbrand terms; heads are variables, so nothing forces evaluation; argument terms grow by one level per step | either fold constants when instantiating a clause body, or introduce a fresh variable with an equation for each compound argument (`P₁ = 1.01·P − MP`), as CLP(R)'s `→r` does | folding is sound because the domain interprets terms by evaluation; the equation form keeps terms small (linear total size instead of quadratic) |
| unmerged linear forms: `MP + … + (101/100)·MP` | C | `Lin.add` concatenates term lists; normalisation happens only inside the solver | normalise when reading an atom (`norm` in `linOf`) | `sumTerms_norm` |
| duplicated constraints: `−v1 ≤ 0` twice | B.3 | each gate reads both inputs at the same `s`, and `aᵢ`, `bᵢ` yield the same constraint | keep the store as a set | set membership |
| shared subgoals re-derived: 15 330 nodes for 225 clauses | B.3, all outputs | SLD search is tree-shaped: `cᵢ` is proved again for every `sⱼ` and `cⱼ` above it | table solved subgoals: record `cᵢ(t) ⊂ t ≥ 4i + 3` once, as a derived clause, and resolve with it thereafter | the derived clause is proved by answer soundness plus a projection certificate (lower bound and upward closure) |
| dead local variables `_v0, _v1, …` | B, C | no projection of answers | project the store onto the query's variables as variables become unreachable | two entailments per projected constraint, or the timing certificates of §4.5 |
| nonlinear store blocks testing | — | `consOf` fails on the whole store if one atom is nonlinear | test the linear part only, keeping nonlinear atoms passive, as CLP(R) does | the linear part's refutation refutes the whole store |

Each remedy is either a syntactic normalisation proved `⊣⊢` once, or a step
justified by a certificate at the time it is taken.  The first four are local
changes; tabling and projection change the shape of answers and would need
their own soundness statements (for tabling, that a derived clause is a
consequence of the program — `answer_sound` gives that directly).

## 13. Status, with axioms

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
certificates and everything that evaluates them) and `OrderHom.lfp`.

**Not built.**  Fig. 1's Gentzen system (stage 1); Def 6.5's refined clauses
as formulas; constraints beyond linear arithmetic; the simplifications of §12.

## 14. Remarks on the draft

**Remark 1 (commutativity is what selection independence uses).**  Theorem
9.4 holds for derivations selecting subgoals in any order, and its proof
reorders totals freely: that is commutativity of `⊗`, which the constraint
monoid has only up to `⊣⊢`.  The monad laws the draft asks for (Lemma 4.3,
Theorem 4.4) do not include it.  With a non-commutative monoid of constraints,
answers would depend on the selection rule.  This is also where Prolog's cut
sits; see `docs/qll-clp-pruning-and-cut.md`.

**Remark 2 (refinement through instances).**  Def 6.5 needs Table 1's prenex
form.  Carrying existential witnesses as terms in `Wit` removes the prenexing;
it is also why Theorem 6.8 holds for every table.

**Remark 3 (Proposition 6.6).**  The second half needs the table's constraints
to be lax-provable.  In the canonical model constraints are `◯`-forced at world
2 (through world 3) but not at world 0, so the assumption is a real one.

**Remark 4 (proof terms and checking).**  The draft's derived terms for Fig. 3
are not in the form a bidirectional checker infers; the commuting conversions
`let y ⇐ (let z ⇐ p in q) in r = let z ⇐ p in let y ⇐ q in r` bring them into
it.

**Remark 5 (artefacts of the draft).**  Example 2.1's figures do not match its
queries (§11.C).  Example 9.5 stops after `k = 1`; Lemma 8.3's remaining cases
are left to the reader; "Definition ??" in Example 9.5 and "Definition 7.2" (a
Lemma) in the proof of Theorem 9.4 are dangling.  All are completed or checked
here.

## References

- J. Jaffar, J.-L. Lassez, *Constraint logic programming*, POPL 1987, 111–119.
- J. Jaffar, M. J. Maher, *Constraint logic programming: a survey*, J. Logic
  Programming 19/20 (1994), 503–581.
- J. Jaffar, M. Maher, K. Marriott, P. Stuckey, *The semantics of constraint
  logic programs*, J. Logic Programming 37 (1998), 1–46.
- J. Jaffar, M. J. Maher, P. J. Stuckey, R. H. C. Yap, *Projecting CLP(R)
  constraints*, New Generation Computing 11 (1993), 449–469.
- M. Argenius, A. Voronkov, *Semantics of constraint logic programs with
  bounded quantifiers*, LNAI 1050 (1996), 1–18.
- J. W. Lloyd, *Foundations of Logic Programming*, 2nd ed., Springer 1987.
- M. H. van Emden, R. A. Kowalski, *The semantics of predicate logic as a
  programming language*, J. ACM 23 (1976), 733–742.
- M. Fairtlough, M. Mendler, X. Cheng, *Abstraction and refinement in higher
  order logic*, TPHOLs 2001, LNCS 2152, 201–216.
- E. Moggi, *Notions of computation and monads*, Information and Computation
  93 (1991), 55–92.
