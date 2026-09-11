# Lax Logic for CLP: review against three questions, and the revised plan

Dated 2026-09-11.  Matthew asked for this review before stages 3–6 are
implemented: of the value of the approach, its implementability, and a
significant application, with the plan reviewed against the answers.  Nothing
here is machine-checked unless it names a Lean declaration.  Literature
citations are from memory unless marked *read*.

## 0. The modal relation of the Herbrand models

Matthew's objection: agents in this development keep extending `◯`-free model
theory to `◯` by choosing `Rm = Ri` or `Rm` reflexive, and this is rarely right.
The repository already records why.  With `Rm = Ri` and no fallible worlds,
`◯M` is forced exactly where `¬¬M` is (`force_somehow_iff_notnot`,
`docs/route-b-model.md`), so `Rm = Ri` is the double-negation instance of the
semantics.  It validates non-theorems of QLL.  The designed witness,
kernel-checked in `LaxLogic/QLL/ModalRelation.lean`:

    (◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)

This holds at every world of every model with `Rm = Ri` (`circ_imp_of_rm_eq_ri`,
a classical argument), and QLL does not prove it (`not_prv_circ_imp`: three
worlds `r < s < f`, `f` fallible, `Rm` the identity plus `s → f`).  So a class
of models with `Rm = Ri` cannot be complete for QLL.  Nor can it serve as the
semantics of any extension of LLP whose queries or clause bodies contain `◯`
under `⊃`.

Two things are separate here.

* **The draft's own §7 frame does have every arrow modal**: "where all arrows
  are Rm accessibilities and world 3 is fallible" (temp.pdf, p. 17, *read*).  On
  that four-world frame `Rm` and `Ri` coincide.  That is harmless *for LLP*:
  queries are Σ or `◯`Σ, and `◯` occurs only in clause heads.  Theorem 7.5 at
  worlds 0 and 1 is proved in exactly that setting (`thm_7_5_world0/1`).
* **What was wrong is mine.**  I built `Rm = Ri` into the general Herbrand-frame
  construction (`HFrame.model` set `RA = RE = le` for every frame).  I also
  described Def 7.1 as "a predicate on `CModel`s with `Rm = Ri`".  Both are now
  corrected.  `HFrame` carries its own modal relation `m ⊆ le`.  The §7 frame
  is one instance, whose `m` is its order because the draft draws it so.  Def
  7.1 fixes the frame F; it is not a condition on constraint models in general.

## 1. Is it a contribution to the theory of CLP, beyond the verification?

The reviewers' question was "why a new semantics?".  The answer should be:
*this is not a new semantics for CLP*.  It is a proof-theoretic interface —
proof terms, plus a constraint-extraction map — together with the model theory
that says the interface is exact.  What that interface adds, as I see it:

1. **Certificates for answers.**  An SLD computation of CLP(X) yields an LLP
   proof term whose extracted constraint is the answer constraint (Thm 9.7).
   A CLP system can therefore emit a checkable certificate: a proof term, a
   small verified checker (`Certify.lean`), and a constraint certificate, i.e. a
   solution or a Farkas refutation.  This is the certifying-algorithm paradigm
   (McConnell, Mehlhorn, Näher, Schweitzer, *Computer Science Review* 2011)
   applied to CLP.  I know of no CLP system that certifies its answers.
2. **Separation of logic from constraints, as a theorem.**  Abstraction (Def
   6.2) and refinement (Def 6.5) split a CLP program into an abstract logic
   program and a constraint table, and put it back together.  Thms 6.3/6.8
   make "analyse the control, abstract the constraints" a sound transformation
   with proofs mapping across.  Abstract interpretation of CLP exists, but it
   is not a logic with proof terms.
3. **Monads locate the CLP-specific structure precisely.**  Matthew's question
   was whether the strong-monad laws are too restrictive.  I think they are
   *too weak*, and usefully so:
   * Every monad in a type theory is strong.  The laws only say that the
     extracted constraint does not depend on how a derivation is bracketed.
   * The properties CLP actually relies on are extra structure:
     * *commutativity* of the monad (for the writer monad `C × −`, a
       commutative constraint monoid) is independence of the computation rule,
       Lloyd's switching lemma;
     * *idempotence* is removal of duplicate constraints;
     * *projection* of local variables needs `∃` on constraints: the cylindric
       constraint systems of Saraswat, Rinard and Panangaden (POPL 1991).
   * So the framework separates what every notion of constraint must satisfy
     (the laws) from what particular CLP(X) schemes add.  It also admits
     **non-commutative** constraint monoids, where the computation rule
     matters: time-sequenced, resource, or ordered constraints.  That is a
     genuine new direction.  CLP(X) assumes conjunction.
4. **Database theory: provenance.**  Take the writer monad over the
   multiplicative monoid of a commutative semiring, and sum over the proofs of
   a query.  The result is the provenance polynomial of Green, Karvounarakis and
   Tannen (PODS 2007).  The disjunction of answer constraints of a CLP query is
   the same construction over a constraint semiring.  So LLP constraint
   extraction includes Datalog how-provenance, and semiring-based CLP
   (Bistarelli, Montanari, Rossi, TOPLAS 2001) as the quantitative case.  The
   Herbrand stage already has `T_P` relative to built-in relations.
   Semiring-annotated `T_P` is the natural next step, where convergence is
   delicate (Khamis, Ngo, Pichler, Suciu, Wang, PODS 2022).
5. **Constructive content.**  Completeness for the Horn/LLP fragment holds
   without choice (`lloyd_completeness`, `llp_completeness0/1`), whereas general
   QLL completeness (Lindenbaum) uses it.  The operational semantics of CLP lives
   entirely on the constructive side.

The risk is the same as in 1997: a referee who sees only the semantics.  The
remedy is results that CLP theory cannot state without proof terms: certified
answers, abstraction/refinement as proof transformations, and the
monad-structure dictionary.  The nearest modern work is monadic constraint
programming (Schrijvers, Stuckey, Wadler, JFP 2009).  It models solvers and
search with monads in Haskell, but has no logic and no extraction theorem.

## 2. An efficient, certified implementation in Lean

What exists: the verified checker `certify : Ctx → Pf → Form → Except Err
(Derives p Γ A)`, whose soundness is by construction.  What is needed, and the
design:

* **Proof trees, not raw terms.**  An inductive `CProof` of rule applications:
  `true`, a constraint leaf, `∧`, `∨ᵢ`, `∃t`, clause application.  One tree
  has two typings: *concrete*, a proof of `S` from the CLP program `Π` with
  constraint atoms as leaves, and *abstract*, a proof of `◯S♯` from `Π♯₂`
  (Def 8.2's translation is the identity on trees).  `toPf` sends a tree to
  the draft's Fig. 3 term, which `certify` checks.
* **Extraction** `total`, `active`, `latent` (Def 8.1) as structural maps on
  trees, into constraints represented as formulas.  The monoid laws hold up to
  `⊣⊢`, as the draft says they should.
* **The engine.**  SLD resolution per Table 2 over a goal `c □ φ₁ … φₙ`.
  Because Def 5.1 heads are `P(x₁, …, xₘ)`, resolution is matching, not
  unification: all term structure is in constraints (`eq`, `leq`, …).  The
  engine builds the forest of Thm 9.4 as it goes, so every state carries the
  partial proofs and their total constraint.  Incremental solving (pruning
  unsatisfiable branches) is then exactly §8's active/latent split: the
  latent constraint of a partial proof is what is already committed.
* **Solvers.**
  * A linear-arithmetic solver over ℚ in Lean: Fourier–Motzkin, with
    certificates (a witness for satisfiability, Farkas multipliers for
    unsatisfiability), each checked by a function proved sound.
  * A difference-constraint solver (longest paths, Bellman–Ford) for timing,
    with the potentials as the certificate.
  * **Wolfram.**  A licensed Wolfram 14.3 kernel is on this machine
    (`wolframscript`; `Reduce` answered a test query in under a minute).
    Outside answers are *untrusted*: Lean re-checks every witness exactly.
* **What is certified.**  For a query `S`, the engine returns a tree `p` and an
  answer constraint `c`, and the theorems give `Π ⊢ total(p) ⊃ S` (Cor 9.8).
  When `c` is solved to a witness, the ground instance of `S` holds in the
  least model.  Proof terms are checked at run time by the compiled verified
  checker.  Kernel-checked certificates for large runs would need
  `native_decide`, which the repository does not admit; small runs are checked
  by the kernel.
* **State of the art.**  CLP systems (SICStus/SWI `clp(q,r)`, ECLiPSe, CHR)
  are far faster and certify nothing.  Certified SAT (DRAT) and SMT (proof
  checking in Lean or Coq) certify solvers but not logic programs.  The
  improvement on offer is certification, not speed.  The separation of phases
  (abstract search, then extraction and solving, or interleaved through the
  latent constraint) is a clean account of what CLP systems do anyway.

## 3. A significant program

Timing analysis of combinational circuits is the draft's own motivating
domain (Example 6.1), and it scales.  An `n`-bit ripple-carry adder is `5n`
gates; an `n × n` array multiplier is roughly `6n²`.  Each gate is one LLP
clause `∀t. ∃s₁ s₂. (I₁(s₁) ∧ I₂(s₂) ∧ t ≥ s₁ + d ∧ t ≥ s₂ + d) ⊃ O(t)`: Example
6.1's shape.  A 32-bit adder is about 160 gates plus wiring, and an 8 × 8
multiplier several hundred, so programs of hundreds of clauses arise with no
padding.  The query `◯ O(t)` asks when the output settles.  The extracted
constraint is a system of difference constraints, and its least solution is
the critical path: the standard algorithm of static timing analysis.  Two
more classical CLP programs: the CLP(R) mortgage program, which is linear once
the rate is fixed, and precedence scheduling (difference constraints again).
All three are certified end to end.

## 4. The plan, revised

Two passes throughout, as agreed: every result for the `◯`-free fragment
(CLP(X) with built-in constraints), then extended to `◯` (LLP).  Stage numbers
refer to `docs/qll-clp-implementation-plan.md`.

| step | `◯`-free pass | `◯` pass |
| :-- | :-- | :-- |
| M | `HFrame` with its own modal relation; the double-negation cell (§0) | — |
| C1 | constraint domains; linear ℚ arithmetic with certificates; difference constraints | — |
| C2 | `CProof`, concrete typing, `total`; `Π ⊢ total(p) ⊃ S`; least model with constraint relations `↔` a proof with a true `total` | abstract typing of the same trees; `toPf`; `Π♯₂ ⊢ ◯S♯` (Thm 6.3) |
| 3 | — | writer-monad extraction `|p|`; `|p|` = `total` (Lemma 8.4); the λc equations for `val`/`let` (Lemma 4.3, Thm 4.4 read equationally); commutativity ⟺ order independence |
| 4 | abstraction `♯` of clauses, the constraint table | refinement `♭`; Prop 6.6 via `Prv.disj_sel`; Thm 6.8, Cor 9.8 |
| 6 | Table 2 goal reduction; Thm 9.4 (the forest and its totals) | Thm 9.7 (extracted = answer constraint) |
| E | engine: SLD with a solver interface, proof trees out, run-time `certify` | abstract proofs and extraction out |
| X | examples: mortgage, scheduling, Example 6.1 and 9.5; generated circuits with hundreds of clauses; optional Wolfram cross-check | same through the modal reading |
| 5 | — | world 2 and the fallible world 3 over `Π²`; Thm 7.5 at `i = 2` |
| 1 | Gentzen system (Fig. 1) | last, if time |

**Status, 2026-09-11 (evening).**  Both passes are built, except stage 1.

* `◯`-free pass: M, C1, C2 (proof trees, typing, `Θ ⊢ total(p) ⊃ S`), 6
  (Table 2, Thm 9.4, Cor 9.8), E (`CLPEngine`) and X (`CLPExamples`,
  kernel-checked; `CLPBench`, run).  Bench: adders to `n = 64` (449 clauses),
  carry-out settling at `4n + 3`, certified from both sides; the mortgage
  program exactly over ℚ; scheduling with a disjunctive machine constraint,
  backtracking under a deadline.
* `◯` pass (`CLPAbstract`, `HerbrandCLP`): abstraction and abstract proof trees
  (Thm 6.3); the writer monad and extraction (Lemmas 8.3, 8.4, Thm 9.7);
  refinement through clause instances, Thm 6.8 for arbitrary tables and Prop 6.6
  (first half); the four-world canonical model, Lemma 7.2 and Thm 7.5 for
  `i = 0, 1, 2`; Examples 6.1 and 9.5 carried through both passes.  Every
  `◯`-pass theorem is pinned `[propext]` or `[propext, Quot.sound]`.
* Abstract proofs as λ̄c terms (`CLPCertify`): the direct reading of Fig. 3
  nests `let` in scrutinee position and the verified checker `certify` refuses
  it (`notInferable "ι_t(p)"`); the let-flattened term, equal by the monad's
  commuting conversions, is accepted for Examples 6.1 and 9.5 (`#guard_msgs`
  in the build).  It does not scale: `certify` names each binder
  `freshFor` of the names in scope, which concatenates them
  (`Kit.freshFor_byteSize`), so names double in length with every nested
  `let`; on a 3-bit adder (about 25 nested lets) the run reached 38 GB and was
  killed.  A fresh name one byte longer than the longest in scope would grow
  linearly with the same freshness proof; flagged as a separate task.
* REFUTED: Proposition 6.6, second half (`(p : θ)♭ ⊢ θ` for a modal clause):
  a one-world countermodel (`HerbrandCLP.p66_refuted`).  It holds once the
  table's constraints are assumed lax-true (`p66_with_lax`).
* Not built: stage 1 (Fig. 1's Gentzen system); Def 6.5's refined clauses as
  formulas (they are used through their instances, `RefinedBy`); a
  programmatic Wolfram bridge (Wolfram was used once, by hand, to cross-check
  the mortgage figures).

Two decisions made in writing this.

* **Constraints are formulas.**  `⊗ = ∧`, `ε = ⊤`, and the monoid laws hold
  up to `⊣⊢`.  This is the draft's own choice (§4), and it lets every
  extraction theorem be a `Prv` statement.
* **Constraint atoms are interpreted over the Herbrand universe**, as §7
  assumes ("a relation `R_B` on `H`"): numerals are nullary function symbols,
  and arithmetic terms evaluate by a partial function.  The whole of stage H
  applies unchanged, with `R` the constraint relations.
