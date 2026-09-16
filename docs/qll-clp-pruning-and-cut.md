# Pruning in CLP and Prolog's cut: a research note

Dated 2026-09-11.  Research only; nothing here is implemented.  The question:
is there an obvious, published correlation between constraint pruning in CLP
and Prolog's cut, and could the lax-logic development build on it?

## Short answer

Yes, and it is published, though not under the name "constraint pruning".  The
link runs through **committed choice with constraint guards**.  In concurrent
constraint languages a clause is guarded by a constraint, and committing to a
clause prunes its alternatives, as cut does.  The literature characterises
when such pruning is logically harmless: when the guard is **quiet**, i.e.
*entailed* by the store rather than merely consistent with it.  Prolog's cut is
the unrestricted, order-dependent case.

For this development the link is concrete, because entailment, consistency and
lower bounds all have certificates here already.  Each kind of pruning could be
logged with a certificate and checked.

## What is published

**Pruning operators in logic programming.**  Naish, *Pruning in Logic
Programming* (1995), surveys cut, commit, `once`, conditionals and their
variants.  Pruning operators are typically not declarative, and they cause
incompleteness or unsoundness.  Andrews, *The witness properties and the
semantics of the Prolog cut* (TPLP 3(1), 2003), shows that a generalisation of
Prolog with negation as failure and cut lacks the "witness properties"
(operational consistency of answers).  He then gives a restriction that keeps
cut's choice and first-solution behaviour and has them.

**Cut, algebraically.**  Piróg and Staton, *Backtracking with cut via a
distributive law and left-zero monoids* (JFP 27, 2017), add cut to the list
monad by algebraic effects.  The resulting monad is the monad of free
**left-zero monoids**: cut behaves as an element `!` with `! · x = !`, a
left-zero only.  Equivalently, it is the list monad composed, by a distributive
law, with the monad of a unary idempotent operation.  The scope delimiter of
cut arises as a handler.

**Committed choice and constraints.**
- **Maher**, *Logic semantics for a class of committed-choice programs* (ICLP
  1987), gives the ALPS class a logical semantics. ALPS moves concurrent logic
  programming towards CLP(X), with commitment governed by constraint entailment.
- **Saraswat's** concurrent constraint programming (MIT Press, 1993) makes this
  the primitive. `ask c` blocks until the store entails `c`; `tell c` adds `c`
  if it is consistent.
- **Jaffar–Maher** (the 1994 survey, in the discussion after its Theorem 6.1)
  note that matching, used by GHC and NU-Prolog as a basis for the computation
  rule, corresponds in CLP to constraint entailment.

**Quiet pruning in AKL.**  The Andorra Kernel Language (Haridi–Janson, ICLP
1990; Janson–Haridi) has three guarded choice statements over local constraint
stores:
- **Conditional choice `→`:** Prolog's if-then-else, cut-like. It commits to
  the *first* remaining guard, once that guard's store is **entailed** by the
  external store.
- **Committed choice `|`:** it commits to *any* guard whose store is entailed.
- **Nondeterminate choice `?`:** it proceeds only when a single clause remains,
  or when no other step is possible.

In all three, a guard whose store is inconsistent with the external store fails
and its clause is deleted: pruning by unsatisfiability. Franzén, *Logical
aspects of the Andorra Kernel Language* (SICS R91:12, 1991), gives the logical
reading. AKL restricts pruning to **quiet** guards — no speculative bindings of
external variables — because quiet pruning is comparatively insensitive to the
order of execution.

**Pruning in CLP systems.**
- **Failure pruning:** Jaffar–Maher's `→s` transition fails a derivation whose
  store is inconsistent.
- **Branch and bound** (Van Hentenryck, *Constraint Satisfaction in Logic
  Programming*, MIT Press 1989, the CHIP work) prunes branches whose bound
  cannot beat the incumbent; it is sound for optimal answers, not for all
  answers.
- **Constraint Handling Rules** (Frühwirth, JLP 37, 1998) is a committed-choice
  language of guarded rules that simplify the store.
- **Monadic constraint programming** (Schrijvers–Stuckey–Wadler, JFP 19, 2009)
  treats search strategies and pruning as composable transformers over a
  monadic search tree.
- **Proof logging for constraint programming** (Gocht–McCreesh–Nordström, *An
  Auditable Constraint Programming Solver*, CP 2022) records each pruning step
  as a cutting-planes proof checked by VeriPB. This is the certificate idea
  applied to propagation and search.

## How it lines up with this development

Three kinds of pruning, and the certificate each would carry here.

| pruning | condition | order dependence | certificate available here |
| :-- | :-- | :-- | :-- |
| **failure** (`→s`, AKL's failed guards) | the store is unsatisfiable | none | Farkas multipliers (`certifyVerdict_unsat`) |
| **quiet commit** (AKL `|`, `ask`) | the guard is entailed by the store | little (Franzén) | entailment by refutation (`entailsLe`), Farkas again |
| **bound** (branch and bound) | the branch's objective is bounded by the incumbent | none for optimal answers | `lowerBoundCert` |
| **cut** (Prolog `!`, AKL `→`) | first success in textual order | essential | none needed or possible: the pruned branches are simply dropped |

My reading, not a published result, runs as follows.

- **Failure pruning is a zero, and is harmless.** It corresponds to the
  constraint monoid's zero: `⊥ ∧ c ⊣⊢ ⊥ ⊣⊢ c ∧ ⊥`, a *two-sided* zero. That is
  why it commutes with everything, and why Theorem 9.4 and Corollary 9.8 hold
  for any `ok`.
- **Cut is a left-zero, and that is what makes it order-dependent.** In
  Piróg–Staton it is exactly a *left*-zero, a non-commutative element. Remark 1
  of the write-up notes that selection independence (Theorem 9.4) rests on the
  commutativity of `⊗`. So cut cannot live in this constraint monoid. It lives
  in the search (the monad of alternatives), and its left-zero law is the
  precise point where commutativity fails.
- **Quiet commit sits between the two.** Pruning is justified by an
  entailment, so it can be checked. It prunes alternatives that are logically
  redundant only when their answers are subsumed. Maher's and Franzén's
  semantics make that precise for their languages.

## Directions that would build on it

Each of these would start, per the repository's method, with a formal
statement and a couple of designed countermodel cells, not with a proof.

1. **Certified pruning log.** Record every pruned branch with its reason and
   certificate. There are three kinds: unsatisfiable (Farkas), dominated
   (`lowerBoundCert` against the incumbent), or not selected under a quiet
   commit (entailment certificate). The checkers already exist and are proved
   sound. A branch-and-bound search over adder configurations (fastest adder
   within a gate budget) would be a natural demonstration. It is the analogue,
   for linear arithmetic over ℚ, of VeriPB's cutting-planes logs.
2. **Quiet commit in LLP.** Add guarded clauses `∀x̃. g ⊳ S ⊃ P`, where
   committing requires `store ⊢ g`. Target statements, to be tested before any
   proof:
   - answer soundness (Corollary 9.8) survives, since commitment only discards
     branches;
   - completeness relative to the least model holds for quiet, determinate
     programs. Maher's ALPS result is the model statement.
3. **Cut in the monadic extraction.** Extend the writer monad with a search
   monad of alternatives and Piróg–Staton's left-zero cut. Then state, as a
   designed countermodel, that Theorem 9.4's selection independence fails. This
   would give a formal version, inside the lax framework, of "cut is
   non-logical": it is the non-commutative element.
4. **The modality.** `◯S` reads "`S` up to some constraint". A committed
   choice fixes *which* constraint, before the others are explored. Whether
   commitment has a modal reading, perhaps as a second modality or as a
   restriction of `◯E`, is open; I have no evidence either way.

## Sources

- [Piróg, Staton, *Backtracking with cut via a distributive law and left-zero monoids*, JFP 27 (2017), e17](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/backtracking-with-cut-via-a-distributive-law-and-leftzero-monoids/9B7B1620EEFD293888B7B1E0F805156B)
- [Naish, *Pruning in logic programming*, Technical Report 95/16, University of Melbourne (1995)](https://lee-naish.github.io/papers/prune/)
- [Andrews, *The witness properties and the semantics of the Prolog cut*, TPLP 3(1) (2003)](https://arxiv.org/abs/cs/0201029)
- [Maher, *Logic semantics for a class of committed-choice programs*, ICLP 1987, 858–876](https://dblp.org/db/conf/iclp/iclp87.html)
- Saraswat, *Concurrent Constraint Programming*, MIT Press (1993)
- [Haridi, Janson, *Kernel Andorra Prolog and its computation model*, ICLP 1990, 31–46](https://www.semanticscholar.org/paper/Kernel-Andorra-Prolog-and-its-Computation-Model-Haridi-Janson/d10f83135b2e19e9121cbaa0ea3208792fb8125c)
- [Haridi, Janson, Montelius, Franzén, Brand, Boortz, Danielsson, Carlson, *Concurrent constraint programming at SICS with the Andorra Kernel Language* (extended abstract)](https://people.kth.se/~johanmon/papers/haridi.pdf)
- Franzén, *Logical aspects of the Andorra Kernel Language*, SICS Research Report R91:12 (1991)
- [Jaffar, Maher, *Constraint logic programming: a survey*, JLP 19/20 (1994)](https://www.sciencedirect.com/science/article/pii/0743106694900337)
- [Van Hentenryck, *Constraint Satisfaction in Logic Programming*, MIT Press (1989)](https://mitpress.mit.edu/9780262081818/constraint-satisfaction-in-logic-programming/)
- Frühwirth, *Theory and practice of Constraint Handling Rules*, JLP 37(1–3) (1998), 95–138
- [Schrijvers, Stuckey, Wadler, *Monadic constraint programming*, JFP 19(6) (2009)](https://doi.org/10.1017/S0956796809990086)
- [Gocht, McCreesh, Nordström, *An Auditable Constraint Programming Solver*, CP 2022](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2022.25)
