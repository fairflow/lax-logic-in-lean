# Interpolation, plainly: Craig, uniform, and why lax logic is the hard case

*A guide for teaching, written 2026-09-06 for Matthew Fairtlough. Everything
marked "verified" below was checked by hand in the Kripke semantics or by a
one-line derivation; the results table cites the literature. The machine-checked
parts of the lax-logic story live in the repository `lax-logic-in-lean`.*

---

## 1. The idea in one picture

Two people are arguing. Alice knows about `p` and `q`; Bob knows about `q` and
`r`. Alice asserts a sentence `A` in her vocabulary, and Bob accepts that `A`
forces a sentence `B` in his: `A ⊢ B`. Since Alice and Bob share only the word
`q`, the whole force of the argument must pass through `q`. **Interpolation**
says that it does: there is a sentence `C` using only the shared vocabulary such
that `A ⊢ C` and `C ⊢ B`. Alice can hand Bob `C` and keep `p` to herself.

The interpolant is the *summary of `A` in the shared language*, and the point of
the theorem is that a summary always exists inside the logic itself, without
new symbols.

A first example, verified by two one-line derivations:

    p ∧ (p ⊃ q)  ⊢  q ∨ r         interpolant:  q
    p ∧ (p ⊃ q)  ⊢  q             and           q  ⊢  q ∨ r

## 2. Craig's theorem (1957)

**Statement.** In classical or intuitionistic propositional logic, if `A ⊢ B`
then there is a formula `C` whose atoms occur in both `A` and `B`, with `A ⊢ C`
and `C ⊢ B`. (Craig proved it for first-order logic; the propositional case is
the one to teach first.)

**Why it is true, in one sentence.** Take a cut-free proof of `A ⊢ B` and split
every sequent in it into an `A`-part and a `B`-part; at each rule one can write
down a formula that separates the two parts, building the interpolant from the
leaves up. This is Maehara's method, and it is exactly how the lax-logic
repository proves Craig interpolation for PLL (`LaxLogic/PLLCraig.lean`).

**Why it matters.** Three classical uses:

- *Modularity.* If two theories share a vocabulary and are each consistent, and
  they agree on the shared part, their union is consistent (Robinson's
  consistency theorem, equivalent to Craig).
- *Definability.* If a symbol is implicitly defined by a theory, it is
  explicitly definable (Beth's theorem, a corollary).
- *Verification.* Interpolants are how model checkers summarise "what has been
  established so far" about a program in the vocabulary of the next step.

**What to stress in class.** A Craig interpolant is not unique, not even up
to interderivability: for a fixed `A ⊢ B` the interpolants form an interval
in the shared vocabulary, from the strongest shared consequence of `A` up to
the weakest shared antecedent of `B`, and the interval can have two ends.
Verified example: `A = q`, `B = q ∨ (s ⊃ s)`, shared vocabulary `{q}`; both
`q` and `⊤` are interpolants, and `⊤ ⊬ q`. And the interpolant depends on
`B`: a different `B` may need a different `C`. That dependence is what the
next section removes, and removing it is also what makes the interpolant
unique.

## 3. Uniform interpolation (Pitts, 1992)

Ask for more: a summary of `A` in the language *without `p`* that works for
**every** `B` at once. Two formulas do the job, if they exist:

    ∃p.A   the STRONGEST p-free consequence of A:
           A ⊢ ∃p.A,  and for every p-free ψ,  A ⊢ ψ  iff  ∃p.A ⊢ ψ

    ∀p.A   the WEAKEST p-free antecedent of A:
           ∀p.A ⊢ A,  and for every p-free ψ,  ψ ⊢ A  iff  ψ ⊢ ∀p.A

"Uniform" means uniform in `B`: `∃p.A` is the one interpolant that serves every
`B` not mentioning `p`. The notation is deliberate: these are propositional
quantifiers, and a logic has uniform interpolation exactly when it can express
its own second-order propositional quantifiers.

**Classical logic: trivial.** A propositional atom is either true or false, so

    ∃p.A  =  A[⊤/p] ∨ A[⊥/p]        ∀p.A  =  A[⊤/p] ∧ A[⊥/p]

This is quantifier elimination for Boolean algebra, and it is worth doing one
example on the board: `∃p.(p ∧ (p ⊃ q)) = (⊤ ∧ q) ∨ (⊥ ∧ ⊤) = q`.

**Intuitionistic logic: the recipe fails, the theorem survives.** Take
`A = (p ∨ ¬p) ⊃ q`. The classical recipe gives `q`. But `q` is *not* a
consequence of `A` intuitionistically, because `p ∨ ¬p` is not provable, so
nothing forces `q`. The true strongest `p`-free consequence is

    ∃p.((p ∨ ¬p) ⊃ q)  =  ¬¬q            (verified)

Two checks. `(p ∨ ¬p) ⊃ q ⊢ ¬¬q`, since `¬q` would give `¬(p ∨ ¬p)`, which is
refutable. Strongest: in any Kripke model of `¬¬q` (every end point satisfies
`q`), interpret `p` as `q`; then `p ∨ ¬p` holds exactly where `q` does, so
`(p ∨ ¬p) ⊃ q` holds at the root, and any `p`-free `ψ` refuted somewhere in a
model of `¬¬q` is refuted in a model of `A`. Hence every `p`-free consequence
of `A` follows from `¬¬q`.

Pitts's theorem (1992) is that intuitionistic propositional logic has uniform
interpolation: `∃p.A` and `∀p.A` always exist. Unlike the classical case there
is no substitution recipe; the interpolants are computed by a terminating proof
search (Dyckhoff's contraction-free calculus G4ip is the standard vehicle), and
they can be much larger than `A`.

**Two small examples for the `∀` side** (verified by the instance argument:
substituting a constant for `p` bounds every candidate):

    ∀p.(p ⊃ q)  =  q          (p := ⊤ forces  ψ ⊢ q;  and  q ⊢ p ⊃ q)
    ∀p.(q ⊃ p)  =  ¬q         (p := ⊥ forces  ψ ⊢ ¬q; and  ¬q ⊢ q ⊃ p)

The instance argument is worth naming for students: any `p`-free `ψ` with
`ψ ⊢ A` also satisfies `ψ ⊢ A[χ/p]` for every `p`-free `χ`, so the instances
`A[χ/p]` are upper bounds on `∀p.A`, and when one of them is itself a valid
antecedent it *is* `∀p.A`. (In the repository this is the kernel-checked lemma
`instanceClosed`.) The interesting cases are the ones no instance closes, such as

    ∀p.((p ⊃ q) ∨ (q ⊃ p))  =  q ∨ ¬q

where the answer is not a substitution instance of the body.

## 4. What uniform interpolation buys

- **Forgetting inside the logic.** `∃p.A` is "A with `p` forgotten". A theory
  can be projected onto a sub-vocabulary without leaving propositional logic.
- **Second-order quantifiers for free.** Quantified propositional intuitionistic
  logic collapses to the propositional logic: every `∃p`, `∀p` is definable.
- **Semantics.** On Kripke models `∃p.A` is a *bisimulation quantifier*:
  "some model bisimilar to this one, except on `p`, satisfies `A`". Uniform
  interpolation and bisimulation quantifiers are two faces of one property
  (Ghilardi–Zawadowski, Visser).
- **A sharper tool than Craig.** Every logic with uniform interpolation has
  Craig interpolation (take `C = ∃(atoms of A not in B).A`), but not
  conversely; the table below has the counterexamples.

## 5. Which logics have it

| logic | Craig | uniform | reference |
|---|---|---|---|
| classical propositional | yes | yes, by substitution | folklore |
| intuitionistic (IPC) | yes | **yes** | Pitts 1992; Ghilardi–Zawadowski 1995 (semantic proof) |
| modal K | yes | yes | Ghilardi 1995; Visser 1996 |
| Gödel–Löb GL | yes | yes | Shavrukov 1993 |
| S4 | yes | **no** | Ghilardi–Zawadowski 1995 |
| K4 | yes | **no** | Bílková 2007 |
| propositional lax logic PLL | yes (`PLLCraig.lean`, Maehara) | **open** | this campaign |

The S4 and K4 rows are the teaching point: Craig interpolation is common and
uniform interpolation is not. What separates them is whether the "forgetting"
operation stays inside the logic.

## 6. Why lax logic is the interesting case

Propositional lax logic adds one modality `◯` to intuitionistic logic, with
`A ⊢ ◯A`, `◯◯A ⊢ ◯A`, and `A ⊢ B` giving `◯A ⊢ ◯B`: a nucleus, or a strong
monad. Because `◯` is *reflexive*, the frame conditions that make K and GL
behave are absent, and the frame conditions that break S4 are partly present.
Nobody knows on which side of the table PLL falls.

The campaign in the repository attacks it proof-theoretically, in the same
spirit as Pitts but on a focused sequent calculus for PLL (LJF◯):

1. Define approximants `E_f` (descending from `⊤`) and `A_f` (ascending from
   `⊥`) by a fuel-bounded recursion over the sequent, mirroring the proof search.
2. Prove soundness at every fuel (`Γ ⊢ E_f`, `A_f, Γ ⊢ G`) — **proved**.
3. Prove cofinality: every `p`-free consequence, and every `p`-free sufficient
   antecedent, is reached at some fuel — **proved**, 2026-09-05.
4. Prove that the approximants stabilise up to interderivability at every
   sequent — **open**; this is the theorem. With 2 and 3 it is equivalent to
   uniform interpolation at that sequent, in both directions.

For the `◯`-free fragment the whole route closes and recovers Pitts's theorem
(`uniform_interpolation_IPC`, machine-checked). For PLL the open step is exactly
where the reflexive modality interferes with termination of the proof search:
whether the chains that the modality keeps reopening eventually say nothing new.

## 7. A ten-minute board sequence

1. Alice and Bob, the shared word `q`, `p ∧ (p ⊃ q) ⊢ q ∨ r` with interpolant
   `q`.
2. State Craig; say "cut-free proof, split each sequent" for the proof idea.
3. Ask: can we summarise `A` once and for all, for every `B`? Define `∃p.A`
   and `∀p.A`.
4. Classical: `A[⊤] ∨ A[⊥]`; do `∃p.(p ∧ (p ⊃ q)) = q`.
5. Intuitionistic: `(p ∨ ¬p) ⊃ q`; the recipe gives `q`, the truth is `¬¬q`.
   Say why `q` cannot follow (no excluded middle).
6. State Pitts; show the table; point at S4 as the surprise.
7. One sentence on lax logic: reflexive modality, open, and what "open" means
   when every individual interpolant we have ever computed has been checked.

**Exercises** (answers in §3): compute `∃p.(p ∧ (p ⊃ q))`, `∀p.(p ⊃ q)`,
`∀p.(q ⊃ p)`; explain why the classical recipe fails for `(p ∨ ¬p) ⊃ q`;
show that `∀p.A ⊢ A[χ/p]` for every `p`-free `χ` and use it to bound
`∀p.((p ⊃ q) ∨ (q ⊃ p))` from above by `q ∨ ¬q`.

**Misconceptions to head off.** Craig interpolants are not unique (an
interval, §2); uniform interpolants are, up to interderivability: "strongest
`p`-free consequence" names the least element of the `p`-free consequences
under `⊢`, and a least element of a preorder is unique up to equivalence
(dually for the weakest antecedent). So `∃p` and `∀p` are well-defined
operations on the Lindenbaum algebra, the left and right adjoints of the
inclusion of the `p`-free fragment; the repository proves the uniqueness as
`IsExUIOn.unique` and `IsAllUIOn.unique`. Uniform interpolation is strictly
stronger than Craig. `∃p.A` is a formula of the propositional logic, not of
a richer language, and that is the whole content. "Open" for PLL means no
proof and no counterexample, not "probably false".

## References

- W. Craig, *Three uses of the Herbrand–Gentzen theorem in relating model theory
  and proof theory*, J. Symbolic Logic 22 (1957).
- A. M. Pitts, *On an interpretation of second order quantification in first
  order intuitionistic propositional logic*, J. Symbolic Logic 57 (1992).
- S. Ghilardi and M. Zawadowski, *Undefinability of propositional quantifiers
  in the modal system S4*, Studia Logica 55 (1995); and *A sheaf representation
  and duality for finitely presented Heyting algebras*, J. Symbolic Logic 60
  (1995).
- A. Visser, *Uniform interpolation and layered bisimulation*, Gödel '96,
  Lecture Notes in Logic 6 (1996).
- V. Shavrukov, *Subalgebras of diagonalizable algebras of theories containing
  arithmetic*, Dissertationes Mathematicae 323 (1993).
- M. Bílková, *Uniform interpolation and propositional quantifiers in modal
  logics*, Studia Logica 85 (2007).
- R. Dyckhoff, *Contraction-free sequent calculi for intuitionistic logic*,
  J. Symbolic Logic 57 (1992).
- M. Fairtlough and M. Mendler, *Propositional lax logic*, Information and
  Computation 137 (1997).
