# Proof search and countermodel search: a user's manual

*For a logician who knows PLL but not this codebase.*  Everything below is
about deciding a single sequent `Γ ⊢ C` in propositional lax logic, and
about turning the answer into a Lean theorem.  Every Lean snippet in §§3–6
was compiled against the tree this file sits in.

Files referred to: `LaxLogic/PLLG4Term.lean` (the proof searcher),
`LaxLogic/PLLSearch.lean` (the harness), `LaxLogic/PLLCountermodelEmit.lean`
(the countermodel checker), `LaxLogic/PLLSearchEx.lean` (worked examples),
`LaxLogic/PLLConfluentComplete.lean` and `wip/rnc_probe.lean` (PCLL).

---

## 0. Vocabulary

Terms used throughout, each fixed here.

**PLL.**  Fairtlough–Mendler propositional lax logic: intuitionistic
propositional logic with a modality `◯` satisfying `A ⊃ ◯A`, `◯◯A ⊃ ◯A` and
`(A ⊃ ◯B) ⊃ (◯A ⊃ ◯B)`.  In Lean: formulas are `PLLFormula`
(`.prop`, `.falsePLL`, `.and`, `.or`, `.ifThen`, `.somehow` for `◯`;
`truePLL` abbreviates `⊥ ⊃ ⊥`); derivability from a list of hypotheses is
`LaxND Γ C`.

**PCLL.**  PLL plus the distribution scheme `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`.  See §6.

**Sequent.**  A pair of a hypothesis list `Γ : List PLLFormula` and a
conclusion `C : PLLFormula`, written `Γ ⊢ C`.

**G4iLL″.**  The contraction-free sequent calculus for PLL used by the
searcher (`G4c` in Lean; sixteen rules).  It repairs Iemhoff's G4iLL, which
is incomplete for PLL.  It is equivalent to `LaxND` (`G4c.equiv_nd`).

**Proof term.**  An element of the inductive type `G4cTm Γ C`: a G4iLL″
derivation carried as data rather than as a proposition.  Because it is a
Lean term, Lean's kernel typechecks it; nothing about the program that
produced it needs to be trusted.

**Constraint model.**  The Kripke semantics for PLL (`ConstraintModel`): a
set of worlds with a preorder `Rᵢ` (intuitionistic accessibility), a
sub-preorder `Rₘ ⊆ Rᵢ` (constraint accessibility), a set `F` of *fallible*
worlds, and a hereditary valuation that is total on `F`.  Forcing is the
usual intuitionistic clauses, with

- `w ⊩ ⊥` iff `w ∈ F`, and
- `w ⊩ ◯A` iff for every `v` with `Rᵢ w v` there is `u` with `Rₘ v u` and
  `u ⊩ A`.

**`FinCM`.**  A finite constraint model as concrete data:
`⟨n, ri, rm, fall, val⟩`, with worlds `0, …, n-1`, the relations as lists of
pairs (reflexive pairs implicit), `fall` the fallible worlds, `val` the true
`(world, atom)` pairs.

**Certificate.**  A piece of data whose *type* records the fact one wants,
so that accepting it is a kernel typecheck rather than an act of trust.
Two kinds appear here: a proof term `G4cTm Γ C` (positive), and a pair
`(M, w)` together with a proof of `FinCM.checkB M w Γ C = true` (negative).
`checkB` is a Boolean function that verifies `M` is a well-formed constraint
model, `w` is a world of it, every formula of `Γ` is forced at `w`, and `C`
is not.

**Discover-then-pin.**  The working discipline of this repository.  Search
code is *untrusted*: it is `partial`, may be wrong, and never reduces inside
a proof.  It is used only to *discover* a certificate; the certificate is
then *pinned*: written into the file as a Lean theorem whose proof is the
certificate, rechecked by the kernel, and audited with `#print axioms`.

**Node budget.**  A cap on the total number of sequents the proof searcher
visits.  It is global to the whole search tree, not per branch: a failed
branch hands its remaining budget to the next alternative.  Exhausting the
budget yields "unknown", never "underivable".

**Countermodel-first.**  The staging policy of `Search.decide`: look for a
small countermodel *before* running proof search, because checking a
proposed countermodel is cheap while a failing proof search is not.

**Battery.**  The fixed list of small frames (at most four worlds) that the
countermodel stage decorates with valuations and tests.  It is deliberately
incomplete: a cheap first filter.

**Closure emitter.**  The second countermodel stage (`CounterEmit.emit`):
it builds a candidate model out of the prime deductively-closed subsets of
the subformula closure of the sequent.  It is complete over that closure but
exponential, so it is run only when the closure is small.

---

## 1. What you may believe

Three claims, and nothing else, are underwritten by the kernel.

1. `PLLND.Search.proved_sound : G4cTm Γ C → Nonempty (LaxND Γ C)`.
2. `FinCM.not_provable_of_check : FinCM.checkB M w Γ C = true →
   ¬ Nonempty (LaxND Γ C)` (Kripke soundness).
3. For PCLL, `PLLND.RNC.not_derivU_of_checkConf` (§6).

Everything that *produces* a certificate is untrusted: the backward
searcher, the fast vector evaluator that screens candidate models, the frame
decoration enumeration, the emitter.  Each is `partial` or heuristic,
and every candidate it proposes passes through `checkB` or through Lean's
typechecker before it is returned.  A bug in the search can therefore lose
answers; it cannot manufacture one.

Two consequences worth stating plainly.

- **A failed search proves nothing.**  `G4cTm.find` returning `none` is not
  a completeness oracle.  It means only that this program did not find a
  derivation.  Underivability comes from a countermodel, never from a
  failure.
- **Search results do not reduce in the kernel.**  The searchers are
  `partial`, so `decide {} Γ C` is opaque to `rfl` and to the `decide`
  tactic.  Discovery happens at elaboration time (`#eval`, `#guard`);
  pinning happens by writing the found certificate into the source.

No component uses `native_decide`.  The audits in `PLLSearch.lean` show the
soundness lemmas depending on `[propext, Quot.sound]` only.

---

## 2. Building

```
lake build LaxLogic          # the library
lake env lean MyFile.lean     # elaborate a file, running its #eval / #guard
```

A file of your own needs only `import LaxLogic.PLLSearch` and

```lean
open PLLFormula PLLND PLLND.Search
```

`PLLFormula` has a `Repr` instance printing `⊃`, `∧`, `∨`, `◯`, so `#eval`
on a formula shows it in the usual notation.

---

## 3. Proving a sequent

The positive engine is `G4cTm.find Γ C : Option (G4cTm Γ C)`, backward
search in G4iLL″ with no fuel parameter.  It always terminates: the search
is loop-checked against the canonical form of the sequent (hypotheses
deduplicated and sorted), and along any branch the context only grows by
subformulas of the end-sequent, so keys must repeat.  `Search.prove?` is the
same function under a shorter name.

Discovery.  `G4cTm.pretty` renders a found term as its rule tree.

```lean
def unitSeq : PLLFormula := (prop "p").ifThen (prop "p").somehow

#eval (G4cTm.find [] unitSeq).map (·.pretty)
-- some "(→R (◯R init))"

#guard (G4cTm.find [] unitSeq).isSome
```

`#guard` fails the build if the search stops finding the proof, so it is the
cheap way to keep a discovery under regression control.

Pinning.  Transcribe the rule tree into the constructors of `G4cTm`
(`.impR`, `.laxR`, `.init`, …; the side conditions are list memberships,
usually closed by `simp`), and apply `proved_sound`:

```lean
theorem unit_derivable : Nonempty (LaxND [] unitSeq) :=
  proved_sound (.impR (.laxR (.init (by simp))))

#print axioms unit_derivable
-- 'unit_derivable' depends on axioms: [propext, Quot.sound]
```

For larger terms the implicit arguments of the left rules (which formula of
the context is being decomposed) sometimes need to be supplied by name, e.g.
`.orL (A := prop "p") (B := prop "q") (by simp) …`.  The rule names printed
by `pretty` map to constructors as: `→R` `.impR`, `◯R` `.laxR`, `◯L`
`.laxL`, `∧R` `.andR`, `∨R₁/∨R₂` `.orR1/.orR2`, `∧L` `.andL`, `∨L` `.orL`,
`→Lₐₜ` `.impLProp`, `→L∧` `.impLAnd`, `→L∨` `.impLOr`, `→L→` `.impLImp`,
`→L◯` `.impLLax`, `→L◯◯` `.impLLaxLax`, `init` `.init`, `⊥L` `.botL`.

---

## 4. Refuting a sequent

The negative engine is `Search.refute? cfg Γ C`, which runs the battery and
then, if the subformula closure is small enough, the emitter.  It returns
`Option (Witness Γ C)`, where `Witness Γ C` is a dependent triple
`(M : FinCM) × (w : Nat) ×' (FinCM.checkB M w Γ C = true)`: the model, the
refuting world, and the checker's verdict about *this* sequent.

Discovery:

```lean
def escSeq : PLLFormula := ((prop "p").somehow).ifThen (prop "p")

#eval (match refute? {} [] escSeq with
       | some ⟨M, w, _⟩ => s!"{repr M} @ world {w}"
       | none           => "no countermodel found")
-- "{ n := 2, ri := [(0, 1)], rm := [(0, 1)], fall := [1], val := [(1, "p")] } @ world 0"
```

The configuration argument cannot be omitted while `Γ` and `C` are given
positionally; write `{}` for the defaults.

Pinning.  Copy the model data into the statement and let `decide` run the
checker inside the kernel:

```lean
theorem esc_underivable : ¬ Nonempty (LaxND [] escSeq) :=
  FinCM.not_provable_of_check
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], [(1, "p")]⟩) (w := 0) (by decide)

#print axioms esc_underivable
-- 'esc_underivable' depends on axioms: [propext, Quot.sound]
```

Here `by decide` *is* legitimate: `checkB` is an ordinary total Boolean
function on concrete data, so the kernel evaluates it.  This is the step at
which the untrusted search drops out of the picture entirely: the pinned
theorem mentions only the model.

To look at a model rather than read its data, `LaxLogic/PLLDiagram.lean`
exports a `FinCM` to TikZ or SVG (`Diagram.toTikz`, `Diagram.toSvg`, with
`Diagram.autoPos` for an automatic layout).  That code is outside the trust
story.

---

## 5. The two-sided procedure, and when to cap it

`Search.decide cfg Γ C : Answer Γ C` runs, in order:

1. the battery (certified countermodel, cheap);
2. `G4cTm.find` on the original sequent (proof term);
3. the closure emitter, if `(closure size) ≤ cfg.emitClosureCap` (default 12);
4. `.unknown`.

`Answer Γ C` has three constructors (`.proved t`, `.refuted M w h`,
`.unknown`), and `Answer.toDecision` converts it in one step into a
`Decision Γ C`, i.e. `Nonempty (LaxND Γ C)`, `¬ Nonempty (LaxND Γ C)`, or
`dontKnow`.

```lean
#eval (match decide {} [] escSeq with
       | .proved _      => "PROVED"
       | .refuted _ _ _ => "REFUTED"
       | .unknown       => "UNKNOWN")
-- "REFUTED"
```

**Cost.**  Successes are cheap on both sides.  The bad case is a sequent
that is underivable *and* escapes both countermodel stages: then `find`
must exhaust its search space, which is finite but exponential.  Measured
node counts (nodes visited by `find`, on this tree):

| sequent | nodes |
|---|---:|
| `⊢ p ⊃ ◯p` | 3 |
| `⊢ ◯◯p ⊃ ◯p` | 7 |
| `⊢ (p ⊃ q ⊃ r) ⊃ (p ⊃ q) ⊃ p ⊃ r` | 8 |
| `⊢ ((p ⊃ q) ⊃ p) ⊃ p` (Peirce; underivable) | 8 |
| `⊢ (p ∧ ◯q) ⊃ ◯(p ∧ q)` | 18 |
| `◯((◯p ⊃ r) ⊃ ◯p), ◯p ⊃ r ⊢ r` | 136 |

These are small because the loop key identifies sequents up to order and
duplication of hypotheses and because failed subgoals are memoised.  Growth
is nonetheless exponential in the number of implication hypotheses whose
consequent is unreachable.  The module header of `PLLSearch.lean` reports
searches of several minutes at around twenty-five such hypotheses.

**Node budget.**  Use one whenever you are probing a sequent you suspect is
underivable, or running a sweep in which one slow cell would block the rest.

```lean
-- nodes actually visited (budget minus remainder)
#eval 100000 - (G4cTm.findBounded 100000 [] unitSeq).2
-- 3

#eval (match decide {findBudget := some 2} [] unitSeq with
       | .proved _ => "PROVED" | .refuted _ _ _ => "REFUTED"
       | .unknown  => "UNKNOWN")
-- "UNKNOWN"   -- truncation, not a verdict about the sequent
```

`G4cTm.findBounded budget Γ C` returns the result paired with the
*remaining* budget, and the three readings are:

- `(some t, _)`: a proof term, as trustworthy as `find`'s;
- `(none, k+1)`: the space was exhausted with budget to spare, so this is the
  same (certificate-free) `none` that `find` gives;
- `(none, 0)`: the budget ran out. Unknown, and nothing more.

`Search.prove?Bounded budget Γ C` is the same with the remainder discarded;
`Config.findBudget := some b` threads the budget through `decide`.  Because
`budget - remaining` is the node count, `findBounded` doubles as a profiler
for choosing budgets.

**Widening the battery.**  `Config.frames` is a list of
`⟨n, ri, rm, fall⟩` records; prepend your own shapes to `defaultFrames` when
a family of sequents keeps returning `.unknown`.  `Config.comboCap` bounds
the decoration enumeration per frame, so an atom-rich sequent silently skips
frames that would blow up; raise it if you are prepared to pay.

---

## 6. PCLL

PCLL is PLL plus `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`.  In Lean the scheme instance is
`ConfluentU.distF A B`, and derivability is

```lean
DerivU Γ φ  :=  ∃ L, (every member of L is an instance of distF) ∧
                     Nonempty (LaxND (L ++ Γ) φ)
```

— natural deduction from `Γ` together with finitely many instances of the
scheme.  `DerivU` is sound and complete for *mutually confluent* constraint
models, those satisfying `Rₘ x w → Rᵢ x v → ∃ u, Rᵢ w u ∧ Rₘ v u`
(`derivU_iff_confluent_valid`).  Two things change relative to §§3–5.

**Positive side.**  Search for a PLL proof of `instances ++ Γ ⊢ C`, choosing
the instances by hand (typically one per `∨`-subformula of the sequent), and
convert with `RNC.derivU_of_proved ps : Nonempty (LaxND (ps.map distF ++ Γ) C)
→ DerivU Γ C`.  The conversion is valid whatever instances were used, so
choosing them badly costs a failed search and nothing else.

```lean
def premise : PLLFormula := ((prop "p").or (prop "q")).somehow
def goal    : PLLFormula := ((prop "p").somehow).or ((prop "q").somehow)
def inst    : PLLFormula := ConfluentU.distF (prop "p") (prop "q")

#eval (G4cTm.find [inst, premise] goal).map (·.pretty)
-- some "(→L◯◯ (◯R (∨L (∨R₁ init) (∨R₂ init)))
--             (∨L (∨R₁ (◯L (◯R init))) (∨R₂ (◯L (◯R init)))))"
```

**Negative side.**  A `FinCM` refutes `DerivU` only if it is mutually
confluent.  `RNC.confB M : Bool` decides this, and

```lean
RNC.not_derivU_of_checkConf : confB M = true → FinCM.checkB M w Γ C = true →
                              ¬ ConfluentU.DerivU Γ C
```

is the certificate theorem.  Both hypotheses discharge by `decide`:

```lean
theorem esc_underivable_pcll :
    ¬ ConfluentU.DerivU [(prop "p").somehow] (prop "p") :=
  not_derivU_of_checkConf
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], [(1, "p")]⟩) (w := 0) (by decide) (by decide)
```

**The trap.**  A countermodel returned by `Search.refute?` is *not*
automatically a PCLL refutation.  Ten of the eleven frames in
`defaultFrames` happen to be mutually confluent, but the eleventh is not,
and the emitter produces non-confluent models freely.  Always test `confB`
before reusing a model against `DerivU`.  The distribution axiom itself is
the illustration:

```lean
#eval (match refute? {} [premise] goal with
       | some ⟨M, w, _⟩ =>
           s!"{M.n} worlds, world {w}, mutually confluent = {confB M}"
       | none => "no countermodel found")
-- "20 worlds, world 4, mutually confluent = false"
```

PLL refutes `◯(p ∨ q) ⊢ ◯p ∨ ◯q`, so the model must fail confluence, and
does.

These PCLL definitions live in `wip/rnc_probe.lean`, so a file using them
begins `import wip.rnc_probe`, and the module must be built first with
`lake build wipshared`.  Pinned PCLL certificates in the house style are in
`wip/rncCert.lean` (negative) and `wip/rncCertPos.lean` (positive).

---

## 7. Command-line tools

The `lakefile.toml` declares a number of `lean_exe` targets, most of them
one-off probes.  Two are representative.

```
lake build oracle2 && lake exe oracle2
```

runs a fixed ten-sequent benchmark through the same staged procedure and
prints, per sequent, the verdict, a summary of any countermodel, and the
time. It is a useful smoke test that the toolchain and the staging are
healthy.

```
lake build rncprobe && lake exe rncprobe
```

runs the PCLL probe of §6 over a fixed dictionary of formulas: it prints a
full two-sided entailment matrix and the induced quotient.  It takes
arguments (`c`, `r`, `p`) selecting sub-phases; with none it runs the whole
matrix, which is slow.

`scripts/laxrun.sh help` lists the older CLI (`timing`, `search`, `quant`,
`zoo`), which drives the *fuelled* decider of `PLLG4Dec.lean` over named
instances rather than the searcher described here.

---

## 8. Failure modes

- **`.unknown` on a sequent you believe underivable.**  The battery missed
  it and the closure was too big for the emitter.  Raise
  `Config.emitClosureCap`, or add a frame to `Config.frames`.
- **A run that will not return.**  Set `Config.findBudget`.  There is no
  interrupt: the searcher is a pure function.
- **`decide`/`rfl` failing on a search result inside a proof.**  Expected:
  the searchers are `partial`.  Discover with `#eval`/`#guard`, pin the
  certificate by hand.
- **A transcribed proof term that will not elaborate.**  Supply the implicit
  formula arguments of the left rule by name.
- **A pinned countermodel that `by decide` rejects.**  The model was copied
  against the wrong sequent, or a relation list is not transitively closed:
  `checkB` includes the well-formedness check.

---

## 9. Suggested presentation improvements

Suggestions only; none of these is implemented.

1. **Give the two-sided entry point a name that does not collide with
   `Decidable.decide`.**  `PLLND.Search.decide` shadows the standard
   `decide` under `open`.  Lean's overload resolution copes, but a reader
   cannot tell the two apart by eye, and `decide` in this namespace is also
   the *only* name in the API that is a verb of the ambient logic.
   `settle`, `verdict`, or `Search.run` would all read better.

2. **Provide one `#search` / `#refute` command.**  Every example in this
   manual wraps the call in the same `match … with | .proved _ => "…"`
   boilerplate.  A pair of commands that take a sequent and print a verdict,
   the rule tree, and the countermodel would remove that entirely, and would
   make the tool usable by someone who has not learned the `Answer` type.

3. **Make the `Config` argument optional in practice.**  `refute? {} Γ C`
   and `decide {} Γ C` force every caller to type `{}`.  Wrappers with `Γ`
   and `C` first, and the configuration supplied by named argument when
   wanted, would be the common case made short.

4. **Emit the pinning snippet as text.**  The manual step everyone repeats
   is copying a `FinCM` into a `not_provable_of_check` application, or a
   rule tree into `G4cTm` constructors.  Both are mechanical.  A function
   `Witness Γ C → String` producing the ready-to-paste theorem, and a
   `G4cTm Γ C → String` producing constructor syntax with implicit
   arguments already named, would close the discover-then-pin loop.

5. **Report *why* the answer is `.unknown`.**  At present the three
   failure routes (battery exhausted, budget exhausted, closure over
   `emitClosureCap`) are indistinguishable in the result.  A reason field
   would tell the user which knob to turn, which is exactly the information
   §8 currently supplies in prose.

6. **Fold the confluence test into the API.**  §6's trap (a non-confluent
   countermodel silently reused against `DerivU`) is a correctness hazard
   with a one-line fix: a `refuteConf?` that filters the battery by `confB`,
   and a `Config` flag requesting confluent models, would make the PCLL
   route as safe as the PLL one.  Promoting `confB` and
   `not_derivU_of_checkConf` from `wip/rnc_probe.lean` into the library
   would also let a PCLL user avoid `import wip.…` altogether.

7. **Turn the node budget on by default.**  The failure mode users actually
   hit is a run that does not come back, and the cure, `findBudget`, is
   currently opt-in and undiscoverable.  A generous default (say 10⁵ nodes,
   comfortably above every sequent in the table of §5) with an explicit
   `none` to disable it would trade a rare `.unknown` for a guaranteed
   answer time.

8. **Print formulas, not `FinCM` records.**  The default `repr` of a
   countermodel is a raw structure; the 20-world model of §6 is several
   screens of pair lists.  A compact renderer (worlds by index, the Hasse
   diagram of `Rᵢ` with `Rₘ` edges marked, the forced atoms per world)
   already exists in `PLLDiagram.lean` for pictures and could be reused for
   text.

9. **Refresh the cost figures in the header of `PLLSearch.lean`.**  It
   quotes 825 nodes for the gap sequent `◯((◯p ⊃ r) ⊃ ◯p), ◯p ⊃ r ⊢ r`; the
   measured figure on this tree is 136, the loop key and failure memo having
   landed since.  A cost profile is the part of a module header a user acts
   on, so it is worth keeping current.

10. **State the intended reading order.**  A newcomer currently has to
    discover that `PLLSearch.lean`'s header is the specification,
    `PLLSearchEx.lean` the examples, and `PLLG4Term.lean` the engine.  A
    three-line pointer at the top of each, and a link from the repository
    `README.md`, would cost nothing.
