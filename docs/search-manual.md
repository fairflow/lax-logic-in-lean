# Proof search and countermodel search: a user's manual

*For a logician who knows PLL but not this codebase.*  Everything below is
about deciding a single sequent `Γ ⊢ C` in propositional lax logic, and
about turning the answer into a Lean theorem.  Every Lean snippet in §§3–6
was compiled against the tree this file sits in, and every output shown is
that compilation's own.

Files referred to: `LaxLogic/PLLSearch.lean` (the harness and the API),
`LaxLogic/PLLSearchCmd.lean` (the `#search` / `#refute` commands),
`LaxLogic/PLLSearchConf.lean` (PCLL), `LaxLogic/PLLG4Term.lean` (the proof
searcher), `LaxLogic/PLLCountermodelEmit.lean` (the countermodel checker),
`LaxLogic/PLLSearchEx.lean` (worked examples).

**Reading order.**  `PLLSearchCmd.lean` if you only want to *ask* about a
sequent; `PLLSearch.lean`'s module header for the specification and the cost
profile; `PLLSearchEx.lean` for worked examples; `PLLSearchConf.lean` for
PCLL; `PLLG4Term.lean` for the engine.

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

**Witness.**  A certified countermodel as a dependent triple:
`Witness Γ C = (M : FinCM) × (w : Nat) ×' (FinCM.checkB M w Γ C = true)`.
`WitnessConf Γ C` (§6) additionally carries `RNC.confB M = true`.

**Answer, Verdict, Reason.**  `Answer Γ C` has three constructors
(`.proved t`, `.refuted M w h`, `.unknown`).  `Verdict Γ C` is the same with
the third constructor carrying a `Reason` — `budgetExhausted b`,
`closureTooBig size cap`, or `allStagesMissed` — saying which bound bit.
`Verdict.toAnswer` forgets it.  `Answer.toDecision` and `Verdict.toDecision`
convert either into a `Decision Γ C`: `Nonempty (LaxND Γ C)`,
`¬ Nonempty (LaxND Γ C)`, or `dontKnow`.

**Discover-then-pin.**  The working discipline of this repository.  Search
code is *untrusted*: it is `partial`, may be wrong, and never reduces inside
a proof.  It is used only to *discover* a certificate; the certificate is
then *pinned*: written into the file as a Lean theorem whose proof is the
certificate, rechecked by the kernel, and audited with `#print axioms`.
`Witness.snippet` and `G4cTm.snippet` (§§3–4) emit that theorem as text, so
the pinning step is a copy rather than a transcription.

**Node budget.**  A cap on the total number of sequents the proof searcher
visits.  It is global to the whole search tree, not per branch: a failed
branch hands its remaining budget to the next alternative.  Exhausting the
budget yields "unknown", never "underivable".

**Countermodel-first.**  The staging policy of `Search.settle`: look for a
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
decoration enumeration, the emitter, the `Config.accept` filter.  Each is
`partial` or heuristic, and every candidate it proposes passes through
`checkB` or through Lean's typechecker before it is returned.  A bug in the
search can therefore lose answers; it cannot manufacture one.  The
renderers and snippet emitters of §§3–4 are likewise outside the trust
story: what they print is re-checked by the kernel when it is pasted.

Two consequences worth stating plainly.

- **A failed search proves nothing.**  `G4cTm.find` returning `none` is not
  a completeness oracle.  It means only that this program did not find a
  derivation.  Underivability comes from a countermodel, never from a
  failure.
- **Search results do not reduce in the kernel.**  The searchers are
  `partial`, so `settle {} Γ C` is opaque to `rfl` and to the `decide`
  tactic.  Discovery happens at elaboration time (`#eval`, `#guard`,
  `#search`); pinning happens by writing the found certificate into the
  source.

No component uses `native_decide`.  The audits in `PLLSearch.lean` and
`PLLSearchConf.lean` show the soundness lemmas depending on
`[propext, Quot.sound]` only.

---

## 2. Building

```
lake build LaxLogic          # the library
lake env lean MyFile.lean     # elaborate a file, running its #eval / #guard
```

A file of your own needs only

```lean
import LaxLogic.PLLSearchCmd          -- commands + everything below them
open PLLFormula PLLND PLLND.Search
```

(`import LaxLogic.PLLSearch` alone gives the functions without the commands;
`LaxLogic.PLLSearchConf` adds PCLL.)

`PLLFormula` has a `Repr` instance printing `⊃`, `∧`, `∨`, `◯`, so `#eval`
on a formula shows it in the usual notation.

**Two argument orders.**  The original entry points take the configuration
*first* (`settle cfg Γ C`, `refute? cfg Γ C`), so they need an explicit `{}`
for the defaults.  The wrappers added for everyday use take `Γ` and `C`
first and default the configuration (`verdict Γ C`, `countermodel Γ C`,
`proof Γ C`); a non-default configuration goes in by name,
`verdict Γ C (cfg := …)`.

**One difference between them.**  The sequent-first wrappers and the
commands default to `Search.budgetedConfig`, which sets
`findBudget := some 200000`; `settle {} Γ C` still runs with no budget at
all, exactly as `decide {} Γ C` always did.  See §5.

---

## 3. Proving a sequent

The positive engine is `G4cTm.find Γ C : Option (G4cTm Γ C)`, backward
search in G4iLL″ with no fuel parameter.  It always terminates: the search
is loop-checked against the canonical form of the sequent (hypotheses
deduplicated and sorted), and along any branch the context only grows by
subformulas of the end-sequent, so keys must repeat.  `Search.proof Γ C` is
the same function with the node budget of `budgetedConfig` on;
`Search.prove?` is the unbudgeted original.

### The command

```lean
def unitSeq : PLLFormula := (prop "p").ifThen (prop "p").somehow

#search [] ⊢ unitSeq
```

```
sequent  ⊢ p ⊃ (◯p)
verdict  PROVED   (→R (◯R init))

proof term (G4iLL″):
  (→R (◯R init))

pin it:
theorem found :
    Nonempty (LaxND [] ((PLLFormula.prop "p").ifThen ((PLLFormula.prop "p").somehow))) :=
  PLLND.Search.proved_sound
    (.impR (.laxR (.init (by decide))))

#print axioms found
```

The block under `pin it:` is Lean source: paste it into your file, rename
the theorem, and the kernel rechecks it.  That is the whole
discover-then-pin loop.

### The functions

`G4cTm.pretty` renders a found term as its rule tree; `G4cTm.snippet` renders
it as the pinning source.

```lean
#eval (proof [] unitSeq).map (·.pretty)
-- some "(→R (◯R init))"

#guard (proof [] unitSeq).isSome

#eval IO.println ((proof [] unitSeq).map (·.snippet "unit_derivable") |>.getD "")
-- theorem unit_derivable :
--     Nonempty (LaxND [] ((PLLFormula.prop "p").ifThen ((PLLFormula.prop "p").somehow))) :=
--   PLLND.Search.proved_sound
--     (.impR (.laxR (.init (by decide))))
--
-- #print axioms unit_derivable
```

`#guard` fails the build if the search stops finding the proof, so it is the
cheap way to keep a discovery under regression control.

Pinned, the theorem is:

```lean
theorem unit_derivable : Nonempty (LaxND [] unitSeq) :=
  proved_sound (.impR (.laxR (.init (by decide))))

#print axioms unit_derivable
-- 'unit_derivable' depends on axioms: [propext, Quot.sound]
```

`by decide` and `by simp` both discharge the list-membership side
conditions; `snippet` emits `by decide` because `by simp` pulls
`Classical.choice` into the pinned theorem's axiom set and `by decide` does
not.

If you transcribe a rule tree by hand instead of using `snippet`, the
implicit arguments of the left rules (which formula of the context is being
decomposed) sometimes need to be supplied by name, e.g.
`.orL (A := prop "p") (B := prop "q") (by decide) …`.  The rule names printed
by `pretty` map to constructors as: `→R` `.impR`, `◯R` `.laxR`, `◯L`
`.laxL`, `∧R` `.andR`, `∨R₁/∨R₂` `.orR1/.orR2`, `∧L` `.andL`, `∨L` `.orL`,
`→Lₐₜ` `.impLProp`, `→L∧` `.impLAnd`, `→L∨` `.impLOr`, `→L→` `.impLImp`,
`→L◯` `.impLLax`, `→L◯◯` `.impLLaxLax`, `init` `.init`, `⊥L` `.botL`.

---

## 4. Refuting a sequent

The negative engine runs the battery and then, if the subformula closure is
small enough, the emitter.  `Search.countermodel Γ C` is the sequent-first
form; `Search.refute? cfg Γ C` the configuration-first one.  Either returns
`Option (Witness Γ C)`: the model, the refuting world, and the checker's
verdict about *this* sequent.

### The command

```lean
def escSeq : PLLFormula := ((prop "p").somehow).ifThen (prop "p")

#refute [] ⊢ escSeq
```

```
sequent  ⊢ (◯p) ⊃ p
verdict  REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1

countermodel:
2 worlds, refuting world 0; fallible {1}
  *w0  ⊑> {1}  ⊳ {1}  ⊩ —
   w1  ⊑> {}   ⊳ {}   ⊩ ⊥ (fallible)

pin it:
theorem underivable :
    ¬ Nonempty (LaxND [] (((PLLFormula.prop "p").somehow).ifThen (PLLFormula.prop "p"))) :=
  FinCM.not_provable_of_check
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], [(1, "p")]⟩) (w := 0) (by decide)

#print axioms underivable
```

### Reading the model picture

`Search.renderCM M w?` is the renderer used above; `Witness.render` is it
applied to a witness.  One line per world:

- `*` marks the refuting world;
- `⊑>` lists the **cover** successors of `Rᵢ` — the transitive reduction,
  so an edge implied by two others is not repeated.  On the twenty-world
  model of §6 this is the difference between three readable screens and one;
- `⊳` lists the `Rₘ` successors;
- `⊩` lists the atoms forced there, or `⊥ (fallible)` for a fallible world,
  which forces everything.

```lean
#eval (countermodel [] escSeq).map (·.summary)
-- some "2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1"

#eval IO.println ((countermodel [] escSeq).map (·.render) |>.getD "")
-- 2 worlds, refuting world 0; fallible {1}
--   *w0  ⊑> {1}  ⊳ {1}  ⊩ —
--    w1  ⊑> {}   ⊳ {}   ⊩ ⊥ (fallible)
```

For a picture rather than text, `LaxLogic/PLLDiagram.lean` exports a `FinCM`
to TikZ or SVG (`Diagram.toTikz`, `Diagram.toSvg`, with `Diagram.autoPos`
for an automatic layout), over the same transitive reduction.  That code is
outside the trust story too.

### Pinning

Copy the model data into the statement and let `decide` run the checker
inside the kernel — or let `Witness.snippet` write it for you:

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

---

## 5. The two-sided procedure, and when to cap it

`Search.settle cfg Γ C : Answer Γ C` (the entry point formerly called
`decide`; `decide` remains as an alias) runs, in order:

1. the battery (certified countermodel, cheap);
2. `G4cTm.find` on the original sequent (proof term), capped at
   `cfg.findBudget` when that is set;
3. the closure emitter, if `(closure size) ≤ cfg.emitClosureCap` (default 12);
4. `.unknown`.

`Search.settleWhy` is the same procedure returning `Verdict Γ C`, whose
`.unknown` carries the reason.  `Search.verdict Γ C` and
`Search.verdictWhy Γ C` are the sequent-first forms.

```lean
#eval (verdict [] escSeq).summary
-- "REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1"

#eval (match settle {} [] escSeq with
       | .proved _      => "PROVED"
       | .refuted _ _ _ => "REFUTED"
       | .unknown       => "UNKNOWN")
-- "REFUTED"
```

**Why an answer is `unknown`.**  The three routes are distinguished by
`Reason`, and `Reason.describe` names the knob:

```lean
#eval (verdictWhy [] unitSeq (cfg := { findBudget := some 2 })).summary
-- "UNKNOWN  positive stage truncated: the node budget of 2 ran out
--  (raise Config.findBudget, or set it to none)"

#eval (verdictWhy [] (prop "p") (cfg := { frames := [], emitClosureCap := 0 })).summary
-- "UNKNOWN  emit stage skipped: subformula closure has 2 formulas, cap is 0
--  (raise Config.emitClosureCap)"

#eval (verdictWhy [] unitSeq).reason?
-- none        -- there is a verdict, so there is no reason
```

The third reason, `allStagesMissed`, means the battery, the (exhausted)
proof search and the emitter all ran and none produced a certificate: widen
`Config.frames` or `Config.comboCap`.

**Cost.**  Successes are cheap on both sides.  The bad case is a sequent
that is underivable *and* escapes both countermodel stages: then `find`
must exhaust its search space, which is finite but exponential.  Measured
node counts (nodes visited by `find`, on this tree, 2026-07-27):

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
is nonetheless exponential.  Three underivable families against an
unreachable atom, measured the same way, with `k` premises:

| family | k=1 | k=2 | k=3 | k=4 | k=5 | k=6 |
|---|---:|---:|---:|---:|---:|---:|
| `◯aᵢ ⊃ b` (k of them) together with `◯cᵢ` (k of them) | 11 | 109 | 637 | 2801 | 10411 | 34693 |
| chained `◯aᵢ ⊃ ◯aᵢ₊₁` together with `◯a₀` | 34 | 596 | 7125 | 67608 | 544671 | >3·10⁶ |
| `(pᵢ ⊃ q) ⊃ pᵢ` (Peirce shapes) | 7 | 49 | 277 | 1345 | 5921 | 24409 |

so about ×9, ×3.3 and ×4.2 per extra premise.  The chained family takes 26
seconds at `k=5` and over three minutes at `k=6`: multi-minute thrashes
start at six chained ◯-implications, not at the twenty-five the module
header used to claim.

**Node budget.**  Throughput is 7,000–21,000 nodes per second, falling as
contexts grow, so the default `budgetedConfig` budget of 200,000 nodes
bounds a grinding search at roughly 10–30 seconds.  That default applies to
the sequent-first wrappers (`verdict`, `verdictWhy`, `countermodel`,
`proof`) and to `#search` / `#refute` / `#refuteConf`.  It does **not**
apply to `settle {} Γ C` or `decide {} Γ C`, whose `Config.findBudget`
default is still `none` — deliberately, so that existing probe files keep
the behaviour they were written against.

```lean
-- nodes actually visited (budget minus remainder)
#eval 100000 - (G4cTm.findBounded 100000 [] unitSeq).2
-- 3

-- turn the wrappers' budget off again
#eval (verdict [] escSeq (cfg := { findBudget := none })).summary
-- "REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1"

-- or turn it on for the configuration-first entry point
#eval (settle { findBudget := some 200000 } [] escSeq).summary
-- "REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1"
```

`G4cTm.findBounded budget Γ C` returns the result paired with the
*remaining* budget, and the three readings are:

- `(some t, _)`: a proof term, as trustworthy as `find`'s;
- `(none, k+1)`: the space was exhausted with budget to spare, so this is the
  same (certificate-free) `none` that `find` gives;
- `(none, 0)`: the budget ran out. Unknown, and nothing more.  This is the
  distinction `Reason.budgetExhausted` reports.

`Search.prove?Bounded budget Γ C` is the same with the remainder discarded.
Because `budget - remaining` is the node count, `findBounded` doubles as a
profiler for choosing budgets.

**Widening the battery.**  `Config.frames` is a list of
`⟨n, ri, rm, fall⟩` records; prepend your own shapes to `defaultFrames` when
a family of sequents keeps returning `.unknown`.  `Config.comboCap` bounds
the decoration enumeration per frame, so an atom-rich sequent silently skips
frames that would blow up; raise it if you are prepared to pay.

**Filtering the battery.**  `Config.accept : FinCM → Bool` is an untrusted
pre-filter on candidate models, applied before the verified gate in both
refutation stages.  It defaults to accepting everything; §6 sets it to
`RNC.confB`.

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
(`derivU_iff_confluent_valid`).  Everything below lives in
`LaxLogic/PLLSearchConf.lean`, namespace `PLLND.RNC`; no `import wip.…` is
needed.

**Positive side.**  Search for a PLL proof of `instances ++ Γ ⊢ C`, choosing
the instances by hand (typically one per `∨`-subformula of the sequent), and
convert with `RNC.derivU_of_proved ps : Nonempty (LaxND (ps.map distF ++ Γ) C)
→ DerivU Γ C`.  The conversion is valid whatever instances were used, so
choosing them badly costs a failed search and nothing else.

```lean
def premise : PLLFormula := ((prop "p").or (prop "q")).somehow
def goal    : PLLFormula := ((prop "p").somehow).or ((prop "q").somehow)
def inst    : PLLFormula := ConfluentU.distF (prop "p") (prop "q")

#eval (proof [inst, premise] goal).map (·.pretty)
-- some "(→L◯◯ (◯R (∨L (∨R₁ init) (∨R₂ init)))
--             (∨L (∨R₁ (◯L (◯R init))) (∨R₂ (◯L (◯R init)))))"
```

**Negative side.**  A `FinCM` refutes `DerivU` only if it is mutually
confluent.  `RNC.confB M : Bool` decides this, and

```lean
RNC.not_derivU_of_checkConf : confB M = true → FinCM.checkB M w Γ C = true →
                              ¬ ConfluentU.DerivU Γ C
```

is the certificate theorem.  Both hypotheses discharge by `decide`.

**The trap, and how it is now closed.**  A countermodel returned by
`Search.refute?` is *not* automatically a PCLL refutation: most of
`defaultFrames` happens to be mutually confluent, but not all of it, and the
emitter produces non-confluent models freely.  Rather than test `confB`
afterwards and hope, use `RNC.refuteConf?` (or `RNC.countermodelConf`, or
the `#refuteConf` command), which sets `Config.accept := confB` so that
non-confluent candidates are skipped *during* the search:

```lean
#refuteConf [(prop "p").somehow] ⊢ (prop "p")
```

```
sequent  ◯p ⊢ p  (PCLL)
verdict  REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1 (mutually confluent)

countermodel:
2 worlds, refuting world 0; fallible {1}
  *w0  ⊑> {1}  ⊳ {1}  ⊩ —
   w1  ⊑> {}   ⊳ {}   ⊩ ⊥ (fallible)

pin it:
theorem underivable_pcll :
    ¬ ConfluentU.DerivU [((PLLFormula.prop "p").somehow)] (PLLFormula.prop "p") :=
  PLLND.RNC.not_derivU_of_checkConf
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], [(1, "p")]⟩) (w := 0) (by decide) (by decide)

#print axioms underivable_pcll
```

The distribution axiom itself is the illustration of the difference: PLL
refutes `◯(p ∨ q) ⊢ ◯p ∨ ◯q`, PCLL proves it, and so the PLL countermodel
must be non-confluent — and is.

```lean
#eval (RNC.refuteConf? {} [premise] goal).isSome   -- false
#eval (refute? {} [premise] goal).isSome            -- true
```

`RNC.WitnessConf Γ C` carries both facts, so `RNC.refutedU_sound` turns it
into `¬ ConfluentU.DerivU Γ C` in one application, and
`WitnessConf.snippet` writes the pinned theorem.

The probe files remain where they were: `wip/rnc_probe.lean` (the RNC(◯,{})
matrix) now imports the library module, and pinned PCLL certificates in the
house style are in `wip/rncCert.lean` (negative) and `wip/rncCertPos.lean`
(positive).  Those still need `lake build wipshared` first.

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

- **`UNKNOWN` and you want to know why.**  Use `verdictWhy` / `settleWhy`
  rather than `verdict` / `settle`: the `Reason` names the knob
  (`budgetExhausted`, `closureTooBig`, `allStagesMissed`), which is the
  information the rest of this section used to supply only in prose.
- **`.unknown` on a sequent you believe underivable.**  If the reason is
  `allStagesMissed`, the battery missed it: add a frame to `Config.frames`,
  or raise `Config.comboCap`.  If it is `closureTooBig`, raise
  `Config.emitClosureCap`.
- **A run that will not return.**  Use the sequent-first wrappers or the
  commands, which budget the positive stage by default; or set
  `Config.findBudget` explicitly.  There is no interrupt: the searcher is a
  pure function.
- **`decide`/`rfl` failing on a search result inside a proof.**  Expected:
  the searchers are `partial`.  Discover with `#eval`/`#guard`/`#search`,
  pin the certificate by hand or by `snippet`.
- **A transcribed proof term that will not elaborate.**  Supply the implicit
  formula arguments of the left rule by name — or use `G4cTm.snippet`, which
  does it for you.
- **A pinned countermodel that `by decide` rejects.**  The model was copied
  against the wrong sequent, or a relation list is not transitively closed:
  `checkB` includes the well-formedness check.
- **A PCLL claim resting on a PLL countermodel.**  Use `RNC.refuteConf?` /
  `#refuteConf`, not `refute?`; see §6.
- **`PLLND.Search.decide` shadowing `Decidable.decide`.**  Use `settle` (the
  same function under its current name).

---

## 9. Presentation improvements: status

The ten suggestions this section used to list are now **all implemented**,
two of them with a deliberate deviation, recorded below.  What follows is
the original list with its outcome.

1. **A name for the two-sided entry point that does not collide with
   `Decidable.decide`.**  *Done.*  `PLLND.Search.settle` (and
   `Search.settleWhy` for the reason-carrying version).  `decide` survives
   as a plain definition delegating to `settle`, **not** marked
   `@[deprecated]`: the old name has several dozen call sites across `wip/`,
   and a deprecation warning at each would drown the build log.  The
   sequent-first `verdict` (§5) is the name to reach for in new code.

2. **`#search` / `#refute` commands.**  *Done*, in
   `LaxLogic/PLLSearchCmd.lean`, plus a third, `#refuteConf`, for PCLL.
   Each takes `Γ ⊢ C` and an optional `with cfg`, and prints the sequent,
   the verdict (with the reason when unknown), the proof tree or the
   rendered countermodel, and the pinning snippet.  The `Answer`-matching
   boilerplate is gone from §§3–6.

3. **The `Config` argument optional in practice.**  *Done.*  `verdict`,
   `verdictWhy`, `countermodel` and `proof` take `Γ`, `C` first and default
   the configuration; a non-default one goes in as `(cfg := …)`.

4. **Pinning snippets as text.**  *Done.*  `Witness.snippet`,
   `G4cTm.snippet` and `RNC.WitnessConf.snippet` emit paste-ready theorem
   source including the `#print axioms` line; `srcOf`, `srcOfCtx` and
   `srcOfCM` are the underlying renderers.  Left-rule implicits that the
   goal does not determine are emitted by name, and the membership side
   conditions as `by decide` (measured: `by simp` costs an extra
   `Classical.choice` in the pinned theorem's axiom set).  All three are
   wired into the commands' output.

5. **`.unknown` answers carrying why.**  *Done, with a deviation.*  The
   reason could not be added to `Answer.unknown` itself: `Answer` is
   pattern-matched with all three constructors in `LaxLogic/PLLSearchEx.lean`
   and in several probe files, and giving `unknown` an argument breaks every
   one of those matches.  Instead `Verdict Γ C` is `Answer` with
   `.unknown (r : Reason)`, `Verdict.toAnswer` is the forgetful map, and
   `settleWhy` / `verdictWhy` return the richer type.  `Reason` distinguishes
   `budgetExhausted b`, `closureTooBig size cap` and `allStagesMissed`, and
   `Reason.describe` names the knob.

6. **The confluence test folded into the API.**  *Done.*
   `LaxLogic/PLLSearchConf.lean` promotes `confB`,
   `mutuallyConfluent_of_confB`, `not_derivU_of_checkConf`,
   `derivU_of_proved` and `derivU_of_proved'` out of `wip/rnc_probe.lean`
   (same namespace `PLLND.RNC`, same statements, so the probe's dependents
   are unaffected), and adds `refuteConf?` / `countermodelConf` /
   `WitnessConf` / `refutedU_sound`.  The `Config` flag asked for is
   `Config.accept : FinCM → Bool`, the general pre-filter on candidate
   models; PCLL sets it to `confB`.

7. **The node budget on by default.**  *Done, conservatively.*
   `Config.findBudget`'s own default is **unchanged** (`none`), because the
   probe files depend on the current behaviour of `decide {} Γ C`.  The
   budget is on instead in `Search.budgetedConfig`
   (`defaultFindBudget = 200000`), which is what the sequent-first wrappers
   and the three commands default to; `(cfg := { findBudget := none })`
   turns it off.  Measured, 200,000 nodes bounds a grinding search at
   roughly 10–30 seconds (§5).

8. **Formulas, not `FinCM` records.**  *Done.*  `Search.renderCM` prints one
   line per world — cover edges of `Rᵢ` (transitive reduction), `Rₘ`
   successors, forced atoms, refuting world marked — with
   `Witness.render` / `WitnessConf.render` the witness-level forms and
   `summaryCM` a one-liner.  Used in `#refute` and `#refuteConf` output.
   It is deliberately independent of `PLLDiagram.lean`, whose module does
   file IO at import time; the two agree on the transitive reduction.

9. **The cost figures in the header of `PLLSearch.lean`.**  *Done*, and
   re-measured on this tree rather than copied: the gap sequent
   `◯((◯p ⊃ r) ⊃ ◯p), ◯p ⊃ r ⊢ r` is 136 nodes, not 825; the three-premise
   chained ◯-implication pool is 7,125, not 7,256; and the "multi-minute
   thrash at ~25 premises" is wrong by a wide margin — that family thrashes
   at six.  §5 above carries the same tables.

10. **The intended reading order.**  *Done.*  It heads this file and the
    module header of `PLLSearch.lean`, and `README.md` carries a one-line
    pointer to this manual.

Two things remain *not* done, and are recorded here rather than silently
dropped:

- **`decide` is not deprecated**, only aliased (item 1).  Marking it would
  be the cleaner signal; it is deferred until the `wip/` call sites are
  migrated, which is a separate mechanical change.
- **`Answer.unknown` still carries no reason** (item 5).  The reason lives
  on `Verdict`.  Collapsing the two types is possible once nothing
  pattern-matches `Answer` with a bare `.unknown`.
