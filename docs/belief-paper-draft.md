# Belief in Lax Logic — first draft

*Working draft 2026-07-18, for Matthew Fairtlough. Every mathematical claim
below is machine-checked in the Lean 4 + Mathlib artefact at
`github.com/fairflow/lax-logic-in-lean` unless explicitly marked **open**;
each theorem is anchored to its Lean name and file, and the axiom audit of
every named result is recorded in `docs/pll-formalisation-ledger.md`. Reading
conventions for the interleaved Lean follow `docs/annotated/README.md`:
Lean statements are displayed verbatim in fenced blocks, each followed by an
"in words" translation; proofs are described at the level of their actual
mechanised case structure.*

---

## 1. Introduction

Propositional Lax Logic (PLL) extends intuitionistic propositional logic with
a single modality ◯ obeying three axioms:

    M ⊃ ◯M        ◯◯M ⊃ ◯M        (M ⊃ N) ⊃ (◯M ⊃ ◯N)

Algebraically ◯ is a *nucleus* (an inflationary, idempotent, meet-preserving
operator on a Heyting algebra); categorically it is a strong monad on the
propositions; proof-theoretically it is Moggi's computational metalanguage.
Fairtlough–Mendler (*Inf. & Comp.* 137(1), 1997) introduced it for hardware
verification under constraints, reading ◯M as "M holds under some
constraint".

This paper proposes and defends a different reading: **◯M is "M is
believed"** — belief by a single idealised, evidentially disciplined
believer — and argues that under this reading PLL is the natural minimal
logic of *evidential* belief. The argument has an unusual feature: every
step of it is machine-checked, and several of its pivots were *discovered*
by the machine-checking — points where an attempted proof failed and the
failure was itself provable, redirecting the theory. The paper is therefore
also an essay in method: formalisation not as an audit of finished
mathematics but as an instrument of discovery.

The technical contributions:

1. **The belief algebra** (§3). On a Boolean algebra every nucleus is
   closed — classical belief degenerates to `◯M ⟺ M ∨ a` for a fixed
   proposition `a`, a spectrum bracketed by the total sceptic and the total
   credulist. Intuitionistically the picture is rich: open nuclei
   (hypothetical belief) are invisible classically, and the closed
   ◯-fragment of one free algebra is infinite. Belief is worth having
   *only* constructively.

2. **Evidence semantics** (§4–5). Over Fairtlough–Mendler constraint
   frames we equip atoms with *evidence* from a partial applicative
   structure and define three realisability clause families, differing
   only in how much a realiser is told about the future of the inquiry:
   uniform (⊩ᵘ), strategy (⊩ˢ), and presented-strategy (⊩ᵖ). A sequence
   of machine-checked separation theorems shows the choice is not a matter
   of taste: rigid evidence validates more than PLL proves; strategy
   evidence restores the countermodels but provably cannot support
   completeness; presenting the future at implications — and the proof
   that nothing less suffices is *created by the modality's own
   strategies* — yields a completeness theorem.

3. **Completeness, finitely and without Zorn** (§6). PLL is complete for
   ⊩ᵖ-realisability over finite, token-decorated, checker-verified
   models. The countermodels are built by a canonical-model construction
   in which the Lindenbaum step is an *iterated decision*: PLL's own
   mechanised decision procedure decides, closure formula by closure
   formula, whether to believe or refute. No maximality principle is
   invoked anywhere.

4. **Executable countermodels** (§7). The model theory runs. A verified
   checker certifies finite countermodels by computation; an untrusted
   emitter proposes them from failed proof search; the emitted models are
   *belief-state readouts* — each world lists what is believed and what
   is promised never to be evidenced. Proof search failure becomes a
   structured epistemic explanation.

### 1.1 The idealisation, owned

Following Hintikka (*Knowledge and Belief*, 1962), a doxastic logic
describes not flesh-and-blood believers but an idealisation, and the
idealisation should be stated, not smuggled. Ours is the unit and the
functoriality: `M ⊃ ◯M` says the believer accepts what is true (truth-closed
belief), and `Γ ⊢ M` implies `◯Γ ⊢ ◯M` says belief is closed under
consequence (logical omniscience) — both machine-checked as theorems of the
system, not assumptions about people (`BeliefIdealisation.lean`). Two
further marks distinguish belief from knowledge: there is **no factivity**
(◯M ⊃ M is refutable) and **no D axiom** — ◯⊥ is consistent, and so is its
negation's unprovability: `⊬ ¬◯⊥` (`BeliefFalsum.lean`,
`PLLFrames.lean`). An inconsistent belief does not explode the believer;
it is *quarantined* behind the modality. Introspection is exact:
`◯◯M ⊣⊢ ◯M`. The nearest published neighbour is Artemov–Protopopescu's
intuitionistic belief IEL⁻ (co-reflection without factivity); PLL's ◯ is
conjecturally IEL⁻ plus idempotence — recorded as **open**.

---

## 2. The mechanised base

Everything in this paper stands on a complete mechanisation of PLL: natural
deduction with membership-based contexts (`LaxND`, `PLLNDCore.lean`); the
intrinsically-typed proof-term calculus (`Tm`, `PLLTerms.lean`) with strong
normalisation of full β + let-associativity by ⊤⊤-lifting
(`PLLTopTop.lean`; annotated walk-through in
`docs/annotated/strong-normalisation.md`); a cut-free sequent calculus with
cut elimination, the disjunction property and ◯-reflection
(`PLLSequent.lean`); Kripke constraint semantics with soundness
(`PLLKripke.lean`) and classical completeness (`PLLCompleteness.lean`);
decidability by a terminating, kernel-honest procedure over a *repaired*
Dyckhoff-style calculus (`PLLG4Dec.lean`) — repaired because the published
G4-style calculus for PLL is provably incomplete, with a machine-checked
counterexample (`PLLG4Gap.lean`; a note to its author is in preparation).
Axiom audits: after the 2026-07-18 scrub, the entire proof-theoretic chain
— cut elimination, the calculus equivalences, the disjunction property —
audits at `[propext, Quot.sound]`: **no choice**. The full audit table is
the ledger's Part I.

The semantic objects:

```lean
structure ConstraintModel where
  W : Type
  Ri : W → W → Prop      -- intuitionistic accessibility (a preorder)
  Rm : W → W → Prop      -- constraint accessibility (a preorder, Rm ⊆ Ri)
  F : Set W              -- fallible worlds (hereditary; valuation full there)
  V : String → Set W     -- hereditary valuation
  ...
```

Forcing is intuitionistic at the propositional connectives, `⊥` holds
exactly at fallible worlds, and

    w ⊨ ◯N   iff   ∀ v ≥ᵢ w, ∃ u. v Rₘ u ∧ u ⊨ N :

however inquiry develops, the constraint can somehow be discharged in a
way that yields N. Fallible worlds are what keep ◯⊥ satisfiable — the
quarantine, semantically.

---

## 3. Classical belief is degenerate; constructive belief is rich

**Theorem** (`BeliefCollapse.lean`, `BeliefBooleanIso.lean`). On a Boolean
algebra every nucleus is closed: `j x = x ⊔ j ⊥`. Consequently the nuclei
on B form a lattice isomorphic to B itself (`N(B) ≃o B`), and each belief
operator is `◯M ⟺ M ∨ a` for a fixed `a = ◯⊥`: the believer's entire
doxastic character is one proposition, the "credulity level". At `a = ⊥`
the total sceptic (`◯M ⟺ M`); at `a = ⊤` the total credulist
(`◯M ⟺ ⊤`). There is nothing else classical belief can be.

**Theorem** (`BeliefOpenClosed.lean`, `PLLLaxInfinite.lean`).
Intuitionistically the open nucleus `u_a = (a → ·)` — belief *under the
hypothesis a*, the natural logic of conditional commitment — coincides
with a closed nucleus exactly when excluded middle holds at `a`; and the
closed ◯-fragment `RN(◯, {})` of the free algebra on no generators is
**infinite** (machine-checked enumeration argument). Constructive belief
has infinitely many pairwise-inequivalent modal degrees where classical
belief has a single parameter.

**Theorem** (context completeness; `PLLCtxCompleteness.lean`, after
F&M TYPES 2000). `PLL ⊢ φ` iff for every standard constraint context C,
`IPL ⊢ φ^C`: a proof of ◯M *is* a proof of M under a constraint, uniformly
in the constraint. This is the precise sense in which the belief is
evidential: **a proof of ◯M contains the evidence for believing M**. No
finite set of constraint contexts suffices (Corollary 10) — the evidence
genuinely varies.

Together: (A) classically, belief collapses; (B) constructively it is
rich; (C) the richness is evidential; (D) therefore a non-degenerate logic
of evidential belief is possible *only* over intuitionistic logic. That is
the paper's philosophical spine, and every vertebra is a theorem.

---

## 4. Evidence semantics: the three clause families

Fix a partial applicative structure and an evidence assignment:

```lean
structure Pca where
  Carrier : Type
  app : Carrier → Carrier → Option Carrier
  pair : Carrier → Carrier → Carrier
  fst snd : Carrier → Carrier
  tag : Bool → Carrier → Carrier
  untag : Carrier → Bool × Carrier
  -- pairing and tagging laws

structure Evidence (P : Pca) (C : ConstraintModel) where
  E : String → C.W → Set P.Carrier
  hered_E : ∀ {s w v}, C.Ri w v → E s w ⊆ E s v
  full_E  : ∀ {s w}, w ∈ C.F → ∀ x, x ∈ E s w
```

In words: at each world each atom has a (possibly empty) set of evidencing
elements; evidence persists as inquiry proceeds (*belief increases along
the branching order* — heredity is a theorem for all three relations
below); at fallible worlds everything evidences everything (the semantic
quarantine again).

The three relations agree at atoms (`x` evidences the atom), ⊥ (fallible
worlds only), ∧ (pairing), ∨ (tagging), and differ at ⊃ and ◯. Uniform
realisability ⊩ᵘ evaluates both clauses blind:

    x ⊩ᵘ φ⊃ψ at w  iff ∀ v ≥ w, ∀ b ⊩ᵘ φ at v:  app x b ⊩ᵘ ψ at v
    x ⊩ᵘ ◯φ  at w  iff ∀ v ≥ w, ∃ u. v Rₘ u ∧ x ⊩ᵘ φ at u

— the *same* element must serve every future and every constraint-witness.
Strategy realisability ⊩ˢ (relative to an injective world-coding
κ : W → Carrier) instead makes the ◯-evidence a *function of the presented
future*:

```lean
| .somehow φ, x, w =>
    ∀ v, C.Ri w v → v ∈ C.F ∨
      (∃ y, P.app x (κ v) = some y ∧
        ∃ u, C.Rm v u ∧ P.fst y = κ u ∧ realS P Ev κ φ (P.snd y) u)
```

In words: evidence for ◯φ is a strategy which, *handed the code of
whatever future v actually arrives*, answers with a package naming a
constraint-witness u (as κ u) together with evidence for φ there. The
strategy has no foreknowledge — the future is its input; and the witness
is *named*, not merely asserted, because the elimination rule's
computational content must apply its continuation at that name.

Presented-strategy realisability ⊩ᵖ extends the same courtesy to
implication:

```lean
| .ifThen φ ψ, x, w =>
    ∀ v, C.Ri w v → v ∈ C.F ∨
      (∀ b, realP P Ev κ φ b v →
        ∃ y, P.app x (P.pair (κ v) b) = some y ∧ realP P Ev κ ψ y v)
```

— the realiser of φ⊃ψ receives the pair ⟨κ v, b⟩: the presented world and
the argument. §5 proves this is not a convenience but a necessity.

---

## 5. The separation theorems: evidence discipline determines the logic

All on the three-world *split model* (root r below two incomparable
leaves; A true at one, B at the other) or small variants; all
machine-checked; the labels (i)–(iv) follow the development.

**(i) The bite** (`bite_uniform_split`). At the root, ◯(A∨B) is
*truth-forced* — every future can reach an A-leaf or a B-leaf — but **no
element ⊩ᵘ-realises it**: a uniform realiser carries one tag, and would
have to decide the disjunct before the branch happens. Truth outruns rigid
evidence.

**(ii) Uniform incompleteness** (`uniform_dist_valid`). Dually, the
identity element ⊩ᵘ-realises `◯(A∨B) ⊃ (◯A ∨ ◯B)` at every world of
*every* model — a scheme PLL demonstrably does not prove
(`not_provable_somehow_or_dist`). So PLL is **incomplete** for uniform
realisability: rigid evidence validates a stronger logic (call it PLLᵘ;
its axiomatisation is **open**).

**(iii) Strategy separation** (`strategy_realises_obAB`,
`strategy_dist_refuted`). Under ⊩ˢ a case-splitting strategy realises
◯(A∨B) at the root — the bite vanishes — while `◯(A∨B) ⊃ (◯A ∨ ◯B)`
acquires a genuine countermodel. The first genuine *program* of the
development: evidence that reacts to the future.

**(iv) The ⊃-barrier** (`impdist_not_uniform`). `(◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)`
is not ⊩ᵘ-valid: uniformity fails at implication too, in its own way.

The question the paper then had to answer: is ⊩ˢ the right relation — is
PLL *complete* for it? The answer, discovered in the attempt and then
proved, is no:

**Theorem (the obstruction — fullness is unachievable for ⊩ˢ)**
(`realS_fullness_obstruction`, audit `[propext, Quot.sound]`).

```lean
theorem realS_fullness_obstruction (P : Pca) (κ : obsC.W → P.Carrier)
    (htab : ∀ g : obsC.W → P.Carrier, ∃ s, ∀ i, P.app s (κ i) = some (g i)) :
    ¬ ∃ Ev : Evidence P obsC,
      (∀ (a : String) (w : obsC.W), ∀ x ∈ Ev.E a w, w ∈ obsC.V a) ∧
      (∀ (φ : PLLFormula) (w : obsC.W), obsC.force w φ →
        ∃ x, x ⊩ˢ[Ev, κ, w] φ)
```

In words: on a fixed three-world frame (t at both leaves, p at one, q at
the other), **no** evidence assignment is simultaneously *atom-adequate*
(evidence only where the atom holds) and *full* (every forced formula has
a realiser) — for every applicative structure able to implement finite
lookup tables against the coding. Since adequacy-plus-fullness is exactly
the mutual induction a completeness proof must run, completeness of PLL
for ⊩ˢ is not provable by decoration on these frames.

*Proof idea, and why it is ◯-essential.* Fullness at the atom t hands
over tokens at both leaves; one finite table is then a single strategy s
realising ◯t at *both* incomparable leaves — strategies carry no
world-marks. Feed s to a putative realiser x of `◯t ⊃ (p∨q)` (truth-forced
at the root, vacuously there and via the local atom at each leaf): the ⊃
clause of ⊩ˢ shows x only the argument, so `app x s` is one answer `y`
serving both leaves — whose tag must be *false* at the p-leaf (no
q-evidence there, by atom-adequacy) and *true* at the q-leaf. One Boolean
cannot be both. For a purely intuitionistic antecedent the obstruction
evaporates — world-tagged atom evidence lets a table rescue fullness,
because forcing a disjunction at a branch point is already a commitment
by heredity. What cannot carry world-marks is precisely a *strategy*. The
modality's own evidence discipline forces the repair. ∎

The moral of §5, and the paper's central slogan: **what one may assume
about how evidence meets the future determines which belief logic one
gets.** Rigid evidence: a strictly stronger logic (PLLᵘ). Reactive
evidence at ◯ only: PLL's theorems, but not only they are supportable.
Reactive evidence everywhere: exactly PLL — as §6 proves.

---

## 6. Completeness

### 6.1 Decoration: adequacy and fullness for ⊩ᵖ

The completeness construction decorates *finite, checker-verified* frames.
`FinCM` (`PLLCountermodelEmit.lean`) is a finite constraint model as
literal data — worlds 0..n−1, relations as pair-lists, valuation as
(world, atom)-pairs — with an executable forcing function `forceB`, a
decidable well-formedness check, and a verified reflection lemma
(`force_iff`): the computation *is* the semantics. *Token evidence* gives
each atom one token, exactly where the atom holds.

```lean
theorem realP_adequate_and_full (h : M.WellFormed) (tok : String → P.Carrier)
    (κ : Fin M.n → P.Carrier)
    (htab  : ∀ g, ∃ s, ∀ i, P.app s (κ i) = some (g i))
    (htabP : ∀ g, ∃ s, ∀ i b, P.app s (P.pair (κ i) b) = some (g i)) :
    ∀ φ : PLLFormula,
      (∀ w x, (x ⊩ᵖ[tokenEvidence P M h tok, κ, w] φ) →
        (M.toModel h).force w φ) ∧
      (∃ wit : Fin M.n → P.Carrier, ∀ w,
        (M.toModel h).force w φ →
          (wit w) ⊩ᵖ[tokenEvidence P M h tok, κ, w] φ)
```

In words: over any checked frame with token evidence, whatever is
⊩ᵖ-realised is truth-forced (**adequacy**), and whatever is truth-forced
has an explicit realiser given by a per-world witness function
(**fullness**). Audit: `[propext, Quot.sound]` — the construction is
choice-free, and the reason is worth stating: every branch decision in the
witness is made by the *executable* forcing function. The ∨-witness
computes `forceB w φ` to decide its tag; the ◯-witness searches the finite
frame for its constraint-witness; the ⊃-witness, receiving ⟨κ v, b⟩, looks
up the consequent's witness *at the presented world* — the lookup the
obstruction proves impossible without presentation. The two table
hypotheses are discharged by an explicit algebra `tblPca` of finite lookup
tables (elements: base codes, pairs, tags, and two table formers; the laws
hold by `rfl`), so the closed capstones assume nothing.

*Proof shape (mutual induction on φ).* Adequacy and fullness are proved
simultaneously; each consumes the other at ⊃: adequacy at φ⊃ψ feeds the
antecedent's fullness witness into the realiser and applies adequacy at ψ;
fullness at φ⊃ψ uses adequacy at φ to know the incoming argument marks a
world where φ is forced, hence (by the forcing of the implication) ψ is
forced, hence the table may answer with ψ's witness there. The ◯ cases
thread the named witness through `fst`/`snd` of the strategy's answer. ∎

**The squeeze** (`realP_refutes_sequent`): every countermodel validated by
the verified checker is a ⊩ᵖ-refutation of its sequent — hypotheses
realised at the refuting world, conclusion unrealisable. (Adequacy turns
"conclusion unforced" into "conclusion unrealisable"; fullness realises
the forced hypotheses.)

### 6.2 The finite canonical model, without Zorn

What remained was to *produce* a checked countermodel for every
underivable sequent. The classical canonical model (`PLLCompleteness.lean`,
after F&M §4) works with theories as **triples** (val, fal, mfal): the
validated formulas, the falsified ones, and those falsified at every
constraint-successor — the third component is the semantic record of a
*promise* never to evidence a formula, and it is what stops the fallible
world from trivialising ◯. Consistency is: no finite selection Ds ⊆ fal,
Ts ⊆ mfal has

    val ⊢ ⋁Ds ∨ ◯(⋁Ts)

— note the ◯ guarding the promises: that guard is exactly what makes the
modal cases of the truth lemma cohere with functoriality. Classically the
model's worlds are *maximal* consistent triples, by Zorn.

The finite construction (`PLLFinComp.lean`) replaces maximality with
**closure-totality** over the subformula closure `cl` of the sequent:

```lean
def MaxIn (cl : Finset PLLFormula) (T : FTheory) : Prop :=
  T.Cons ∧ InCl cl T ∧ ∀ φ ∈ cl, φ ∈ T.val ∨ φ ∈ T.fal
```

and Zorn with an **iterated decision**:

```lean
noncomputable def extendStep (T : FTheory) (φ : PLLFormula) : FTheory :=
  if (T.insVal φ).Cons then T.insVal φ else T.insFal φ

theorem lindenbaum {cl} {T} (hT : T.Cons) (hIn : InCl cl T) :
    ∃ T', T.le T' ∧ MaxIn cl T' ∧ T'.mfal = T.mfal
```

In words: walk the closure once; at each formula ask the decision
procedure whether believing it stays consistent, and believe or refute
accordingly; the else-branch is safe by the same disjunction-combination
argument that classically proves every formula lands in val or fal.
Consistency of a finite triple is *decidable* — it reduces to a single
derivability check on the full selection (`cons_iff_check`), decided by
the mechanised decision procedure. And the fold leaves the promises
untouched — the truth lemma needs exactly that.

Three points deserve a conventional reader's attention:

* **The maximal-theory lemmas collapse.** Under totality, the classical
  Lemma 4.2 suite (primeness of val, implication decomposition, the
  falsification laws, mfal ⊆ fal) is proved with *singleton* selections
  where the classical proofs combine two extension-failure witnesses with
  list surgery. Totality is not just constructively available — it is
  simpler.

* **The truth lemma's three extensions.** Membership in val forces;
  membership in fal refutes (`truth_lemma`). The induction needs three
  Lindenbaum extensions, each now a decided fold: refuting φ⊃ψ extends
  ⟨val+φ, {ψ}, ∅⟩; forcing ◯φ at a future extends ⟨val₁+φ, ∅, mfal₁⟩ —
  the promises *carried across* to the constraint-witness; refuting ◯φ
  extends ⟨val, ∅, {φ}⟩ — a promise *created*, which every
  constraint-successor then honours (mfal ⊆ fal at total triples closes
  the case).

* **Nothing infinitary anywhere.** `finite_canonical_countermodel`: every
  underivable sequent is refuted at a world of its finite canonical
  model. The worlds are then enumerated into literal checker data
  (`canonFinCM`), a transfer lemma identifies the two forcings on closure
  formulas, and:

```lean
theorem emitter_completeness {Γ : List PLLFormula} {C : PLLFormula}
    (h : ¬ Nonempty (LaxND Γ C)) :
    ∃ (M : FinCM) (w : Nat), FinCM.checkB M w Γ C = true
```

### 6.3 The crown

```lean
theorem derivable_iff_no_realP_refutation {Γ : List PLLFormula}
    {C : PLLFormula} :
    Nonempty (LaxND Γ C) ↔
      ¬ ∃ (M : FinCM) (w : Nat) (hwf : M.WellFormed) (hlt : w < M.n),
        (∀ ψ ∈ Γ, ∃ x,
          x ⊩ᵖ[tokenEvidence tblPca M hwf tok₀, tblκ, ⟨w, hlt⟩] ψ) ∧
        ¬ ∃ x, x ⊩ᵖ[tokenEvidence tblPca M hwf tok₀, tblκ, ⟨w, hlt⟩] C
```

**A sequent is derivable exactly when no token-decorated, checker-verified
finite model realisability-refutes it.** Forward: soundness plus adequacy
and fullness — a derivable conclusion is forced wherever its realised
hypotheses are, hence realised by its own fullness witness. Backward: the
finite canonical model. Every quantifier ranges over concrete objects —
finite models as printable data, one token per atom, realisers in an
explicit algebra of finite lookup tables — and the backward case decision
is made by the decision procedure, not by excluded middle.

*Audit status.* The decoration half is `[propext, Quot.sound]` outright.
The canonical-model half currently inherits `Classical.choice` from
*measured, named* residues in the decidability infrastructure (a least-
height step awaiting a height-bounded decider; Mathlib finite-set
internals) — not from any set-theoretic principle in the mathematics. A
mechanical drilling task is in progress; when it lands, the crown's audit
drops to `[propext, Quot.sound]` with no change to any statement or proof
here.

---

## 7. Worked examples: the models, run

*(Pre-conclusion section. Everything here is generated by the artefact —
the countermodels by `#eval` of the emitter, the proof terms by the
kernel — and re-checkable by running the cited files.)*

### 7.1 A belief that cannot be cashed: ◯p ⊬ p

The emitter (`CounterEmit.emit`) proposes countermodels from failed proof
search; the verified checker certifies them; wrong proposals cannot
produce wrong certificates. For ◯p ⊢ p it emits a five-world model, pinned
in the library as data:

```lean
def demoM : FinCM :=
  { n := 5
    ri := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),
           (2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]
    rm := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,2),(2,3),(2,4),(3,3),
           (3,4),(4,4)]
    fall := [4]
    val := [(3, "p"), (4, "p")] }
```

Read as belief states: w2 believes exactly ◯p (the refuting world); w3
believes ◯p and p — the future where the constraint has been discharged;
w4 is the fallible ceiling; w1 is the state that has *promised* never to
evidence p (its only constraint-successor is itself). At w2, ◯p is forced
— every future can still reach w3 or w4 — but p is not. The kernel-checked
certificate:

```lean
theorem somehow_p_not_p :
    ¬ Nonempty (LaxND [(prop "p").somehow] (prop "p")) :=
  FinCM.not_provable_of_check (M := demoM) (w := 2) (by decide)
```

`decide` re-runs the verified checker inside the kernel: no
`native_decide`, audit `[propext, Quot.sound]`, choice-free. And by the
squeeze the same model realisability-refutes the sequent
(`somehow_p_not_p_realP_tbl`): ◯p is ⊩ᵖ-realised at w2, p unrealisable.

### 7.2 The ∨-distribution, refuted by a machine that shows its work

For ◯(p∨q) ⊢ ◯p ∨ ◯q the emitter builds twenty worlds; its human-readable
report (verbatim `#eval` output):

    refuting world: w4  (20 worlds)
      w4: believes [◯(p ∨ q)]
      w5: believes [◯(p ∨ q)], promises-false [◯p, p]
      w6: believes [◯(p ∨ q)], promises-false [◯q, q]
      ...

The refuting world believes exactly ◯(p∨q); its two critical futures carry
the standing promises "never p" and "never q". A promise, once made, binds
all constraint-successors (Rₘ preserves the promise component) — so from
w5 no future evidences p, killing ◯p there; symmetrically ◯q dies at w6;
the disjunction ◯p ∨ ◯q therefore fails at w4 while ◯(p∨q) survives —
each promise-world can still discharge *the disjunction* through its
unpromised disjunct. The machine has rediscovered, and certified, the
hand-built split model — and the printout *is* the epistemic explanation
of the search failure.

### 7.3 A proof compiled to evidence: the applicative composite

The sequent ◯A, ◯(A⊃B) ⊢ ◯B — combine a belief in A with a belief in the
implication — has the kernel-checked proof term (printed by `Tm.pretty`):

    let val• := #0 in (let val• := #2 in val (#0 #1))

i.e. `bind x (λa. bind f (λg. val (g a)))`: run the belief in A, obtaining
evidence a under its constraint; *under that constraint*, run the belief
in A⊃B, obtaining g; apply; return. Two `bind`s — sequential constraint
discharge, in the order chosen by the proof. (The backward searcher finds
the same theorem as the sequent derivation `(◯L (◯L (◯R (→Lₐₜ init))))` —
two left-◯ rules then the axiom under an application.)

Uniform extraction (`extract`, O3) compiles this derivation to a
polynomial over any combinatorially complete applicative structure, by
the equations `laxIntro ↦ identity`, `laxElim p₁ p₂ ↦ (λ-abstract p₂) ·
p₁`, `impElim ↦ application`:

    (λa. (λg. g · a) · f) · x

— the proof *is* this program; `extract_sound` proves its value
⊩ᵘ-realises ◯B wherever the context is realised. Under the strategy
clause (`extractS`, O3ˢ) the same derivation compiles to the reactive
form: presented a future c, run x's strategy at c to get ⟨named witness
u₁, evidence a⟩, run f's strategy *at the name u₁*, apply, and return
under the composed constraint — `laxElim`'s extraction is literally
`λc. (⟦continuation⟧ · snd(s₁·c)) · fst(s₁·c)`. Sequential composition of
beliefs is the meet law of the evidence semantics (`ob_strength`), and it
is machine-checked that **no confluence assumption appears anywhere** —
belief composition is ordered, as inquiry is.

### 7.4 What the examples teach

Soundness-grade evidence (extracted from proofs) is *frame-uniform*: one
polynomial serves every model. Completeness-grade evidence (the fullness
witnesses of §6.1) is *frame-aware*: the tables are built by surveying the
finite frame. That asymmetry is the formal shadow of a familiar epistemic
one — what is provable has evidence that needs no knowledge of the
situation; what is merely true here has evidence only relative to a survey
of this situation's futures. The presented future κ v is an *input at
evaluation time*, not an oracle: strategies are reactive policies over an
unfolding inquiry, and the gradual-discovery reading of the frames
survives intact. The idealisation lives exactly where Hintikka put it: in
the completeness theorem's omniscient survey, owned and stated.

---

## 8. Related work

Artemov–Protopopescu's intuitionistic epistemic logic: IEL⁻ (belief:
co-reflection `A → KA`, no factivity, K⊥ consistent) is the closest
system; PLL adds idempotence — the precise relationship is **open**
(conjecture: PLL-◯ = IEL⁻ + ◯◯A ⊃ ◯A). Justification logic's forgetful
reading forces factivity and is therefore not this. The constraint reading
of F&M and the monadic reading of Moggi/Benton–Bierman–de Paiva are the
two established computational faces of PLL; the belief reading is
compatible with both — the double-negation believer (`Rₘ = Rᵢ, F = ∅`
gives ◯M ⊣⊢ ¬¬M, machine-checked) recovers the continuation reading as a
special case. Realisability semantics for modal/lax logics: [survey to be
completed against `docs/realisability-modal-lit.md`]. The G4-style
terminating calculus for PLL is due to Iemhoff; the machine-checked
incompleteness of the published rules and the repaired calculus G4iLL″
are part of this artefact (a separate corrective note is in preparation).

## 9. Method: formalisation as instrument

Every claim above is a Lean theorem; the ledger records, for each, the
axioms it stands on — a hierarchy from *nothing at all* (the
Kleene–Brouwer well-foundedness used in the normalisation development)
through `[propext]`, `[propext, Quot.sound]` (no choice — most of this
paper), to classical (`Classical.choice`, now confined to measured
residues of the decidability infrastructure and the genuinely classical
Zorn completeness kept for comparison). Three times in this development an
attempted proof *refuted* its intended theorem and redirected the theory:
the collapse lemma for ⊩ˢ (refuted; led to the squeeze reformulation), a
claimed normality failure (refuted; ◯ is normal, `nucleus_himp_le`), and
the fullness obstruction (§5) — the discovery that the ⊃-clause must
present the future, which *created* ⊩ᵖ. We take this to be the working
reality of formalisation for mathematics at research level: the checker is
not a notary but a collaborator with an unerring nose for the case one
had not considered.

On routes to publication for machine-checked mathematics by unaffiliated
authors (full verified survey: `docs/publication-routes.md`): the working
plan is the split the survey recommends — the technical core to a
formalisation-literate venue (CPP 2027, submission 10 September 2026,
with a fuller journal version to JAR's Proof Pearls track or LMCS
afterwards: the perfectoid-spaces trajectory), and the belief argument as
a companion paper to a philosophical-logic venue (the new diamond-OA
*Philosophical Logic*, or Studia Logica). The artefact is made citable by
a Zenodo-archived GitHub release with `CITATION.cff`, following the
now-standard practice of citing Lean repositories as first-class research
objects (perfectoid spaces, the Mathlib paper, the Liquid Tensor
Experiment). One administrative note: arXiv's January 2026 endorsement
policy means an unaffiliated first-time arXiv author needs a personal
endorsement — a solvable, one-email matter given prior conventional
publications in the field.

## 10. Conclusion and open problems

PLL, read doxastically, is the minimal logic of one idealised evidential
believer; its belief is worth having only constructively; its evidence
semantics is forced into a unique shape by machine-checked obstructions;
and it is complete for that shape over finite, executable, explainable
models built by its own decision procedure.

**Open**: the K₁ instantiation of the table hypotheses via partial
computable functions (choice-free statement would need care around
`Part`); axiomatising PLLᵘ, the logic of rigid evidence; the exact
relation to IEL⁻; the tripos-level statement of the evidence semantics;
uniform interpolation for PLL (the repaired calculus gives the height
bound Iemhoff's method lacked; the mechanised probe continues); and the
axiom-audit drill to bring the entire chain to `[propext, Quot.sound]`.

---

*Appendix (planned): annotated walk-throughs in the style of
`docs/annotated/strong-normalisation.md` for (a) the truth lemma with its
three decided extensions, (b) adequacy/fullness for ⊩ᵖ, (c) the
obstruction. The Lean statements quoted in this draft are verbatim from
`LaxLogic/PLLEvidence.lean`, `LaxLogic/PLLFinComp.lean`,
`LaxLogic/PLLRealCompleteness.lean`, `LaxLogic/PLLCountermodelEmit.lean`
and `wip/belief_realisability.lean` at commit 32022fd.*
