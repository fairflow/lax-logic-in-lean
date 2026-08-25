# T1 handoff — the single prompt

*Everything between the two rules below is the agent's opening
message. Copy it whole; it is self-contained. Recommended: **Opus 5,
effort high** — rationale in `docs/disproof-handoff.md` §3.*

*Last revised 2026-08-14 (adds the repaired normalisation pipeline and
the dictionary's true status; supersedes the version that named
`Rewrite.simplify`/`fullSet`).*

---

You are continuing a machine-checked investigation in the Lean 4 repo
`lax-logic-in-lean` (PLL = Fairtlough–Mendler propositional lax logic:
intuitionistic propositional logic with a modality `◯` whose Kripke
clause is `∀∃` — `w ⊩ ◯φ` iff every `Ri`-successor of `w` has an
`Rm`-successor forcing `φ`). Work on the current branch; do not open
a PR.

Read these FIRST, in order, and follow their standing rules:

* `CLAUDE.md` (repo root) — especially **§ Testing for counterexamples**;
* `docs/disproof-handoff.md` — the dedicated handover for this thread.
  **Your task is T1.**
* `docs/frj-lifting.md` — the design, and the two screens that
  licensed it;
* `docs/rn-dictionary-status.md` — what the certified simpset is, what
  it is not, and the two defects that were found in it. Read this
  before you use the normaliser or trust a null result from it.

**Setup.** A fresh worktree has no build cache: run
`cp -Rc <repo-root>/.lake .lake` (APFS clone, instant) before
building. **Never delete any `.lake` directory** — they are shared
across sessions. Build with `lake build Reject`.

## What exists

`Reject/` is a FORWARD, model-generating refutation calculus for PLL,
after Fiorentini–Ferrari's FRJ(G) (JLC 2021, the S4 model-generation
calculus). Its principle: **rules ARE model constructors, and each
rule's soundness is a forcing lemma about the construction.** A
refutation is built forwards; nothing is searched and nothing fails.
This is what dissolved the `∀∃` obstacle — "all `Rm`-successors" is a
construction-time side condition, because the model is the
derivation's own product.

* `Reject/Build.lean` — `addRoot` (adds a root BELOW one model),
  `addRoot_force_some` (forcing is unchanged above the new root — why
  this is the safe direction, unlike the refuted `addTop`),
  `boxRefuteHere` (◯∈), `boxRefuteAbove` (◯∉), `boxHolds` and
  `boxHoldsRoot` (the ◯-positive rule), `solo`, `not_laxND_of_root`.
  The core lemmas are AXIOM-FREE.
* `Reject/Demo.lean` — `⊬ ¬◯⊥` and `⊬ ◯p` as construction terms.
* `Reject/Audit.lean` — the adversarial pass. **Read this before you
  design anything**; it is where `addRoot_not_confluent` lives.

## Your task: T1, the JOIN rule

Generalise `addRoot` from ONE premise model to SEVERAL: a fresh root
below the disjoint union of models `M₁ … Mₙ`, with the join declaring
which components are `Rm`-successors of the new root. Without it the
calculus builds only chains, which is why the demos are the corpus's
two smallest facts.

Deliver, in `Reject/Join.lean`:

1. **The constructor** — the model, satisfying every `ConstraintModel`
   law (`Rm ⊆ Ri`; both relations preorders; `F` hereditary; `V`
   hereditary and full on `F`). Expect a sum/sigma world type; keep
   the plumbing as simple as you can make it.
2. **The preservation lemma** — the analogue of `addRoot_force_some`:
   forcing is unchanged inside each component. This is the
   load-bearing lemma; get it right before anything else.
3. **The modal rules at a join** — `◯∈`/`◯∉` in the multi-premise
   setting, and the ◯-positive rule. Follow `boxRefuteHere_exact`'s
   discipline: state the premises so they are EXACTLY the semantic
   condition, and PROVE that equivalence.
4. **A worked composition** — a refutation that genuinely needs
   branching (a root with two incomparable successors), certified end
   to end via `not_laxND_of_root`. A `∨`-shaped or `⊃`-shaped goal
   from `docs/pcll-closed-fragment-catalogue.md` is the natural
   target.
5. **`#print axioms` pins** on every result, transcribed VERBATIM from
   the build output — never guessed, never edited by hand.

## The decision you must make explicitly, and record

The adversarial pass proved (`addRoot_not_confluent`, a machine-checked
counterexample) that **`addRoot` does NOT preserve mutual
confluence**. This matters: the licence for a UNARY ◯-refutation rule
holds on reduced AND confluent frames (`docs/frj-lifting.md` §3, an
exhaustive probe — 100% at n = 3, 52,800 worlds), whereas in full PLL
the rule's arity grows with frame size. A constructor that leaves the
confluent class loses that licence. So choose, state, and justify ONE:

* **(a)** carry a confluence side condition on the join, staying in
  the class where the ◯-rule is unary — the PCLL-first route,
  **RECOMMENDED**; or
* **(b)** accept non-confluent constructions and give the ◯-rule its
  general list-of-premises form.

Do not drift into one. Record the choice and its reason in
`docs/disproof-handoff.md` as a dated section.

## Method (non-negotiable — repo doctrine)

* **Screen before you prove.** Every candidate rule gets an
  extensional attack BEFORE a proof is scoped, in this order: corpus
  replay (the catalogue's classes; the G4iLL blocker
  `◯((◯p→r)→◯p), ◯p→r ⇒ r`), then boundary cells (empty component
  list; a single component — which must degenerate to `addRoot`; a
  one-world component; an empty modal cone; a fallible component),
  then frontier extension (one step past every passing stratum), then
  branch coverage (every match arm of the definition exercised).
* **Check the degenerate case of every rule.** The audit found
  `boxHolds` incomplete precisely because the reflexive case was
  missed.
* **Normalise before you search.** Pipe every screen cell through

      Rewrite.simplifyWith Rewrite.fullSetC fuel φ

  — canonicalise, then alternate rewriting by the 237 kernel-checked
  rules with re-canonicalising, to a fixpoint. Always sound:
  `Rewrite.simplifyWith_interd` is unconditional. **Use `simplifyWith`
  against `fullSetC`**, not `simplify` and not `fullSet`: the rules
  must be canonicalised too, or the canonicaliser sorts goals out of
  their reach. Measured: the pipeline rewrites 89% of flat cells for a
  34% crank cut, and collapses 3,996 nested ∧/∨ trees to 25 distinct
  forms. Report the shrink rate you get.
* **Bank what you prove, then re-run the loop.** Any NEW certified
  `Interd` goes into `Rewrite/`; banking is finished only after
  `lean_exe rwscreen` and `lean_exe rnextend` have been re-run and the
  axiom pins re-transcribed. **Never harvest an unproved cell** —
  `wip/rnDict.lean` has 87 `sorry`ed cells of which four are REFUTED,
  and taking them by name is what tainted the first simpset.
* **Harnesses are COMPILED** (a `lean_exe`), never interpreted
  `#eval`, and stream one appended line per cell so a killed run loses
  nothing.
* **Three-valued verdicts**: `pass` / `fail` / `flag`, with `fail`
  only ever on a certificate and `flag` never dropped silently.
* **Controls on null results.** A screen that finds nothing must carry
  a control proving the pipeline fires on cells it provably should,
  and an adversarial check that it does NOT "settle" something known
  false. `wip/rn_extend.lean` is the worked pattern — its 0-of-87
  null result is only trustworthy because the control reads 237/237
  in the same run.
* **Claim discipline**: PROVED means sorry-free with a pinned
  `#print axioms`; everything else is OPEN or REFUTED, and the three
  are kept distinct. Do not overstate — an earlier round of this very
  investigation was corrected for exactly that.

## Out of scope

Completeness (that is T2 — do not start it), the searcher (T3), the
109 catalogue flags (T4), uniform interpolation (PARKED by Matthew's
decision), and the `BiLax/` directory (retained but inactive; `◯∃` is
unused machinery).

## Report

A dated section appended to `docs/disproof-handoff.md`: what is PROVED
with its pins, the confluence decision and why, what the screens
found, and what T2 now inherits. Commit and push to the current
branch; do not open a PR.
