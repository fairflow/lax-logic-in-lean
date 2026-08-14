# T1 handoff — the single prompt

*Paste the block below as the agent's opening message.  Recommended:
**Opus 5, effort high**.  Rationale in `docs/disproof-handoff.md` §3.*

---

You are continuing a machine-checked investigation in the Lean 4 repo
`lax-logic-in-lean` (PLL = Fairtlough–Mendler propositional lax logic).
Read these three files FIRST, in order, and follow their standing
rules: `CLAUDE.md` (repo root — especially § TESTING FOR
COUNTEREXAMPLES), `docs/disproof-handoff.md` (the dedicated handover
for this thread; your task is **T1**), and `docs/frj-lifting.md` (the
design, and the two screens that licensed it).

**Setup**: if you are in a fresh worktree it has no build cache — run
`cp -Rc <repo-root>/.lake .lake` (APFS clone, instant) before
building. Never delete any `.lake` directory: they are shared across
sessions. Build with `lake build Reject`.

## What exists

`Reject/` is a FORWARD, model-generating refutation calculus for PLL,
after Fiorentini–Ferrari's FRJ(G). Its principle: **rules ARE model
constructors, and each rule's soundness is a forcing lemma about the
construction.** A refutation is built forwards; nothing is searched
and nothing fails.

* `Reject/Build.lean` — `addRoot` (adds a root BELOW one model),
  `addRoot_force_some` (forcing unchanged above the new root — why
  this is the safe direction), `boxRefuteHere` (◯∈), `boxRefuteAbove`
  (◯∉), `boxHolds` + `boxHoldsRoot` (◯-positive), `solo`,
  `not_laxND_of_root`. The core lemmas are AXIOM-FREE.
* `Reject/Demo.lean`, `Reject/Audit.lean` — worked refutations and the
  adversarial pass. Read `Audit.lean` before you design anything.

## Your task: T1, the JOIN rule

Generalise `addRoot` from ONE premise model to SEVERAL: a fresh root
below the disjoint union of models `M₁ … Mₙ`, with the join declaring
which components are `Rm`-successors of the new root. Without it the
calculus can build only chains, which is why the demos are the
corpus's two smallest facts.

Deliver, in `Reject/Join.lean`:

1. **The constructor** — the model, satisfying every `ConstraintModel`
   law (`Rm ⊆ Ri`, both preorders, `F` hereditary, `V` hereditary and
   full on `F`). Expect a sum/sigma world type; keep the plumbing as
   simple as you can make it.
2. **The preservation lemma** — the analogue of `addRoot_force_some`:
   forcing is unchanged inside each component. This is the load-bearing
   lemma; get it right before anything else.
3. **The modal rules at a join** — `◯∈`/`◯∉` in the multi-premise
   setting, and the ◯-positive rule. Follow `boxRefuteHere_exact`'s
   discipline: state the premises so they are EXACTLY the semantic
   condition, and PROVE that equivalence.
4. **A worked composition** — a refutation that genuinely needs
   branching (a root with two incomparable successors), certified end
   to end via `not_laxND_of_root`. A `∨`-shaped or ⊃-shaped goal from
   `docs/pcll-closed-fragment-catalogue.md` is the natural target.
5. **`#print axioms` pins** on every result, transcribed VERBATIM from
   the build output (never guessed).

## The decision you must make explicitly, and record

The adversarial pass proved (`addRoot_not_confluent`, a machine-checked
counterexample) that **`addRoot` does NOT preserve mutual
confluence**. This matters: the licence for a UNARY ◯-refutation rule
holds on reduced AND confluent frames (`docs/frj-lifting.md` §3, an
exhaustive probe). A constructor that leaves the confluent class loses
that licence. So choose, state, and justify ONE of:

* **(a)** carry a confluence side condition on the join, staying in the
  class where the ◯-rule is unary — the PCLL-first route,
  RECOMMENDED; or
* **(b)** accept non-confluent constructions and give the ◯-rule its
  general list-of-premises form.

Do not drift into one. Record the choice and its reason in
`docs/disproof-handoff.md` as a dated section.

## Method (non-negotiable — repo doctrine)

* **Screen before you prove.** Every candidate rule gets an
  extensional attack BEFORE a proof is scoped: corpus replay first
  (the catalogue's classes, the G4iLL blocker), then boundary cells
  (empty component list, a single component — must degenerate to
  `addRoot`, a component with one world, an empty modal cone, a
  fallible component), then frontier extension, then branch coverage.
  Harnesses are COMPILED (`lean_exe`), never interpreted `#eval`, and
  stream one line per cell.
* **Check the degenerate case of every rule.** The audit found
  `boxHolds` incomplete precisely because the reflexive case was
  missed.
* **Normalise before you search.** Pipe every screen cell through
  `Rewrite.simplify Rewrite.fullSet fuel φ` (canonicalise, then
  rewrite by 324 kernel-checked rules) and report the shrink rate.
  Always sound — `Rewrite.simplify_interd` is unconditional. Use
  `simplify`, never `norm` alone: measured, canonicalising first takes
  the rewrite rate from 13% to 68%, and on nested ∧/∨ trees it
  collapses 3,996 distinct forms to 167. Bank any NEW certified `Interd` you prove
  into `Rewrite/`, so the next campaign is cheaper.
* **Three-valued verdicts**: pass / fail / flag, with `fail` only on a
  certificate and `flag` never dropped silently.
* **Claim discipline**: PROVED means sorry-free with a pinned
  `#print axioms`; everything else is OPEN or REFUTED, and the three
  are kept distinct. Do not overstate — a previous round of this very
  investigation was corrected for exactly that.

## Out of scope

Completeness (that is T2 — do not start it), the searcher (T3),
uniform interpolation (PARKED), and the `BiLax/` directory (retained
but inactive; `◯∃` is unused machinery).

## Report

A dated section appended to `docs/disproof-handoff.md`: what is
PROVED with its pins, the confluence decision and why, what the
screens found, and what T2 now inherits. Commit and push to the
current branch; do not open a PR.
