# Away-run report — 29 July to 2 August 2026

Matthew is away until Sunday 2 August, 12:00 BST, and asked for continuous
work with no check-ins.  This file is the running record: **plan, running
results, and the resume pointer** if the run is cut short.  It is written to
be read by someone who was not present.

Latest revision: see the dated sections; newest last.

---

## 0. Where the work is

Two live threads, in two worktrees of `lax-logic-in-lean`:

| thread | worktree | branch | subject |
|---|---|---|---|
| **syntactic** | `.claude/worktrees/agent-a6d28ed6d9d9b868d` | `ui-confluence` | uniform interpolation for **plain PLL** via the truncated quantifier tables |
| **semantic** | `LaxLogic/.claude/worktrees/agitated-nobel-443fbd` | `claude/ui-proof-status-8a40d5` | the layered-bisimulation / amalgamation route |

The syntactic thread is the main line.  It is about **plain PLL** (`G4c`),
not PCLL.  PCLL, PILL and PICLL enter only as *scope*: refuting models that
are mutually confluent and infallible refute those systems too, so an
obstruction exhibited by such a model is not an artefact of plain PLL.

## 1. Vocabulary

Every term used below, in standard language.

* **quantifier tables.**  `itpE p S fuel b Γ` and `itpA p S fuel b Γ C`
  (`LaxLogic/PLLG4UITrunc.lean`) are formulas built by recursion on `Γ`;
  they are the candidate uniform interpolants.  `itpE` is a conjunction of
  clauses (`andAll`), `itpA` a disjunction (`orAll`).  `p` is the variable
  being eliminated, `S` a finite set of formulas closed under immediate
  subformulas ("piece-closed"), `Γ` the context.
* **fuel** `fuel` — the recursion bound on context growth.
* **budget** `b` — a *second* recursion bound, read at exactly two clause
  shapes: a context formula `(A⊃B)⊃D` and a context formula `◯A⊃B`.  Each
  of those clauses is deleted when `b = 0` and otherwise produces a
  component at `b−1`.  These are the **budget-gated** clauses.
* **starved.**  A state `(Γ, C, b)` is starved when the clause list of
  `itpA` is empty, so the table is *literally* `⊥` (`orAll [] = ⊥`).
* **defect** `defect S Γ = |S ∖ Γ|` — how much of the space is not yet in
  the context.  Context growth strictly decreases it.
* **jump goals** `jumpGoals S` — the goals a budget-gated clause can put in
  first-component position: `A⊃B` from `(A⊃B)⊃D ∈ S`, and `A`, `◯A` from
  `◯A⊃B ∈ S`.
* **the descent.**  The statement

      Δ ⊢ itpE p S fuel (c+1) Γ ,  Δ ⊢ itpA p S fh (c+1) Γ g
      ──────────────────────────────────────────────────────
      Δ ⊢ itpA p S fuel c Γ g                    (fh ≤ fuel)

  i.e. lowering the budget by one is harmless, financed by the existential
  table at the higher budget.  Lower budget means fewer disjuncts, hence a
  *stronger* formula, so the descent is a stabilisation statement.
* **room requirement** `need : Finset PLLFormula → List PLLFormula →
  PLLFormula → Nat` — the budget the descent needs at a configuration.
  `Descends p need` (`wip/descent2.lean`) is the descent with `need S Γ g ≤ c`
  as its budget hypothesis.  It is a *parameter*: three fixed budget laws
  were refuted in July, so the law is now solved for rather than guessed.

## 2. Status at the start of the run (29 July, 22:00 BST)

PROVED, sorry-free and axiom-pinned:

* `descends_of_othDescends` — the descent follows from the others-descent
  for any `need` with a floor of one (`wip/descent2.lean`).
* `not_ambGuardAscent`, `not_roomFreeDescent` — two of the four interfaces
  `wip/cascadeBox.lean` reduces to are false; both refuting models are
  mutually confluent and infallible, so the refutations reach PCLL, PILL
  and PICLL (`wip/ascRefute.lean`).
* `refutation_lower_bound` — every workable `need` asks ≥ 2 at the
  refuting configuration.

OPEN: `cascade_low_pos_box` (`wip/absorb_base.lean`) — the tower's only
`sorry`, and the last thing between the repo and `uniform_interpolation_PLL`.

## 3. Plan as of 29 July 22:00

**Phase A** — bracket the budget law from above, and settle whether the
`cascadeBox` architecture can be repaired at all.
**Phase B** — the branch-by-branch rebuild, countermodel search *before*
every proof attempt.
**Phase C** — solve the accumulated laws, wire into the tower.
**Phase D** — audit, scope transfer to PCLL/PILL/PICLL, then the semantic
thread.

Stall rule: no branch gets more than about four hours without movement.

---

## 4. Result 1 (30 July, ~00:00) — the budget tier has no base case

`wip/floorRefute.lean`, PROVED sorry-free, `[propext, Quot.sound]`.

**`not_floorDescent`: the descent at target budget `0` is FALSE.**  At

    S = {◯(⊥⊃⊥), ⊥⊃⊥, ⊥},   Γ = [],   g = ◯(⊥⊃⊥) ∈ S

the target table is *literally* `⊥` — at the empty context the environment
table is empty, and at budget `0` both the `◯`-goal clause and the
truncation disjunct are budget-gated away (`itpA_starve_floor`, already in
`wip/starve.lean`).  The source table at budget `1` is satisfiable.  So the
descent would derive `⊥` from consistent hypotheses.  **No countermodel
search was needed**: the only semantic input is that the two hypotheses are
jointly consistent, checked in the one-world model.

**Why this reshapes the plan.**  `wip/cascadeBox.lean`'s `oth_descent` is a
three-tier induction: strong induction on the defect, then strong induction
on the budget `c` (carrying `1 ≤ c`), then structural induction on the
source fuel.  Its three "floor" interfaces exist because the middle tier has
no recursive call at `c = 1`: a budget-gated clause of the *target* table at
budget `c` puts its first component at `c−1`, so that branch needs the
descent at `(c → c−1)`, and at `c = 1` that is the descent to budget `0`.

Now both of the bottom two rungs are refuted:

* target budget `0` — false (this result);
* target budget `1` — false (`wip/ascRefute.lean` §2).

So **raising the floor does not give the budget tier a base case.**  A floor
at `n` needs the descent at `n−1`; `n = 1` and `n = 2` are both closed off
by countermodel, and there is no reason to expect `n = 3` to behave
differently, because the obstruction is the *shape* of the gated clause and
not the numeral.  The recursion has to terminate on some other measure:
context growth (defect), or the pigeonhole over `jumpGoals S` that
`wip/absorb_base.lean`'s `cascade_main` already implements.

**Consequence for the rebuild.**  `oth_descent`'s architecture is not
repairable by choosing a better constant.  The parametrised `Descends need`
statement stands (it is the target either way), but the *proof* must come
from the defect/pigeonhole side, not the budget side.

**A second lower bound on `need`, and candidate B dead twice over.**  The
same configuration is an instance of `Descends` at target budget `0`, so it
forces `1 ≤ need S [] g` at a space whose **gated-piece count is zero**.
The gate-count candidate `needGate` asks for `0` there, so it is refuted by
data (`needGate_excluded`), not only by the proof obligation
`NeedFloor1` (`needGate_not_floor1`).  The earlier elimination used the
empty space and could be dismissed as degenerate; this space is piece-closed
with a genuine `◯`-goal.

**Resume here:** the next step is *not* to continue rebuilding
`wip/cascadeBox.lean`.  It is to build the starvation classification that
`cascade_low_pos_box`'s own failure analysis names as step one — which
`(Γ, g, b)` starve — and from it a `(defect, budget)`-lexicographic landing
map for the residue.  `wip/starve.lean` has the first four bricks.

---

## 5. Result 2 (30 July, ~01:00) — completeness is available, and does not shortcut this

Worth recording so a later session does not spend days on it.

`LaxLogic/PLLCompleteness.lean` proves `consequence_iff_derivable : Γ ⊨- φ ↔
Nonempty (LaxND Γ φ)` — full soundness **and** completeness for the
Fairtlough–Mendler constraint semantics, sorry-free, over `Γ` a list.  With
`G4c.equiv_nd` this means *any* sequent about the quantifier tables could in
principle be proved semantically instead of by building a derivation.  That
is attractive because the descent's known obstruction is a proof-engineering
one (continuations cannot cross a `◯`-introduction), and semantics has no
continuations.

It does not work, for a reason worth stating.  Semantically, the descent says
a monotone iteration has reached its fixed point by step `c`.  The iteration
is over *hereditary* sets of worlds, and the recursive references in the
tables sit under `⊃` and `◯`, so they are evaluated at other worlds: the
state is a function on worlds, not a finite vector, and a monotone iteration
in that lattice has no finite bound.  The syntactic pigeonhole works because
it counts *goals* visited in a derivation, and goals live in the finite set
`jumpGoals S`.  So completeness is a genuine escape hatch for individual
sequents but not for the general statement.

## 6. Result 3 (30 July, ~02:00) — the boundary does not climb; one statement left

Full detail in PROGRESS §84.  Headline: `wip/ascprobe.lean` measures the
*ambient-relative existential ascent* (never probed before) at every position
along `◯`-gated chains of length 2, 3, 4, and the descent at *jump goals*.
Every `checkB`-certified failure is at budget `0` or `1`; there is not one
certified failure at budget `≥ 2` anywhere, up to four live gates and defect
15.  The assumed product law would predict boundaries 63, 108, 165 for those
three chains; the measurement is flat.  So the room requirement is not a size
measure.

Also landed: `needKcap`, the **ledger law** — exactly what the tower's entry
condition `kcap S < c + 2` pays, with `kcap_room` reproved locally — and

    ledgerDescent_of_othDescends : OthDescends p needKcap → LedgerDescent p S

where `LedgerDescent` is `cascade_low_pos_box`'s statement.  The tower's
holdout is now **one named proposition**.

## 7. Result 4 (30 July, ~03:00) — the goal side closes; the residue is two branches

Full detail in PROGRESS §85.

An exhaustive transcription of the clause tables gives a structural fact:
**every budget-decrementing reference sits at the same context, and every
context-growing reference sits at the same budget.**  So the recursion is
well-founded on the lexicographic pair `(defect, budget)` with no pigeonhole
at all — the seen-set machinery of `cascade_main` is there to avoid the
*false* budget-`0` base case, not to make the recursion stop.  And the budget
tier is entered only at **jump goals**, one step at a time.

`wip/goalDesc.lean` then settles the goal side: six of the seven goal
families close, because a budget-gated *goal* clause demotes only its
existential component, and the ambient supplies that free by downward
monotonicity.  No goal branch ever touches budget `0`.  The seventh — the
fresh antecedent — needs the ascent, isolated as `FreshAntAscent`.

Consequently the entire low-budget difficulty lives in the **environment**
clauses, and precisely two branches remain, both at target budget `1`:

1. the γ-clause's **boxed** disjunct, which would need the descent to budget
   `0` at a boxed goal — certified false as a plain statement, so it must be
   routed through a different target disjunct;
2. the **fresh-antecedent ascent at budget `1`** — refuted, so that branch
   needs its own floor treatment.

The other two of `oth_descent`'s four interfaces now look reachable: the atom
jump goal at budget `0` is *proved by search* (`wip/jumpprobe.lean`, at
`findBudget` up to 200 000, for chain2 and chain3), and the `⊃` case is open
but unrefuted.

Also: the floor law `NeedFloor1` was too strong.  It is used only for the
truncation disjunct, which exists only at `◯`-goals, so
`GoalDesc.desc_of_oth_nonbox` weakens it to `NeedBoxFloor1` — a floor at
boxed goals only.  That is what admits `needShape`, the goal-shape law the
measurement points to (`0` at atoms, `1` at boxed goals, `2` elsewhere),
which survives both certified lower bounds exactly.

**Resume here:** `wip/sealprobe.lean` hands the two blocked branch
obligations to the two-sided oracle as ordinary sequents (with the defect
tier's contribution pre-applied), for chain2 and chain3 and four goal shapes.
A `PROVED` there is a blueprint for the Lean proof; a `REFUTED!` says the
interface is individually false and the branch needs the full recursive
hypothesis rather than the pre-applied form.  Output goes to
`wip/sealprobe_out.txt`.

## 8. Result 5 (30 July, ~06:00) — no uniform route closes the last branch

Full detail in PROGRESS §87; the standing technical statement is
`docs/descent-problem.md`.

§86 reduced the descent to one branch at one budget: the **boxed γ-disjunct of
the environment table at target budget 1**.  At that point the target table
offers exactly three kinds of disjunct, and the branch's third hypothesis is
already the second conjunct of two of them, so the branch closes iff one of

    (a)  A@0(Γ, A)                      (b)  ◯( E@0(Γ) ⇢ A@0(Γ, ◯A) )
    (c)  the goal clause of C

is derivable from the three hypotheses.  That is a finite question about three
*small* sequents rather than one large one — and the oracle answers it.

**All three are individually false** (`wip/sealRefute.lean`, sorry-free), at a
configuration whose γ-head is an ordinary atom rather than the eliminated
variable, with both refuting models **infallible and mutually confluent** — so
the refutations reach PCLL, PILL and PICLL:

    not_route_a ,  not_route_b ,  not_route_bot
    not_uniformRouteA ,  not_uniformRouteB

So the branch **cannot be closed by a uniform route; it needs a case analysis
over the target's disjuncts.**  This is the explanation of the July record:
every mechanism surveyed there — remap, seal-crossing, collapse — is a uniform
route, and each therefore had to fail.  It also explains why no countermodel to
the branch obligation *itself* has been found in any probed configuration: in
each of the three refuting models a **different** route succeeds, so the
obligation is plausibly true while every one-move proof of it is impossible.

One caveat, stated because it bounds the result: the three hypotheses used are
the ambient, the source's boxed component, and the defect tier's contribution
*pre-applied* as `A@1(B::Γ,C)`.  The real interface hands over the recursive
hypothesis rather than one instance of it.  The enumeration of *which target
disjunct* is complete either way (it is read off the clause table); what the
pre-applied form bounds is the *material* available to reach it.

## 9. Where the whole problem now stands

Combining the run's measurements, the financing of the descent's recursion is
complete except at one point:

| what the recursion needs | budget | status |
|---|---|---|
| goal-side branches | any | **proved** (`wip/goalDesc.lean`), never reach budget 0 |
| the three gated environment first components | target ≥ 2 | **proved** (`wip/envDesc.lean`) |
| descent at **atom** jump goals | 0 | **proved by search** (`wip/jumpprobe.lean`) |
| descent at **`⊃`-shaped** jump goals | 0 | **proved by search** (chainII1) |
| descent at **boxed** jump goals | 0 | **certified false** |
| the ∃-ascent at a fresh antecedent | ≥ 2 | no certified failure in any probed configuration |
| the ∃-ascent at a fresh antecedent | 1 | **certified false** |

So **everything reduces to budget-1 phenomena**, and exactly two branches
remain there: the boxed γ-disjunct (uniform routes all refuted, obligation
plausibly true) and the fresh-antecedent ascent (refuted in its uniform form).

That is a considerably sharper position than the run began in, where the
statement of record was "four jointly unsatisfiable interfaces" with no
localisation and a budget law that had been guessed three times and refuted
three times.

**Resume here:** two options, in order of expected value.
1. Prove the ∃-ascent at budget `≥ 2`, conditional on the jump-goal descents.
   That would let the descent be assembled above budget 1, making "budget 1 is
   the entire residue" a theorem rather than an analysis.  Mechanical but
   large: the existential clause table has eleven shapes, of which nine are
   ungated and reduce to the defect tier.
2. Build the case analysis for the boxed γ-branch at budget 1.  The three
   refuting models of `wip/sealRefute.lean` say what the cases must
   distinguish; turning that into a *decidable syntactic* case split is the
   open problem.
