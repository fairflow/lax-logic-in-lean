# The why-chain: what today's local task is for

*2026-08-16, from Matthew's own recitation. A standing record of the goal
chain, top to bottom, so a future session can re-derive why a local task
exists. Each link is checked against the repo record; unconfirmed details
are marked as recollection.*

## Matthew's framing (verbatim, so it does not drift)

> "what is interesting is that the mid-range goal, so far unstated as it
> is complex and not easy to articulate exactly, is often lost in the
> local and immediate goals. A situation familiar to me from my days of
> manual formal verification (early days of Lego (Randy Pollack)): the
> wood is lost in the trees.
>
> Why were we pursuing the route of a discalculus? Because we wanted a
> more efficient countermodel search. Why did we want proper rules
> rather than partial procedures? So we humans can understand it and as
> this would help with efficient countermodel search. Why did we want
> efficient countermodel search? Because we were (a) trying to map out
> RN(◯,{}) which was stuck on 15 classes for multiple days and (b)
> getting stuck in the weeds with finding a proof of UI for PLL and
> checking out potential lemmas and places where the proof was stuck
> required testing whether the statements might be untrue. Why did we
> originally choose a presentation of PLL into Type? Because we wanted
> effective procedures. And so this would have been beneficial for FRJ
> too. Why did we not stop once we had proved PLL decidable? Because the
> decision procedure was proved correct by introducing complexity bounds
> that were effectively non-computable and they were not even needed to
> find proofs and countermodels. So this led to an effective (and
> verifiable!) proof procedure: but unfortunately a very inefficient
> disproof procedure via generate-and-test exhaustively generated
> countermodels. So...we ended up with FRJ(◯)."

## The chain, top down

**A. Certified disproof as cheap as certified proof (the mid-range
goal).** Under the machine-checked mandate a claim is PROVED, REFUTED or
OPEN, and REFUTED needs a kernel-checked countermodel. If one costs
orders of magnitude more than a proof, every campaign accumulates OPEN
cells it cannot afford to settle. *Nowhere stated as a goal in the
record. The closest is `docs/disproof-handoff.md` §1: a refutation should
be "a finite syntactic object, built forwards by rules, checkable by a
decidable rule-application predicate", so that "REFUTED is as cheap as
PROVED under the machine-checked mandate, and the 109 open flags of the
closed-fragment catalogue become attackable". Link A above is my
reconstruction from that sentence, not a quotation.*

**B1. Mapping RN(◯,{}) was blocked on the negative side.** CONFIRMED.
`PROGRESS.md` §43 (2026-07-26): fifteen variable-free representatives
certified pairwise distinct by 165 pinned countermodels, some separations
needing 5 or 6 worlds so the ≤4-world battery cannot see them;
`RN(◯,{}) ≥ 16` pinned; the 16-class closure round then failing
"massively", class count rising through every observed crank window.
`docs/rn-dictionary-status.md` names the four refuted cells
(`q8 ∧ q10`, `q9 ⊃ q4`, `q12 ⊃ q4`, `q14 ⊃ q4`);
`docs/pcll-picll-arc-report.md` records the 15-class closure
kernel-refuted with ≥ 25 classes certified and no plateau. *"Stuck on 15
classes for multiple days" is corroborated in substance, not as a
duration: the 15/16 count stands from 2026-07-26, and the computed
22-class order lands 2026-08-14.*

**B2. UI for PLL was blocked on testing statements.** CONFIRMED.
`HANDOFF.md` §10: the room-free route REFUTED at `Γ = []`, the surviving
room-carrying statement proved not decide-feasible, "so it cannot be
screened in either direction: it has to be built", hence shelved. Two
invariants were drawn from it: a false statement compiles the whole stack
and passes every axiom pin, because it is a `sorry`; and a clean screen
is a statement about the screen. That is Matthew's "testing whether the
statements might be untrue", now standing policy in `CLAUDE.md`
("Testing for counterexamples"). UI for PLL is OPEN.

**C. Efficient countermodel search** is the shared bottleneck. CONFIRMED:
`CLAUDE.md` rule 3 records the two-sided engine settling the closed
corpus about 10³ times cheaper than the G4c oracle, with
kernel-`decide`-checkable certificates.

**D. Rules, not partial procedures.** CONFIRMED, with the diagnostic:
`docs/calculus-formalisation-method.md` step 2 gives the mechanical test,
is the judgment an indexed inductive family with one constructor per
rule, whose indices are the sequent? If not it is a certificate format,
"you cannot induct on it, and its soundness lives outside the data". The
anti-pattern was committed twice (`Reject/`'s framing, then `FRJO/`'s
`RT`/`wf` layer) and corrected in `470171a` and `3e1f59a`. This is the
link Matthew calls the discalculus route (standard term: refutation
calculus).

**E. Take the calculus from the literature.** CONFIRMED. Commit `13edb70`
(2026-08-13): Skura is not the template (non-analytic, model search
hidden in a side condition), no refutation calculus exists for any
intuitionistic modal logic, the right template is Fiorentini–Ferrari's
FRJ(G) plus their RS4 method. Two invented calculi had already been
dropped.

**F. FRJ◯ was built before FRJ, and its soundness is REFUTED.**
CONFIRMED with dates. `FRJO/` starts `8a01cf8` (2026-08-15 23:00); the
base `FRJ/` starts `0045773` (2026-08-16 12:24). Between them, `4730e30`:
"ExtractForces (W3b) is REFUTED for worldOK v3 — three certified cells",
and `bdb46bd`: "Reconstruction PROVED, ExtractForces REFUTED, v4
specified". v2 was refuted too, its goal conjunct reading a bounded
searcher so budget failure admitted bad nodes.

**G. Today: FRJ(G) for IPC alone, faithfully.** CONFIRMED.
`docs/frj-fidelity.md`: source is the arXiv LaTeX of arXiv:1804.06689
(`frj-corr.tex`), not the in-repo paraphrase `docs/frj-lifting.md`, which
is what produced the unsound FRJ◯ table. Soundness and completeness both
proved, sorry-free, with `frj_iff_not_IPL`.

## The prior spine

**P1. PLL judgments live in `Type`.** The fact is confirmed:
`inductive LaxND : List PLLFormula → PLLFormula → Type`
(`LaxLogic/PLLNDCore.lean:72`), `Deriv Γ φ := Nonempty (LaxND Γ φ)`, and
`G4cTm` a Type-valued proof-term calculus. *The motive ("we wanted
effective procedures") is not recorded; `PLLNDCore.lean`'s header gives a
different rationale, no green slime and cast-freedom. Recollection.* That
it would help FRJ is directly corroborated: `docs/frj-fidelity.md` says
the last choice-elimination step needs the completeness construction
Type-valued, "so the proof must return derivations rather than assert
their existence — and it is also the step that turns completeness into an
actual algorithm from countermodel to derivation".

**P2. Decidability was proved, and its bounds are not runnable.**
CONFIRMED as policy: `CLAUDE.md` rule 3, never drive discovery through
`decideFuel`, "its fuel bounds are infeasible and it will hang".
*Which specific bounds are the culprit is itemised nowhere I found.
Recollection as to "effectively non-computable".*

**P3. Hence certificate engines: proof cheap, disproof expensive.**
CONFIRMED. The searcher returns `.proved` / `.refuted` / `.unknown`, the
refutation a `FinCM` checked by `checkB`, default battery eleven frames
of ≤ 4 worlds. Genuine separations needing five or six worlds fall
outside it, so the fallback is exhaustive generation.

## What this chain implies for the next decision

**PROVED** (sorry-free, kernel-checked): PLL decidability via the
repaired G4iLL″; `G4c`'s cut, contraction, completeness and equivalence
with `SC`, `LaxND`, `Tm`; focalization for PLL (`bridge_iff`, `[propext,
Quot.sound]`); the two-sided engine reproducing the settled matrix
158/158 and 302/302 with zero conflicts; and on `frj-ipc`, FRJ(G)'s
soundness, completeness and `frj_iff_not_IPL`. One qualification on the
last: `FRJ/` has zero `sorry` and zero in-file `#print axioms` pins, so
the pins are still owed under the repo's mandate; the audit is written up
in `docs/frj-fidelity.md`, and choice-freedom is verified so far only for
`Basic`, `Calculus`, `Step`, `Model` on branch `frj-choicefree`.

**REFUTED** (kernel-checked countermodels): Iemhoff's G4iLL as complete
for PLL; FRJ◯ soundness at both worldOK v2 and v3 (three certified cells
for v3; v4 specified, not built); the 15-class closure of the
variable-free fragment; the room-free UI route.

**OPEN**: uniform interpolation for PLL; `CimpAnt`; FRJ◯ soundness at v4;
choice-free FRJ for `Sound`, `Complete`, `Minimal`; the exact structure
of RN(◯,{}), with 109 flags unsettled in the PCLL catalogue.

No recommendation on FRJ/FRJ◯ is offered: Matthew has said he will state
his own proposal.

## The general observation

The mid-range goal is the link that goes unrecorded, for a structural
reason rather than through carelessness: it is the only link that is not
a task. Local goals are easy to write down because they have a definition
of done, a file and a commit message; the mid-range goal has none of
these, is expensive to state precisely, and changes shape as the campaign
learns. So the record fills with trees. The cost is not confusion about
what is being done but loss of the criterion for whether it should be
done at all: without link A, links D to G are unfalsifiable as choices.
This is the hazard Matthew names from the early Lego days with Randy
Pollack; the countermeasure is this document, refreshed whenever a link
is added at the bottom.
