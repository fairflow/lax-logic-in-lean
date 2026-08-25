# Adopting a calculus from the literature: the six-step method

*Written 2026-08-16 at Matthew's request, after the LJF◯ campaign
(succeeded) and the FRJ◯ campaign (failed at step 2, and the failure is
the most instructive thing in this document).  Standing method: this is
the route to take whenever a proof-theoretic capability is missing and
somebody has already built the calculus for it.  Companion to the
retrospective practice recorded in `HANDOFF.md`.*

The situation this addresses: **we need a proof-theoretic capability we
do not have, and inventing one from scratch has a poor track record
here.**  Two invented calculi were dropped (the labelled route, with its
unbounded fresh-label generation; and the Rauzer-style attempt), and the
one place we lifted a *paraphrase* of a published calculus rather than
the calculus itself produced an unsound rule table twice over.  The
literature is the cheaper source of correctness.

---

## The six steps

### 1. Search the literature for a calculus matching the requirement

State the requirement as a *capability*, not as a shape.  For the
disproof campaign the requirement was exactly one sentence:

> find a refutation calculus that yields a procedure for constructing
> countermodels directly from a possibly unprovable sequent.

Not "a rejection calculus", not "a dual sequent calculus" — those are
shapes, and committing to a shape early is what produced the labelled
dead end.  The capability admits several architectures, and the search
should report which ones exist.

Read the sources **at source**, and prefer the version with the most
detail: the journal version over the conference version, the LaTeX
source over the PDF where arXiv provides it (exact rule tables, exact
side conditions, no OCR loss, and the numbering is machine-greppable).
Record what was read in full and what was not.

**Deliverable:** a plan document naming the calculus, the papers, what
was read at source, and the architecture it commits us to.

### 2. Implement the calculus sorry-free

Transcribe the rules **clause by clause from the original text**,
filling genuine gaps and repairing genuine mistakes as they are found,
and recording each such intervention as an intervention.

Two failure modes, both observed:

* **Formalising from a paraphrase.**  FRJ◯'s rule table was derived from
  an in-repo summary of the source rather than from the source.  The
  resulting `world` rule corresponded to no published calculus, and was
  refuted twice (v2 read a bounded searcher, so budget failure admitted
  bad nodes; v3 constrained the stable zone only by membership in the
  universe, never by closure).  A summary written for orientation is not
  a specification.  *If the transcription cannot cite a line of the
  original for a rule, that rule is invented.*

* **A certificate format wearing the word "calculus".**  A plain tree
  plus an external validity checker is not a calculus: you cannot induct
  on it, and its soundness lives outside the data.  This anti-pattern
  was committed twice here (`Reject/`'s framing, then `FRJO/`'s `RT`/`wf`
  layer).  The test is mechanical — **is the judgment an indexed
  inductive family with one constructor per rule, whose indices are the
  sequent?**  If not, it is a certificate format.

**Deliverable:** the judgment as an indexed inductive family, side
conditions as decidable fields, compiling with zero sorries, plus a
fidelity table mapping every Lean definition to the numbered definition
it encodes.

### 3. Prove the existing results

Soundness and completeness are the essential pair, and for a refutation
calculus they do not look like the positive case:

* **soundness** is a *model construction* — a derivation yields a
  countermodel — and its corollary is the negative statement that the
  goal is unprovable;
* **completeness** starts *from* an arbitrary countermodel and builds a
  derivation, typically by induction on the height of the model.

Follow the published proofs. Where the paper offers two routes, choose on
cost and say why: FRJ(G)'s journal version derives completeness as a
corollary of duality with a second calculus plus a search procedure,
while its §6 (and the earlier conference version) proves it directly by
a construction on the countermodel. The direct route is a fraction of
the work and is equally published.

**The asymmetry that matters:** completeness against an over-permissive
rule table is nearly free, since extra rules only make it easier.  The
content of a refutation calculus is in soundness.  So **prove or screen
soundness first**; a completeness theorem obtained before soundness has
been screened is worth very little, which is precisely the position
FRJO/ ended in.

Apply the repo's standing counterexample mandate to the *statements*
before scoping their proofs (`CLAUDE.md`, "Testing for counterexamples").
Three certified cells refuted FRJ◯'s soundness statement in minutes;
that screen should have run before any of the proof effort, not after.

**Deliverable:** the two theorems, sorry-free, `#print axioms` pinned and
transcribed verbatim.  PROVED / REFUTED / OPEN kept rigidly distinct.

### 4. Extract efficient algorithms from the formal proofs

Formal proofs carry termination bounds chosen to make the *proof* easy,
and those bounds are routinely infeasible to run: the fuel in a
decidability theorem is there to satisfy the kernel, not the CPU.  The
executable procedure is a separate artefact, extracted from the proof's
content but not bound by its measures.

The precedent is the PLL decidability work: the decidability theorem's
own fuel bounds are unusable, so discovery runs on the certificate
engines instead, and `CLAUDE.md` rule 3 records the standing prohibition
on driving search through the theorem.

**Deliverable:** a searcher that runs, with its complexity understood,
kept separate from the theorem it was extracted from.

### 5. Provide a verification step for what the search discovers

The searcher is untrusted; its output is not.  Discover-then-pin: the
procedure proposes a proof or a countermodel, and a *verified* checker
accepts it, so that the kernel — not the searcher — is what stands behind
a claim.  This is what makes it legitimate to run an unverified,
efficient search and still report a machine-checked result.

**Deliverable:** a decidable checker with a soundness theorem, and worked
kernel exemplars that replay a discovered object by `decide` (never
`native_decide`, which taints the axiom set).

### 6. Test thoroughly on an existing corpus, then past its limits

Replay the corpus we already have before generating anything new: the
repo's hard instances carry content that random cells miss.  Then push
past it — the standing rule is that each round's residue shape defines
the next stratum.  Cross-check engines against each other where two
independent routes settle the same cells, and report conflicts as
findings.

**Deliverable:** corpus results with timings, a comparison against the
incumbent engine, and a named frontier.

---

## Where each campaign stands against this

| Step | LJF◯ (proof side) | FRJ◯ (disproof side) | FRJ for IPC (current) |
|---|---|---|---|
| 1 Literature | done — focusing, Liang–Miller | done — FRJ(G), RK(Ξ) read at source | done — TOCL 2020 full text, LaTeX source |
| 2 Implement | done, indexed inductive | **FAILED — paraphrase, unsound twice** | in progress |
| 3 Results | soundness + completeness PROVED; `bridge_iff` a genuine biconditional | completeness proved, soundness REFUTED | in progress |
| 4 Extract | done — `searchProves`, depth-fuelled | not reached | not reached |
| 5 Verify | done — two-sided engine, kernel-replayable | not reached | not reached |
| 6 Test | done — full 462-cell corpus, 0 conflicts | corpus screen only | not reached |

The current FRJ-for-IPC campaign exists because step 2 failed on the
modal lift, and the only way to know whether the base was ever right is
to do the base case faithfully, against the published proofs, with no
modality in sight.

## The one-line version

**Steps 1–3 buy correctness from the literature; steps 4–6 buy
performance back.  Doing them in the other order, or skipping the
original text at step 2, is how both failures here happened.**
