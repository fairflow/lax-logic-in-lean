# Paper skeleton: "Mechanising is not extending"

*One-page plan for the paper version of `docs/llm-formalisation-case-study.md`.
Working title: "Mechanising is not extending: a case study in LLM-assisted
formalisation, and the testing theory it needs".*

## Thesis

Mechanising known mathematics and extending it are different activities with
different failure modes. Mechanisation succeeds because the statement is given
and the kernel is a complete oracle for the only thing at risk. Extension fails
because the statement is the artefact at risk and there is no oracle for it. The
substitute is a testing discipline over statements, and software testing theory
already supplies it.

## Structure (12 pages, ITP/CPP format)

| § | content | pp. |
|---|---|---|
| 1 | Introduction: the campaign in one page; the thesis; contributions | 1 |
| 2 | Setting: PLL, uniform interpolation, the machine-checked mandate, the human/model configuration | 1 |
| 3 | The measurement: where the `sorry`s are. 5 in 50 kLOC of mechanised known mathematics, all in the extension line; 1 load-bearing in the extension's kernel; five refuted routes, none in mechanisation | 1 |
| 4 | The nine rounds, as a table, and round 9 as the pivot | 1.5 |
| 5 | Why extension goes off track: four mechanical causes, of which "a `sorry` lets a false statement pass every automated gate" is the sharpest | 1 |
| 6 | The statement-hygiene ledger: eight rules, each with the incident that bought it; the observation that all eight are checks a machine could run | 1.5 |
| 7 | **The testing-theory gap** (core technical section): anatomy of the round-9 3-way interaction fault; the mapping to boundary-value analysis, category-partition, t-way covering arrays, metamorphic relations, statement mutation, definition-clause coverage, fault seeding, shrinking; the screen-power principle | 2.5 |
| 8 | Tooling: ten requirements for a proof-engineering test layer; what Plausible and the constrained-generation line already give; what is absent | 1 |
| 9 | The human-in-the-loop record: interventions that changed outcomes; where self-direction drifted; the unsupervised-run experiment; the vocabulary cost | 1.5 |
| 10 | Threats to validity; related work; conclusion | 1 |

The Montague/formal-semantics material is **not** in this paper. It becomes a
separate two-page position piece.

## Claimed contributions

1. A measured account of the mechanise/extend asymmetry in one substantial Lean 4
   development, with the `sorry` distribution as the primary evidence.
2. Eight transferable statement-hygiene rules, each traceable to a specific wasted
   build.
3. The identification of statement testing as the missing discipline, with a
   concrete mapping from software testing theory to proof engineering, anchored in
   a documented 3-way interaction fault that a purpose-built property-based
   harness missed nine times.
4. A requirements list for a proof-engineering test layer, with a survey of what
   the Lean ecosystem currently provides.
5. A human-guidance record usable by practitioners who were not present.

## Evidence that must be added before submission

- **Prospective counterfactual** (highest value, lowest cost): re-specify the
  round-4 screen with boundary and 3-way discipline, without knowledge of the
  round-9 witness, and measure whether it finds the refutation.
- **Mutant-kill matrix** for the round-4 statement under the round-4 screen.
- **A second, smaller case** run with the rules in place from the start.
- Complete cost accounting (coordinator tokens, human hours).
- Consent and quotation policy for the transcript; decision on model attribution.
- Independent verification of the ecosystem survey's citations.

## Target venues

| rank | venue | form | rationale |
|---|---|---|---|
| 1 | **ITP** | experience report / rough diamond | best audience for the whole argument; established tolerance for negative-result method papers |
| 2 | **CPP** | experience report | same audience, known submission logistics for this author |
| 3 | **TAP** (Tests and Proofs) | full paper, §7 + §8 only | the venue that exists for exactly this interface; would want the mutant-kill data |
| 4 | **AITP** | extended abstract | fastest route to circulation for §6 and §9 |
| 5 | **ICST** practice track | full paper, §7 + §8 | testing theory applied to a new domain; needs the counterfactual experiment |
| 6 | **JAR** | journal version | after 1 and 3, with the second case added |

Companion position piece (2 pages, separate venue, e.g. an AI-for-mathematics or
computational-semantics workshop): *formal semantics in the Montague tradition as
the next target for LLM + prover + human guide + testing tools*, arguing that its
native entailment-judgement corpus supplies the oracle whose absence is this
case study's central finding.

## Non-goals

- No claim of mathematical progress on uniform interpolation for PLL. It is OPEN,
  and was OPEN before and after.
- No claim that the method rules are validated. They are derived from one case and
  are offered as hypotheses with their provenance attached.
- No general claim about LLM capability. One model family, one problem, no control.
