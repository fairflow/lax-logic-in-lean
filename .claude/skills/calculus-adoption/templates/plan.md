# Adoption plan: <CALCULUS>

*Stage 1 deliverable. Reviewable without opening any code. **No Lean until
Matthew has reviewed this.***

## The requirement

One sentence, naming a **capability**, not a shape. Committing to a shape
early is what produces dead ends.

> e.g. *find a refutation calculus that yields a procedure for
> constructing countermodels directly from a possibly unprovable sequent.*

## The candidates considered

| Calculus | Source | Why it does / does not fit |
|---|---|---|

State what was ruled out and why — the search is part of the record.

## The source

* Paper, venue, year, arXiv id.
* **Which file was read**, in full or in part. Prefer the arXiv LaTeX
  source over the PDF, and the journal version over the conference one.
* **Appendix**: present? read? what is in it?
* Does the paper prove the same theorem twice by different routes? Cost
  both; the shorter one is equally published.

## Kind of result

Which of `reference/result-kinds.md` applies, and the consequences for the
encoding.

## Scope

**In scope** (by section and label):

**Out of scope**, explicitly:

## Results to be reproduced

Generated: `paper_skeleton.py --arxiv <id> -o skeleton.md`. Paste or
reference the table. **Key every row on its `\label`.**

## Existing repo results consumed read-only

| Result | Where | Why it is safe to consume |
|---|---|---|

If the answer is *none*, say so and say why — it removes a whole class of
risk (a borrowed notion meaning something subtly different).

## Divergence log

Opened empty. A divergence is recorded **when it is made**.

| # | Paper item (label) | What the paper says | What is proved here | Why |
|---|---|---|---|---|

## Statement-level decisions reserved for Matthew

Anything that is a choice about *what is true*, not about how to prove it.
