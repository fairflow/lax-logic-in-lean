# <CALCULUS> — fidelity record

*The deliverable that makes the formalisation checkable against the
original: every Lean definition and theorem listed against the numbered
item it encodes, and every divergence recorded as a divergence.*

Source: <paper>, read from <file>. **Numbering note:** say which version's
numbers are cited, since a paper's arXiv source and its journal version
generally differ; labels are the stable key.

## Scope

In scope / out of scope.

## Mapping

| Paper item (label) | Lean name | Status |
|---|---|---|

Status is exactly one of:

* **PROVED** — sorry-free, with a pinned `#print axioms`
* **REFUTED** — kernel-checked countermodel
* **OPEN** — anything carrying a `sorry`, or unattempted
* *out of scope*

Kept rigidly distinct. A statement carrying a `sorry` is OPEN however
convincing it looks.

## Divergences

Numbered, each citing the paper item by label, saying what the paper
states, what is proved here instead, and why. Two kinds occur and should
be distinguished:

* the paper is **wrong or over-stated** — prove the directions actually
  used, and say so;
* the paper is **under-specified** — say how it was specified, and that
  the choice was ours.

## Axioms

Pins, generated with `#axiom_pin` and guarded by `#guard_msgs` in
`Audit.lean`. Transcribe verbatim; never retype.
