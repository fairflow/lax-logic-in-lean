# FRJLax — FRJ◯ built afresh

FRJ(G) (Fiorentini–Ferrari, arXiv:1804.06689) extended with the lax
modality ◯, built **effective and choice-free from line one**.

Empty by design: the brief is `docs/frj-lax-handoff.md`. Read it, and
the repo `CLAUDE.md`, before adding anything here.

Two things this directory is not:

* It is not `FRJO/`. That is the abandoned first attempt, whose
  `ExtractForces` is REFUTED for `worldOK` v3 (three kernel-checked
  cells, commit `4730e30`). Nothing from it is imported or copied.
* It is not a copy of `FRJ/`. That development is PROVED over IPC and is
  the *result set to reprise*, not a base to import: its calculus is
  `Finset`-based and its constructors carry computed indices in their
  return types, which is exactly what is being redesigned here.

Templates: `LaxLogic/PLLNDCore.lean` (slime-free, `Type`-valued,
cast-free) and `LaxLogic/LJFOCore.lean` (zero imports).

---

## SUPERSEDED, 2026-08-16 21:40

This directory was a parallel re-derivation of FRJ(G) §2 and §3 with the
modality carried from line one.  While it was being built, `FRJ/` on
`frj-lax` was finished — choice-free, `List`-based, with **canonical
contexts** (`nf`) — and the handoff was rewritten to say: extend that
development, do not rebuild it.

The reassessment is `docs/frjlax-reassessment.md`.  In short: the rule
table here reaches index-equality by never computing an index (every
conclusion context enters through the membership-equality relation `≐`),
where `FRJ/` reaches it by normalising the computed index with `nf G`.
Both work; the second is the one the ◯-free theory settled on, so this
one is redundant.

What was kept out of it, and where:

* the modal semantics lemmas and the three screens — to be re-homed on
  `FRJ/`'s `Kripke` once it carries `Rm` and `Fal`;
* the three-zone `Ĝ = Ĝ_at ∪ Ĝ_imp ∪ Ĝ_◯`, to be applied to `FRJ/`'s
  `gHat`;
* the rule design and the `◯p ⊃ p` gap finding —
  `docs/frjlax-modal-rules.md`;
* the source reading and the numbering corrections —
  `docs/frj-lax-plan.md` §1, `docs/frj-fidelity.md`.

**One defect found here and not to be repeated**: `Circ.lean` stated its
result as `¬ PLL G`, the classical side of the constructive divergence.
The modal results belong on the **countermodel** side — `∃ K, ¬ K.valid G`
— since `¬ ∀ K, K.valid G → ∃ K, ¬ K.valid G` is not constructively valid
and `frj_iff_not_IPL` is the one place `Classical.choice` enters `FRJ/`.

Nothing here is imported by anything.  It is kept for the record.
