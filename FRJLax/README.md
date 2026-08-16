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
