# `docs/` — the working record

These are working documents: design notes, campaign plans, retrospectives,
literature surveys and status pages accumulated while the development was built.
They are kept because the reasoning behind a definition is often worth more than
the definition, and because a superseded plan records why the route was
abandoned.

**They are not the guide.** Start from [`README.md`](../README.md) at the repo
root, which walks the finished development in order;
[`NOTES-FOR-DEVELOPERS.md`](../NOTES-FOR-DEVELOPERS.md) says what is in the
build and what is not.

## Two cautions when reading anything here

**Paths may be stale.** Many documents reference modules under `wip/`, and
`Rewrite/` and `FRJO/`, which are the working record and are **not distributed
on this branch** — they remain on the development branches and in history. A
reference to `wip/foo.lean` is a pointer into that record, not a file you can
open here. Executables named in these documents (`rwscreen`, `rnextend`,
`twosided`, `rnfrj`, `frjcert`, …) are likewise not declared on this branch.

**Status may be stale.** A document states what was true when it was written.
The authority on what is PROVED is the build: `Core.lean` is the list of
finished material and `Core/Audit.lean` pins the axioms of each terminal
theorem, so a claim that fails is a build failure. Where a document and the
build disagree, the build wins.

## The ones worth reading first

- [`calculus-map.md`](calculus-map.md) — **the** provenance reference: which
  proof system each result belongs to. Read it before asserting provenance.
- [`search-manual.md`](search-manual.md) — how the certificate-carrying search
  engines are driven, and the discover-then-pin discipline.
- [`next-session.md`](next-session.md) — the live threads, as of its date.
- [`rn-dictionary-status.md`](rn-dictionary-status.md) — the RN(◯,{})
  dictionary, **withdrawn 2026-08-21** and to be taken as completely unverified
  until it is rebuilt. Kept as the record of the flaw, which is worth reading:
  open cells were recorded as `sorry`ed theorems, so an unanswered question and
  an unproved assertion became indistinguishable. Nothing in `Core` depends on
  it.
- [`archive/`](archive) — superseded material, kept deliberately rather than
  deleted.
