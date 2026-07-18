# Belief in Lax Logic — TeX source

CPP 2027 skeleton (created 2026-07-19). Purpose, in order: (1) real page
counts for the selection plan in `../docs/belief-paper-selection.md`;
(2) the submission source, grown by the merge pass.

## Build

```
latexmk -lualatex belief.tex
```

TeX Live 2025; LuaLaTeX for Unicode (see the TAPS note at the head of
`belief.tex`).

## Files

| file | role |
|---|---|
| `belief.tex` | acmart wrapper: class options, fonts, listings setup, theorem environments, metadata, TODOs |
| `abstract.tex` | abstract (from draft rev 2) |
| `body.tex` | §§1–10, poured from `../docs/belief-paper-draft.md` rev 2 by pandoc + fix-ups (theorem environments, `\cite`s); content edits carry `%% TODO(D…)` markers keyed to the selection doc |
| `appendix.tex` | Appendices A–E stubs per the selection doc §4 |
| `unicode.tex` | generated listings `literate` table, **currently unused** — kept solely for a possible future pdflatex/TAPS port (where listings + literate is the working combination) |
| bibliography | `../docs/belief.bib` (119 entries; pruning is a later human step) |

## Provenance and editing discipline

`body.tex` is a *derived pour* of the markdown draft, not yet the master.
Until Matthew declares the switch-over, substantive prose edits should
happen in `../docs/belief-paper-draft.md` and be re-poured, or be made in
both places knowingly; the merge pass (selection doc §2) is expected to
make `body.tex` the master thereafter.

Engineering decisions, measured not guessed (2026-07-19):

- **No `listings` package.** Under LuaLaTeX its scanner reorders
  non-ASCII glyphs (`[◯p]` prints `◯[p]`), its `literate` keys never
  match, its `breaklines` livelocks, and active-character workarounds
  break `\lstinline` scanning. Code blocks are fancyvrb `Verbatim`
  (keeping the `lstlisting` environment name), rendered by DejaVu Sans
  Mono with a luaotfload fallback to STIX Two Math for the few missing
  glyphs (⊩, ⊨) — zero missing characters, correct order.
- **No inline verbatim.** All inline code is `\texttt` with pour-time
  escaping and Unicode→math substitution, robust in any argument
  position.

Known skeleton limitations, deliberate for now:

- a few wide Lean blocks overflow the two-column measure and are to be
  reflowed by hand at the merge pass;
- prose mathematics is rendered by pour-time Unicode→`\ensuremath`
  substitution — page-honest but typographically rough; the merge pass
  converts the load-bearing formulas to real math;
- citations cover only the inline `[F&M 1997]`-style references plus a
  handful of obvious ones; the full citation pass is merge-pass work.
