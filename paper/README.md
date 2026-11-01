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
| `appendix.tex` | Appendices A–E in full (listings at `\scriptsize` — reference material) |
| `figs/` | TikZ countermodel diagrams, copied from the build-regenerated `../docs/figures/*.tikz` with two mechanical patches (`∅`→`\varnothing`, `◯`→`\bigcirc` — raw Unicode fails in math mode); re-copy after regenerating the art |
| `unicode.tex` | generated listings `literate` table, **currently unused** — kept solely for a possible future pdflatex/TAPS port (where listings + literate is the working combination) |
| `latexmkrc` | regenerates `commitsha.tex` (git-ignored) before each build; it feeds the subtitle's version stamp — artefact commit and build date on page 1, the series convention adapted to acmart |
| bibliography | `../docs/belief.bib` (119 entries; pruning is a later human step) |

## Provenance and editing discipline

`body.tex` is now the **working master** (the merge pass of 2026-07-19
applied decisions D2–D9 here, and `../docs/belief-paper-draft.md`
carries a supersession note). Edit the TeX directly; the markdown draft
is kept only as the revision-2 record.

## Sharing builds

`belief.pdf` is **tracked in git** (a `!belief.pdf` exception to the
`*.pdf` ignore), so the current build can be shared by a repository
link — e.g. GitHub renders it in-browser at
`.../blob/<branch>/paper/belief.pdf`. Rebuild and re-commit it at
sharing points to keep the link current (no need to commit it on every
micro-edit — it is a ~370 KB binary blob). The commit-stamped copies
`belief-<shortsha>.pdf` remain gitignored scratch, used only in chat to
avoid a stale side-panel render being mistaken for the latest build.

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

Status of the earlier limitations (2026-07-19, done):

- Lean displays reflowed to the two-column measure (one ~2 pt residual);
- prose mathematics converted to real math (pour-time `\ensuremath`
  chains merged);
- citation sweep complete (70 of 119 entries cited).
