---
name: verso-paper
description: Build a paper about Lean work with Verso — vanilla (printable PDF carrying every Lean statement, plus an HTML companion) or blueprint (the one live dependency-graph site) — with the Lean statements printed from the compiled library and transcribed into conventional notation. Use when asked to write up, document, or produce a paper, report, or PDF about a Lean development, to convert a blueprint document to a standalone one, or to rebuild `CLPPaper`.
---

# A Verso paper about Lean work

The record of why is `docs/verso-paper-workflow.md`; this is the checklist.
The worked example is `CLPPaper/` + `scripts/clp-paper.sh` (2026-09-14).

## 0. Fix the parameters first (ask if the request does not settle them)

| parameter | options | default here |
|---|---|---|
| genre | **vanilla** (`VersoManual`) / blueprint (`VersoBlueprint`) | vanilla; blueprint only for the repo's one Pages site |
| engine | **Verso** (HTML + TeX from one source) / LaTeX only | Verso; Verso's `tex/main.tex` is a LaTeX document if hand editing is wanted |
| outputs | PDF, HTML companion (one page + per section) | both |
| Lean code | **included** (`{docstring Name}` prints the statement) / linked only | included; links do not survive printing |
| transcription | conventional-notation line above each Lean statement | yes (`docs/verso-paper-workflow.md` §3 has the dictionary) |
| branch | where sources and scripts are pushed | the campaign branch; push by explicit `sha:refs/heads/<branch>` |
| output paths | must be gitignored | `docs/<paper>/`, `docs/<paper>.pdf` |
| delivery | push + tell the reader to pull; SendUserFile the PDF | never a link to a worktree path |

## 1. Layout

```
<Lib>.lean                 import <Lib>.Paper
<Lib>/Paper.lean           #doc (Manual) "Title" =>  lead prose  {include 0 <Lib>.Sections.X} …
<Lib>/Sections/X.lean      import VersoManual + the library; one #doc per section
<Lib>Main.lean             manualMain (%doc <Lib>.Paper) (options := args)
lakefile.toml              [[lean_lib]] name = "<Lib>"   -- NOT in defaultTargets
scripts/<paper>.sh         scripts/verso-paper.sh <Lib> <Lib>Main.lean docs/<paper> docs/<paper>.pdf
.gitignore                 docs/<paper>/  docs/<paper>.pdf
```

## 2. Write each result as prose → math → Lean

```
Words.  PROVED / REFUTED / OPEN stated in the prose.

$$`\Gamma \vdash \bigcirc A`

{docstring Full.Name +allowMissing}
```

* One `{docstring}` per name per document; later mentions `` {name}`Full.Name` ``.
* Definitions: `{docstring}` prints constructors and fields (`hideFields`,
  `hideStructureConstructor` to trim).
* A checked statement without the docstring: a ```` ```signature ```` block.
* Every `#doc` needs lead prose; backtick bare `[…]`; no pipe tables in Verso
  markup; math is `` $`…` `` / `` $$`…` ``.
* Verify every name compiles before writing prose around it (`#check` in a
  scratch file against the built library).

## 3. Build and check

```
scripts/verso-paper.sh <Lib> <Lib>Main.lean docs/<paper> docs/<paper>.pdf
```

Expect `tex errors: 0`, `missing glyphs: 0`, and the page count.  Then look
at two pages of the PDF (`pdftoppm -r 70 -png -f N -l N`) — a results page
and a code-heavy page — before delivering.  `scripts/verso-tex-pdf.sh` is
where the font patch lives (DejaVu from TeX Live, glyph fallback, A4,
breakable verbatim); extend its `fallback` string if a new glyph is reported.

## 4. Converting a blueprint document

`scripts/blueprint-to-vanilla.py <Lib>/Sections/*.lean`, then strip the
blueprint imports and `{blueprint_graph}`/`{blueprint_summary}` from
`Paper.lean`, swap the main for `manualMain`, rebuild, write the math lines.

## 5. Deliver

Commit sources + scripts + `.gitignore`; push with the fast-forward guard;
say the sha and "pull, then `scripts/<paper>.sh`"; SendUserFile the PDF.
Record the paper in HANDOFF.md.
