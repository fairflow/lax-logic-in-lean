---
name: verso-paper
description: Build a paper about Lean work with Verso — vanilla (printable PDF carrying every Lean statement, plus an HTML companion) or blueprint (the one live dependency-graph site) — with the Lean statements printed from the compiled library and transcribed into conventional notation. Use when asked to write up, document, or produce a paper, report, or PDF about a Lean development, to convert a blueprint document to a standalone one, or to rebuild `CLPPaper`.
---

# A Verso paper about Lean work

The record of why is `docs/verso-paper-workflow.md`; this is the checklist.
The worked example is `CLPPaper/` + `scripts/clp-paper.sh` (2026-09-14) in
`fairflow/lax-logic-in-lean`, branch `lax-obligations` (later `main`).  Project
skills are read from the main checkout's `.claude/skills/`, not from a
worktree or another branch, so this skill is also installed at
`~/.claude/skills/verso-paper/` (a copy; the repo file is the source).  If
the current branch lacks the scripts, fetch them from the branch that has
them before step 3:

```
git checkout origin/lax-obligations -- scripts/verso-paper.sh scripts/verso-tex-pdf.sh scripts/lean-to-math.py scripts/blueprint-to-vanilla.py CLPPaper/Src.lean
```

## 0. Fix the parameters first (ask if the request does not settle them)

| parameter | options | default here |
|---|---|---|
| genre | **vanilla** (`VersoManual`) / blueprint (`VersoBlueprint`) | vanilla; blueprint only for the repo's one Pages site |
| engine | **Verso** (HTML + TeX from one source) / LaTeX only | Verso; Verso's `tex/main.tex` is a LaTeX document if hand editing is wanted |
| outputs | PDF, HTML companion (one page + per section) | both |
| Lean code | **included** (`{docstring Name}` prints the statement) and/or **linked** (`{srcLink}\`Name\`` → `path:line` → GitHub at the build commit) | both |
| transcription | conventional-notation statement generated from the declaration's type (`{stmt}`) | yes; extend the notation table in `CLPPaper/Math.lean` for another object language |
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

{stmt}`Full.Name`

{docstring Full.Name +allowMissing}

{srcLink}`Full.Name`
```

Three roles, all generated from the compiled declaration at build time, none
edited by hand: `{stmt}` (the statement as mathematics, from the type:
binders → quantifiers, hypotheses → premises, the object language through the
notation table in `CLPPaper/Math.lean`, generic fallback for the rest; a
`def`/`inductive` prints nothing), `{docstring}` (Verso's own: signature +
docstring), `{srcLink}` (`path:line` → GitHub at the build commit).

`srcLink` is a document-local role (`CLPPaper/Src.lean`: copy it into a new
paper's lib): it reads the declaration's module and line from the
environment and `git rev-parse HEAD` / `git remote get-url origin` at build
time, so the link is to the exact line at the commit that was built (push
before the reader follows it).  In TeX it is a real hyperlink via `\oldhref`
(Verso's template footnotes every `\href`).

* One `{docstring}` per name per document; later mentions `` {name}`Full.Name` ``.
* Definitions: `{docstring}` prints constructors and fields (`hideFields`,
  `hideStructureConstructor` to trim).
* A checked statement without the docstring: a ```` ```signature ```` block.
* Every `#doc` needs lead prose; backtick bare `[…]`; no pipe tables in Verso
  markup; math is `` $`…` `` / `` $$`…` ``.
* Verify every name compiles before writing prose around it (`#check` in a
  scratch file against the built library).
* Prose is the author's; formulas in prose are Verso math (`` $`…` ``).
  `scripts/lean-to-math.py` converts Unicode formulas in *source* prose to
  math once, as an authoring aid; it is not a build step and no output is
  ever edited.

## 2b. Version and build stamp (every generated document carries both)

`<Lib>/VERSION` holds a hand-bumped number (bump it for every delivered
draft); the first line of `Paper.lean` is `` {buildStamp}`<Lib>/VERSION` ``
(role in `CLPPaper/Src.lean`), which renders
`Version 0.3 · lax-obligations@0e190ea · built 2026-09-14 17:05 BST` in HTML
and TeX from the file, `git` (branch, short hash, `+` when the tree is dirty)
and the clock at build time.  The reader identifies the latest draft by the
version; the hash says exactly what was built.

## 3. Build and check

```
scripts/verso-paper.sh <Lib> <Lib>Main.lean docs/<paper> docs/<paper>.pdf
```

Expect `tex errors: 0`, `missing glyphs: 0`, the page count, and
`html-single: … unresolved: 0 empty, 0 find/` — `verso-paper.sh` rewrites the
one-page HTML so it reads from `file://` too (Verso's `<base href="./">`,
`find/?…` permalinks and `href=""` table of contents all resolve to a
directory listing when the file is opened directly; anchors survive).  The
per-section `html-multi/` still needs a server.  Then look
at two pages of the PDF (`pdftoppm -r 70 -png -f N -l N`) — a results page
and a code-heavy page — before delivering.  `scripts/verso-tex-pdf.sh` is
where the font patch lives (DejaVu from TeX Live, glyph fallback, A4,
breakable verbatim); extend its `fallback` string if a new glyph is reported.

## 4. Converting a blueprint document

`scripts/blueprint-to-vanilla.py <Lib>/Sections/*.lean`, then strip the
blueprint imports and `{blueprint_graph}`/`{blueprint_summary}` from
`Paper.lean`, swap the main for `manualMain`, add `{stmt}`/`{srcLink}` lines
around each `{docstring}` (the converter's `--roles` does this), rebuild.

## 5. Deliver: the reader builds in their own checkout

Everything the reader needs is under git: sources, scripts, `.gitignore`.
Their flow (Matthew, 2026-09-14; serving from the builder's worktree was
tried and rejected):

```
git -C <their checkout> merge --ff-only <branch>
lake build                      # the library; the paper lib is outside defaultTargets
scripts/<paper>.sh --open       # lake build <Lib> (incremental) + HTML + TeX + PDF, then open both
```

The first run in a checkout that has never built Verso compiles it (minutes);
after that the script is about a minute.  Outputs land at
`docs/<paper>.pdf` and `docs/<paper>/html-single/index.html` in *their*
checkout, which is the only place a path is openable for them.  So in the
reply: the sha, those three lines, and nothing relative to the builder's
worktree.  SendUserFile the PDF as well when they are away from the machine.
Record the paper in HANDOFF.md.
