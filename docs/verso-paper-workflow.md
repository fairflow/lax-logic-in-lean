# Writing a paper about Lean work with Verso: the workflow

Established 2026-09-14 on the CLP paper (`CLPPaper/`, branch
`lax-obligations`).  The operational checklist is the project skill
`.claude/skills/verso-paper/SKILL.md`; this file is the rationale and the
record of what was tried.

## 1. The two Verso routes, and when each applies

| | blueprint (`VersoBlueprint`) | vanilla (`VersoManual` only) |
|---|---|---|
| purpose | the one live dependency-graph site GitHub Pages builds for the repo | any standalone document |
| result markup | `:::theorem "id" (uses := …) (lean := "Name")` nodes | prose + `{docstring Name}` |
| what the reader gets | status chips, graph, hover code (HTML only) | the Lean statement itself, in HTML **and** TeX |
| TeX / PDF | statements only: the node's Lean code is dropped | `docstring` and `signature` blocks have TeX renderers |
| published where | GitHub Pages (one main document per repo) | wherever you put the build outputs |

Rule: a document about finished work that must be printable goes vanilla.
The blueprint genre is reserved for the repo's live blueprint.

## 2. Vanilla Verso in this repo

* Verso is vendored at `.lake/packages/verso` (v4.31.0).  Nothing to install
  for HTML.  The PDF needs a full TeX Live (`/Library/TeX/texbin/xelatex`,
  memoir, fontspec, tcolorbox, fvextra, newunicodechar, the Source Pro font
  packages and the DejaVu fonts, all present in TeX Live 2025).
* A paper is a `[[lean_lib]]` **outside** `defaultTargets` (so `lake build`
  never pulls Verso into the ordinary build), with a root module
  `<Lib>.lean`, a `<Lib>/Paper.lean` carrying `#doc (Manual) "Title" =>` and
  `{include 0 <Lib>.Sections.X}` lines, one `#doc` per section file, and a
  `<Lib>Main.lean`:

  ```lean
  import VersoManual
  import CLPPaper.Paper
  open Verso.Genre.Manual
  def main (args : List String) : IO UInt32 :=
    manualMain (%doc CLPPaper.Paper) (options := args)
  ```

* Each result is written as

  ```
  Prose stating the result in words.

  $$`\bigcirc(A \lor \bigcirc B) \vdash \bigcirc(A \lor B)`

  {docstring LaxLogic.QLL.circ_or_circ_collapse +allowMissing}
  ```

  `{docstring}` prints the declaration's label, its full signature (the
  statement of a theorem; the constructors of an inductive; the fields of a
  structure) and its docstring, from the compiled library, so a statement in
  the paper cannot drift from the code.  It renders to HTML and to a
  `docstringBox` in TeX.  Each name may be documented **once** per document
  (the docstring domain rejects duplicates); further mentions use
  `` {name}`Name` ``.  `+allowMissing` keeps a missing docstring a warning.
  Options: `hideFields`, `hideStructureConstructor`, `label := "…"`.
* `{srcLink}\`Full.Name\`` (document-local role, `CLPPaper/Src.lean`) prints
  `LaxLogic/QLL/BodyCirc.lean:528` linked to that line of the repository on
  GitHub at the commit being built (`git rev-parse HEAD`, origin URL), in
  HTML and in the PDF (`\oldhref`, the unmodified `\href` Verso's template
  keeps).  Included *and* linked, then: the statement is printed by
  `{docstring}`, the proof is one click away.  Push before the link is used.
* Alternative when you want a checked statement without the docstring:
  a ```` ```signature ```` block containing `theorem Name (x : A) : T`; Verso
  elaborates it against the environment and fails the build if it is wrong.
* Markup rules that bit: every section needs lead prose after its `#doc`
  line; bare `[…]` is link syntax (backtick it); `{ref}` needs a declared
  tag; there are no pipe tables (use a code block or the `table` directive);
  math is `` $`…` `` inline and `` $$`…` `` displayed (KaTeX in HTML, native
  in TeX); code is verbatim.

## 3. The mathematics is generated from the statements

`{stmt}\`Full.Name\`` (role in `CLPPaper/Math.lean`) prints the declaration's
type as display mathematics, at build time, from the compiled environment:

* `∀`-binders become quantifiers without type annotations
  (`\forall\, q,\ A,\ B.`; Matthew, 2026-09-14), hypotheses become premises
  (one per line, `\Longrightarrow`), instance arguments vanish;
* the object language goes through a notation table: `Prv Γ A` is
  `Γ ⊢ A`, `¬ Prv` is `⊬`, `PEq` is `⊣⊢`, `Form.and/or/imp/circ/forall_/exists_`
  are `∧ ∨ ⊃ ◯_q ∀x. ∃x.` with de Bruijn binders named `x, y, z, …` by depth,
  `Form.pred "geq" [a,b]` is `a ≥ b`, `Tm.fn "add"` is `+`, a list context is a
  comma sequence and `Θ.forms` is `Θ`;
* everything else has a generic reading (`∧ ∨ ↔ = ≠ ∈ ∃ λ`, numerals, lists,
  pairs, `b = true` as `b`, applications as `\mathit{f}(a, b)` with implicit
  arguments dropped) and, last, Lean's own printer in typewriter;
* a declaration whose type is not a proposition prints nothing;
* rows longer than about 78 visible characters are broken at binary
  connectives, shallowest parenthesis depth first, continuation rows
  indented (neither KaTeX nor TeX breaks display mathematics by itself).

The same declaration always gives the same mathematics and it cannot drift
from the code; nothing in the output is edited by hand.  For another object
language, extend the table (`form`, `tm`, `ctx`, and the `generic` cases).
The prose around a result is the author's; formulas in it are written as
Verso math.  `scripts/lean-to-math.py` exists only as an authoring aid that
converts Unicode formulas in *source* prose to math; it is not a build step.

## 3b. Version and build stamp

Every generated document carries a version number (humans recognise it) and
the git hash (machines need it).  `CLPPaper/VERSION` holds the number,
bumped by hand for every delivered draft; `Paper.lean` opens with
`` {buildStamp}`CLPPaper/VERSION` ``, a role in `CLPPaper/Src.lean` that
reads the file, `git rev-parse --abbrev-ref HEAD`, `git rev-parse --short
HEAD`, `git status --porcelain` (a `+` marks a dirty tree) and `date` when the
document is built, and prints e.g. `Version 0.3 · lax-obligations@0e190ea ·
built 2026-09-14 17:05 BST` in HTML and in the PDF.  Because the stamp is
computed when `Paper.lean` is elaborated, `verso-paper.sh` removes that
module's compiled outputs before `lake build`, so it is recomputed on every
build; the other modules stay incremental.  Build after committing and the
stamp names the commit without a `+`.  The stamp also defines
`\versoBuildStamp`, which the TeX step centres above the running heads on
every page (two-line header, `headheight=26pt`).

## 4. Build

```
scripts/verso-paper.sh <Lib> <Main.lean> <out-dir> <out.pdf>
```

does `lake build <Lib>`, runs the main with `--with-html-single --with-tex`,
then `scripts/verso-tex-pdf.sh <out-dir>/tex <out.pdf>`.  The TeX step
patches Verso's `main.tex` before running `xelatex` three times: Verso asks
for the system font "DejaVu Sans Mono" (absent on a Mac) — we load TeX Live's
copy by file name; the Source Pro text fonts lack `◯ ℚ ⊨ …` — DejaVu Sans is
declared as a per-glyph fallback with `newunicodechar`; Verso emits plain
`verbatim`, which cannot break lines — it is routed through fancyvrb at
`\small` with `breaklines`; links are coloured text, not hyperref's boxes
(Matthew: "goodbye and good riddance"); `amsmath`/`amssymb` are loaded (Verso's preamble
has neither, and the transcriptions use `\Vdash`, `\nvdash`, `\square`,
`\rightsquigarrow`).  A4, 24 mm margins.  The script reports TeX
errors and missing glyphs; both must be 0.

After rendering, `verso-paper.sh` rewrites `html-single/index.html` so it can
be opened from `file://`: Verso emits `<base href="./">`, section permalinks
through `find/?domain=…&name=ID` and a local table of contents with
`href=""`, all of which a browser turns into a directory listing when the
file is opened directly.  The base tag is dropped, permalinks become `#ID`
(the `name` is the heading's id), and the contents links are matched to
their headings by section number.  `html-multi/` is left as Verso made it
and needs a server.

For the CLP paper the wrapper is `scripts/clp-paper.sh [--open|--serve]`,
writing `docs/clp-paper/{html-single,html-multi,tex}` and `docs/clp-paper.pdf`.

## 5. Outputs are build artefacts

HTML and PDF are **gitignored** (`docs/clp-paper/`, `docs/clp-paper.pdf`).
What is pushed is the source and the scripts; a reader rebuilds with one
command, or is sent the PDF.  Serve HTML over HTTP (`--serve`), never
`file://`: relative section links become directory listings.

## 6. Delivery

The reader builds in their own checkout; everything needed is under git.
Matthew's flow (2026-09-14):

```
git -C /Users/matthew/Lean/qll-review merge --ff-only lax-obligations
lake build
scripts/clp-paper.sh --open
```

The third line runs `lake build CLPPaper` (outside `defaultTargets`, so the
plain `lake build` does not cover it; incremental after the first run, which
compiles Verso if that checkout never has), renders HTML and TeX, compiles
the PDF, and opens `docs/clp-paper.pdf` and
`docs/clp-paper/html-single/index.html`.  Serving the outputs from the
builder's worktree over HTTP (`--serve`) exists but was rejected as the
delivery route; a PDF is also sent directly (SendUserFile) for reading away
from the machine.  Markdown links to files in a reply are dead: they resolve
in the assistant's worktree.

## 7. Converting an existing blueprint paper

`scripts/blueprint-to-vanilla.py <Lib>/Sections/*.lean` rewrites each node
into its body plus a `{docstring}` block, drops `:::group` blocks and the
blueprint imports, and documents a name only once.  Then remove the
blueprint imports and `{blueprint_graph}`/`{blueprint_summary}` from
`Paper.lean`, replace the main with `manualMain`, build, and write the
mathematical lines by hand (§3).  What is lost: status chips, the dependency
graph, `uses` edges.  What is gained: the statements in print.

## 8. LaTeX without Verso

If only a `.tex` is wanted, the same Lean statements can be printed with
`Lean.PrettyPrinter.ppSignature` from a `#eval` script and pasted into a
`Verbatim` environment; the transcription table above still applies.  Not
exercised here — Verso's TeX output already is a LaTeX document
(`<out-dir>/tex/main.tex`, memoir class) that can be edited by hand.
