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
  In the PDF the path may break after each `/`, so a link in running text
  never makes an overfull line (v0.8).
* Alternative when you want a checked statement without the docstring:
  a ```` ```signature ```` block containing `theorem Name (x : A) : T`; Verso
  elaborates it against the environment and fails the build if it is wrong.
* Markup rules that bit: every section needs lead prose after its `#doc`
  line; bare `[…]` is link syntax (backtick it); `{ref}` needs a declared
  tag; there are no pipe tables (use the `wtable` directive of §3c, or Verso's
  `table`);
  math is `` $`…` `` inline and `` $$`…` `` displayed (KaTeX in HTML, native
  in TeX); code is verbatim.

## 3. The mathematics is generated from the statements

`{stmt}\`Full.Name\`` (role in `CLPPaper/Math.lean`) prints the declaration's
type as display mathematics, at build time, from the compiled environment:

* `∀`-binders become quantifiers without type annotations
  (`\forall\, q,\ A,\ B.`; Matthew, 2026-09-14), hypotheses become premises
  (`\Longrightarrow`), instance arguments vanish;
* the object language goes through a notation table: `Prv Γ A` is
  `Γ ⊢ A`, `¬ Prv` is `⊬`, `PEq` is `⊣⊢`, `Form.and/or/imp/circ/forall_/exists_`
  are `∧ ∨ ↠ ◯_q ∀x. ∃x.` (↠ since v0.6, the library's notation) with de
  Bruijn binders named `x, y, z, …` by depth, a nested object-level `∧`/`∨`
  bracketed on both sides, `Form.pred "geq" [a,b]` is `a ≥ b`, `Tm.fn "add"`
  is `+`, a predicate or argument list that is a variable is printed as
  `p(us)`, a list context is a comma sequence and `Θ.forms` is `Θ`; goals and
  machine states are `c □ φ₁, …, φₙ`, `Consequence`/`HTrue` are `⊨`, forcing is
  `M, s ⊨ A`, a bundled map `⇑f x` is `f(x)`;
* everything else has a generic reading (`∧ ∨ ↔ = ≠ ∈ ∃ λ`, numerals, lists,
  pairs, `b = true` as `b`, applications as `\mathit{f}(a, b)` with implicit
  arguments dropped) and, last, Lean's own printer in typewriter;
* proof trees, partial proof trees and abstract proof trees are written with
  the names of their rules (v0.8): an open leaf `hole S` is `⟨S⟩`,
  `andI p q` is `∧I(p, q)`, `orL p` is `∨I₁(p)`, a constraint leaf is its
  atom, `clause w ts p` is `clause_w^{ts}(p)` (no superscript for `[]`), and
  `val`, `andC`, `orL`, `exC`, `impC` are `val`, `∧◯`, `∨◯₁`, `∃◯_t`, `↠◯_w`;
* a conjunction of steps of `Step`, `SLD.SLDStep` or `SLD.SLDCStep` with the
  same parameters, each step starting where the previous one ends, is printed
  as a run: a first row with the relation and its parameters, then one state
  per row after `⇝` (Table 2) or `⟶` (the machines) (v0.8);
* constants of `LaxLogic.QLL.CLPExamples` are read as variables: `θ3` is
  `θ₃`, `ex95` is `ex₉₅` (v0.8);
* a declaration whose type is not a proposition prints nothing;
* a statement is set on one row when it fits `rowMeasure`, 95 estimated
  characters (a long arrow counts three; the estimate runs high, so this is
  about nine tenths of the line); otherwise the premises are filled into rows
  after the quantifier prefix, and a piece still too long is broken at the
  shallowest parenthesis depth, at `⟺`/`⟹` before the other connectives;
  continuation rows are indented (neither KaTeX nor TeX breaks display
  mathematics by itself).  A quantifier below the root stays on one line.
  (v0.7; v0.6 set one premise per row, Matthew asked for compact displays.)

The same declaration always gives the same mathematics and it cannot drift
from the code; nothing in the output is edited by hand.  For another object
language, extend the table (`form`, `tm`, `ctx`, and the `generic` cases).
The prose around a result is the author's; formulas in it are written as
Verso math.  A worked example obeys the same rule: every concrete state, tree
and constraint the text shows is the `{stmt}` of a kernel-checked library
statement, followed in the prose by its `{srcLink}` rather than its
`{leanDecl}`, since the statement is the display (v0.8: the running example,
`run95_*` in `LaxLogic/QLL/CLPExamples.lean`).  `scripts/lean-to-math.py` exists only as an authoring aid that
converts Unicode formulas in *source* prose to math; it is not a build step.

## 3a. Layout devices (CLP paper, v0.6)

The v0.5 PDF had 87 overfull lines, mostly Lean signatures in boxes and
tables set as code.  v0.6 adds, all document-local:

* `{leanDecl}` (`CLPPaper/Decl.lean`) fills the signature to 88 columns
  (v0.7): the statement is cut at its top-level `→ ↔ ∨ ∧` and at the
  binders of a long `∀`/`∃`, and a line breaks only before a binder or piece
  that does not fit; a piece keeps Lean's notation, and its brackets are
  exactly those Lean prints in the whole statement.  A structure's own
  fields follow `where` in binder form, `(arity : ℕ) (body : Form) …`;
  constructors of at most 40 characters stand two to a line in aligned
  columns (a symbol the monospaced font has is set in it, not in the
  proportional fallback font: `\leanSymbolfont`, defined by `{texSetup}`).
  It prints in an fvextra
  `Verbatim` at `\footnotesize` that breaks long lines, with a thin rule on
  the left and the source link flush right below it, never separated from it
  by a page break; a signature of at most 12 lines is not split across pages
  (`samepage`, which needs `bgcolorboxoverlap=0pt`: by default fvextra puts
  a `\vspace{-0.25pt}` after every line, and TeX may break the page at that
  glue whatever the line penalties say).  The docstring is printed only with
  `+doc`.  In HTML the same block is a `lean-decl` div with wrapping `pre`.
* `:::wtable (widths := "0.3 0.7") +header` (`CLPPaper/Layout.lean`) takes a
  list of rows, each a list of cells, and sets a real table: TeX `tabular`
  with `p{}` columns at the given fractions of `\linewidth` (text wraps inside
  a cell), HTML `<table>` with a `colgroup`.
* `{texSetup}` (`CLPPaper/Layout.lean`) emits raw TeX once: chapters do not
  start new pages, compact chapter and section headings, a table of contents
  to chapter depth, tight lists, `\emergencystretch`.  HTML is unaffected.
* `scripts/verso-tex-pdf.sh` appends `$VERSO_TEX_EXTRA` to the preamble;
  `scripts/clp-paper.sh` sets it to `\let\cleardoublepage\clearpage` (no blank
  recto pages).  Other papers are unaffected unless they set it.

Result: 41 pages, 0 overfull lines (v0.5: 54 pages, 87).  v0.7, with the
compact displays: 34 pages, 0 overfull lines.  v0.8, with the running
example and the sections' opening paragraphs: 38 pages, 0 overfull lines.

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
