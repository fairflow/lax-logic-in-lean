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

## 3. Transcribing Lean statements into conventional notation

The Lean statement is printed by `{docstring}`; the transcription goes in the
`$$`…`` line above it.  The dictionary used in the CLP paper:

| Lean | LaTeX |
|---|---|
| `Prv Γ A` / `PEq A B` | `\Gamma \vdash A` / `A \dashv\vdash B` |
| `.circ q A` | `\bigcirc_q A` (or `\bigcirc A` when `q` is fixed) |
| `.and .or .imp .top .bot` | `\land \lor \supset \top \bot` |
| `.all A`, `.ex A` (locally nameless) | `\forall x.\,A(x)`, `\exists x.\,A(x)` |
| `¬ Prv …` | `\nvdash` (state as REFUTED with the countermodel named) |
| `(a.ext T).1` | `\pi_1|a|_T` |
| `Θ.HeadsOK isC` | prose ("no clause head is a constraint") |

`scripts/lean-to-math.py <Lib>/Sections/*.lean` makes the first pass: a code
span that contains a logical symbol and no Lean-only token becomes math (a
paragraph that is one formula becomes display math), with the dictionary
above, `\mathit{}` for multi-letter identifiers and `w0 → w_0`; headings are
left alone.  Read the diff and fix by hand.  Keep the mathematical line a
statement, not a paraphrase; keep PROVED / REFUTED / OPEN in the prose.  The
TeX build is the check: a bad macro is a TeX error, and the script reports the
count.

## 3b. Version and build stamp

Every generated document carries a version number (humans recognise it) and
the git hash (machines need it).  `CLPPaper/VERSION` holds the number,
bumped by hand for every delivered draft; `Paper.lean` opens with
`` {buildStamp}`CLPPaper/VERSION` ``, a role in `CLPPaper/Src.lean` that
reads the file, `git rev-parse --abbrev-ref HEAD`, `git rev-parse --short
HEAD`, `git status --porcelain` (a `+` marks a dirty tree) and `date` when the
document is built, and prints e.g. `Version 0.3 · lax-obligations@0e190ea ·
built 2026-09-14 17:05 BST` in HTML and in the PDF.

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
`\small` with `breaklines`; `amsmath`/`amssymb` are loaded (Verso's preamble
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
