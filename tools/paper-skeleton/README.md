# paper-skeleton

Turn a paper's LaTeX source into a fidelity-table skeleton — the Stage 1
deliverable of a calculus-adoption campaign, otherwise built by hand.

```bash
./paper_skeleton.py --arxiv 1804.06689 -o skeleton.md
./paper_skeleton.py --src path/to/main.tex -o skeleton.md --json items.json
```

It resolves `\input`/`\include`, strips comments, finds theorem-like
environments, **compiles the document and reads the `.aux`** for the
numbers, flags `\appendix`, and emits the table, the full statements, and
an empty divergence log.

## Where the numbers come from

The `.aux`, where LaTeX records

```
\newlabel{lemma:lhs}{{1}{11}{}{theorem.1}{}}
```

— label, printed number, page. That is exact. A source never contains its
printed numbers: every one is a `\ref` resolved at compile time.

If the document will not compile, the tool lists items **with no number**
rather than a guessed one.

## Why it works this way (a mistake worth keeping)

The first version simulated LaTeX's counters from the document class's
conventions. It was confidently wrong about arXiv:1804.06689: it reported
`Lemma 3.5` for the result the compiler numbers **Lemma 1**, and it had a
plausible-looking argument for 3.5 built on the `llncs` class sharing one
counter across `theorem`, `lemma` and `example`. `llncs` does no such
thing — each kind has its own counter and no section prefix.

On the strength of that simulation I "corrected" this repo's fidelity
record, which had not been wrong. The edit was reverted. Matthew's
question — *wouldn't it be easier to build the TeX and read the
references?* — is the whole answer: reimplementing LaTeX is not worth it
when LaTeX is installed, and a simulation that is wrong is worse than no
number at all, because it is asserted with the same confidence as a
correct one.

## Cite by label, not by number

Labels are stable across versions; numbers are not. The FRJ paper's arXiv
source numbers `lemma:lhs` as *Lemma 1*; the journal version numbers the
same result *3.4*. Both are "the paper". Only `lemma:lhs` identifies it
unambiguously, which is why the generated table keys every row on its
label and carries the number and page as a convenience.

## Options

    --arxiv ID     download the e-print source
    --src FILE     use a local main .tex
    --dir DIR      use an already-extracted source tree
    -o FILE        write Markdown (default stdout)
    --json FILE    also emit the items as JSON
    --no-compile   skip compilation; items carry no numbers
    --keep DIR     keep a downloaded source here

## Where the statement text comes from

The compiled PDF, via `pdftotext`, keyed by the page the `.aux` gives.
Not the LaTeX source.

The first version emitted raw source into the table, and it was
unreadable — `$\proves{\FRJof{G}}G$ implies $G\not\in\IPL$`. That is not
a Markdown-viewer limitation. Two separate reasons it cannot work:

1. **The macros are the paper's own.** `frj-corr.tex` defines 164 of
   them. `\proves`, `\FRJof`, `\Lhs`, `\Clo`, `\mapstorz` mean nothing
   outside its preamble, so no renderer anywhere can display them.
2. **Markdown has no math.** CommonMark specifies none at all. `$…$` and
   `$$…$$` are an *extension* — GitHub added them in 2022, Pandoc has
   `tex_math_dollars` — and even where implemented they cover maths, not
   arbitrary LaTeX, and never undefined macros.

So the tool reads what LaTeX printed. `\qed`'s box (⊔⊓) marks the end of
a statement, which is a more reliable stop than any heuristic on the
source. Titles are taken from the printed heading too, so
`(Soundness of $\FRJof{G}$)` arrives as `(Soundness of FRJ(G))`.

The LaTeX source is still kept, folded under each statement, because
that is what a transcription is checked against.

### Known limitation: section headers

The 38 item rows are macro-free, but **section grouping headers still show
the paper's macros** (`§ The calculus $\FRJof{G}$`), because a section
heading has no `\label` in this paper and so no `.aux` entry to key its
printed text by.

An attempt to match printed headings by keyword made it worse — it
replaced a correct-but-ugly title with a body line that happened to
contain "calculus". Reverted. The headers only group the table, so a
macro in one costs nothing; guessing a wrong title costs accuracy.

## No HTML in the output

The first version used `<sub>` for page numbers, `<br/>` inside table cells,
and `<details>` to fold the LaTeX source. In a viewer without HTML support
the `<details>` does not collapse, so the folded source is displayed inline
— which is what made the output look "full of undigested TeX" even after
the statements had been fixed. The source was never the problem; the
container was.

Now: no HTML at all. Table cells are one line, `Lemma 3 · lemma:wg · p.19`,
and every LaTeX source lives in a single **LaTeX sources** section at the
end, so reading the statements is uninterrupted.

## Two ways to get statement text

    --text pdf      (default) the printed text via pdftotext: Unicode prose,
                    readable in any viewer, e.g.
                        σ1 7→ σ2 implies ⟨0,0,0⟩ ⪯ wg(σ2) ≺ wg(σ1).
    --text pandoc   pandoc with the paper's own \newcommand definitions
                    extracted brace-aware and prepended, so its macros are
                    EXPANDED to standard LaTeX, e.g.
                        $\mathrm{Mod}(\mathcal{D}_S)$
                    Better structurally, and renderable by any viewer that
                    supports $…$ math — but Markdown has no math in the
                    spec, so many do not.

`pandoc` is also the automatic fallback whenever the PDF lookup fails.
Extracting the macros **brace-aware** is essential: line-wise extraction
truncates multi-line definitions, leaves braces unbalanced, and makes
pandoc give up on the whole file silently.

Items that neither route can extract are marked as such, never filled with
raw source. On the FRJ paper that is 2 of 38 — one unlabelled example,
which has no `.aux` entry and so no page to look on.

## Repairing the extractor's glyph damage

`pdftotext` maps a TeX font's glyphs to Unicode one code point at a time,
so composed and negated symbols come out wrong — predictably, and
therefore repairably. Do not pass its output through raw.

    pdftotext -raw          reading order preserved, so a superscript stays
                            where it belongs, and no spurious spaces before
                            a closing delimiter (the default and -layout
                            modes both insert them, and -layout also floats
                            the superscript to its own line)

Then, each verified against the printed page:

    7→        → ↦          the mapsto glyph extracts as digit-7 plus arrow
    X + U+0338 → ≠ ∉ ⊈ …   COMBINING LONG SOLIDUS arrives either side of
                            its base character
    ⊅∈        → ⊃∉         a negation that landed on the wrong glyph of a
                            two-symbol rule name
    σ1        → σ₁         subscripts are flattened to adjacent digits
    σ′ 1      → σ′₁        …and separated from a prime
    σn        → σₙ         index letters likewise
    σ1 R ↦0   → σ₁ ↦ᴿ₀     a lone capital before an arrow is that arrow's
                            superscript, and belongs after it
    ↦∗        → ↦*
    coun- ter → counter    end-of-line hyphenation

Subscript restoration fires only after a Greek letter, a prime or an
arrow, where the reading is unambiguous. A superscript such as `O(N 2 )`
keeps its space and is deliberately left alone: guessing there would turn
N² into N₂.
