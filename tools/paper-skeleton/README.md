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
