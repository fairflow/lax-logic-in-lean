# paper-skeleton

Turn a paper's LaTeX source into a fidelity-table skeleton — the Stage 1
deliverable of a calculus-adoption campaign, which is otherwise built by
hand from a PDF.

```bash
./paper_skeleton.py --arxiv 1804.06689 -o skeleton.md
./paper_skeleton.py --src path/to/main.tex -o skeleton.md --json items.json
```

It resolves `\input`/`\include`, strips comments, finds theorem-like
environments (including those a document class predefines rather than
declaring with `\newtheorem`), **simulates the counters** so items come
out as `Lemma 3.5` rather than "the 17th lemma", flags `\appendix`, and
emits the table, the full statements, and an empty divergence log.

## The one thing to know

**Numbers are inferred; labels are exact.** A LaTeX source never contains
the printed numbers — every one is a `\ref` resolved at compile time — so
the tool simulates LaTeX's counters from the document class's
conventions. The `\label`s *are* in the source. Key your fidelity table
on labels; treat numbers as a convenience, and check the model against
the PDF on two items before trusting a whole table.

This is not hypothetical. On its first run against arXiv:1804.06689 the
tool disagreed with this repo's own fidelity record, which cited
`lemma:lhs` as Lemma 3.4. The tool said 3.5, and was right: `llncs`
shares one counter across `theorem`, `lemma` and `example`, §3 opens with
Theorem 3.1 and then three examples, so `lemma:lhs` is the fifth item.
The record's own later numbers (Lemma 3.9, Theorem 3.10) only make sense
under that same shared counter, so it was internally inconsistent — the
hand count had skipped an *unlabelled* example. Corrected in
`docs/frj-fidelity.md` and in the `FRJ/` docstrings.

Unlabelled environments are exactly where a manual count goes wrong,
because there is no anchor to notice them by.

## Options

    --arxiv ID        download the e-print source
    --src FILE        use a local main .tex
    --dir DIR         use an already-extracted source tree
    -o FILE           write Markdown (default stdout)
    --json FILE       also emit the items as JSON
    --numbering M     override the counter model:
                      shared,section | perkind,section | shared,none
    --keep DIR        keep a downloaded source here
