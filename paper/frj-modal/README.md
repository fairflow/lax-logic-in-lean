# The FRJ-modal paper

A record of the mechanisation: the forward refutation calculus FRJ(G) for
intuitionistic propositional logic, and the first step of its extension
with the lax modality.  Mathematical exposition in the body, **all Lean
code in the appendix**, quoted from and linked to as the body goes along.

Build:

```bash
cd paper/frj-modal && lualatex frj-modal.tex && lualatex frj-modal.tex
```

Two passes: the second resolves the table of contents and the appendix
cross-references.  Requires LuaLaTeX (for the Lean symbol set) with DejaVu
Sans Mono and a STIX Two Math fallback — both ship with TeX Live.

`frj-modal.pdf` is **git-ignored**: it is regenerable, and it is 97 pages
of which most is the appendix listing the Lean sources verbatim, so the
sources are the record and the PDF is a view of them.
