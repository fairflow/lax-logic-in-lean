# The tools, and when to run each

The first three were built during the FRJ campaign because their absence
cost real time; `#deslime` was built after it, when the campaign's worst
structural problem turned out to have had no check at all. They live in
`lax-logic-in-lean`; `Meta/` imports nothing but `Lean`, so it can be
copied into any Lean project as-is.

## `paper-skeleton` — Stage 0/1

`tools/paper-skeleton/paper_skeleton.py`, stdlib only.

```bash
./paper_skeleton.py --arxiv 1804.06689 -o skeleton.md
./paper_skeleton.py --src main.tex -o skeleton.md --json items.json
```

Produces the fidelity-table skeleton: every numbered result with its
label, printed number, page and printed statement, plus an empty
divergence log. It **compiles the document** and reads numbers from the
`.aux`, statements from the PDF via `pdftotext -raw`, and section titles
from the `.aux` table of contents.

Two things it will tell you that matter:

* **how many items are in an appendix** — read them before scoping any
  proof;
* **which items have no `\label`** — marked *(no own label; number
  inferred)*. These are the ones a hand count silently skips.

**Cite by label, never by number.** A paper's arXiv source and its
journal version number the same results differently: `lemma:lhs` is
*Lemma 1* in the arXiv source of arXiv:1804.06689 and *3.4* in the
journal version. Only the label identifies a result across versions.

## `#rules` — Stage 2

`Meta/Rules.lean`. Prints an indexed inductive family's constructors as
inference figures, classifying each binder **by type**: a binder whose
type ends in an application of the family (possibly under `∀`) is a
premise, any other `Prop` is a side condition, an explicit binder that is
neither is data the rule names, implicit data binders are schematic and
left implicit.

```lean
import Meta.Rules
#rules FRJ.FRJi
```

```
impInI
    FRJi G St (nf G (Th ++ Lam)) B
    ───────────────────────────────────────────
    FRJi G (nf G (St ++ Lam)) (nf G Th) (A.imp B)
    if   cap Th Lam = []
         Clo (nf G (St ++ Lam)) A
         A.imp B ∈ sfR G
```

Compare that against the paper's figure line by line. It is also the
right thing to paste when asking Matthew to sign off a rule *before* it
is built on — which is a standing request, not a courtesy.

It renders what the constructor *says*, so content hidden inside a
definition (`joinCtxAt stab th rhs F`) shows as the definition's name.
Reading that still takes a second step.

## `#choice_path` — Stage 3

`Meta/Audit.lean`.

```lean
#choice_path myTheorem      -- shortest chain to Classical.choice, with modules
#choice_sources myTheorem   -- which direct dependencies are tainted
#axiom_path sorryAx thm     -- any axiom
#axiom_pin myTheorem        -- emit the #guard_msgs block, ready to paste
```

`#choice_path` answers *why*, which `#print axioms` does not:

```
'FRJ.frj_iff_not_IPL' reaches 'Classical.choice' by:
  0. FRJ.frj_iff_not_IPL   [«this file»]
  1. not_not               [Mathlib.Logic.Basic]
  2. Classical.propDecidable [Init.Classical]
  3. Classical.choice      [Init.Prelude]
```

Read the module column: where the names stop being yours is where the
axiom enters from the library.

**Use `#axiom_pin` to generate pins; never retype them.** A transcription
slip in a pin is a silent hole in the machine-checked mandate.

Do not guess at a dirty pin. Twice in one campaign the choice was in a
tool rather than an argument, and the guess was wrong both times.


---

## `#deslime` — computed indices in constructor return types

    import Meta
    #deslime FRJ.FRJr FRJ.FRJi

Defined in `Meta/Deslime.lean` (imports `Lean` only). Reports, per
constructor of an indexed inductive family, which indices of its
**conclusion** are computed and which head symbol computes them; lists
the clean constructors by name. Warns when anything is slimed, `logInfo`
otherwise. It never fails a build.

**Run it at stage 2, before proving anything over the family.** A slimed
family cannot be case-analysed, so every later proof is fought across
transports the unifier will not discharge — and the usual response is to
bend the statement until the computed forms coincide, which is a fidelity
failure invisible to a green build.

Run a **control** first — a family you already believe clean, e.g.
`PLLND.LaxND` (0 of 12). A checker that flags everything tells you
nothing. `Nat` offsets (`n + 1`) are inert by design, so height-indexed
families come out clean.

Full rationale, the fix, and the repo-wide census: `green-slime.md`.
