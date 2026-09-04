import Verso
import VersoManual
import VersoBlueprint
-- The import runs ONE WAY.  This chapter imports the development; no file of
-- the development imports verso.  That is what keeps verso out of the
-- ordinary build graph, and it is why (lean := "...") below can render each
-- declaration's own docstring without putting @[blueprint] attributes into
-- LaxLogic/.
import LaxLogic.PLLFormula
import LaxLogic.PLLProof
import LaxLogic.PLLNDCore
import LaxLogic.PLLKripke
import LaxLogic.PLLCompleteness

/-!
VERSO CHEAT SHEET — everything used in this file, and nothing else.

  #doc (Manual) "Title" =>      starts the document.  Everything after is
                                markup, not Lean, until the file ends.

  :::group "label"              a heading-level grouping for nodes.  Purely
  prose                         structural: it does NOT affect proof status
  :::                           or dependency edges.

  :::definition "label" (...)   a blueprint node.  Also :::theorem,
  prose                         :::proposition, :::lemma, :::corollary.
  :::                           The label is the identity — pick it once and
                                keep it; everything else is cheap to change.

  :::proof "label"              attaches a proof body to the node with that
  prose                         label.  Optional.
  :::

  Options inside the (...) of a node:
    (parent := "group_label")   which group it belongs to
    (lean := "A.B.c")           attach a Lean declaration.  Comma-separated
                                for several.  THIS is what makes the status
                                derived from the compiler instead of claimed.
    (uses := "l1, l2")          dependency edges without prose references
    (tags := "a, b")            free-form labels shown as chips
    (effort := "small")         small | medium | large only.  There is
                                deliberately no "done": effort is an
                                estimate, status comes from the code.

  In prose:
    {uses "label"}[]            a reference that ADDS a dependency edge.
                                Empty [] means "generate the text for me".
    {bpref "label"}[]           a link with NO dependency edge.
    {docstring A.B.c}           renders the declaration in full: signature,
                                docstring, fields/constructors.  You will
                                RARELY want this: (lean := "...") on the node
                                already does all of it.  Using both duplicates
                                the whole block.
    $`x + y`                    inline maths (KaTeX).
    $$`\frac{a}{b}`             display maths.
    *bold*  _emphasis_          NOTE: single asterisk.  `**bold**` is an error.

  Render (publishes nothing):   ./scripts/ci-pages.sh
  Add --pdf for a PDF.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The PLL development" =>

A walk through the core of the mechanisation, from syntax to completeness.
Each node names a real declaration, so its status is read off the compiler.

# Syntax

:::group "syntax"
The object language.
:::

:::definition "formula" (parent := "syntax") (lean := "PLLFormula")
TODO — say what the formula type is.
:::

`(lean := "PLLFormula")` above already renders the declaration: its kind,
its file, its status chip, its signature, its constructors, and its docstring
if it has one.  A separate `{docstring PLLFormula}` would repeat all of that,
so this chapter does not use one.

`PLLFormula` happens to have no docstring, so the rendered block shows the
signature and the six constructors with no prose above them.  That is the
undocumented case, and the build says so:

    warning: 'PLLFormula' is not documented.

A warning, not an error — the build passes.  Documenting the *type* is worth
doing; documenting every constructor is usually not, since `and`, `or` and
`ifThen` are self-explanatory to anyone in the field.  If the warnings become
noise, `set_option verso.docstring.allowMissing true` at the top of this file
silences them.

(An explicit `{docstring X}` on an undocumented `X` is an ERROR rather than a
warning.  That is the only reason this file once needed the option.)

# Natural deduction

:::group "nd"
The proof system.
:::

:::definition "laxnd" (parent := "nd") (lean := "PLLND.LaxND")
TODO.
:::


:::definition "iplnd" (parent := "nd") (lean := "PLLND.IPLND")
TODO — the intuitionistic fragment, for comparison.
:::


:::definition "erase" (parent := "nd") (lean := "PLLND.erase, PLLND.isIPL")
TODO — erasing the modality, and the predicate for being modality-free.
:::


:::theorem "conservativity" (parent := "nd") (lean := "PLLND.conservativity")
TODO.  Depends on {uses "laxnd"}[] and {uses "erase"}[].
:::


# Semantics

:::group "sem"
Constraint models, after Fairtlough and Mendler.
:::

:::definition "model" (parent := "sem") (lean := "PLLND.ConstraintModel")
TODO.
:::


:::definition "force" (parent := "sem") (lean := "PLLND.ConstraintModel.force")
TODO — the forcing relation.  Interprets {uses "formula"}[] in
{uses "model"}[].
:::


:::theorem "force_hered" (parent := "sem") (lean := "PLLND.ConstraintModel.force_hered")
TODO — heredity.
:::


:::definition "consequence" (parent := "sem") (lean := "PLLND.Consequence")
TODO — semantic consequence.
:::


:::theorem "soundness" (parent := "sem") (lean := "PLLND.soundness")
TODO.  Depends on {uses "laxnd"}[] and {uses "force"}[].
:::


# Completeness

:::group "compl"
The canonical model construction.
:::

:::definition "maxconsistent" (parent := "compl") (lean := "PLLND.MaxConsistent")
TODO.
:::


:::definition "canonical" (parent := "compl") (lean := "PLLND.canonical")
TODO — the canonical model.  Built from {uses "maxconsistent"}[], and is a
{uses "model"}[].
:::


:::theorem "truth_lemma" (parent := "compl") (lean := "PLLND.truth_lemma")
TODO.  Depends on {uses "canonical"}[].
:::


:::theorem "completeness" (parent := "compl") (lean := "PLLND.completeness")
TODO.  Depends on {uses "truth_lemma"}[].
:::


:::theorem "adequacy" (parent := "compl") (lean := "PLLND.valid_iff_provable")
TODO — soundness and completeness together.  Depends on
{uses "soundness"}[] and {uses "completeness"}[].
:::


# Proof objects

:::group "proofobj"
Proofs as data.
:::

:::definition "pllproof" (parent := "proofobj") (lean := "PLLProof")
TODO.  A second undocumented declaration, kept so you can watch the
warnings disappear as you write the docstrings.
:::

