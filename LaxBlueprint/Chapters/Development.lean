import Verso
import VersoManual
import VersoBlueprint
-- The import runs ONE WAY.  This chapter imports the development; no file of
-- the development imports verso.  That is what keeps verso out of the
-- ordinary build graph, and it is why {docstring ...} below works without
-- putting @[blueprint] attributes into LaxLogic/.
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
    {docstring A.B.c}           pull that declaration's own docstring in,
                                verbatim, rendered from Markdown.
    $`x + y`                    inline maths (KaTeX).
    $$`\frac{a}{b}`             display maths.
    *bold*  _emphasis_          NOTE: single asterisk.  `**bold**` is an error.

  Render (publishes nothing):   ./scripts/ci-pages.sh
  Add --pdf for a PDF.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- REQUIRED while the core is undocumented.  {docstring X} reports a missing
-- docstring on X, or on any of its constructors/fields, as an ERROR by
-- default, so without this the chapter does not build.  Flip to `false`
-- (or delete the line) once the declarations below are documented: that
-- turns the blueprint into a gate that keeps them documented.
set_option verso.docstring.allowMissing true

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

Below is the *undocumented* case you asked about.  `PLLFormula` has no
docstring.  By default that is a build ERROR, not a warning, and it is
reported for the declaration AND for each of its constructors — which is why
this file sets `verso.docstring.allowMissing` above.  With that set, the
command below reports each missing docstring as a warning and renders the
signature with no prose body:

{docstring PLLFormula}

Three ways to respond, in the order I would try them:

1. *Write the docstring on the declaration.*  Add `/-- … -/` above
   `inductive PLLFormula` in `LaxLogic/PLLFormula.lean`.  The text then lives
   with the definition and appears here automatically.  This is the point of
   the exercise, and it is why the warning is useful rather than noise.
2. *Write the prose in the node instead*, in the `:::definition` body above,
   and delete the `{docstring …}` line.  Fine when the remark is about the
   blueprint's narrative rather than about the declaration.
3. *Leave the option as it is* (`allowMissing := true`, set at the top of
   this file) while the core is undocumented, then delete that line once it
   is.  The default is strict, so removing the line turns the blueprint into
   a gate: an undocumented core declaration then fails the build.

# Natural deduction

:::group "nd"
The proof system.
:::

:::definition "laxnd" (parent := "nd") (lean := "PLLND.LaxND")
TODO.
:::

{docstring PLLND.LaxND}

:::definition "iplnd" (parent := "nd") (lean := "PLLND.IPLND")
TODO — the intuitionistic fragment, for comparison.
:::

{docstring PLLND.IPLND}

:::definition "erase" (parent := "nd") (lean := "PLLND.erase, PLLND.isIPL")
TODO — erasing the modality, and the predicate for being modality-free.
:::

{docstring PLLND.erase}

:::theorem "conservativity" (parent := "nd") (lean := "PLLND.conservativity")
TODO.  Depends on {uses "laxnd"}[] and {uses "erase"}[].
:::

{docstring PLLND.conservativity}

# Semantics

:::group "sem"
Constraint models, after Fairtlough and Mendler.
:::

:::definition "model" (parent := "sem") (lean := "PLLND.ConstraintModel")
TODO.
:::

{docstring PLLND.ConstraintModel}

:::definition "force" (parent := "sem") (lean := "PLLND.ConstraintModel.force")
TODO — the forcing relation.  Interprets {uses "formula"}[] in
{uses "model"}[].
:::

{docstring PLLND.ConstraintModel.force}

:::theorem "force_hered" (parent := "sem") (lean := "PLLND.ConstraintModel.force_hered")
TODO — heredity.
:::

{docstring PLLND.ConstraintModel.force_hered}

:::definition "consequence" (parent := "sem") (lean := "PLLND.Consequence")
TODO — semantic consequence.
:::

{docstring PLLND.Consequence}

:::theorem "soundness" (parent := "sem") (lean := "PLLND.soundness")
TODO.  Depends on {uses "laxnd"}[] and {uses "force"}[].
:::

{docstring PLLND.soundness}

# Completeness

:::group "compl"
The canonical model construction.
:::

:::definition "maxconsistent" (parent := "compl") (lean := "PLLND.MaxConsistent")
TODO.
:::

{docstring PLLND.MaxConsistent}

:::definition "canonical" (parent := "compl") (lean := "PLLND.canonical")
TODO — the canonical model.  Built from {uses "maxconsistent"}[], and is a
{uses "model"}[].
:::

{docstring PLLND.canonical}

:::theorem "truth_lemma" (parent := "compl") (lean := "PLLND.truth_lemma")
TODO.  Depends on {uses "canonical"}[].
:::

{docstring PLLND.truth_lemma}

:::theorem "completeness" (parent := "compl") (lean := "PLLND.completeness")
TODO.  Depends on {uses "truth_lemma"}[].
:::

{docstring PLLND.completeness}

:::theorem "adequacy" (parent := "compl") (lean := "PLLND.valid_iff_provable")
TODO — soundness and completeness together.  Depends on
{uses "soundness"}[] and {uses "completeness"}[].
:::

{docstring PLLND.valid_iff_provable}

# Proof objects

:::group "proofobj"
Proofs as data.
:::

:::definition "pllproof" (parent := "proofobj") (lean := "PLLProof")
TODO.  A second undocumented declaration, kept so you can watch the
warnings disappear as you write the docstrings.
:::

{docstring PLLProof}
