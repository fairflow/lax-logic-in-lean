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

  In prose INSIDE A NODE.  Not in a chapter's preamble: outside a node
  these fail the build with "uses declaration outside an informal
  enviroment" (sic).  In preamble text, name the node in words.
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
    *bold*  _emphasis_          NOTE: single asterisk.  Doubling them is
                                an error.

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
The type of PLL formulae in long form
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
Natural deduction style lax proofs as an inductive type
:::


:::definition "iplnd" (parent := "nd") (lean := "PLLND.IPLND")
The intuitionistic fragment, defined here as an inductive proposition
:::


:::definition "erase" (parent := "nd") (lean := "PLLND.erase, PLLND.isIPL")
Erases the modality, and adds the predicate for being modality-free.
:::


:::theorem "conservativity" (parent := "nd") (lean := "PLLND.conservativity")
PLL is conservative over IPL: a modality-free formula is provable in the lax
system exactly when it is provable intuitionistically.  So the modality adds
expressive power without adding theorems in the old language — which is the
minimum any proposed modality must clear.  Depends on {uses "laxnd"}[] and
{uses "erase"}[].
:::


# Semantics

:::group "sem"
Constraint models, after Fairtlough and Mendler.
:::

:::definition "model" (parent := "sem") (lean := "PLLND.ConstraintModel")
Fairtlough–Mendler constraint models: an intuitionistic frame carrying a
second, modal accessibility relation and a set of *fallible* worlds.  The
fallible worlds are the departure from ordinary Kripke semantics, and they
are what let `◯⊥` be satisfiable without collapsing the model.
:::


:::definition "force" (parent := "sem") (lean := "PLLND.ConstraintModel.force")
Forcing: the interpretation of {uses "formula"}[] in {uses "model"}[].  The
`◯` clause is the one to read carefully — `w ⊩ ◯A` asks for `A` at every
modally reachable world, so the modality quantifies over *constraints*, not
over time or knowledge.
:::


:::theorem "force_hered" (parent := "sem") (lean := "PLLND.ConstraintModel.force_hered")
Heredity: forcing is preserved upwards along the intuitionistic order.  The
standard Kripke condition, and the reason the valuation carries its own
monotonicity requirement.
:::


:::definition "consequence" (parent := "sem") (lean := "PLLND.Consequence")
Semantic consequence.
:::


:::theorem "soundness" (parent := "sem") (lean := "PLLND.soundness")
Soundness: everything derivable is valid.  The easy direction, proved by
induction on the derivation.  Depends on {uses "laxnd"}[] and
{uses "force"}[].
:::


# Completeness

:::group "compl"
The canonical model construction.
:::

:::definition "maxconsistent" (parent := "compl") (lean := "PLLND.MaxConsistent")
Maximal consistent theories, obtained by Zorn.  Consistency here carries a
nonemptiness guard on the finite choices, and that guard is doing real work:
it is what makes the theory of *all* formulas consistent, and so — after
extension — maximally consistent.  That theory is the single fallible world
of {uses "canonical"}[].
:::


:::definition "canonical" (parent := "compl") (lean := "PLLND.canonical")
The canonical model, built from {uses "maxconsistent"}[] and shown to be a
{uses "model"}[].  Worlds are theories — triples of formulas validated,
falsified, and falsified at every modal successor — and the third component
is what the modality needs and what an ordinary intuitionistic canonical
model does not have.
:::


:::theorem "truth_lemma" (parent := "compl") (lean := "PLLND.truth_lemma")
The truth lemma: in {uses "canonical"}[], a formula is forced at a theory
exactly when the theory validates it.  The technical heart of the
construction.  Depends on {uses "canonical"}[].
:::


:::theorem "completeness" (parent := "compl") (lean := "PLLND.completeness")
Completeness: everything valid is derivable.  Depends on
{uses "truth_lemma"}[] — and, unavoidably on this route, on choice; see
{uses "completeness_twice"}[].
:::


:::proposition "completeness_twice" (parent := "compl")
Completeness is proved *twice*, by routes with different logical
strength, and the difference is machine-checked rather than asserted:

* `PLLND.completeness` — `[propext, Classical.choice, Quot.sound]`
* `FRJ.Gbu.W.PLL_iff_laxND` — `[propext, Quot.sound]`
* `FRJ.Gbu.W.decideLaxND` — `[propext, Quot.sound]`

The canonical-model route above uses choice, at the maximal-consistent
extension ({uses "maxconsistent"}[], via Zorn).  The Gbu◯/FRJW dichotomy
route does not: for every formula it returns either a PLL proof or a PLL
disproof carrying a countermodel, and that single construction yields
completeness, decidability and the finite poset model property together.

So Zorn is not ultimately needed.  The constructive route is the decision
procedure, and it is developed in its own chapter; this node exists to
point forward to it, because a reader meeting {uses "completeness"}[] here
should not be left thinking choice is essential to it.
:::

:::theorem "adequacy" (parent := "compl") (lean := "PLLND.valid_iff_provable")
Adequacy: derivability and validity coincide.  Depends on
{uses "soundness"}[] and {uses "completeness"}[].
:::


# Proof objects

:::group "proofobj"
Proofs as data.
:::

:::definition "pllproof" (parent := "proofobj") (lean := "PLLProof")
Proofs as explicit data, with their own validity predicate — a different
representation from {uses "laxnd"}[], kept for the parts of the development
that need to compute with proofs rather than induct over them.

It is load-bearing for exactly one theorem and superseded everywhere else.
`PLLHilbert.lean` states the Hilbert system as a checker over explicit
proof lists (`PLLProof.isValid`) and proves `hilbert_to_ND`, that a valid
Hilbert proof of `φ` yields a natural-deduction derivation; that is the only
module importing `PLLProof`, and the only place the explicit lists are
computed with.  Every other part of the development that needs proofs as
data uses the term calculus, whose terms are the derivations themselves
with their reduction theory.  The representation is therefore kept as the
Hilbert-side interface, not as a second proof format, and it would retire
with a restatement of the Hilbert system over terms.
:::

