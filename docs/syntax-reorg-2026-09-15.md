# Syntax and layout: tagged turnstiles, and the reorganised `LaxLogic/`

Branch `syntax-reorg`, 2026-09-15.  Matthew's brief: "design a new syntactic
approach using true argument [tag] notation getting rid of ⊢- and ⊨-, … and
reorganise the directories and files", plus "when unambiguous simple ⊢ and ⊨
with ⊬ and ⊭".  This records what was decided, what was rejected and why, and
what is deliberately left for a later step.

## 1. The problems (from the 2026-09-15 discussion)

1. One glyph per relation, disambiguated by suffix characters: `⊢-` (PLL ND),
   `⊨-` (PLL Kripke consequence), `⊢q` (QLL), `⊩q` (QLL, set contexts), `⊫`
   (QLL consequence), `⊢qll p : A` (QLL proof terms).  Letters in a token read
   as variables (`Γ ⊢q ◯_q A` has two unrelated q's); `-` reads as minus.
2. The same kind of relation gets different glyphs in different developments
   (`⊨-` against `⊫`), and the typeset paper mistook `⊫` for `⊩`.
3. Scoping alone does not separate relations that meet in one section.
4. The infoview (level 0), Lean notation (1b) and typeset mathematics (3)
   should agree, with the symbol chosen once.

## 2. The design: the tag is the relation

    Γ ⊢[R] A     :=  R Γ A                derivability in the calculus R
    Γ ⊨[R] A     :=  R Γ A                semantic consequence R
    Γ ⊬[R] A     :=  ¬ R Γ A              if R Γ A : Prop
                     ¬ Nonempty (R Γ A)   if R Γ A : Type   (derivations as data)
    Γ ⊭[R] A     :   likewise
    Γ ⊢ A, Γ ⊨ A, Γ ⊬ A, Γ ⊭ A              the default relation of the open scope

`R` is an ordinary Lean term: the inductive or definition of the calculus,
possibly partially applied (`Γ ⊢[G4h n] C` is `G4h n Γ C`).  Hence:

* theorems can quantify over calculi: `∀ R, … Γ ⊢[R] A …`;
* constants and variables share one syntax;
* hovering the tag in the infoview shows the calculus, go-to-definition works;
* a new calculus needs no new glyph and no registration beyond one attribute.

Infrastructure: `LaxLogic/Util/Turnstile.lean` (Lean core only).

    attribute [turnstile] LaxND                      -- register (global), derivability
    attribute [turnstile consequence] Consequence    -- register, semantic
    attribute [scoped turnstile_default] LaxND       -- plain ⊢ inside this namespace

**Plain symbols, when unambiguous.**  `Γ ⊢ A` elaborates to the in-scope
default of that kind.  With several in scope (PLL and QLL both open; a list
and a set context in QLL) the one whose context type, then formula type, fits
is taken; if none or several fit, elaboration fails and asks for a tag.

**Printing.**  An application of a registered relation prints as `Γ ⊢ A` when
the relation is an in-scope default and no other in-scope default of the same
kind has the same type, otherwise as `Γ ⊢[R] A` (the tag printed as Lean
prints the constant, so short when its namespace is open).  `¬ R Γ A` and
`¬ Nonempty (R Γ A)` print with `⊬`/`⊭` under the same rule, but only in the
form matching the relation's sort.

**Precedence** (first version) 55, both sides 56.  Superseded the same day by
§2.1, which lowers a sequent to 26 so that formulas need no parentheses.

### 2.1 Sequent-style contexts and PLL formula notation

Matthew: "build the formula category, PLL first, with sequent-style
contexts"; "sequents are great without :: and Γ, A for A :: Γ is indeed
conventional and convenient both sides"; "we don't have to use ⊃ … Use a
double headed arrow of some kind please instead."

**Contexts.**

    Γ, A, B ⊢ C    is  B :: A :: Γ ⊢ C              (list context)
                   is  insert B (insert A Γ) ⊢ C     (set context)
    A, B ⊢ C       is  [A, B] ⊢ C  (no context variable)
    ⊢ C            is  [] ⊢ C  (or ∅)
    A :: Γ ⊢ C, Γ ++ Δ ⊢ C, [p, q] ⊢ C, insert A S ⊢ C   still accepted

Printing uses the same forms: `LaxND (p :: Γ) q` prints `Γ, p ⊢ q`.  An
empty context prints as `⊢ C` only when no other in-scope default could read
it; with `LaxND` and `SetDeriv` both defaults in `PLLND` it prints `[] ⊢ C`.

**Formulas** (PLL, scoped in `PLLND`, `LaxLogic/PLL/Syntax/Formula.lean`):

| notation | constructor | precedence |
|---|---|---|
| `◯A` | `somehow` | prefix, max |
| `A ∧ B` | `and` | 35, right |
| `A ∨ B` | `or` | 30, right |
| `A ↠ B` | `ifThen` | 27, right |
| `⊥` | `falsePLL` | atom |

The notation is the same inside and outside a sequent, so no quotation
brackets are needed.

`∧`, `∨` and `⊥` keep the tokens and precedences of Lean's `And`/`Or` and
Mathlib's `Bot.bot`, and are **not** overloaded notations.  The first version
declared them as scoped notations, which makes every use a choice between two
parses, and Lean elaborates such alternatives one by one without postponement.
Two failures followed in the library build: `a[i]!.val ⊆ b[j]!.val ∧ …`
inside an `if` was reported ambiguous (both alternatives elaborate while the
operand types are unknown, `PLL/Semantics/FinComp.lean`), and in
`x ⊓ xᶜ = ⊥` the formula `⊥` was chosen (the leaves of `=` are elaborated
without an expected type, `PLL/Semantics/CtxCompleteness.lean`).  The design
now: inside `PLLND`, a scoped macro sends `∧`, `∨`, `⊥` to one elaborator
that waits for the expected type if it is not yet known, takes the formula
connective when the expected type is `PLLFormula`, or, with no expected type
at all, when the left operand elaborates to a formula, and otherwise
elaborates `And`, `Or` or `Bot.bot` exactly as before.  Printing uses
unexpanders to the same tokens.

**Why these precedences.**  A sequent is 26, its context side 56, its formula
side and every context entry after a comma 27.  The formula side must be
parsed at a precedence at or below `↠` (27) so that `Γ ⊢ A ↠ B` needs no
parentheses, and the sequent's own precedence must be below that, or a context
entry `p ↠ q` would absorb a following `⊢`: with the sequent at 55,
`Γ, p ↠ q ⊢ r` parses as `Γ, p ↠ (q ⊢ r)`.  `→` (25) and `↔` (20) stay
outside: `Γ ⊢ A → Γ, A ⊢ B` is an implication between sequents.

**Binders.**  In `∀ x : T, Γ ⊢ A` and `∀ φ ∈ Ds, Γ, φ ⊢ χ` the comma belongs
to the binder, but a parser for `Γ, A ⊢ B` alone reads `T, Γ ⊢ A` as one
sequent (observed in the first build: `LaxLogic/PLL/ND/Theorems.lean`, line
159, "unexpected token '|'; expected ','").  So the identifier that opens a
comma context goes through a zero-width check, `Guard.ctxIdent`, that reads
the characters before it and refuses when it is the type of an unbracketed
binder (`∀ ∃ Σ Π ∑ ∏ ⋃ ⋂ ⨆ ⨅ λ`, names, `:`) or the right side of a binder
predicate (`∈ ∉ ⊆ ⊂ ⊇ ⊃ ≤ < ≥ > ≠`).  A hypothesis `(h : Γ, p ⊢ q)`, a
statement `theorem t : Γ, p ⊢ q` and `have h : Γ, p ⊢ q` are unaffected.

**Remaining cost of the low precedence** (each an error, never a silent
misparse):

* a sequent next to a `Prop` connective tighter than `→` is parenthesised:
  `P ∧ (Γ ⊢ A)`, `P ∨ (Γ ⊬ A)`, `(Γ ⊢ A) ∧ P`;
* `¬ Γ ⊢ A` does not parse as `¬ (Γ ⊢ A)`; write `Γ ⊬ A`;
* the first entry before a comma is an identifier, so `◯p, q ⊢ r` is written
  `Γ, ◯p, q ⊢ r` or `[◯p, q] ⊢ r`;
* a context with no context variable is ambiguous when a list and a set
  default are both in scope (`p, q ⊢ r` in `PLLND`); write `[p, q] ⊢ r` or
  a tag.

**Elaboration detail.**  Each candidate default is elaborated with error
recovery switched off and no coercions: otherwise a failed candidate
(`insert φ Γ` at a list type when `Γ` is a set) elaborates to `sorry` and
counts as a fit, and `⊢` is reported ambiguous.  That was the first build's
failure in `LaxLogic/PLL/ND/Consequence.lean` and `LaxLogic/QLL/Complete.lean`.

**Not yet done** (after §2.1): QLL formula notation, done in §2.2; the QLL
proof-term judgement `Γ ⊢qll p : A`.

### 2.2 QLL formula notation: modalities and quantifiers

Matthew: "now do QLL: ◯[q], ◯[∀], ◯[∃] and quantifiers"; earlier, "the
modalities: ◯[q], ◯[∀], ◯[∃] if those are possible otherwise ◯[A] and ◯[E]".
All three are possible.  `LaxLogic/QLL/Notation.lean`, scoped to
`LaxLogic.QLL`:

| notation | formula |
|---|---|
| `◯[∀] A`, `◯[∃] A` | `.circ .all A`, `.circ .ex A` |
| `◯[q] A` | `.circ q A`, `q : Q` a variable |
| `A ∧ B`, `A ∨ B`, `A ↠ B` | `.and`, `.or`, `.imp` |
| `⊥`, `⊤` | `.bot`, `.top` (with `LaxLogic.QLL.NotationOrder`) |
| `∀' A`, `∃' A` | `.forall_ A`, `.exists_ A`, `A` a de Bruijn body |
| `∀ x, A`, `∃ x, A` | `.forall_ (A.closeWith "x")`, `x : Tm` standing for `.fvar "x"` |

Examples, pinned in `LaxLogic/Util/TurnstileTests.lean`:

    Γ, ◯[∀] A ⊢ ◯[∃] A ∨ B          -- Prv (.circ .all A :: Γ) (.or (.circ .ex A) B)
    Γ ⊢ ∀' A → Γ ⊢ ∃' A
    ∀ x, Form.pred "P" [x] ↠ ◯[∃] (Form.pred "Q" [x])

**Two quantifier forms, because the development has two uses.**  The
metatheory quantifies over bodies: `Prv Γ (.forall_ A) → Prv Γ (A.openAt 0 t)`.
There `∀' A` is the direct reading, and it is Mathlib's notation for the de
Bruijn quantifiers of first-order `BoundedFormula`.  Concrete formulas want
names: `∀ x, A` elaborates `A` with a Lean variable `x : Tm`, replaces it by
`.fvar "x"`, and closes over that name, which is the mathematical meaning of
`∀x.A` (a free `x` in `A` becomes bound).  The CLP paper's generator prints
`.forall_ A` as `∀x. A`, which is the body reading with a chosen name; the Lean
notation keeps the two apart.

**Printing.**  `.forall_ (A.closeWith "x")` prints `∀ x, A`.  A body built only
from constructors, literals and bound individuals is opened with the first
name of `x y z x1 …` not already in it and prints the same way; the printed
term elaborates to one that is definitionally equal (`closeWith` computes the
body back).  Every other body prints `∀' A`.

**Shared connectives.**  With both `PLLND` and `LaxLogic.QLL` open, two scoped
notations for `↠` would again be overloaded.  So `∧ ∨ ↠ ⊥ ⊤` moved to one
module, `LaxLogic/Util/Connectives.lean`: `↠` is its syntax, and each
development registers its constructors with a scoped attribute,
`attribute [scoped connective imp] Form.imp`.  One elaborator per connective
picks the constructor of the formula type that is expected, or, with no
expected type, of the left operand's type; printing is one delaborator driven
by the same registry.  PLL's notation from §2.1 now uses it too; its pins are
unchanged.

**Named quantifiers and Lean's `∀`.**  Inside `LaxLogic.QLL` a scoped macro sends
`∀ x, b` and `∃ x, b` (one untyped binder) to an elaborator that builds the
formula only when the expected type is `Form`, and otherwise elaborates Lean's
own `∀` (calling the built-in elaborator, so the macro does not fire again) or
Lean's own expansion `Exists fun x => b`.  A first attempt fell back to
`∀ (x : _), b`: the explicit hole behaves differently from an omitted binder
type in a declaration header, and `example : ∃ n, n = 3` failed.

**`⊥` and `⊤`.**  The QLL core imports no Mathlib, and a second `⊥` syntax
beside Mathlib's would be ambiguous wherever both are loaded (Lean does not
merge overloaded alternatives that elaborate to the same term).  So `⊥ ⊤` for
QLL live in `LaxLogic/QLL/NotationOrder.lean`, which imports
`Mathlib.Order.Notation`; `LaxLogic/QLL/Complete.lean` imports it.  In the
Mathlib-free core, `.bot` and `.top` are written as constructors and print as
such.

**Where the notation is active.**  `LaxLogic/QLL/Lc.lean` and
`LaxLogic/QLL/Deriv.lean` import `Notation`, so every QLL module downstream of
either has it; `Syntax`, `Surface`, `Interp`, `Size`, `Countable` and `LinQ`
import only `Syntax` and do not.

**Not changed.**  `Surface.lean`'s own category `qf[…]` still writes `◯∀`,
`◯∃` and `⊃` in its input and in `render`.  Aligning it (`◯[∀]`, `↠`) would
change the strings it renders, which `SurfaceTests.lean`, `Judgement.lean`,
`CLP.lean`, `CLPCertify.lean` and `CLPExamples.lean` use; it is left as a
separate step.  `Form.pred "P" [x]` has no notation.

### Rejected alternatives

| alternative | why not |
|---|---|
| a glyph per relation (status quo) | problems 1–2 |
| notation-only labels, `⊢[ND]` as a fixed token | labels inside tokens again; no quantification over calculi; nothing to hover |
| an enumeration of calculi + a class `Turnstile (t : Calculus) Ctx Fm` | tag names clash with existing declarations (`SC` is the sequent calculus's inductive); context and formula types differ across calculi, so the class needs out-params that fight elaboration of `[] ⊢ A`; an instance per calculus; statements elaborate to `Turnstile.rel t Γ A`, not the calculus, so existing lemmas stop matching syntactically |
| scoped plain notations per development (`scoped infix " ⊢ " => Prv`) | each is a distinct syntax kind, so printing `⊬` generically is impossible and the two scopes open together overload unpredictably |

## 3. What was converted

| before | relation | after | default in |
|---|---|---|---|
| `Γ ⊢- A` | `PLLND.LaxND` (Type) | `Γ ⊢ A` | `PLLND` |
| `Γ ⊨- A` | `PLLND.Consequence` | `Γ ⊨ A` | `PLLND` |
| `Γ ⊢q A` | `LaxLogic.QLL.Prv` | `Γ ⊢ A` | `LaxLogic.QLL` |
| `Γ ⊩q A` | `LaxLogic.QLL.SetPrv` (Set context) | `Γ ⊢ A` | `LaxLogic.QLL` |
| `Γ ⊫ A` | `LaxLogic.QLL.Consequence` | `Γ ⊨ A` | `LaxLogic.QLL` |
| `Γ ⊩ φ` | `PLLND.SetDeriv` (Set context) | `Γ ⊢ φ` | `PLLND` |

The search commands (`#search`, `#refute`, `#refuteConf`, `#searchNF`,
`#refuteNF`, `#pinsrc`, `#draw`) parse `Γ ⊢ C` themselves; their context
argument is now parsed at precedence 56 so that it stops at the turnstile.

## 4. Deliberately not converted (next steps)

* (Done in a follow-up commit: PLL `SetDeriv` is plain `⊢` on a set context,
  like QLL's `SetPrv`.  Only its 137 uses in Lean code were rewritten; the other
  `⊩` in comments and printed countermodels are forcing and stay.)
* `Γ ⊢qll p : A` (QLL proof-term judgement): a three-place judgement wants its
  own form, `Γ ⊢[R] p : A`.
* Realisability `x ⊩ᵘ[Ev, w] φ` and friends: already bracketed and scoped.
* Other calculi (`SC`, `G4c`, `G4h`, `LJF`, …) are not registered yet, so they
  still print as applications.  Registering one is one attribute line, and it
  changes their printed form in `#guard_msgs` outputs.
* A variable tag (`R : List F → F → Prop` in a generic theorem) prints as `R Γ A`:
  printing recognises registered constants only.
* The Toolkit challenge corpus (`LaxLogic/ToolkitTest/Challenge/`) keeps its own
  private `⊬`: those files are frozen restatements for prover evaluation.
* The modality notation (`◯∃`/`◯∀`, the ⊕/⊗ proposal) and the typeset level
  (a registry keyed by constant for the paper generator) are separate decisions.
* Verso documents print plain symbols only if they `open scoped` the
  development; the fully-qualified-name problem is unchanged.

## 5. The directory layout

115 modules moved out of the top level; declaration names and namespaces are
unchanged.  A new module name is the old one without the `PLL`/`Belief`
prefix, under a topic directory, so an old name maps back mechanically.

    LaxLogic/
      Obligation.lean   QLL.lean              umbrellas (unchanged)
      Belief/           9   nuclei and belief (BeliefX, NucleusJoin)
      Focusing/         3   LJF, LJFComplete, IPCFocused
      Obligation/           unchanged
      PLL/
        Syntax/         5   Formula, Axiom, Proof, Polar, FinsetKit
        ND/             9   NDCore, Terms, Subst, Hilbert, Theorems, Consequence, …
        Normalisation/  5   Normal, StrongNorm, Reducibility, TopTop, Confluence
        Semantics/     10   Kripke, Frames, Completeness, CtxCompleteness, FinComp, …
        Realisability/  2   Evidence, RealCompleteness
        Sequent/        3   Sequent, Focused, Craig
        G4/            21   G4, G4P*, G4H* and the termination modules
        UI/            11   G4UI*, UIChains, Cand*, NoFall*
        SemUI/         15   SemUI*
        Search/        13   Search*, Decide, Diagram*, Demos, Exec, Run
        Timing/         6   Timing*, Async, Constraints
      QLL/                  unchanged
      ToolkitTest/          unchanged
      Util/             4   FormattingUtils, GuardMsgsShow, KleeneBrouwer, Turnstile

The move is one commit of pure renames (so git's rename detection carries
other branches' edits to the moved files), then one commit rewriting imports
and path references in `LaxLogic/`, `wip/`, the papers, `tools/`,
`prover-toolkit/`, `scripts/` and `docs/` (`HANDOFF.md` is append-only and gets
this mapping instead).  The mapping is executable: `scripts/reorg-2026-09-15.py`
(`--table` prints it).

## 6. Merging other branches

* Edits another branch made to a moved file follow it to its new path when
  merged (rename detection; the files changed only in their import lines).
* Conflicts arise where the other branch changed an import line, added a new
  top-level module, or used one of the retired glyphs.  For such a branch:
  merge `syntax-reorg` into it, then run
  `scripts/reorg-2026-09-15.py --rewrite` there to fix imports mechanically, and
  replace `⊢- ⊨- ⊢q ⊩q ⊫` by `⊢ ⊨ ⊢ ⊢ ⊨`.
* New top-level modules on other branches are not moved by the script; they
  belong in the table first.

## 7. The mapping

| old module | new module |
|---|---|
| `LaxLogic.BeliefBooleanIso` | `LaxLogic.Belief.BooleanIso` |
| `LaxLogic.BeliefCollapse` | `LaxLogic.Belief.Collapse` |
| `LaxLogic.BeliefExamples` | `LaxLogic.Belief.Examples` |
| `LaxLogic.BeliefFalsum` | `LaxLogic.Belief.Falsum` |
| `LaxLogic.BeliefIdealisation` | `LaxLogic.Belief.Idealisation` |
| `LaxLogic.BeliefNormality` | `LaxLogic.Belief.Normality` |
| `LaxLogic.BeliefOpenClosed` | `LaxLogic.Belief.OpenClosed` |
| `LaxLogic.BeliefRealisability` | `LaxLogic.Belief.Realisability` |
| `LaxLogic.FormattingUtils` | `LaxLogic.Util.FormattingUtils` |
| `LaxLogic.GuardMsgsShow` | `LaxLogic.Util.GuardMsgsShow` |
| `LaxLogic.IPCFocused` | `LaxLogic.Focusing.IPCFocused` |
| `LaxLogic.KleeneBrouwer` | `LaxLogic.Util.KleeneBrouwer` |
| `LaxLogic.LJF` | `LaxLogic.Focusing.LJF` |
| `LaxLogic.LJFComplete` | `LaxLogic.Focusing.LJFComplete` |
| `LaxLogic.NucleusJoin` | `LaxLogic.Belief.NucleusJoin` |
| `LaxLogic.PLLAsync` | `LaxLogic.PLL.Timing.Async` |
| `LaxLogic.PLLAxiom` | `LaxLogic.PLL.Syntax.Axiom` |
| `LaxLogic.PLLCandLeast` | `LaxLogic.PLL.UI.CandLeast` |
| `LaxLogic.PLLCandOr` | `LaxLogic.PLL.UI.CandOr` |
| `LaxLogic.PLLCandidate` | `LaxLogic.PLL.UI.Candidate` |
| `LaxLogic.PLLCompleteness` | `LaxLogic.PLL.Semantics.Completeness` |
| `LaxLogic.PLLConfluence` | `LaxLogic.PLL.Normalisation.Confluence` |
| `LaxLogic.PLLConfluentComplete` | `LaxLogic.PLL.Semantics.ConfluentComplete` |
| `LaxLogic.PLLConsequence` | `LaxLogic.PLL.ND.Consequence` |
| `LaxLogic.PLLConstraints` | `LaxLogic.PLL.Timing.Constraints` |
| `LaxLogic.PLLCountermodel` | `LaxLogic.PLL.Semantics.Countermodel` |
| `LaxLogic.PLLCountermodelEmit` | `LaxLogic.PLL.Semantics.CountermodelEmit` |
| `LaxLogic.PLLCraig` | `LaxLogic.PLL.Sequent.Craig` |
| `LaxLogic.PLLCtxCompleteness` | `LaxLogic.PLL.Semantics.CtxCompleteness` |
| `LaxLogic.PLLDecide` | `LaxLogic.PLL.Search.Decide` |
| `LaxLogic.PLLDemos` | `LaxLogic.PLL.Search.Demos` |
| `LaxLogic.PLLDiagram` | `LaxLogic.PLL.Search.Diagram` |
| `LaxLogic.PLLDiagramCmd` | `LaxLogic.PLL.Search.DiagramCmd` |
| `LaxLogic.PLLEvidence` | `LaxLogic.PLL.Realisability.Evidence` |
| `LaxLogic.PLLExec` | `LaxLogic.PLL.Search.Exec` |
| `LaxLogic.PLLFinComp` | `LaxLogic.PLL.Semantics.FinComp` |
| `LaxLogic.PLLFiniteModel` | `LaxLogic.PLL.Semantics.FiniteModel` |
| `LaxLogic.PLLFinsetKit` | `LaxLogic.PLL.Syntax.FinsetKit` |
| `LaxLogic.PLLFocused` | `LaxLogic.PLL.Sequent.Focused` |
| `LaxLogic.PLLFormula` | `LaxLogic.PLL.Syntax.Formula` |
| `LaxLogic.PLLFrames` | `LaxLogic.PLL.Semantics.Frames` |
| `LaxLogic.PLLG4` | `LaxLogic.PLL.G4.G4` |
| `LaxLogic.PLLG4Adm` | `LaxLogic.PLL.G4.G4Adm` |
| `LaxLogic.PLLG4Dec` | `LaxLogic.PLL.G4.G4Dec` |
| `LaxLogic.PLLG4Gap` | `LaxLogic.PLL.G4.G4Gap` |
| `LaxLogic.PLLG4H` | `LaxLogic.PLL.G4.G4H` |
| `LaxLogic.PLLG4HAdm` | `LaxLogic.PLL.G4.G4HAdm` |
| `LaxLogic.PLLG4HComp` | `LaxLogic.PLL.G4.G4HComp` |
| `LaxLogic.PLLG4HCtr` | `LaxLogic.PLL.G4.G4HCtr` |
| `LaxLogic.PLLG4HCut` | `LaxLogic.PLL.G4.G4HCut` |
| `LaxLogic.PLLG4HInv` | `LaxLogic.PLL.G4.G4HInv` |
| `LaxLogic.PLLG4HStr` | `LaxLogic.PLL.G4.G4HStr` |
| `LaxLogic.PLLG4Inv` | `LaxLogic.PLL.G4.G4Inv` |
| `LaxLogic.PLLG4P` | `LaxLogic.PLL.G4.G4P` |
| `LaxLogic.PLLG4PAdm` | `LaxLogic.PLL.G4.G4PAdm` |
| `LaxLogic.PLLG4PInv` | `LaxLogic.PLL.G4.G4PInv` |
| `LaxLogic.PLLG4PStr` | `LaxLogic.PLL.G4.G4PStr` |
| `LaxLogic.PLLG4Set` | `LaxLogic.PLL.G4.G4Set` |
| `LaxLogic.PLLG4Space` | `LaxLogic.PLL.G4.G4Space` |
| `LaxLogic.PLLG4Term` | `LaxLogic.PLL.G4.G4Term` |
| `LaxLogic.PLLG4Tower` | `LaxLogic.PLL.G4.G4Tower` |
| `LaxLogic.PLLG4UI` | `LaxLogic.PLL.UI.G4UI` |
| `LaxLogic.PLLG4UIAdq` | `LaxLogic.PLL.UI.G4UIAdq` |
| `LaxLogic.PLLG4UIStab` | `LaxLogic.PLL.UI.G4UIStab` |
| `LaxLogic.PLLG4UITrunc` | `LaxLogic.PLL.UI.G4UITrunc` |
| `LaxLogic.PLLG4ipComplete` | `LaxLogic.PLL.G4.G4ipComplete` |
| `LaxLogic.PLLHilbert` | `LaxLogic.PLL.ND.Hilbert` |
| `LaxLogic.PLLIdempotency` | `LaxLogic.PLL.ND.Idempotency` |
| `LaxLogic.PLLJudgmental` | `LaxLogic.PLL.ND.Judgmental` |
| `LaxLogic.PLLKripke` | `LaxLogic.PLL.Semantics.Kripke` |
| `LaxLogic.PLLLaxInfinite` | `LaxLogic.PLL.Semantics.LaxInfinite` |
| `LaxLogic.PLLNDCore` | `LaxLogic.PLL.ND.NDCore` |
| `LaxLogic.PLLNoFall` | `LaxLogic.PLL.UI.NoFall` |
| `LaxLogic.PLLNoFallNF` | `LaxLogic.PLL.UI.NoFallNF` |
| `LaxLogic.PLLNoFallSep` | `LaxLogic.PLL.UI.NoFallSep` |
| `LaxLogic.PLLNormal` | `LaxLogic.PLL.Normalisation.Normal` |
| `LaxLogic.PLLPolar` | `LaxLogic.PLL.Syntax.Polar` |
| `LaxLogic.PLLProof` | `LaxLogic.PLL.Syntax.Proof` |
| `LaxLogic.PLLRealCompleteness` | `LaxLogic.PLL.Realisability.RealCompleteness` |
| `LaxLogic.PLLReducibility` | `LaxLogic.PLL.Normalisation.Reducibility` |
| `LaxLogic.PLLRun` | `LaxLogic.PLL.Search.Run` |
| `LaxLogic.PLLSearch` | `LaxLogic.PLL.Search.Search` |
| `LaxLogic.PLLSearchCmd` | `LaxLogic.PLL.Search.SearchCmd` |
| `LaxLogic.PLLSearchConf` | `LaxLogic.PLL.Search.SearchConf` |
| `LaxLogic.PLLSearchDemo` | `LaxLogic.PLL.Search.SearchDemo` |
| `LaxLogic.PLLSearchEx` | `LaxLogic.PLL.Search.SearchEx` |
| `LaxLogic.PLLSearchNoFall` | `LaxLogic.PLL.Search.SearchNoFall` |
| `LaxLogic.PLLSearchPin` | `LaxLogic.PLL.Search.SearchPin` |
| `LaxLogic.PLLSemUI` | `LaxLogic.PLL.SemUI.SemUI` |
| `LaxLogic.PLLSemUIAdjoin` | `LaxLogic.PLL.SemUI.SemUIAdjoin` |
| `LaxLogic.PLLSemUIAmalg` | `LaxLogic.PLL.SemUI.SemUIAmalg` |
| `LaxLogic.PLLSemUIBox` | `LaxLogic.PLL.SemUI.SemUIBox` |
| `LaxLogic.PLLSemUIChar` | `LaxLogic.PLL.SemUI.SemUIChar` |
| `LaxLogic.PLLSemUICtx` | `LaxLogic.PLL.SemUI.SemUICtx` |
| `LaxLogic.PLLSemUIDesc` | `LaxLogic.PLL.SemUI.SemUIDesc` |
| `LaxLogic.PLLSemUIFrag` | `LaxLogic.PLL.SemUI.SemUIFrag` |
| `LaxLogic.PLLSemUIHenkin` | `LaxLogic.PLL.SemUI.SemUIHenkin` |
| `LaxLogic.PLLSemUILaw` | `LaxLogic.PLL.SemUI.SemUILaw` |
| `LaxLogic.PLLSemUILayered` | `LaxLogic.PLL.SemUI.SemUILayered` |
| `LaxLogic.PLLSemUIOFree` | `LaxLogic.PLL.SemUI.SemUIOFree` |
| `LaxLogic.PLLSemUIRes` | `LaxLogic.PLL.SemUI.SemUIRes` |
| `LaxLogic.PLLSemUISplit` | `LaxLogic.PLL.SemUI.SemUISplit` |
| `LaxLogic.PLLSemUITrace` | `LaxLogic.PLL.SemUI.SemUITrace` |
| `LaxLogic.PLLSequent` | `LaxLogic.PLL.Sequent.Sequent` |
| `LaxLogic.PLLStrongNorm` | `LaxLogic.PLL.Normalisation.StrongNorm` |
| `LaxLogic.PLLSubst` | `LaxLogic.PLL.ND.Subst` |
| `LaxLogic.PLLTactics` | `LaxLogic.PLL.ND.Tactics` |
| `LaxLogic.PLLTerms` | `LaxLogic.PLL.ND.Terms` |
| `LaxLogic.PLLTheorems` | `LaxLogic.PLL.ND.Theorems` |
| `LaxLogic.PLLTiming` | `LaxLogic.PLL.Timing.Timing` |
| `LaxLogic.PLLTimingAdder` | `LaxLogic.PLL.Timing.TimingAdder` |
| `LaxLogic.PLLTimingLookahead` | `LaxLogic.PLL.Timing.TimingLookahead` |
| `LaxLogic.PLLTimingRipple` | `LaxLogic.PLL.Timing.TimingRipple` |
| `LaxLogic.PLLTopTop` | `LaxLogic.PLL.Normalisation.TopTop` |
| `LaxLogic.PLLUIChains` | `LaxLogic.PLL.UI.UIChains` |

## 8. Verification (2026-09-15)

* After the move and again after the notation change: `lake build` of every
  LaxLogic module named individually (192; the root file does not import QLL
  or the Toolkit corpus), both paper libraries, and the 107 `wip/` modules that
  had been compiled at baseline: `Build completed successfully (9235 jobs)`.
* `LaxLogic.QLL.CLPWolfram` through `scripts/clp-wolfram.sh` (bridge on
  `LEAN_PATH`, Wolfram 14): exit 0, every Wolfram answer checked in Lean.
* `LaxLogic/Util/TurnstileTests.lean`: elaboration and printing pinned with
  `#guard_msgs` (inside and outside each scope, both scopes open, negation for
  Prop- and Type-valued relations, the set context, a tag with an argument,
  the no-default error); a deliberately wrong pin was run and failed.
* The 169 `wip/` files never compiled at baseline were not run: several are
  heavy sweeps.  Instead every `import LaxLogic…` in `wip/` and `Archive/` was
  resolved against the new tree (none unresolved), and each such file whose
  change goes beyond import lines was inspected: comments naming moved paths,
  two generated `import` strings in `wip/five.lean` and `wip/rungPin.lean`, and
  one `⊨-` → `⊨` in `wip/onevar.lean`.  Two over-eager glyph replacements
  (a printed `[q12]⊢q9` label, a `⊢-order` comment) and four `⊣⊢-` compounds
  were caught by this inspection and restored.

**After §2.1 (contexts, formula notation, binder guard; 2026-09-15 evening).**

* Every `LaxLogic/` module named individually except `QLL.CLPWolfram`:
  `Build completed successfully (8751 jobs)`.  `LaxPaper`, `CLPPaper` and the
  107 baseline `wip/` modules: `Build completed successfully (9165 jobs)`.
  `scripts/clp-wolfram.sh`: exit 0.
* `declaration uses sorry` warnings in `LaxLogic/`: the same eight warnings in
  seven files as in the baseline builds (three in `PLL/SemUI`, four in the
  Toolkit challenge corpus).
* Failures met on the way, each a design fault fixed in the notation rather
  than patched at the site: candidate elaboration with error recovery
  (ambiguity reported for `insert φ Γ ⊢ ψ`), binder capture
  (`∀ C : PLLFormula, S ⊢ A`), overloaded `∧`/`⊥` (FinComp, CtxCompleteness).
  Site edits were only the parentheses and `⊬` rewrites listed in HANDOFF.
* `LaxLogic/Util/TurnstileTests.lean` pins, besides the earlier ones: comma
  contexts in both directions for list and set relations, formulas inside and
  outside sequents, the no-context-variable ambiguity error, `[] ⊢ A` printing,
  implications between sequents, the binder cases (`∀ x : T,`, `∀ x y : T,`,
  `∀ φ ∈ Ds,`, `∃ C : T,`, a hypothesis `(h : Γ, p ⊢ q)`), `A = ⊥` for a
  formula, and `∧` between propositions of not-yet-known type.
* The 169 never-compiled `wip/` files were scanned for the idioms the lower
  precedence rejects (`¬ Γ ⊢ A`, `P ∧ Γ ⊢ A`, `P ∨ Γ ⊢ A`, `Γ = Δ ⊢ A`) and
  for competing formula notations: no occurrence outside comments and strings.

**After §2.2 (QLL modalities and quantifiers, shared connectives).**

* Every `LaxLogic/` module named individually except `QLL.CLPWolfram`:
  `Build completed successfully (8754 jobs)`.  `LaxPaper`, `CLPPaper` and the
  107 baseline `wip/` modules: `Build completed successfully (9168 jobs)`.
  `scripts/clp-wolfram.sh`: exit 0.  `sorry` warnings unchanged.
* The first full build failed in `PLL/Semantics/CtxCompleteness.lean` and the
  test file: the `Bot.bot` fallback was quoted hygienically in a module without
  Mathlib and could not resolve at the use site; fixed by a pre-resolved name.
* New pins in `LaxLogic/Util/TurnstileTests.lean`: the three modalities in
  both directions, in sequents, `⊥ ⊤` for formulas and for `Prop`, `∀'`/`∃'`,
  named quantifiers in both directions including a free `x` avoided by the
  printer, Lean's own `∀ ∃ ∧ ∨` inside the scope, and PLL and QLL formulas
  with both developments open.  Two deliberately wrong pins (swapped
  modalities; the capturing name `x`) were run and failed.
* No `wip/` file opens `LaxLogic.QLL`, and no file outside the library uses
  the tokens `◯[`, `∀'`, `∃'`, `↠`.
