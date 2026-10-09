import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Notation" =>

The core types are written in long form: a PLL formula is built from the
constructors of `PLLFormula` (`prop`, `falsePLL`, `and`, `or`, `ifThen`,
`somehow`), and a QLL formula from those of `LaxLogic.QLL.Form`.  On top of
that the library defines the conventional notation.  This chapter lists it,
says what must be opened to use it, and says when Lean prints it back.

The design record is `docs/syntax-reorg-2026-09-15.md`; the printed forms
below are pinned by `#guard_msgs` in `LaxLogic/Util/TurnstileTests.lean`,
so a change to any of them fails the build.

# Where notation can be written, and where it is shown

Writing.  In a Lean file every notation in scope can be used anywhere a term
is expected: in definitions, theorem statements, hypotheses, `have` and
`show`, and tactic arguments.  Scoped notation is in scope after
`open PLLND` (PLL) or `open LaxLogic.QLL` (QLL), or the `open scoped`
form of either.  The turnstiles are global syntax, so they parse
everywhere; the untagged forms need a default relation from an opened
namespace (below).

Showing.  Goals in the infoview, `#check`, `#print`, error messages and
`#guard_msgs` all go through one printer, Lean's delaborator.  A notation is
shown there only if two things hold: it has a printer (an unexpander or a
delaborator; every notation in this chapter has one unless stated), and
its namespace is open at the point being printed.  So when you conduct a
proof interactively, the goal display uses the special notation only in a
file that opens the namespace, and only for the forms that print back;
everything else is shown in long form, for example `PLLFormula.ifThen A B`
or a tagged turnstile.  You never type into the infoview itself: what you
type in the editor is limited only by scope.

Verso documents (this Blueprint and the papers) use the same printer, so a
document shows short names and notation exactly where its source file opens
the namespace.  The PLL chapters of this Blueprint open `PLLND`, so their
signatures use the PLL notation above, and an untagged `⊢` there is
`PLLND.LaxND`, the namespace's `turnstile_default`; the decision-procedure
chapter opens `FRJ`, `FRJ.Gbu`, `FRJ.Gbu.W` and `PLLND`.  A chapter that opens
neither shows signatures in long form, with fully qualified names.  The names
written in `(lean := …)` are resolved in the same scope, so they too are
written short, except where a short name would also denote something else:
`PLLND.Ne` and `PLLND.Sub` keep their prefix because Lean has its own `Ne`
and `Sub`.

`#eval` is different again: it uses `toString`/`Repr`, which for
`PLLFormula` still writes `⊃` for implication and `⊤` for `⊥ ⊃ ⊥`
(`LaxLogic/PLL/Syntax/Formula.lean` lines 88–89).

# PLL formulas

Scoped in `PLLND` (`LaxLogic/PLL/Syntax/Formula.lean`):

* `◯A` is `PLLFormula.somehow A` (prefix, binds tightest).
* `A ∧ B`, `A ∨ B` are `.and`, `.or`, with Lean's own tokens and precedences.
  They are not overloaded notations: one elaborator waits for the expected
  type and builds `And`/`Or` exactly as before when the type is a `Prop`.
* `A ↠ B` is `.ifThen A B` (precedence 27, right).  The token parses
  everywhere but elaborates only where a formula type is known; elsewhere it
  fails with "`↠` needs a formula type".
* `⊥` is `.falsePLL`, beside Mathlib's `⊥` by the same mechanism.
* There is no `⊤` notation; `truePLL` is an abbreviation for `⊥ ↠ ⊥`.

All of these print back.

# Sequents and turnstiles

Global syntax (`LaxLogic/Util/Turnstile.lean`):

* `Γ ⊢[R] A` and `Γ ⊨[R] A` mean `R Γ A`; the tag names the calculus.
* `Γ ⊬[R] A` and `Γ ⊭[R] A` mean `¬ R Γ A`, or `¬ Nonempty (R Γ A)` when
  `R` is a type of derivations.
* Untagged `⊢ ⊨ ⊬ ⊭` use the default relation of an opened namespace whose
  context and formula types fit.  With no default in scope: "no default
  relation for `⊢` in scope".
* Contexts: `Γ, A, B ⊢ C` is `B :: A :: Γ` for a list context and
  `insert B (insert A Γ)` for a set; `A, B ⊢ C` is `[A, B] ⊢ C`; `⊢ C` has
  the empty context.
* Typing judgements: `Γ ⊢ p : A`, with typed entries `Γ, u : B ⊢ p : A`,
  for relations registered as `[turnstile typing]`.

Registered relations and their defaults:

* `PLLND.LaxND`, `PLLND.SetDeriv` (`⊢`) and `PLLND.Consequence` (`⊨`):
  defaults in `PLLND`.
* `LaxLogic.QLL.Prv`, `SetPrv`, `Derives` (typing) and `Consequence`:
  defaults in `LaxLogic.QLL`.  `LaxLogic.QLL.Derivable` is registered but is
  not a default, so it prints as `⊢[Derivable]`.

Not registered: `SC`, `G4`, `G4c`, `G4h`, `LJF` and the other calculi; they
print in application form, for example `SC [◯A₀] A₀`.  Registering one is
one attribute line, and it changes printed forms in `#guard_msgs` outputs.
A relation that is a variable (in a generic theorem over `R`) always prints
as `R Γ A`.

Recorded restrictions:

* A sequent beside a `Prop` connective tighter than `→` needs parentheses:
  `P ∧ (Γ ⊢ A)`.  `→` and `↔` stay outside, so `Γ ⊢ A → Γ, A ⊢ B` is an
  implication between sequents.
* `¬ Γ ⊢ A` does not parse as a negated sequent; write `Γ ⊬ A`.
* The first entry before a comma must be an identifier: write
  `Γ, ◯p, q ⊢ r` or `[◯p, q] ⊢ r`, not `◯p, q ⊢ r`.
* A context with no context variable is ambiguous when a list and a set
  default are both in scope (`p, q ⊢ r` in `PLLND`); write `[p, q] ⊢ r` or
  a tag.
* Inside an unbracketed binder (`∀ x : Γ, …`) the comma is the binder's.
  Hypotheses `(h : Γ, p ⊢ q)`, statements and `have` are unaffected.
* Lean's own `⊢` in tactic locations (`simp at h ⊢`) is unaffected.
* The search commands (`#search Γ ⊢ C` and relatives) have their own parser
  and accept no comma contexts.

# QLL

Scoped in `LaxLogic.QLL` (`LaxLogic/QLL/Notation.lean`):

* `◯[∀] A`, `◯[∃] A`, `◯[q] A` for the quantified modality.
* `∧ ∨ ↠` as for PLL; `⊥ ⊤` only where `LaxLogic.QLL.NotationOrder` is
  imported (it brings in Mathlib; the QLL core is Mathlib-free and writes
  `.bot`, `.top`).
* `∀ x, A` and `∃ x, A` with one untyped binder, when the expected type is
  `Form`; `∀ x : T, …` and `∀ x y, …` are always Lean's.  `∀' A` and `∃' A`
  take a de Bruijn body.
* `P(t, u)`, `f(t)`, `P()` for predicates and function terms.

`◯[·]`, `∀'` and `∃'` bind tightly: `◯[∀] (A ∧ B)` needs its parentheses.
All of these print back, with fresh names `x y z x1 …` for bound variables.

Global literal syntax (`LaxLogic/QLL/Surface.lean`, `Judgement.lean`):
`qf[…]` for formulas, `qp[…]` for proof terms (`λu. p`, `val[∀]`,
`let[∀] u ⇐ p in q`, `case`, …) and `qd[Γ ⊢ p : A]` for judgements.
Literal proof terms print back as `qp[…]`.

# Other areas

* BiLax, scoped in `BiLax`: `⇾`, `⤙`, `◯∀`, `◯∃`, which print back;
  the flipped arrows `⇽` and `⤚` do not.
* Obligations: `◯∀[p] M`, `◯∃[p] M` (`LaxLogic/Obligation/Modality.lean`).
* Realisability, scoped in `PLLND.BeliefReal`: `x ⊩ᵘ[Ev, w] φ`,
  `x ⊩ˢ[Ev, κ, w] φ`, `x ⊩ᵖ[Ev, κ, w] φ`.
* The order on classes: `a ⋖[S] b` and `⋖` (`RNDB/Order.lean`); `⋗`
  prints as the `⋖` form.
* `Γ ≐ Δ` for context equality in FRJ (`FRJ/Basic.lean`).

The printed forms in this section are not pinned by tests.

# Retired glyphs

Older documents and branches use symbols that no longer exist: `⊢-`,
`⊩` and `⊢q`/`⊩q` are now `⊢`; `⊨-` and `⊫` are now `⊨`; `⊢qll p : A`
is now `Γ ⊢ p : A`; the PLL implication `⊃` is now `↠`; the surface forms
`◯∀ ◯∃ ∀x. A val∀ let∀` are now `◯[∀] ◯[∃] ∀ x, A val[∀] let[∀]`.
`scripts/reorg-2026-09-15.py` translates old module paths.
