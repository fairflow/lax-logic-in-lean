/-
# `LaxLogic.QLL.Judgement` — `qj[Γ ⊢ p : M]`

`qf[…]` gives a formula and `qp[…]` a proof term; a *judgement* needs both at
once, together with a context, and writing the three brackets out by hand is
exactly the noise the surface layer exists to remove.  So:

    qj[u : A ⊃ B, v : A ⊢ u v : B]      the proposition   (`Derivable`)
    qd[u : A ⊃ B, v : A ⊢ u v : B]      the type of its derivations (`Derives`)

with `qj[J]` reducing to `Nonempty qd[J]` by definition, which is the whole of
`Derivable = Nonempty ∘ Derives`.  Both brackets are kept: a theorem is stated
with `qj`, a derivation is *built* at type `qd`.

This module, not `Surface`, is where the notation lives, because it is the
first thing in the surface layer that mentions the calculus.

## Context order

The context is written left to right in the conventional order — leftmost
entry bound first, so a repeated name is shadowed by the entry to its *right*,
matching `Ctx.lookup?`, which searches the head of the list first.  The macro
therefore reverses at expansion time, not at run time: the elaborated type
contains a literal list, with no `List.reverse` left in it to obscure the
goal display.

`renderJ` reverses to match, and `JudgementTests.lean` gates the round trip.
-/
import LaxLogic.QLL.Surface
import LaxLogic.QLL.Deriv

namespace LaxLogic.QLL.Surface

open LaxLogic.QLL

/-! ## Printing -/

/-- A context entry, `p : M`. -/
def renderEntry (e : Pf × Form) : String :=
  renderPf e.1 ++ " : " ++ render e.2

/-- A context, in the conventional order: the list's *last* entry leftmost. -/
def renderCtx (Γ : Ctx) : String :=
  ", ".intercalate (Γ.reverse.map renderEntry)

/-- A judgement.  The result parses back inside `qj[…]` and `qd[…]`. -/
def renderJ (p : Pf) (Γ : Ctx) (M : Form) : String :=
  (if Γ.isEmpty then "" else renderCtx Γ ++ " ") ++ "⊢ " ++ renderPf p ++ " : " ++ render M

/-! ## Input notation -/

declare_syntax_cat qllEntry
declare_syntax_cat qllJudge

/-- `p : M` — a context entry.  The left-hand side is a full proof term, not
just a variable, because a residual obligation need not be a variable. -/
syntax qllPf:0 " : " qllForm:0 : qllEntry

syntax qllEntry,* " ⊢ " qllPf:0 " : " qllForm:0 : qllJudge

/-- A single context entry, as a `Pf × Form`. -/
syntax "qe[" qllEntry "]" : term
macro_rules | `(qe[$p:qllPf : $M:qllForm]) => `((qp[$p], qf[$M]))

/-- A context in surface syntax, as a `Ctx`. -/
syntax "qc[" qllEntry,* "]" : term
macro_rules
  | `(qc[$[$es],*]) => do
      let es := es.reverse
      `(([$[qe[$es]],*] : Ctx))

/-- The *type of derivations* of a judgement: `Derives p Γ M`. -/
syntax "qd[" qllJudge "]" : term

/-- A judgement as a proposition: `Derivable p Γ M`. -/
syntax "qj[" qllJudge "]" : term

macro_rules
  | `(qd[$[$es],* ⊢ $p:qllPf : $M:qllForm]) => do
      let es := es.reverse
      `(Derives qp[$p] [$[qe[$es]],*] qf[$M])
  | `(qj[$[$es],* ⊢ $p:qllPf : $M:qllForm]) => do
      let es := es.reverse
      `(Derivable qp[$p] [$[qe[$es]],*] qf[$M])

end LaxLogic.QLL.Surface
