/-
# `LaxLogic.QLL` — a deep embedding of the abstract logic of TPHOLs 2001

`LaxLogic.Obligation` renders the paper *shallowly*: a refinement pair is a Lean
proposition and its proof is a Lean proof.  This library renders it *deeply*: a
formula is a tree, a proof term is a tree, and whether the second proves the
first is decided by a program.

| module | what it holds |
| :-- | :-- |
| `Syntax`  | `Tm`, `Q`, `Form`, `Pf`, `Ctx` — locally nameless, two binder sorts |
| `Deriv`   | `Derives p Γ M` in `Type`, one constructor per rule of Fig. 5; `Derivable = Nonempty ∘ Derives` |
| `Lc`      | local closedness, the open/close roundtrip, and deciding it |
| `Kit`     | fresh names, size lemmas, errors, lookup — what the checker is built from |
| `Certify` | the checker: `Except Err (Derives p Γ M)` — soundness typed, not proved |
| `Surface` | named variables in and out; the printed form is the input form |
| `Judgement` | `qj[Γ ⊢ p : M]` (the proposition) and `qd[…]` (the type of its derivations) |
| `Interp` | Figs. 3 and 4 — the refinement types `|M|` and the refinement relation `p : M` |

Fig. 5's `Subst` is not a rule here; see `Deriv.lean`.

There is **one** checker.  A `Prop`-returning one (`Check.lean`) existed
alongside it until the two were shown to agree on a corpus; it is deleted.

Figs. 3 and 4 are built.  `InterpTests.lean` exhibits one model and two
constraints separating `○∀` from `○∃` in both directions, which is the content
Fig. 5 does not carry: its modal rules are one schema for both.

**OPEN**, with nothing asserting otherwise: completeness of the checker for
normal terms; Fig. 6, the interpretation of proof terms, without which
soundness of `Derives` against `Sat` cannot even be stated; and sufficiency of
the residual obligations.  The checker refuses certain β-redexes; see
`Certify.lean`.
-/
import LaxLogic.QLL.Syntax
import LaxLogic.QLL.Deriv
import LaxLogic.QLL.Lc
import LaxLogic.QLL.Kit
import LaxLogic.QLL.Certify
import LaxLogic.QLL.Surface
import LaxLogic.QLL.Judgement
import LaxLogic.QLL.Interp
