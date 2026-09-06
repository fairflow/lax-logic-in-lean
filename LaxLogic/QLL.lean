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
| `Lc`      | local closedness and the open/close roundtrip; wanted for Figs. 3 and 4 |
| `Check`   | the deciding checker, `Except Err Unit` |
| `Certify` | the certificate-returning checker, `Except Err (Derives p Γ M)` — soundness typed, not proved |
| `Sound`   | freshness and lookup lemmas, used to *build* derivations |
| `Surface` | named variables in and out; the printed form is the input form |

Fig. 5's `Subst` is not a rule here; see `Deriv.lean`.  Neither checker
supersedes the other — see the supersession table in `Check.lean`.

**OPEN**, with nothing asserting otherwise: completeness of either checker, and
everything downstream of Figs. 3 and 4 — the refinement reading `⊨`, soundness
against it, and sufficiency of the residual obligations.
-/
import LaxLogic.QLL.Syntax
import LaxLogic.QLL.Deriv
import LaxLogic.QLL.Lc
import LaxLogic.QLL.Check
import LaxLogic.QLL.Sound
import LaxLogic.QLL.Certify
import LaxLogic.QLL.Surface
