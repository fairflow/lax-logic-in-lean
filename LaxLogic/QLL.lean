/-
# `LaxLogic.QLL` — a deep embedding of the abstract logic of TPHOLs 2001

`LaxLogic.Obligation` renders the paper *shallowly*: a refinement pair is a Lean
proposition and its proof is a Lean proof.  This library renders it *deeply*: a
formula is a tree, a proof term is a tree, and whether the second proves the
first is decided by a program.

| module | what it holds |
| :-- | :-- |
| `Syntax`  | `Tm`, `Q`, `Form`, `Pf`, `Ctx` — locally nameless, two binder sorts |
| `Deriv`   | `Derives p Γ A` in `Type`, one constructor per rule of Fig. 5; `Derivable = Nonempty ∘ Derives` |
| `Lc`      | local closedness, the open/close roundtrip, and deciding it |
| `Kit`     | fresh names, size lemmas, errors, lookup — what the checker is built from |
| `Certify` | the checker: `Except Err (Derives p Γ A)` — soundness typed, not proved |
| `Surface` | named variables in and out; the printed form is the input form |
| `Judgement` | `qj[Γ ⊢ p : A]` (the proposition) and `qd[…]` (the type of its derivations) |
| `Interp` | Figs. 3 and 4 — the refinement types `|A|` and the refinement relation `p : A` |
| `Denote` | Fig. 6 — the constraint a derivation denotes, `⟦d⟧ : Val 𝔐 A` |
| `Sound`  | soundness: the denoted constraint refines the derived formula |
| `CLP`    | §3's two lax resolution rules, derived, and what they compute |
| `LLP`    | §5 of the CLP draft: Σ-formulas, program clauses, the five derived rules of Fig. 3 |
| `Size`   | the size of a formula, unchanged by opening (induction through `∃`) |
| `Horn`   | Horn clauses (primitive positive bodies); a Def 5.1 clause split into them by the draft's `ind(S)` |
| `Herbrand` | Lloyd's least Herbrand model, as a one-world Kripke model; Lloyd's theorem and completeness for Horn programs |
| `HerbrandLLP` | §7 on worlds 0 and 1: the two-world Herbrand model of a Def 5.1 program; Theorem 7.5 for `i = 0, 1` |
| `Weaken` | a derivation's eigenvariables, and weakening under their avoidance |
| `Rename` | renaming an individual through a derivation; re-basing an eigenvariable |
| `Kripke` | the Kripke semantics: varying domains, two lax relations, fallible states |
| `Prov`   | the consequence relation for the model theory, and its soundness |
| `Complete` | the canonical model, and completeness on the quantifier-free fragment |

Fig. 5's `Subst` is not a rule here; see `Deriv.lean`.

## Two notational departures from the report

* **Formulas are `A`, `B`, not `M`, `N`.**  The model is Fraktur `𝔐`, which
  copies and pastes as a plain `M` — so a displayed statement mentioning both a
  model and a formula becomes unreadable the moment anyone quotes it.  The
  report has no models and could spend `M` on formulas; we cannot.  Verbatim
  quotations of the report keep its letters.
* **The refinement relation is `Refines`, not `Sat`.**  Fig. 4 is captioned
  "Equations for abstraction and refinement" and `p : M` is read "`p` refines
  `M`".  `Refines 𝔐 env ρ A v` is indexed by the witness `v`, so it is a
  realizability relation, not satisfaction; `⊨` and `Sat` stay free for a
  model-theoretic semantics of the modalities, which does not exist here.

There is **one** checker.  A `Prop`-returning one (`Check.lean`) existed
alongside it until the two were shown to agree on a corpus; it is deleted.

Figs. 3 and 4 are built.  `InterpTests.lean` exhibits one model and two
constraints separating `○∀` from `○∃` in both directions, which is the content
Fig. 5 does not carry: its modal rules are one schema for both.

Figs. 3, 4 and 6 are built and **soundness is proved**: if every assumption's
constraint refines its formula then so does the one the derivation produces.
Its one hypothesis is that the individual terms written into the proof term
carry no loose index; see `Sound.lean` for why that is not avoidable and why
nothing else is needed.

**OPEN**, with nothing asserting otherwise: completeness of the checker for
normal terms, and sufficiency of the residual obligations.  The checker refuses
certain β-redexes; see `Certify.lean`.
-/
import LaxLogic.QLL.Syntax
import LaxLogic.QLL.Deriv
import LaxLogic.QLL.Lc
import LaxLogic.QLL.Kit
import LaxLogic.QLL.Certify
import LaxLogic.QLL.Surface
import LaxLogic.QLL.Judgement
import LaxLogic.QLL.Interp
import LaxLogic.QLL.Denote
import LaxLogic.QLL.Sound
import LaxLogic.QLL.CLP
import LaxLogic.QLL.Weaken
import LaxLogic.QLL.Rename
import LaxLogic.QLL.Kripke
import LaxLogic.QLL.Prov
import LaxLogic.QLL.Complete
import LaxLogic.QLL.Size
import LaxLogic.QLL.Complete1
import LaxLogic.QLL.RefineIncomplete
import LaxLogic.QLL.Bridge
import LaxLogic.QLL.Abstract
import LaxLogic.QLL.PaperSemantics
import LaxLogic.QLL.LLP
import LaxLogic.QLL.Horn
import LaxLogic.QLL.Herbrand
import LaxLogic.QLL.HerbrandLLP
