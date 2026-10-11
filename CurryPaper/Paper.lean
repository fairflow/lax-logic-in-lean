import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import LaxLogic.PLL.Semantics.CtxCompleteness

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- Names in the rendered signatures are printed relative to these namespaces.
open PLLND PLLND.Ctx

#doc (Manual) "A Solution to Curry's Problem, Mechanised" =>

A Lean 4 mechanisation of the results of

> Matt Fairtlough and Michael Mendler.
> *On the Logical Content of Computational Type Theory: A Solution to Curry's Problem.*
> In Types for Proofs and Programs (TYPES 2000), Springer LNCS 2277,
> pp. 63–78, 2002.  DOI 10.1007/3-540-45842-5_5.

Everything here is in one file of the library,
`LaxLogic/PLL/Semantics/CtxCompleteness.lean`.  Each node below carries the
declaration it names, so its status is read off the compiler.  Nothing on this
page was proved for the page: it reports what the library already contains.

# What the paper claims

Propositional lax logic, PLL, is the logic of the modality of computational
type theory.  Curry's problem asks what that modality means.  The paper's
answer is that `◯` ranges over *constraints*.  A basic constraint is a pair of
formulas `K`, `L` acting on a formula by

$$`[K, L]\,φ \;=\; K ⊃ (φ ∨ L)`

A *standard constraint* `C` is a finite conjunction of basic constraints, and
`φ^C` is `φ` with every subformula `◯ψ` replaced by `C[ψ^C]`, the same `C` at
every occurrence.  The main theorem is context completeness:

$$`\mathrm{PLL} ⊢ φ \quad\Longleftrightarrow\quad \text{for every standard constraint } C,\;\; \mathrm{IPL} ⊢ φ^{C}`

So a formula is a theorem of lax logic exactly when it is an intuitionistic
theorem under every reading of the modality as a constraint.  The paper also
shows that the standard constraints form a Boolean algebra, and that no finite
set of them is enough.

# Definitions

:::group "curry_defs"
Constraints and the constraint translation.
:::

:::definition "curry_basic" (parent := "curry_defs") (lean := "basic")
The basic constraint `[K, L]` applied to `x`: the formula `K ⊃ (x ∨ L)`.
:::

:::definition "curry_std" (parent := "curry_defs") (lean := "StdCtx")
A standard constraint: a finite list of pairs `(K, L)`, read as the conjunction
of the basic constraints.  The empty list is the constraint that is always
true.  Uses {uses "curry_basic"}[].
:::

:::definition "curry_apply" (parent := "curry_defs") (lean := "applyC")
`C[x]`: the standard constraint `C` applied to `x`.
:::

:::definition "curry_sub" (parent := "curry_defs") (lean := "subC")
The translation `φ^C`: every `◯ψ` becomes `C[ψ^C]`.  Uses
{uses "curry_apply"}[].
:::

# Theorem 6: context completeness

:::group "curry_thm6"
The solution to Curry's problem.
:::

:::definition "curry_translate" (parent := "curry_thm6") (lean := "translate")
The translation of derivations: a PLL derivation of `φ` from `Γ` becomes a
derivation of `φ^C` from `Γ^C`, for any standard constraint `C`.  This is the
content of "every constraint is a sound reading of the modality", in full
sequent form.  Uses {uses "curry_sub"}[].
:::

:::theorem "curry_sound" (parent := "curry_thm6") (lean := "thm6_soundness")
Soundness direction: if `φ` is a PLL theorem then `φ^C` is provable, for every
standard constraint `C`.  Uses {uses "curry_translate"}[].
:::

:::theorem "curry_lemma7" (parent := "curry_thm6") (lean := "lemma7")
Lemma 7.  Over a finite constraint model, completed with one fresh variable per
world, the modality is a single standard constraint: `◯ψ` and `C₀[ψ]` are forced
at the same worlds.
:::

:::theorem "curry_complete" (parent := "curry_thm6") (lean := "thm6_completeness")
Completeness direction: if `φ^C` is provable for every standard constraint `C`,
then `φ` is a PLL theorem.  By contraposition from the finite model property
and {uses "curry_lemma7"}[].
:::

:::theorem "curry_thm6_main" (parent := "curry_thm6") (lean := "thm6")
Theorem 6, both directions.  Uses {uses "curry_sound"}[] and
{uses "curry_complete"}[].
:::

The statement that is machine-checked is

$$`\mathrm{PLL} ⊢ φ \quad\Longleftrightarrow\quad \text{for every standard constraint } C,\;\; \mathrm{PLL} ⊢ φ^{C}`

with `C` ranging over constraints whose `K` and `L` are arbitrary PLL formulas.
This differs from the paper's wording in two places, and the difference is
bridged by remarks in the source, not by a stated theorem:

* When `K` and `L` are modality-free, `φ^C` is modality-free (`subC_isIPL`, in
  the library), and PLL is conservative over IPL (`conservativity`), so
  provability of `φ^C` in PLL is provability in IPL.
* The completeness proof uses the hypothesis at one constraint only, the `C₀` of
  Lemma 7, whose `K` and `L` are propositional variables and disjunctions of
  them.  So the proof establishes the paper's form, with `C` restricted to
  IPL constraints.

The paper's form, restricted to IPL constraints and with IPL provability on the
right, is therefore a short corollary of what is here; it is not yet stated as
a theorem of the library.

# Corollary 10: no finite set of constraints suffices

:::group "curry_cor10"
The formulas `χ_m` and the incompleteness of every finite set of constraints.
:::

:::definition "curry_chi" (parent := "curry_cor10") (lean := "chi")
The family `χ_0 = ◯⊥`, `χ_{m+1} = ◯(◯p_{m+1} ⊃ (p_{m+1} ∨ χ_m))`.
:::

:::theorem "curry_lemma8" (parent := "curry_cor10") (lean := "lemma8")
Lemma 8.  A standard constraint of depth at most `m` makes `χ_m^C` provable.
:::

:::theorem "curry_lemma9" (parent := "curry_cor10") (lean := "lemma9")
Lemma 9.  No `χ_m` is a PLL theorem.  The countermodels are an explicit family
of models on the natural numbers.
:::

:::theorem "curry_cor10_main" (parent := "curry_cor10") (lean := "corollary10")
Corollary 10.  For every finite set of standard constraints there is a formula
that every constraint in the set translates to a theorem and that is not a PLL
theorem.  Uses {uses "curry_lemma8"}[] and {uses "curry_lemma9"}[].
:::

# Theorem 2: the constraints form a Boolean algebra

:::group "curry_thm2"
The algebra of standard constraints.
:::

:::theorem "curry_thm2_main" (parent := "curry_thm2") (lean := "thm2_boolean_algebra")
Theorem 2.  Under semantic equivalence, with meet the conjunction of
constraints, the standard constraints form a Boolean algebra: a bounded
distributive lattice in which every constraint has a complement.
:::

:::definition "curry_quot" (parent := "curry_thm2") (lean := "CQuot.instBooleanAlgebra")
The same fact as an instance: the quotient of the standard constraints by
equivalence is a `BooleanAlgebra`.  Uses {uses "curry_thm2_main"}[].
:::

# Axioms

Read from the repository's proof-status ledger (`docs/status-ledger.jsonl`),
which records `Lean.collectAxioms` for every declaration.

* `propext`, `Quot.sound` only: the translation `translate`, the soundness
  direction `thm6_soundness`, Theorem 2 (`thm2_boolean_algebra` and the
  `BooleanAlgebra` instance).
* `propext`, `Classical.choice`, `Quot.sound`: Lemma 7, the completeness
  direction, Theorem 6, the formulas `χ_m`, Lemmas 8 and 9, Corollary 10.

The use of `Classical.choice` is deliberate here and is not typical of the
library, most of which avoids it.  It enters, among other places, through the finite model property,
the choice of fresh variable names for the worlds of a model, and the
enumeration of an infinite supply of propositional variables for `χ_m`.  No
declaration on this page depends on `sorry` or on `native_decide`.

# What is not mechanised

* The paper's Theorem 6 in its exact wording (IPL constraints, IPL
  provability): see the remark under Theorem 6.
* The paper's Theorem 5, soundness and completeness of PLL for constraint
  models, is not proved in this file; it is the library's
  `consequence_iff_derivable`, mechanised from Fairtlough and Mendler 1997.
* The library's models are preorders where the paper has partial orders.
* The type-theoretic side of the paper, the reading of proofs as programs of
  computational type theory, is not treated.

{blueprint_graph}
