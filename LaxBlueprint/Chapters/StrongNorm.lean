import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.PLLStrongNorm
import LaxLogic.PLLReducibility
import LaxLogic.PLLTopTop

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Strong normalisation" =>

This chapter is the part of the development that goes beyond the I&C paper,
which is why it stands on its own.

The shape of the argument is worth stating before the results, because it
is not the usual one.  `Step` splits into two fragments: β-reduction for
every connective, and `let`-associativity.  Each is strongly normalising
*in isolation*, by quite different methods — a weight for assoc, a
Kripke–Tait reducibility argument for β.  Neither result composes with the
other, and this is not a gap in the proofs but a fact about the calculus,
established by machine-checked counterexamples.  Strong normalisation of
the freely interleaved reduction therefore needs a semantic method over the
whole relation, and that is Lindley–Stark ⊤⊤-lifting.

# The two fragments

:::group "frag"
Each half of `Step`, normalising on its own.
:::

:::definition "astep" (parent := "frag") (lean := "PLLND.AStep")
The `let`-associativity fragment: re-bracketing nested binds, without
touching any β-redex.
:::

:::definition "weight" (parent := "frag") (lean := "PLLND.Tm.weight")
A weight on terms, strictly decreasing along {uses "astep"}[].
:::

:::theorem "assoc_sn" (parent := "frag") (lean := "PLLND.assoc_sn")
Assoc terminates, by {uses "weight"}[].  The argument is genuinely simple —
a natural-number measure and nothing else — and it is worth presenting for
that reason, as the contrast against which the difficulty of the other
fragment, and then of their union, can be seen.
:::

:::definition "rstep" (parent := "frag") (lean := "PLLND.RStep")
The β fragment: one clause per connective.
:::

:::definition "rsn" (parent := "frag") (lean := "PLLND.RSN")
The reducibility predicate, defined by recursion on the type.  The `◯` clause
is where the design decision sits: this is the value-style interpretation,
and {uses "kont"}[] later replaces it.
:::

:::theorem "red_sn" (parent := "frag") (lean := "PLLND.Red.sn")
Reducible terms are strongly normalising — the easy half of the reducibility
method.
:::

:::theorem "beta_sn" (parent := "frag") (lean := "PLLND.beta_sn")
β is strongly normalising, by Kripke–Tait reducibility over {uses "rsn"}[]
and {uses "red_sn"}[].  Note the asymmetry with {uses "assoc_sn"}[]: no
measure on terms does this, because β duplicates arbitrary subterms.
:::

:::theorem "step_split" (parent := "frag") (lean := "PLLND.step_split")
Every `Step` is an {uses "astep"}[] or an {uses "rstep"}[].  This is what
makes "the two fragments" a partition rather than a manner of speaking, and
it is what the next section needs in order to say that *both* halves
terminate and the whole still might not.
:::

# The fragments do not compose

:::group "nocomp"
A negative result, and the reason the chapter needs a third method.
:::

:::proposition "no_quasicommutation" (parent := "nocomp")
Each fragment creates redexes of the other, so *both* orientations
of Bachmair–Dershowitz quasi-commutation fail, and {uses "assoc_sn"}[]
together with {uses "beta_sn"}[] does not yield termination of
{uses "step_split"}[]'s union.

The witnesses are machine-checked, in the `Counterexamples` namespace at
the end of `LaxLogic/PLLReducibility.lean`: a term `ce₁` that is
β-irreducible but assoc-steps to `ce₁assoc`, which then β-steps; and a term
`ce₂` that is assoc-irreducible but β-steps to `ce₁`.

Worth recording why no measure repairs this, since it is the natural first
thought: β duplicates arbitrary subterms through substitution, and the
β-redexes that assoc creates have unbounded scrutinees, which the
subsequent `let`-β duplicates in turn.  Nor does the phased strategy
"β to completion, then assoc, then repeat" help — that would prove one
strategy normalises, which is weak normalisation, already available from
cut elimination.
:::

# The full reduction

:::group "full"
Lindley–Stark ⊤⊤-lifting, and the theorem it delivers.
:::

:::definition "kont" (parent := "full")
Continuation stacks, and the biorthogonal `⊤⊤` closure that reinterprets the
`◯`-clause: `◯A` is reducible when it behaves well against every reducible
continuation, rather than when it holds a reducible value.  The value-style
interpretation used for {uses "beta_sn"}[] is exactly the `K = []` shadow of
this one, which is why the upgrade is a strengthening and not a fresh start.
:::

:::theorem "fundamental_step" (parent := "full") (lean := "PLLND.fundamental_step")
The fundamental theorem of the logical relation, over the full reduction:
every well-typed term is reducible under any reducible substitution.  Uses
{uses "kont"}[].
:::

:::theorem "strong_normalisation" (parent := "full") (lean := "PLLND.strong_normalisation")
Strong normalisation of the full reduction: `SNt t` for every `t : Tm Γ φ`,
β and assoc freely interleaved.  This closes what
{uses "no_quasicommutation"}[] showed could not be closed compositionally,
and it is the last of the three normalisation results.
:::

:::theorem "normalize_spec" (parent := "full") (lean := "PLLND.Tm.normalize_spec")
The certified normaliser's specification: the function terminates and
delivers a normal form of its input.
:::
