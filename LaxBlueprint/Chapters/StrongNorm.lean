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
TODO — the `let`-associativity fragment.
:::

:::definition "weight" (parent := "frag") (lean := "PLLND.Tm.weight")
TODO — the weight that decreases along {uses "astep"}[].
:::

:::theorem "assoc_sn" (parent := "frag") (lean := "PLLND.assoc_sn")
TODO — assoc terminates, by {uses "weight"}[].  A genuinely simple
argument, and worth showing as the contrast with what follows.
:::

:::definition "rstep" (parent := "frag") (lean := "PLLND.RStep")
TODO — the β fragment.
:::

:::definition "rsn" (parent := "frag") (lean := "PLLND.RSN")
TODO — the reducibility predicate.
:::

:::theorem "red_sn" (parent := "frag") (lean := "PLLND.Red.sn")
TODO — reducible terms are strongly normalising.
:::

:::theorem "beta_sn" (parent := "frag") (lean := "PLLND.beta_sn")
TODO — β is strongly normalising, by Kripke–Tait reducibility over
{uses "rsn"}[] and {uses "red_sn"}[].
:::

:::theorem "step_split" (parent := "frag") (lean := "PLLND.step_split")
TODO — every `Step` is an {uses "astep"}[] or an {uses "rstep"}[].  This is
what makes "the two fragments" a partition rather than a manner of
speaking.
:::

# The fragments do not compose

:::group "nocomp"
A negative result, and the reason the chapter needs a third method.
:::

:::proposition "no_quasicommutation" (parent := "nocomp")
TODO.  Each fragment creates redexes of the other, so **both** orientations
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
TODO — continuation stacks, and the biorthogonal `⊤⊤` closure that
reinterprets the `◯`-clause.  The value-style interpretation used for
{uses "beta_sn"}[] is exactly the `K = []` shadow of this one.
:::

:::theorem "fundamental_step" (parent := "full") (lean := "PLLND.fundamental_step")
TODO — the fundamental theorem of the logical relation, over the full
reduction.  Uses {uses "kont"}[].
:::

:::theorem "strong_normalisation" (parent := "full") (lean := "PLLND.strong_normalisation")
TODO — strong normalisation of the full reduction: `SNt t` for every
`t : Tm Γ φ`, β and assoc freely interleaved.  This closes what
{uses "no_quasicommutation"}[] showed could not be closed compositionally.
:::

:::theorem "normalize_spec" (parent := "full") (lean := "PLLND.Tm.normalize_spec")
TODO — the certified normaliser's specification.
:::
