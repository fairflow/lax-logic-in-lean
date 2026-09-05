import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.PLLTerms
import LaxLogic.PLLConstraints

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The proof-term calculus" =>

The computational reading of PLL: proofs as terms, and terms as programs
whose `◯`-structure records the constraints under which a result is
delivered.  This is the Curry–Howard side of Fairtlough–Mendler, and the
object of the normalisation results that follow.

:::group "tm"
The term language and its substitution machinery.
:::

:::definition "var" (parent := "tm") (lean := "PLLND.Var")
TODO.
:::

:::definition "tm" (parent := "tm") (lean := "PLLND.Tm")
TODO.  Intrinsically typed: a term carries its context and its type, so
{uses "var"}[] is a position in the context rather than a name.
:::

:::definition "sub" (parent := "tm") (lean := "PLLND.Sub")
TODO — simultaneous substitutions, and the renaming machinery they are
built on.
:::

:::definition "subst" (parent := "tm") (lean := "PLLND.Tm.subst")
TODO.  Substitution on {uses "tm"}[] along a {uses "sub"}[].
:::

:::theorem "cut" (parent := "tm") (lean := "PLLND.Tm.cut")
TODO — cut as a term operation, the computational content of the
admissibility of cut.
:::

# Terms compute constraints

:::group "constraints"
F&M §1(6): the timing-analysis reading, in which a proof term evaluates to
the constraint under which its result becomes available.
:::

:::definition "sem" (parent := "constraints") (lean := "PLLND.sem")
TODO.
:::

:::definition "eval" (parent := "constraints") (lean := "PLLND.Tm.eval")
TODO.  Evaluation of a {uses "tm"}[] in an environment, delivering a
constraint rather than a value.
:::

:::definition "gates" (parent := "constraints") (lean := "PLLND.gate, PLLND.twoGates")
TODO — the worked circuit example.  This is the concrete case that makes
the constraint reading legible, and it is worth keeping in front of a
reader early.
:::
