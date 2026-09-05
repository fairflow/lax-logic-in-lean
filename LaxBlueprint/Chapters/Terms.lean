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
delivered.  This is the Curry–Howard side of Fairtlough–Mendler, and it is
the object of the normalisation results in the two chapters that follow.

The calculus is *intrinsically typed*: a term carries its context and its
type, so there are no ill-typed terms to exclude and no separate typing
judgment to prove sound.  The cost is that substitution has to be defined
with the types moving too, which is what the renaming and substitution
machinery below exists for.

# The term language

:::group "tm"
The syntax, and the substitution machinery it needs.
:::

:::definition "var" (parent := "tm") (lean := "PLLND.Var")
A variable is a *position* in the context, not a name.  That is what makes
weakening and exchange bookkeeping rather than α-conversion.
:::

:::definition "tm" (parent := "tm") (lean := "PLLND.Tm")
The terms.  One constructor per rule of the natural-deduction system, so a
term *is* a derivation, read as data.  The two `◯` constructors are the
interesting ones: `val` embeds a value under the modality, and `bind`
sequences a computation with a body — the monadic reading on which the whole
constraint interpretation rests.
:::

:::definition "sub" (parent := "tm") (lean := "PLLND.Sub")
Simultaneous substitutions, built over renamings.  The two-layer
construction — renamings first, then substitutions — is the standard way of
breaking the circularity in which substitution needs weakening and weakening
needs substitution.
:::

:::definition "subst" (parent := "tm") (lean := "PLLND.Tm.subst")
Substitution of a {uses "sub"}[] through a {uses "tm"}[].
:::

:::theorem "cut" (parent := "tm") (lean := "PLLND.Tm.cut")
Cut as a term operation.  This is the computational content of the
admissibility of cut: where the sequent calculus shows a cut can be
*eliminated*, here it is *performed* — and the two facts meet again at weak
normalisation in the next chapter.
:::

# Terms compute constraints

:::group "constraints"
F&M §1(6), the timing-analysis reading.
:::

:::definition "sem" (parent := "constraints") (lean := "PLLND.sem")
The interpretation a term is evaluated into.
:::

:::definition "eval" (parent := "constraints") (lean := "PLLND.Tm.eval")
Evaluation of a {uses "tm"}[] in an environment.  What comes out is not a
value but a *constraint*: the condition under which the result becomes
available.  That is the point of the modality — `◯A` is not `A` but "`A`,
once something holds", and the term records what.
:::

:::definition "gates" (parent := "constraints") (lean := "PLLND.gate, PLLND.twoGates")
The worked circuit example.  A gate's output is available only once its
inputs have settled, and composing two gates composes their timing
constraints — which is exactly what `bind` does.

This example earns a place early in any presentation of the theory: it turns
the modality from a piece of proof theory into something a reader can watch
working, and it is the shortest route to why PLL is not simply S4.
:::
