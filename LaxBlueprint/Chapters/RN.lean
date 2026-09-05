import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The RN(◯) lattice" =>

OUTLINE ONLY — structure proposed, prose and Lean attachments not yet
written.  Sources are `RNDB/`, `docs/rho-structure.md`, `docs/rho-order.md`
and the catalogue pages; those are consulted for wording and not reproduced
here.

The object: the ordering of the `◯`-and-`⊥` formulas in one variable up to
interderivability, its Hasse diagram, and the dictionary of classes.  It is
small enough to see whole, which is what makes it useful — and the standing
task is to extend it to more complex formulas, where "seeing it whole" stops
being available and the database has to carry what intuition did.

:::group "rn_order"
The order itself.
:::

:::definition "rn_carrier" (parent := "rn_order")
TODO — what `RN(◯,{})` is: which formulas, and interderivability as the
quotient.
:::

:::definition "rn_order_def" (parent := "rn_order")
TODO — `Lt`, `Covers`, `CoversIn` (`RNDB/Order.lean`): the order and its
covering relation, which is what the Hasse diagram draws.
:::

:::proposition "rn_classification" (parent := "rn_order")
TODO — the classification: the image of `h` is the rungs together with `⊤`,
and the complement is infinite.  PROVED; cite the mechanisation.
:::

:::proposition "rn_width" (parent := "rn_order")
TODO — unbounded width: the collapse statements form an infinite antichain.
PROVED.  This is the result that makes the lattice interesting rather than
a curiosity, and it should be stated early.
:::

:::group "rn_db"
The database, and why it is a database.
:::

:::definition "rn_claim" (parent := "rn_db")
TODO — `Claim`, `Evidence`, `Entry`, `Frontier` (`RNDB/Types.lean`), and
the un-sorriable `ok` field: an entry cannot record a claim it has no
evidence for.  Worth explaining, because it is the design decision that
makes a machine-maintained catalogue trustworthy.
:::

:::definition "rn_engines" (parent := "rn_db")
TODO — `Engine` and `DerivRule`: which instrument settled each cell, kept
in the record so a later reader can re-run it.
:::

:::group "rn_next"
The open direction.
:::

:::proposition "rn_extension" (parent := "rn_next")
TODO — OPEN.  Extending the lattice to more complex formulas: more
variables, deeper ◯-nesting.  State what is known to survive, what is known
to fail, and what the obstruction is, rather than describing this as
"future work".  The catalogue and the ρ-order structure document already
contain most of the answer; the task is to say it in one page.
:::
