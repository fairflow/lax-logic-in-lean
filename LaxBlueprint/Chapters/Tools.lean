import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Tools" =>

OUTLINE ONLY — structure proposed, prose and Lean attachments not yet
written.  The register this is drawn from is `TOOLS.md` at the repository
root; that file is the maintained source and should stay so.  This chapter
is for a reader who wants to know what instruments exist and what each one
is *for*, not how to invoke it.

:::group "tools_search"
Proof search and countermodel search: the two-sided engine.
:::

:::definition "search_cmds" (parent := "tools_search")
TO WRITE — the `#search` / `#refute` / `#refuteConf` / `#draw` commands, and
the trap `docs/search-manual.md` §0 names: a countermodel refutes PCLL only
if it is mutually confluent, so a PCLL claim wants `#refuteConf`, not
`#refute`.  That distinction is the one a newcomer gets wrong.
:::

:::definition "two_sided_engine" (parent := "tools_search")
TO WRITE — the two-sided engine: LJF◯ backward search proves, FRJ(◯) trees
refute, and each side emits a kernel-checkable object.  Cross-reference the
decision procedure chapter rather than repeating it.
:::

:::group "tools_cert"
Certificates and hygiene.
:::

:::definition "certificates" (parent := "tools_cert")
TO WRITE — discover-then-pin: a search hit is re-emitted as a Lean term the
kernel checks, so a search result never has to be trusted.
:::

:::definition "axiom_hygiene" (parent := "tools_cert")
TO WRITE — `Meta/Audit.lean` and `Meta/Sweep.lean`: axiom bounds and estate
sweeps.  Worth stating the standing rule explicitly, since it is the
methodological spine of the whole development: `#print axioms` is the only
recognised checker, and a result whose axioms are a strict superset of
what it replaces is surfaced rather than accepted.
:::

:::definition "proofstates" (parent := "tools_cert")
TO WRITE — `pstates`, the proof-state recorder: elaborates a file, walks the
info trees, and writes a self-contained HTML page replaying every tactic
step with its goals before and after.  This is the instrument that makes
the development legible to someone who is not running Lean, and it belongs
in any presentation to co-developers.
:::
