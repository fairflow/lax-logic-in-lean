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
Four commands settle a single sequent `Γ ⊢ C` and print a verdict, the
evidence for it, and a paste-ready theorem recording it
(`LaxLogic/PLLSearchCmd.lean`; the manual is `docs/search-manual.md`).
`#search Γ ⊢ C` runs the staged procedure and answers either way; `#refute
Γ ⊢ C` looks for a countermodel and emits it as a kernel-checkable
certificate; `#draw Γ ⊢ C to "f.svg"` searches and draws the countermodel in
one step.  The trap the manual names first: a countermodel refutes PCLL, the
confluent extension, only if it is mutually confluent, and most interesting
countermodels are not, so a PCLL claim wants `#refuteConf Γ ⊢ C`, which
searches the confluent frame battery, and never `#refute`.  A proof of a
PCLL sequent is obtained by adding the distribution instances as premises
and calling `#search`.
:::

:::definition "two_sided_engine" (parent := "tools_search")
The two-sided engine (`lake exe twosided`; certified layer
`wip/ljfo_link.lean`) is the default instrument for a PLL sequent question.
One side runs backward proof search in the focused calculus LJF◯ and, on
success, returns a derivation the kernel checks; the other builds an FRJ◯
refutation tree and, on success, returns a countermodel the verified checker
accepts.  The two searches share the sequent and the budget, and whichever
side closes first settles the cell with an object rather than a verdict.
The FRJW dichotomy of the decision-procedure chapter is the theorem that one
side always closes; the engine is its computational face, and the chapter
on decision is where that argument lives.
:::

:::group "tools_cert"
Certificates and hygiene.
:::

:::definition "certificates" (parent := "tools_cert")
Discover, then pin.  No search result is ever trusted as a result: a hit is
re-emitted as a Lean term (a derivation, or a finite model with its
checker call) and re-checked by the kernel, so the searcher may be partial,
heuristic and kernel-opaque without any loss.  A countermodel found by any
engine is escalated with `FinCM.not_provable_of_check`
(`LaxLogic/PLLCountermodelEmit.lean`), which fixes the frame and decides
the check; a proof found by the G4c searcher is replayed as a `G4cTm`
term.  The certificate is what enters the record; the search that found it
is a private matter of the tool.
:::

:::definition "axiom_hygiene" (parent := "tools_cert")
`Meta/Audit.lean` and `Meta/Sweep.lean` carry the axiom discipline of the
development.  A result is PROVED only when it is sorry-free and its axiom
set is pinned; the pin is `#axioms_within f [propext, Quot.sound]`, an
upper bound (the declared axioms are what would be acceptable, not
necessarily all used), checked by `collectAxioms`, the only recognised
oracle, so that `native_decide` and a stray classical instance are caught
and not merely printed.  `#axioms_within_pin f` emits the measured set
ready to paste, so a bound is generated, never retyped.  Because bounds
are opt-in and silence is not evidence, `#axiom_sweep [LaxLogic, FRJ, LJF]`
walks every declaration of a library and reports any outside the allowed
set; the production estate (`lake build Production`) runs that sweep with
`sorryAx` forbidden, and a module is promoted into it only when the sweep
passes.  A result whose axioms are a strict superset of what it replaces is
surfaced, with `#axiom_path` locating the entry, rather than accepted.
:::

:::definition "proofstates" (parent := "tools_cert")
`pstates` (`tools/proofstates/`, `lake build pstates`) is the proof-state
recorder.  It elaborates a Lean file, walks Lean's own info trees, and
writes one self-contained HTML page that replays every tactic step of every
proof in the file: the tactic as written, its position in the tactic tree,
the goals before it, the goals after it, and the difference.  The page can
be paused, scrubbed, played at a chosen speed and navigated by declaration,
and any state can be pinned into a collection with a note and exported as
Markdown or JSON.  It exists because reading a proof someone else developed
means reconstructing its intermediate states, which Lean otherwise offers
only through the infoview, one cursor position at a time, in an editor with
the file elaborated live; a recording detaches the states from the editor
and from Lean itself, so that a reviewer can enter the proof at any point
without running anything.  It is the instrument for presenting this
development to a co-developer, and the annotated proof-state files of the
record are its output.
:::
