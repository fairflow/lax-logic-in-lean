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
(`LaxLogic/PLL/Search/SearchCmd.lean`; the manual is `docs/search-manual.md`).
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
(`LaxLogic/PLL/Semantics/CountermodelEmit.lean`), which fixes the frame and decides
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

:::group "tools_decide"
Deciding a sequent and closing a goal.
:::

:::definition "pll_cli" (parent := "tools_decide")
`lake exe pll "<formula>"` (`tools/Decide.lean`), with the command form
`#decide φ to "out.svg"` (`tools/DecideCmd.lean`), is the user-facing
decider.  The untrusted FRJW engine saturates a store; the verified checker
`checkClosed` certifies that the store is closed, which settles the formula
one way or the other.  A PROVED answer comes with a proof term and a
snippet that re-elaborates it; a REFUTED answer comes with a countermodel,
drawn as SVG, and a kernel certificate that is checked by default.  Exit
codes 0–3 are checked, rejected (a defect), parse error, and
not-closed-within-bound, which is a frontier and never a verdict.
:::

:::definition "pll_g4c" (parent := "tools_decide")
`pll_g4c` (`LaxLogic/PLL/Search/Run.lean`) closes a concrete PLL
derivability goal by certificate splicing: it runs the fuel-free searcher
`G4cTm.find` as untrusted code, then re-elaborates the derivation it found as
an explicit `G4cTm` term, which the kernel checks.  It replaced `pll_g4`,
which ran the incomplete Iemhoff calculus under `native_decide`.
:::

:::group "tools_external"
Tools shared with other developments.
:::

:::definition "lean_certify" (parent := "tools_external")
Lean certify (`github.com/fairflow/lean-certify`, v0.1.0, a Lake
dependency of this repository) is a generic harness for certified
computation: an untrusted producer computes, a checker proved sound checks
its output in the kernel, and termination arguments stay in the theory.  It
grew out of this development's own practice (the oracle pattern of
`FRJO/Core.lean`) and is shared with the locus project.  `CertifyAdoption.lean`
is this repository's acceptance test: it packages `FinCM.checkB` and
`not_provable_of_check`, unchanged, as a `Certify.Certifier`, reproduces one
ρ-refutation through it, watches the gate reject corrupted models, and runs
the harness's lints, which reject the `WellFounded.fix` decider `decideG4`
and flag the `Finset` construction inside `decideFuel`.  The module is
outside the default build targets.  Background:
`docs/certified-computation-findings-2026-10-09.md`.
:::

:::definition "prover_toolkit" (parent := "tools_external")
The prover toolkit (`prover-toolkit/`, also called ax-prover-cascade) is
for attempting Lean goals with a language model and verifying the result
properly.  It depends on nothing in this repository.  Its parts: a corpus
index that serves this development's own declarations, notation included,
in place of Mathlib search; an axiom gate that flags a proof whose axioms
strictly exceed those of the proof it replaces; a checker (`verify.py`) that
splices a proof under the verbatim statement and rejects `sorry` and
`native_decide`; and a cost model per verified theorem.  It ships two
skills: `prove-lemma`, which drives the external prover ax-prover through a
hosted model API, and `prove-lemma-agent`, in which Claude proves the lemma
itself with the toolkit's search and check.  Status: the hosted route has
not been made to work here, and the substitute that would let ax-prover run
on a Claude subscription (`claude_shim.py`) is incomplete: its live mode is
built, but tool calls are not, and a run is blocked because ax-prover is not
installed and the command-line Claude cannot sign in
(`prover-toolkit/README.md`).  The corpus index, the checker and
`prove-lemma-agent` work on their own.
:::

:::group "tools_record"
Keeping the record and publishing it.
:::

:::definition "estate_scripts" (parent := "tools_record")
The proof-status ledger: `scripts/check-ledger.sh` regenerates the status of
every built declaration and fails on a regression (a new `sorry`, a new
axiom, a new `native_decide`); `scripts/check-imports.py` checks that every
import names a module that exists; `scripts/readme-figures.py --check`
checks that the README's figures match the record; `scripts/claim-scan.py`
and `scripts/reconcile-claims.py` reconcile claims in the prose against the
record.  CI runs the first three on every push to `main`.
:::

:::definition "rndb_tools" (parent := "tools_record")
The RN database (`RNDB/`) holds the certified facts about the closed
fragment, each entry carrying its proof.  `lake exe rhocover` is the
catalogue workbench (order matrix, operation tables, new-class probes);
`lake exe frjcert` and `lake exe rnpin` emit and pin certificates;
`tools/rho-hasse.sh` draws the Hasse diagram.  The catalogue page,
`docs/rn-catalogue.html`, is published with this site.
:::

:::definition "verso_pipeline" (parent := "tools_record")
The papers are Verso documents built from the compiled library, so every
Lean statement they print is the statement the kernel checked.
`scripts/verso-paper.sh` builds one as HTML and PDF (`scripts/clp-paper.sh`
for the CLP paper); `scripts/ci-pages.sh` and `scripts/ci-papers.sh` build
this site, the papers and the explorers for GitHub Pages.
:::

:::group "tools_skills"
Procedures for Claude.
:::

:::definition "skills" (parent := "tools_skills")
Written procedures that Claude follows in this repository, in
`.claude/skills/`: `calculus-adoption` (adopt a proof system from the
literature and mechanise it end to end); `iterate-to-goal` (run a
mechanisation campaign as rounds converging on one stated goal);
`verso-paper` (build a paper or blueprint with Verso);
`constraint-supersession-check` (before retiring any design, check that its
replacement discharges every constraint the old one did).  The two proving
skills are in `prover-toolkit/skill/`.
:::
