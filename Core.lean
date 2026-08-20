/-
# `Core` — the publishable core of the PLL development

Every module imported below belongs to a campaign whose terminal result
is PROVED (or, in one case, is a completed REFUTATION), is sorry-free,
and reaches no `wip/` module.  `Core/Audit.lean` pins the axioms of each
campaign's terminal theorem, so the claims this file makes are checked by
the build rather than asserted here.

Campaigns that did NOT reach their terminal result are excluded WHOLE,
including their sorry-free parts.  See `README.md` §"What is not here".

Read `README.md` first; `docs/calculus-map.md` is the provenance
reference for which proof system any given result belongs to.
-/

/- ## 1. Syntax, and `LaxND` — the reference system

`Deriv Γ φ := Nonempty (LaxND Γ φ)` is what "PLL proves" means
throughout.  Fairtlough–Mendler 1997's `◯R`, `◯M`, `◯F`; conservativity
over IPL; and the Hilbert embedding (half of their Theorem 2.3). -/
import LaxLogic.PLLFormula
import LaxLogic.PLLProof
import LaxLogic.PLLAxiom
import LaxLogic.PLLNDCore
import LaxLogic.PLLConsequence
import LaxLogic.PLLTheorems
import LaxLogic.PLLHilbert
import LaxLogic.PLLSubst
import LaxLogic.Deriv

/- ## 2. Constraint semantics: soundness, completeness, the FMP

F&M's constraint models with fallible worlds and the `∀∃` clause for
`◯`, reproduced field for field.  Soundness and completeness; the finite
model property (their Theorem 4.6); a finitary canonical model needing
no Zorn; and A-bisimulation with its invariance theorem. -/
import LaxLogic.PLLKripke
import LaxLogic.PLLCompleteness
import LaxLogic.PLLFrames
import LaxLogic.PLLFiniteModel
import LaxLogic.PLLFinComp
import LaxLogic.PLLCountermodel
import LaxLogic.Bisim

/- ## 3. `SC` — the cut-free sequent calculus

F&M Figure 2 (Iemhoff's `GPLL`).  Cut elimination is their Theorem 2.6;
with it come the subformula property and the disjunction property
(Lemma 2.7(i)). -/
import LaxLogic.PLLSequent

/- ## 4. `G4iLL` refuted, and `G4c` — the repaired calculus

Iemhoff's contraction-free `G4iLL`, transcribed faithfully, is
**machine-checked INCOMPLETE** for PLL: `PLLG4Gap` exhibits
`◯((◯p→r)→◯p), ◯p→r ⇒ r`, derivable in `SC` and rejected by the verified
decider.  `G4p` is the first repair, `G4h`/`G4c` the final one, for which
cut, height-preserving and then full cut-free contraction, completeness
and the equivalences `G4iLL″ = SC = LaxND = Tm` are all unconditional.
Decidability is F&M Theorem 2.8. -/
import LaxLogic.PLLFinsetKit
import LaxLogic.KleeneBrouwer
import LaxLogic.PLLG4
import LaxLogic.PLLG4Inv
import LaxLogic.PLLG4Adm
import LaxLogic.PLLDecide
import LaxLogic.PLLG4Gap
import LaxLogic.PLLG4P
import LaxLogic.PLLG4H
import LaxLogic.PLLG4HInv
import LaxLogic.PLLG4HAdm
import LaxLogic.PLLG4HStr
import LaxLogic.PLLG4HCtr
import LaxLogic.PLLG4HCut
import LaxLogic.PLLG4HComp
import LaxLogic.PLLG4Space
import LaxLogic.PLLG4Set
import LaxLogic.PLLG4Dec
import LaxLogic.PLLG4Term
import LaxLogic.PLLG4ipComplete

/- ## 5. Proof terms, and strong normalisation

The computational metalanguage of `LaxND`, its reduction, confluence,
and **strong normalisation of the full interleaved reduction** (β for
every connective plus `let`-assoc) by Lindley–Stark ⊤⊤-lifting.  A
result about terms, not about derivability. -/
import LaxLogic.PLLTerms
import LaxLogic.PLLNormal
import LaxLogic.PLLConfluence
import LaxLogic.PLLIdempotency
import LaxLogic.PLLReducibility
import LaxLogic.PLLStrongNorm
import LaxLogic.PLLTopTop
import LaxLogic.PLLTactics

/- ## 6. Curry's problem

Fairtlough–Mendler, *A Solution to Curry's Problem* (TYPES 2000,
LNCS 2277), Theorem 6 — `PLL ⊢ φ` iff `IPL ⊢ φ^C` for every standard
constraint `C` — proved in both directions, with Corollary 10: no
finite set of constraints is complete. -/
import LaxLogic.PLLCtxCompleteness

/- ## 7. PCLL, and the infallible extension

F&M Theorem 4.7: `PLL + ◯(A∨B) ⊃ (◯A∨◯B)` is complete for mutually
confluent models, and `PLL + ¬◯⊥` for models with no fallible worlds.
Ours: the variable-free fragment collapses to `{⊥, ⊤}` under `¬◯⊥`, and
the two extensions diverge on `◯`-normalised sequents. -/
import LaxLogic.PLLConfluentComplete
import LaxLogic.PLLNoFall
import LaxLogic.PLLNoFallNF
import LaxLogic.PLLNoFallSep

/- ## 8. The closed fragment RN(◯,{})

`closed_lax_infinite`: the `◯`-only, variable-free fragment is infinite —
proved three independent ways (height, width, depth).  So no finite
operation table can ever close it. -/
import LaxLogic.PLLLaxInfinite

/- ## 9. Craig interpolation

By Maehara's method over the cut-free calculus. -/
import LaxLogic.PLLCraig

/- ## 10. Search, countermodels, diagrams

The certificate-carrying engines: untrusted search, kernel-checked
results.  A verified countermodel checker and emitter, the `#search` /
`#refute` / `#refuteConf` / `#draw` commands, and a runnable manual. -/
import LaxLogic.FormattingUtils
import LaxLogic.GuardMsgsShow
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchEx
import LaxLogic.PLLSearchConf
import LaxLogic.PLLSearchNoFall
import LaxLogic.PLLSearchCmd
import LaxLogic.PLLSearchPin
import LaxLogic.PLLCountermodelEmit
import LaxLogic.PLLDiagram
import LaxLogic.PLLDiagramCmd
import LaxLogic.PLLSearchDemo
import LaxLogic.PLLDemos
import LaxLogic.PLLRun

/- ## 11. Timing analysis of combinational circuits

Mendler's proofs-as-delays reading (*Timing Analysis of Combinational
Circuits in Intuitionistic Propositional Logic*, FMSD 17(1), 2000):
proof terms evaluated in the strong monad `T A = ℕ × A` with `+` for
sequential composition and `max` for reconvergent fanout.  His §7 `CIRC`
example is reproduced with its false-path punchline. -/
import LaxLogic.PLLConstraints
import LaxLogic.PLLTiming
import LaxLogic.PLLTimingRipple
import LaxLogic.PLLTimingAdder
import LaxLogic.PLLTimingLookahead
import LaxLogic.PLLAsync

/- ## 12. Belief, nuclei, and realisability

PLL read as a logic of idealised evidential belief.  `◯` is a nucleus;
it validates K; classical belief is degenerate (every nucleus on a
Boolean algebra is closed).  The crown is
`derivable_iff_no_realP_refutation`: a sequent is derivable exactly when
no presented-strategy realisability structure refutes it. -/
import LaxLogic.NucleusJoin
import LaxLogic.PLLEvidence
import LaxLogic.PLLRealCompleteness
import LaxLogic.BeliefCollapse
import LaxLogic.BeliefBooleanIso
import LaxLogic.BeliefNormality
import LaxLogic.BeliefIdealisation
import LaxLogic.BeliefFalsum
import LaxLogic.BeliefOpenClosed
import LaxLogic.BeliefRealisability

/- ## 13. `FRJ(G)` — refutation as positive derivation, for IPC

Fiorentini and Ferrari's forward refutation calculus (TOCL 21(3), 2020;
arXiv:1804.06689), formalised faithfully: soundness, completeness, and
`frj_iff_not_IPL`.  No modality — this is the intuitionistic base case,
independent of everything above. -/
import FRJ.Basic
import FRJ.Model
import FRJ.Calculus
import FRJ.Step
import FRJ.Sound
import FRJ.Fallible
import FRJ.Modal
import FRJ.Minimal
import FRJ.Saturate
import FRJ.Erase
import FRJ.Extract
import FRJ.Complete
import FRJ.Audit

/- ## 14. `Reject` — refutation as positive derivation, for PLL

The forward model-generating refutation calculus for PLL, after
Fiorentini–Ferrari's JLC 2021 S4 calculus.  T1: the constructors are
sound.  T2: they are complete — every countermodel of a reduced model is
built by `solo` and `join`, so a certificate format becomes a calculus. -/
import Reject.Build
import Reject.Audit
import Reject.Join
import Reject.Height
import Reject.Bisim
import Reject.Complete
import Reject.Reduce
import Reject.Cert
import Reject.Demo

/- ## 15. Focused proof search: focalization for PLL, and UI for IPC

Liang–Miller's `LJF` for the intuitionistic base, and `LJF◯` — its
lax-flagged extension.  Two finished results: focalization for PLL
(`LJFO.bridge_iff` / `LJFO.FocalizationPLL` — LJF◯ derivability
coincides with PLL derivability, so focused search loses nothing), and
uniform interpolation for IPC (`LJFIPC.uniform_interpolation_IPC`,
Pitts' properties for the `◯`-free fragment).

Uniform interpolation for **PLL** is a different question and is OPEN;
nothing here claims it.  The modules that pursue it (`LaxLogic.LJFO`
with its conditional obligation `CimpAnt`, `LJFOSearch`, `FRJO/`) are
not imported. -/
import LaxLogic.LJF
import LaxLogic.LJFComplete
import LaxLogic.LJFOCore
import LaxLogic.LJFOBridge

/- ## 16. Axiom-audit tooling

`#choice_path` / `#choice_sources` / `#axiom_path` / `#axiom_pin`:
`#print axioms` says *whether* a declaration depends on an axiom, not
*why*.  These answer the why, over `collectAxioms` — the only sound
oracle. -/
import Meta.Rules
import Meta.Slime
import Meta.Audit
