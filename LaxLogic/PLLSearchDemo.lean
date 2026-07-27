import LaxLogic.PLLSearchCmd

/-!
# A runnable companion to `docs/search-manual.md`

Open this file in VS Code, put the cursor on any command below, and read the
Lean infoview: what the infoview shows is exactly the text in the docstring
immediately above that command.

That is not a convention maintained by hand.  Every example here is written as

```lean
/--
info: <the output>
-/
#guard_msgs in
<the command>
```

`#guard_msgs` compares the command's actual output against the docstring and
fails the build if they differ.  So in this file:

* a **docstring beginning `info:`** is *printed* — the toolkit produced it, and
  the build checks that it still does;
* everything **below `#guard_msgs in`** is *typed* — it is what you would write
  in a file of your own;
* the `#guard_msgs`/docstring wrapper itself is scaffolding for this file only.
  In your own file you would type just the command and look at the infoview.

One command is left unguarded, at §5.4, because its output is a twenty-world
model; it is marked there.

The sections follow §§2–6 of `docs/search-manual.md`, which explains what the
commands do and defines the vocabulary (certificate, witness, node budget,
discover-then-pin, mutual confluence).  This file does not repeat any of that;
it shows the same examples running.

Your own file needs two lines, and no more:

```lean
import LaxLogic.PLLSearchCmd
open PLLFormula PLLND PLLND.Search
```

Note on names: this module lives in `namespace PLLND.SearchDemo`, so
`#print axioms` reports e.g. `PLLND.SearchDemo.unit_derivable`.  At the top
level of a file of your own the same line would read `unit_derivable`.
-/

open PLLFormula PLLND PLLND.Search

namespace PLLND.SearchDemo

/-! ## 1. The sequents used below

Ordinary definitions; nothing search-specific.  `docs/search-manual.md` §1
fixes the notation. -/

/-- `⊢ p ⊃ ◯p` — the unit of the modality.  Derivable. -/
def unitSeq : PLLFormula := (prop "p").ifThen (prop "p").somehow

/-- `⊢ ◯p ⊃ p` — the converse.  Underivable. -/
def escSeq : PLLFormula := ((prop "p").somehow).ifThen (prop "p")

/-- `⊢ (p ∧ ◯q) ⊃ ◯(p ∧ q)` — derivable, and a little bigger. -/
def conjSeq : PLLFormula :=
  ((prop "p").and ((prop "q").somehow)).ifThen (((prop "p").and (prop "q")).somehow)

/-- The two hypotheses of `◯((◯p ⊃ r) ⊃ ◯p), ◯p ⊃ r ⊢ r`: the sequent that
G4iLL″ derives and Iemhoff's G4iLL misses. -/
def gapA : PLLFormula :=
  ((((prop "p").somehow).ifThen (prop "r")).ifThen ((prop "p").somehow)).somehow

/-- Second hypothesis of the sequent of `gapA`. -/
def gapB : PLLFormula := ((prop "p").somehow).ifThen (prop "r")

/-- `◯(p ∨ q)` — the premise of the distribution axiom (§5). -/
def premise : PLLFormula := ((prop "p").or (prop "q")).somehow

/-- `◯p ∨ ◯q` — its conclusion. -/
def goal : PLLFormula := ((prop "p").somehow).or ((prop "q").somehow)

/-- The distribution instance `◯(p ∨ q) ⊃ (◯p ∨ ◯q)`, as a PLL formula. -/
def inst : PLLFormula := ConfluentU.distF (prop "p") (prop "q")

/-! ## 2. The three commands (manual §2) -/

/-! ### 2.1 `#search` on a derivable sequent

You type the one command.  The infoview prints four things: the sequent, the
verdict, the proof term, and — under `pin it:` — Lean source you can copy. -/

/--
info: sequent  ⊢ p ⊃ (◯p)
verdict  PROVED   (→R (◯R init))

proof term (G4iLL″):
  (→R (◯R init))

pin it:
theorem found :
    Nonempty (LaxND [] ((PLLFormula.prop "p").ifThen ((PLLFormula.prop "p").somehow))) :=
  PLLND.Search.proved_sound
    (.impR (.laxR (.init (by decide))))

#print axioms found
-/
#guard_msgs in
#search [] ⊢ unitSeq

/-! ### 2.2 Pinning what §2.1 found

Select the five lines under `pin it:` in the infoview, paste them into your
file, and rename `found`.  Nothing else changes: the text below is that paste,
with `found` renamed to `unit_derivable`.  The search is now out of the
picture — the kernel rechecks the proof term on its own. -/

theorem unit_derivable :
    Nonempty (LaxND [] ((PLLFormula.prop "p").ifThen ((PLLFormula.prop "p").somehow))) :=
  PLLND.Search.proved_sound
    (.impR (.laxR (.init (by decide))))

/-- info: 'PLLND.SearchDemo.unit_derivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unit_derivable

/-! ### 2.3 `#refute` on an underivable sequent

`#refute` skips proof search and runs the countermodel engines only.  The
model is printed in the compact picture form: `*` marks the refuting world,
`⊑>` the cover successors of `Rᵢ`, `⊳` the `Rₘ` successors, `⊩` the atoms
forced (manual §2, "Reading the model picture"). -/

/--
info: sequent  ⊢ (◯p) ⊃ p
verdict  REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1

countermodel:
2 worlds, refuting world 0; fallible {1}
  *w0  ⊑> {1}  ⊳ {1}  ⊩ —
   w1  ⊑> {}   ⊳ {}   ⊩ ⊥ (fallible)

pin it:
theorem underivable :
    ¬ Nonempty (LaxND [] (((PLLFormula.prop "p").somehow).ifThen (PLLFormula.prop "p"))) :=
  FinCM.not_provable_of_check
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], [(1, "p")]⟩) (w := 0) (by decide)

#print axioms underivable
-/
#guard_msgs in
#refute [] ⊢ escSeq

/-! ### 2.4 Pinning what §2.3 found

Again a paste of the `pin it:` block, with `underivable` renamed.  The `by
decide` is the kernel running `checkB` on the concrete model. -/

theorem esc_underivable :
    ¬ Nonempty (LaxND [] (((PLLFormula.prop "p").somehow).ifThen (PLLFormula.prop "p"))) :=
  FinCM.not_provable_of_check
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], [(1, "p")]⟩) (w := 0) (by decide)

/-- info: 'PLLND.SearchDemo.esc_underivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms esc_underivable

/-! ### 2.5 `#refute` when it finds nothing

Run on a derivable sequent, `#refute` reports an absence, not a claim.  Both
negative engines are incomplete, so this output never means "derivable". -/

/--
info: sequent  ⊢ p ⊃ (◯p)
verdict  NO COUNTERMODEL FOUND

This asserts nothing about the sequent: the battery and the closure emitter
are both incomplete.  Widen Config.frames, or raise Config.emitClosureCap.
-/
#guard_msgs in
#refute [] ⊢ unitSeq

/-! ### 2.6 `#refuteConf`: the PCLL version

Same sequent shape, but only mutually confluent models are accepted, so the
theorem printed is about `ConfluentU.DerivU` and not about `LaxND`.  Manual
§5 says when this matters; §5.4 below shows a sequent on which it does. -/

/--
info: sequent  ◯p ⊢ p  (PCLL)
verdict  REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1 (mutually confluent)

countermodel:
2 worlds, refuting world 0; fallible {1}
  *w0  ⊑> {1}  ⊳ {1}  ⊩ —
   w1  ⊑> {}   ⊳ {}   ⊩ ⊥ (fallible)

pin it:
theorem underivable_pcll :
    ¬ ConfluentU.DerivU [((PLLFormula.prop "p").somehow)] (PLLFormula.prop "p") :=
  PLLND.RNC.not_derivU_of_checkConf
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], [(1, "p")]⟩) (w := 0) (by decide) (by decide)

#print axioms underivable_pcll
-/
#guard_msgs in
#refuteConf [(prop "p").somehow] ⊢ (prop "p")

/-! ### 2.7 Pinning what §2.6 found

The paste again.  Two `by decide`s this time: one for mutual confluence
(`confB`), one for the refutation itself (`checkB`). -/

theorem esc_underivable_pcll :
    ¬ ConfluentU.DerivU [((PLLFormula.prop "p").somehow)] (PLLFormula.prop "p") :=
  PLLND.RNC.not_derivU_of_checkConf
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], [(1, "p")]⟩) (w := 0) (by decide) (by decide)

/-- info: 'PLLND.SearchDemo.esc_underivable_pcll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms esc_underivable_pcll

/-! ### 2.8 A configuration after `with`

Any of the three commands takes `with cfg`.  Here the node budget is cut to
2, which is not enough even for this three-node search, so the verdict is
`UNKNOWN` and the reason names the field to raise. -/

/--
info: sequent  ⊢ p ⊃ (◯p)
verdict  UNKNOWN  positive stage truncated: the node budget of 2 ran out (raise Config.findBudget, or set it to none)

no certificate: the verdict line says which bound bit.
-/
#guard_msgs in
#search [] ⊢ unitSeq with { findBudget := some 2 }

/-! ## 3. The functions behind the commands (manual §3)

The commands display what these return.  In a program — sweeping a family of
sequents, say — you call them directly. -/

/-! ### 3.1 The two argument orders

`verdict`, `verdictWhy`, `countermodel` and `proof` take the sequent first and
default the configuration (to `budgetedConfig`).  `settle`, `settleWhy` and
`refute?` take the configuration first, so `{}` must be written out — and `{}`
means *no* node budget, unlike `budgetedConfig`. -/

/-- info: "REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1" -/
#guard_msgs in
#eval (verdict [] escSeq).summary

/-- info: "REFUTED" -/
#guard_msgs in
#eval (match settle {} [] escSeq with
       | .proved _      => "PROVED"
       | .refuted _ _ _ => "REFUTED"
       | .unknown       => "UNKNOWN")

-- A non-default configuration goes in by name in the sequent-first order.
/-- info: "REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1" -/
#guard_msgs in
#eval (verdict [] escSeq (cfg := { findBudget := none })).summary

/-! ### 3.2 Why an answer is `unknown`

`verdictWhy` and `settleWhy` carry a `Reason`, which names the parameter to
change.  The three below are `budgetExhausted`, `closureTooBig`, and the
absence of any reason at all. -/

/--
info: "UNKNOWN  positive stage truncated: the node budget of 2 ran out (raise Config.findBudget, or set it to none)"
-/
#guard_msgs in
#eval (verdictWhy [] unitSeq (cfg := { findBudget := some 2 })).summary

/--
info: "UNKNOWN  emit stage skipped: subformula closure has 2 formulas, cap is 0 (raise Config.emitClosureCap)"
-/
#guard_msgs in
#eval (verdictWhy [] (prop "p") (cfg := { frames := [], emitClosureCap := 0 })).summary

/-- info: none -/
#guard_msgs in
#eval (verdictWhy [] unitSeq).reason?

/-! ### 3.3 Widening the battery

A `Frame` is `⟨n, ri, rm, fall⟩`, with `ri` the strict part of `Rᵢ`,
transitively closed.  Prepending one to `defaultFrames` puts it first in the
sweep, so it is the frame the battery reports here. -/

/-- A five-world chain, prepended to the standard battery. -/
def myCfg : Config :=
  { frames := ⟨5, [(0,1),(1,2),(2,3),(3,4),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)],
                  [(0,1)], [4]⟩ :: defaultFrames }

/-- info: "REFUTED  5 worlds, refuting world 0, |Rᵢ| = 10, |Rₘ| = 1, fallible 1" -/
#guard_msgs in
#eval (verdict [] escSeq (cfg := myCfg)).summary

/-! ### 3.4 Rendering a model, and the snippet emitter

`Witness.summary` is the one-line form, `Witness.render` the picture, and
`Witness.snippet` the pinning theorem — the last is literally what `#refute`
prints under `pin it:`. -/

/-- info: some "2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 1" -/
#guard_msgs in
#eval (countermodel [] escSeq).map (·.summary)

/--
info: 2 worlds, refuting world 0; fallible {1}
  *w0  ⊑> {1}  ⊳ {1}  ⊩ —
   w1  ⊑> {}   ⊳ {}   ⊩ ⊥ (fallible)
-/
#guard_msgs in
#eval IO.println ((countermodel [] escSeq).map (·.render) |>.getD "")

-- Ask for the snippet under a name of your choosing, and it comes back ready
-- to paste: this is the text §2.4 pasted.
/--
info: theorem esc_underivable :
    ¬ Nonempty (LaxND [] (((PLLFormula.prop "p").somehow).ifThen (PLLFormula.prop "p"))) :=
  FinCM.not_provable_of_check
    (M := ⟨2, [(0, 1)], [(0, 1)], [1], [(1, "p")]⟩) (w := 0) (by decide)

#print axioms esc_underivable
-/
#guard_msgs in
#eval IO.println ((countermodel [] escSeq).map (·.snippet "esc_underivable") |>.getD "")

/-! ## 4. Proof terms (manual §4) -/

/-! ### 4.1 The rule tree

`Search.proof` is the positive engine alone, under the standard budget.
`G4cTm.pretty` renders the found term as its rule tree. -/

/-- info: some "(→R (◯R init))" -/
#guard_msgs in
#eval (proof [] unitSeq).map (·.pretty)

/-- info: some "(→R (∧L (◯L (◯R (∧R init init)))))" -/
#guard_msgs in
#eval (proof [] conjSeq).map (·.pretty)

-- A plain `#guard` prints nothing and fails the build if the search ever stops
-- finding the proof: the cheap way to keep a discovery under regression control.
#guard (proof [] unitSeq).isSome

/-! ### 4.2 The snippet, again

`G4cTm.snippet` is the positive counterpart of `Witness.snippet`; this is the
text §2.2 pasted. -/

/--
info: theorem unit_derivable :
    Nonempty (LaxND [] ((PLLFormula.prop "p").ifThen ((PLLFormula.prop "p").somehow))) :=
  PLLND.Search.proved_sound
    (.impR (.laxR (.init (by decide))))

#print axioms unit_derivable
-/
#guard_msgs in
#eval IO.println ((proof [] unitSeq).map (·.snippet "unit_derivable") |>.getD "")

/-! ### 4.3 Counting nodes

`G4cTm.findBounded budget Γ C` returns the result paired with the *remaining*
budget, so `budget - remaining` is the number of sequents visited.  That makes
it the profiler for choosing a `findBudget`. -/

/-- info: 3 -/
#guard_msgs in
#eval 100000 - (G4cTm.findBounded 100000 [] unitSeq).2

/-- info: 18 -/
#guard_msgs in
#eval 100000 - (G4cTm.findBounded 100000 [] conjSeq).2

/-! ### 4.4 The awkward sequent

`◯((◯p ⊃ r) ⊃ ◯p), ◯p ⊃ r ⊢ r` is the sequent G4iLL″ derives and Iemhoff's
G4iLL misses.  136 nodes, and the tree shows `→L◯◯` doing the work. -/

/-- info: some "(→L◯◯ (→L→ (→R (→L◯◯ (◯R init) init)) (◯L (◯R init))) init)" -/
#guard_msgs in
#eval (proof [gapA, gapB] (prop "r")).map (·.pretty)

/-- info: 136 -/
#guard_msgs in
#eval 100000 - (G4cTm.findBounded 100000 [gapA, gapB] (prop "r")).2

/-! ## 5. PCLL (manual §5)

PCLL is PLL plus `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`.  Its derivability relation is
`ConfluentU.DerivU Γ C`: natural deduction from `Γ` together with finitely
many instances of that scheme. -/

/-! ### 5.1 Proving in PCLL: pick the instances, then search

Add the instances to the context by hand and run the ordinary PLL searcher.
Choosing them badly costs a failed search and nothing else. -/

/--
info: some "(→L◯◯ (◯R (∨L (∨R₁ init) (∨R₂ init))) (∨L (∨R₁ (◯L (◯R init))) (∨R₂ (◯L (◯R init)))))"
-/
#guard_msgs in
#eval (proof [inst, premise] goal).map (·.pretty)

/-! ### 5.2 Pinning the PLL half

`#search [inst, premise] ⊢ goal` prints the same tree together with a pinning
snippet.  That snippet is long — it writes both formulas out in full and
supplies the implicit formula arguments of the left rules by name — but it is
still just a paste.  Here it is, with `found` renamed to `dist_pll`. -/

theorem dist_pll :
    Nonempty (LaxND [((((PLLFormula.prop "p").or (PLLFormula.prop "q")).somehow).ifThen (((PLLFormula.prop "p").somehow).or ((PLLFormula.prop "q").somehow))), (((PLLFormula.prop "p").or (PLLFormula.prop "q")).somehow)] (((PLLFormula.prop "p").somehow).or ((PLLFormula.prop "q").somehow))) :=
  PLLND.Search.proved_sound
    (.impLLaxLax (A := ((PLLFormula.prop "p").or (PLLFormula.prop "q"))) (B := (((PLLFormula.prop "p").somehow).or ((PLLFormula.prop "q").somehow))) (X := ((PLLFormula.prop "p").or (PLLFormula.prop "q"))) (by decide) (by decide) (.laxR (.orL (A := (PLLFormula.prop "p")) (B := (PLLFormula.prop "q")) (by decide) (.orR1 (.init (by decide))) (.orR2 (.init (by decide))))) (.orL (A := ((PLLFormula.prop "p").somehow)) (B := ((PLLFormula.prop "q").somehow)) (by decide) (.orR1 (.laxL (A := (PLLFormula.prop "p")) (by decide) (.laxR (.init (by decide))))) (.orR2 (.laxL (A := (PLLFormula.prop "q")) (by decide) (.laxR (.init (by decide)))))))

/-- info: 'PLLND.SearchDemo.dist_pll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dist_pll

/-! ### 5.3 Crossing to PCLL

`RNC.derivU_of_proved ps` discharges the instances: you pass the pairs whose
`distF` you added, and it hands back a `DerivU` for the original context. -/

theorem dist_pcll : ConfluentU.DerivU [premise] goal :=
  RNC.derivU_of_proved [(prop "p", prop "q")] dist_pll

/-- info: 'PLLND.SearchDemo.dist_pcll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dist_pcll

/-! ### 5.4 The trap: `#refute` succeeds where `#refuteConf` must decline

PLL refutes `◯(p ∨ q) ⊢ ◯p ∨ ◯q` and PCLL proves it (§5.3 just did).  So every
PLL countermodel to it is non-confluent, and a PCLL claim resting on one would
be wrong.  `#refuteConf` filters by confluence *during* the search and
correctly comes back empty; `#refute` does not filter and comes back with a
model.  Reaching for `#refute` here is the mistake the manual warns about. -/

/-- info: false -/
#guard_msgs in
#eval (RNC.refuteConf? {} [premise] goal).isSome

/-- info: true -/
#guard_msgs in
#eval (refute? {} [premise] goal).isSome

/--
info: sequent  ◯(p ∨ q) ⊢ (◯p) ∨ (◯q)  (PCLL)
verdict  NO CONFLUENT COUNTERMODEL FOUND

This asserts nothing.  Note that a countermodel found by #refute is NOT
usable here unless it is mutually confluent — that is exactly what this
command enforces.
-/
#guard_msgs in
#refuteConf [premise] ⊢ goal

-- The one unguarded command in this file.  `#refute` on the same sequent
-- succeeds, and what it returns is the closure emitter's work rather than the
-- battery's: twenty worlds, and a pinning snippet several thousand characters
-- long.  It is left unpinned for its size, not because it is unstable: the
-- search is a pure function and returns the same model every time.  Worth
-- looking at once, because it is the case the compact renderer of §3.4 exists
-- for — `repr` on this `FinCM` is several screens of raw pair lists.
--
-- infoview shows: `verdict  REFUTED  20 worlds, refuting world 4, |Rᵢ| = 198,
-- |Rₘ| = 101, fallible 1`, then the twenty-line model picture, then the
-- pinning theorem.
#refute [premise] ⊢ goal

/-! ## 6. Command-line tools (manual §6)

Nothing to run inside a Lean file; these are shell commands, listed here so
the tour is complete.

```
lake build LaxLogic                       -- build the library
lake env lean MyFile.lean                 -- elaborate a file of your own
lake build oracle2   && lake exe oracle2  -- ten-sequent benchmark, a smoke test
lake build rncprobe  && lake exe rncprobe -- the PCLL entailment matrix (slow)
scripts/laxrun.sh help                    -- the separate fuelled-decider CLI
```

The pinned PCLL certificates in the house style live in `wip/rncCert.lean`
(negative) and `wip/rncCertPos.lean` (positive); those need
`lake build wipshared` first.

## 7. Failure modes (manual §7)

Three worth knowing, none of which can be shown as a passing command:

* **`decide` or `rfl` on a search result inside a proof.**  It will fail, and
  that is expected: the searchers are `partial`, so `settle {} Γ C` does not
  reduce in the kernel.  Discovery happens at elaboration time (`#eval`,
  `#guard`, the commands); pinning happens by writing the certificate into the
  source, as §§2.2, 2.4, 2.7 and 5.2 do.
* **A transcribed proof term that will not elaborate.**  Supply the implicit
  formula arguments of the left rules by name — `(A := …)`, `(B := …)` — or
  let `G4cTm.snippet` do it, as in §5.2.
* **`PLLND.Search.decide` shadowing `Decidable.decide`.**  Under
  `open PLLND.Search` it does.  Use `settle`, which is the same function.
-/

end PLLND.SearchDemo
