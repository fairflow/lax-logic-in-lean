/-
# Layer 1 — the certification register

The RN(◯,{}) dictionary is built in three layers.  This is the bottom
one: **the list of theorems the database is allowed to cite**, each
re-pinned here with a `#guard_msgs`-checked `#print axioms`.

## Why a register at all, when the theorems already have pins

Because a pin in the file that proves a theorem checks that theorem.  A
pin HERE checks that the theorem is still the one the database thinks it
is citing.  If a cited result drifts — gains `Classical.choice`, gains
`sorryAx`, changes namespace, disappears — the failure surfaces at the
register, in one place, rather than as a silently weaker guarantee spread
across a few hundred entries.

Two gaps this exposed on the first pass, 2026-08-21:

* `LaxLogic/PLLLaxInfinite.lean:634` had a bare `#print axioms` with NO
  `#guard_msgs`.  It printed into the build log and checked nothing —
  a pin in appearance only.  Guarded here.
* `FRJ/Sound.lean` had **no pin at all** for `FRJ.soundness`, the
  theorem the entire refutation engine rests on.  Pinned here, and the
  answer is better than expected: `[propext, Quot.sound]`, choice-free.

## Where OPEN results go

An unproved statement gets a `def … : Prop` — a NAME for the statement,
asserting nothing — and never a sorried theorem.  A `sorry` ASSERTS: it
produces an inhabitant of the type, so `theorem foo : P := sorry` can be
applied, cited, and depended on exactly as if it were proved, and is
distinguishable from a proof only by reading its body or its axioms.
That is how the round-1 dictionary came to state 323 cell theorems of
which 87 were assertions.

The pattern is taken from `FRJO/Core.lean:270,277`, which states
`SoundnessFRJO` and `CompletenessFRJO` this way.  `FRJO/` is otherwise
dormant (excluded from the current scope) and this is the one thing
lifted out of it.

## What is NOT here

Layer 2 (the engines and the verification harness) is `tools/`; layer 3
(the database) does not exist yet.  Nothing in this file may import
either — the arrow runs upward only.
-/
import LaxLogic.PLLLaxInfinite
import LJF.OBridge
import LaxLogic.RN.Reps
import Reject.Cert
import Reject.Reduce
import FRJ.Sound
import FRJ.Search.Engine
import FRJ.Profile
import wip.ladder8
import wip.ljfo_link
import wip.rnEmbed
import wip.rnSep
import wip.rnSepColl

namespace Certified

/-! ## 1. The fragment is infinite, so no finite dictionary can close it

    RN(◯,{}) is infinite.

Proved three independent ways (height, width, depth); there is no floor
and the order is not a complete lattice.  This is the reason the database
is a growing record of DISCOVERED classes and not a table of all of them,
and the reason every negative claim in it must carry the representative
set it is relative to. -/

/-- info: 'PLLND.LaxInfinite.closed_lax_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.LaxInfinite.closed_lax_infinite

/-! ## 2. The RN({p}) ladder, and its embedding into RN(◯,{})

The ladder order is decidable arithmetic (`rnSub_order`), its cover
relation is computed and stable out to rung 24 (`covers9_stable`), and
the substitution `p ↦ ◯⊥` carries RN({p}) separations into RN(◯,{})
(`rn_transfer_pll`). -/

/-- info: 'PLLND.RNEmbed.rnSub_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.RNEmbed.rnSub_order

/-- info: 'PLLND.RNEmbed.covers9_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.RNEmbed.covers9_eq

/-- info: 'PLLND.RNEmbed.covers9_stable' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.RNEmbed.covers9_stable

/-- info: 'PLLND.RNEmbed.rn_transfer_pll' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.RNEmbed.rn_transfer_pll

/-! ## 3. The representatives, and the 2026-08-21 extension to `q15`

`q15 := q9 ⊃ q4` is a genuinely new class, not a renaming: it is
separated from every one of `q0 … q14`, and four syntactically different
formulas collapse onto it. -/

/-- info: 'RNReps.reps_length' does not depend on any axioms -/
#guard_msgs in
#print axioms RNReps.reps_length

/-- info: 'PLLND.SemUI.RND.sep_0_16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.SemUI.RND.sep_0_16

/-- info: 'PLLND.SemUI.RND.coll_w1_w2' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.SemUI.RND.coll_w1_w2

/-! ## 4. LJF◯ ⟺ PLL, and LJF◯ focused search as the PROOF engine

`bridge_iff` and `FocalizationPLL` are what make an LJF◯ answer an answer
about PLL at all.  `laxND_of_searchProves` is soundness of the search,
`searchProves_complete` its completeness; both choice-free.  Note the
asymmetry that travels with this engine permanently: `searchProves`
returning `false` certifies NOTHING at any fuel. -/

/-- info: 'LJFO.bridge_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.bridge_iff

/-- info: 'LJFO.FocalizationPLL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.FocalizationPLL

/-- info: 'TwoSidedLink.laxND_of_searchProves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TwoSidedLink.laxND_of_searchProves

/-- info: 'TwoSidedLink.searchProves_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TwoSidedLink.searchProves_complete

/-! ## 5. FRJ(◯) as the REFUTATION engine

`FRJ.soundness` is the whole of what the engine is entitled to claim.  It
CONSTRUCTS a countermodel out of the refutation derivation (`modR`); it
never enumerates candidate models.  That is why it is the canonical
finder, and why generate-and-test is banned as a discovery method: a
battery filter cannot beat a construction, it can only check one.

Completeness is OPEN — see §7. -/

/-- info: 'FRJ.soundness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.soundness

/-! ## 5a. The PROFILE LEMMA — the family enumeration is an artefact

PROVED 2026-08-21, sorry-free and choice-free (`FRJ/Profile.lean`, 35
theorems).  Every join rule's conclusion context and every side condition
is a function of four aggregates of the premise family

    Σ := ⋃ⱼ stab j   Θ := ⋂ⱼ th j   M := ⋂ⱼ (stab j ++ th j)   Υ := { rhs j }

and — the clause that makes MERGING safe — whether a further row may join
is a function of `(Σ, M)` alone:

    J1 (b ∷ 𝔉)  ⟺  J1 𝔉  ∧  b.stab ⊆ M(𝔉)  ∧  Σ(𝔉) ⊆ b.stab ++ b.th

So two families with the same profile produce the same conclusion AND
admit exactly the same extensions.  A search may keep one witness per
profile instead of enumerating families, which bounds the cost by the
GOAL's subformula universe rather than by the database size.

This licenses replacing `famsUpTo` with a hash-consed monotone fixpoint.
It does NOT by itself make such an engine correct: that needs the
differential test against the frozen oracle `wip/frj_sat.lean`.  Design
note: `docs/frj-profile-search.md`. -/

/-- info: 'FRJ.Profile.J1_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.Profile.J1_cons

/-- info: 'FRJ.Profile.joinCtxAtP_prof' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.Profile.joinCtxAtP_prof

/-! ## 6. `Reject.certifies` as the INDEPENDENT CHECKER

Registered as a checker, NOT as a finder.  `Reject.certifies` re-derives
a refutation through different code from FRJ(◯)'s, so it is a genuine
cross-check on a model FRJ(◯) built.  Driving it as a search means
filtering a battery of generated models, which is exactly the discovery
method the process rule excludes.

`not_laxND_iff_built` is the completeness theory of the refutation side.
It uses `Classical.choice`: it asserts that a countermodel EXISTS, and
does not construct one.  Cite it for theory, never as evidence for a
cell. -/

/-- info: 'Reject.not_laxND_of_certifies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Reject.not_laxND_of_certifies

/-- info: 'TwoSidedLink.two_sided_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TwoSidedLink.two_sided_disjoint

/-! The `Classical.choice` below is the whole point of the distinction:
that theorem says a countermodel EXISTS, and hands back no model.  It is
theory about the refutation side, never evidence for a cell.  Contrast
`FRJ.soundness` (§5), which is choice-free because FRJ(◯) BUILDS the model
it is talking about. -/

/-- info: 'Reject.not_laxND_iff_built' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Reject.not_laxND_iff_built

/-! ## 7. OPEN — stated, never asserted

Each of these is a `def … : Prop`.  It gives the statement a name so that
documents and plans can refer to it precisely, and it produces NO
inhabitant, so nothing can accidentally be built on it. -/

/-- **OPEN.**  Completeness of FRJ(◯): every PLL-invalid formula has a
refutation derivation.  Soundness is `FRJ.soundness` above; this is the
converse.  The live route is the demand-closure predicate `AllMet` of
`FRJ/Saturate.lean`, whose progress lemma IS this statement's open
content.  Status: `docs/frj-w4.md` §9. -/
def CompletenessFRJ : Prop := ∀ G : FRJ.Form, ¬ FRJ.PLL G → FRJ.Provable G

/-- **OPEN.**  Completeness of the SEARCH, as distinct from the calculus:
every derivation the calculus admits is found by saturation at some
`Config`.  This is what a negative search result would need in order to
mean anything beyond "not found at this bound".

Until it is proved, `Tools/Search.lean` has exactly one negative outcome,
`not-found-within-bound`, and no way to report "no derivation exists".
The two caps most likely to obstruct it are the join arities `jmax` and
`pmax`, which `FRJ.Search.Stats` did not record at all until
2026-08-21 (`jmaxBinding` / `pmaxBinding`). -/
def SearchComplete : Prop :=
  ∀ G : FRJ.Form, FRJ.Provable G →
    ∃ cfg : FRJ.Search.Config, FRJ.Search.derivable G (FRJ.Search.saturate G cfg).1 = true

/-! ### The "dual of LJF◯" claim gets NO declaration here

`FRJO/Core.lean` states its own `SoundnessFRJO` / `CompletenessFRJO` in
the style above, and those two are the register entries for it should
`FRJO/` ever wake up.  Nothing is restated here, because a `def … : Prop
:= True` would be a declaration with fake content — the same fault as a
sorried theorem wearing a different hat.

For the record, since the claim is cited elsewhere: "FRJ(◯) is derived as
the DUAL of LJF◯ search" is the opening line of `FRJO/Core.lean`, so it
is a claim about the DORMANT `FRJO/` development and not about `FRJ/`.
`FRJ/` is Fiorentini–Ferrari's FRJ(G) lifted to ◯, its soundness is
semantic (extract a Kripke model), and LJF◯ occurs nowhere in it.  The
duality is a construction, not a theorem; the two theorems that would
make it one are both open, and `FRJO/Core.lean` records them correctly.
-/

end Certified
