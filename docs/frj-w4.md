# W4 — completeness of FRJ◯ with modal goals

Design record, 2026-08-17.  Sources: the TOCL paper's §6 construction
(read at source, mechanised ◯-free in `FRJ/Minimal.lean`) and the repo's
machine-checked PLL semantics.  The JLC 2021 S4 paper is UNOBTAINABLE
(decision recorded in `docs/frj-fidelity.md`); every device below is
OURS unless tied to a TOCL device.

## 0. Where the ◯-free construction stands

`minMod` (Lemma 6.4 as data) runs on the lexicographic measure
`(ht a, t, size C)`: world height, irregular-before-regular, right
formula.  Two witness records:

    IrrWit a C : Σ;Θ → C  with  Σ ⊆ Λ*_a ⊆ Σ∪Θ           (anchored AT a)
    RegWit a C : Γ ⇒ C   with  wld ≥ a  and  Λ*_wld ⊆ Γ   (anchor may FLOAT up)

The float (`wld`) is how `C = A ⊃ B` refuted only strictly above `a` is
handled: the sequent is built at the witness `e` and *serves* at `a`,
since refutation persists downward and `Λ*` grows upward (modulo `Cl`,
`lamStar_mono`).  Entry point: `minMod K.root 1 G`.

## 1. The two calculus deltas

**(D1) `Λ*` learns the modality.**  `forceStar` gains the clause

    ⊩* (◯X)  iff  a ⊩ ◯X  and  a ⊮ X

exactly parallel to the implication clause (forced, body unforced =
irredundant left data; if `X` is forced then `◯X` is recovered by
`Clo.circ`).  Consequences, all mirroring the `⊃` cases:
`forceStar_shape` gains `isCirc`; `lamStar_subset_gHat` routes to
`Ĝ_◯`; `mem_clo_lamStar` gains the case (`X` forced → IH + `Clo.circ`;
`X` unforced → `◯X ∈ Λ*` literally); `lamStar_mono` likewise.  The
three lemmas `circPart_lamStar_nil` / `unionAll_circPart_nil` /
`lamStar_not_circ` become FALSE unconditionally and survive only under
`hcf`; the ◯-free paths of `Minimal.lean` keep them with `hcf`
threaded.

**(D2) the missing irregular rule `◯∉`.**  `FRJi` currently has no
constructor with a `◯`-consequent, so no context containing an
implication with modal antecedent is ever derivable: `hJ2` demands the
antecedent in `Υ = {rhs of the irregular premises}`, and nothing
supplies `rhs = ◯Z`.  Concretely `G = (◯p ⊃ q) ⊃ q` (PLL-underivable,
Peirce-shaped) has every countermodel forcing `◯p ⊃ q` with `◯p`
unforced at the root, so its root context is unreachable — a
completeness gap in the W3 calculus, found by the design pass.  The
repair is the exact analogue of `⊃∉` (a regular premise whose world
sits above and witnesses the failure):

    Γ ⇒ Z   (tag ∈ {barren, chain Z})
    --------------------------------  ◯∉,  Θ ⊆ Cl(Γ) ∩ Ĝ
          [] ; Θ → ◯Z

Soundness: the premise world `v` forces `Cl(Γ) ⊇ Θ`, and its whole
extracted modal cone refutes `Z` (that is what the tag certifies,
`tag_cone`), so `v ⊮ ◯Z` with `v` itself as the `∃`-witness.  `v`
realises the conclusion.  No analogue of `⊃∉`'s `hAnot` is imposed
until the soundness build demands one; if one is needed it will surface
as an unclosable goal, not as a silent weakening.

No other rule changes: joins keep prime/`∨` consequents (the paper's
discipline); `◯`-consequents are built on top by `◯∈` (regular) and
`◯∉` (irregular).

## 2. The visit, extended

Per world `a` of the input countermodel `K` (root infallible; upper
worlds MAY be fallible — that is the point of W3):

**Fallible worlds own no sequents.**  They force everything, refute
nothing; they enter only as `⋈^⊥` declarations at worlds below.

**The join trichotomy at an infallible `a`:**

1. modal part of `Λ*_a` empty → the barren joins, unchanged.
2. modal part nonempty, no pledge needed → the FALLIBLE join `⋈^⊥`:
   it keeps the whole modal zone with NO premise and no condition.
   (The extracted model then has a declared fallible successor that `K`
   does not have — harmless: `Mod(D)` must refute `G`, not reproduce
   `K`.  Cost: concise/minimal models are sacrificed; height bounds and
   minimality are W5, out of scope.)
3. pledge `Z` needed (a `◯∈` step at this world is coming) → the
   PROMISE join, family = the proper `Rm`-successors of `a` in `K`,
   every component built with consequent `Z` and pledge `Z`.

**The regular `C = ◯Z` case** (`t = 1`): let `e ≥ a` be minimal with
"the whole `Rm`-cone of `e` refutes `Z`" (nonempty by `a ⊮ ◯Z`; a
`minEta`-style minimiser `minZeta`).  If `e = a`: build the pledged
RegWit for `Z` at `a` (trichotomy case 1 or 3), then `◯∈` — the tag is
`barren` or `chain Z` by construction.  If `e ≠ a`: recurse at
`(e, 1, ◯Z)` (height drops) and float the anchor, exactly the `⊃`
pattern.  Two structural gifts make case `e = a` self-contained:

- `Rm` reflexive ⇒ `e`'s cone contains `e`, so `e ⊮ Z` and the `Z`-wit
  exists at `e` (measure: same height, same `t`, `size Z < size ◯Z`);
- `Rm` transitive ⇒ every proper `Rm`-successor `u` has its own cone
  inside `e`'s, so `u ⊮ Z` and the component recursion stays pledged
  (measure: `ht u < ht e`).
- if `e`'s cone is `{e}` alone, the modal part of `Λ*_e` is
  automatically empty (a forced `◯Y` with only the reflexive witness
  forces `Y`, which `⊩*` excludes), so the BARREN join suffices and no
  empty promise family is ever needed.

**The irregular `C = ◯Z` case** (`t = 0`): `◯∉` from the pledged
regular `Z`-wit at `e` (same `e`), with `Θ := nf(Λ*_a)`, `hTh` via
`lamStar_mono` up to the wit's anchor — the `impNotIn` case verbatim
with the tag condition in place of the antecedent conditions.

**Multiplicity is solved by anchors, not by tags.**  A world refuting
several distinct `◯Z₁, ◯Z₂` gets SEPARATE dedicated sequents (one per
right formula, as the paper's `σ(α, C)` bookkeeping already has it),
each pledged to its own `Zᵢ`, each possibly anchored at a different
witness `eᵢ`.  The single-pledge `Tag` never has to carry two pledges
at once.  No pledge-set generalisation, no multi-conclusion sequents.

## 3. The corner and its resolution (settled 2026-08-17, Screen 4)

The exposed case was: build the pledged `Γ ⇒ Z` at anchor `u` with
`Z = A ⊃ B` compound and `u ⊮ A`.  The ◯-free construction would FLOAT
to the minimal `e' ≥ u` forcing `A` — but `e'` can lie outside the
pledging cone.  `FRJ/Modal.lean` Screen 4 (`pledgeChain`, a three-world
chain, kernel-checked) shows the configuration is REALISABLE, and the
same model shows the way out:

**Pledged witnesses anchor at classical refutation sites; they never
float.**  For `Z = A ⊃ B` refuted at `u`, anchor at any `m ≥ u` with
`m ⊩ A` and `m ⊮ B` (a `minEta` witness): there `⊃∈` discharges `A`
from the closure locally and the recursion continues on `B` at the SAME
anchor.  For `Z = ◯Z'` the anchor is a cone-refuting witness and the
recursion nests one pledge deeper (right-formula size drops).  The
recursion climbs `≤` and terminates at `≤`-maximal worlds, where the
modal part of `Λ*` is empty — `circPart_lamStar_nil_of_maximal`, PROVED
— so the barren join suffices and the tag is `barren` for free.

Two facts make the re-route legitimate:

- a promise component is a SEQUENT, not a world of `K`: `Mod(D)` must
  refute the goal, not reproduce `K`, so components may be anchored at
  ANY `K`-world whose `Λ*` gives the (J5)/(J7) closure coverage —
  anchors above the nominal `Rm`-successor still cover, since forcing
  persists up and `Λ*` grows up modulo `Cl` (`lamStar_mono`);
- a barren-tagged component certifies its pledge by its own right
  formula alone: the extracted cone is its root, and the root refutes
  `Z` because `Z` IS its consequent (Lemma 3.9(i)).

So no calculus change is needed and no saturation property of `K` has
to be assumed.  What remains mandated before the construction is
scoped:

- **(T2) end-to-end corpus.**  A bounded forward-saturation engine for
  FRJ◯ (subsumption, tiny signatures), run on the two-sided engine's
  certified corpus: every PLL-underivable `G` in range must become
  `Provable`; no PLL-derivable one may (soundness already forbids it,
  so this direction is an engine-correctness control).  Underivable
  seeds: `¬◯⊥`, `◯p ⊃ p`, `(◯p ⊃ q) ⊃ q` (now a PROVED cell,
  `provable_circ_peirce`), `¬¬◯⊥`, `◯(p ∨ q) ⊃ ◯p ∨ ◯q`, `p ∨ ¬p`,
  `◯p ⊃ ◯q`, and `◯`-goal shapes `◯Z` with `Z` compound (the corner's
  own family).  Derivable CONTROLS: the unit and multiplication
  instances, `⊤`, and the G4iLL blocker
  `◯((◯p → r) → ◯p) ⊃ ((◯p → r) → r)` — PLL-derivable (it is the
  sequent G4iLL *misses*; an earlier draft of this list had it on the
  wrong side).

## 4. Statement targets

    (A) completeness  : ¬ K.Fal K.root → ¬ K.force K.root G → Provable G
    (B) frj_iff_countermodel :
          Provable G ↔ ∃ K, ¬ K.Fal K.root ∧ ¬ K.force K.root G
    (C) frj_iff_not_PLL : Provable G ↔ ¬ PLL G        [stretch]

(A) drops both `hcf` and global infallibility from the W3 statement.
(B)'s soundness half is done (extracted roots are p-sequent worlds,
never fallible).  (C) additionally needs "every PLL-invalid formula has
a FINITE `FRJ.Kripke` countermodel" — a bridge from the repo's
decidability/canonical machinery or from the two-sided engine's
Built-tree certificates; scoped only after (A).

Out of W4 scope, recorded for W5: height bounds (`Rn`, the quadratic
derivation-height), minimal-height countermodels, and the dual
saturated-database direction (`GBU`-style proof extraction for PLL).

## 5. Order of work

1. ~~`◯∉` into `FRJi` + `Step.lean` plumbing + the `lemma39I` soundness
   case~~ **DONE 2026-08-17**: rule, plumbing (`Step`, `OccI`, `wfI`,
   extraction), soundness case, and the witness cell
   `provable_circ_peirce` / `not_PLL_circ_peirce_by_calculus`, all
   green with pins.
2. ~~(D1) `forceStar`/`lamStar` modal clause + `hcf`-threading~~
   **DONE 2026-08-17**: the `⊩*` `◯`-clause is in; Lemma 6.5
   (`mem_clo_lamStar`) now holds for the FULL modal signature and
   DROPPED `hcf` (only infallibility remains, for `⊥`); the three
   nil-lemmas are `hcf`-conditional; `circPart_lamStar_nil_of_maximal`
   added; the ◯-free `minMod` compiles threaded.
3. ~~(T1) the semantic probe~~ **DONE 2026-08-17** — Screen 4; corner
   resolved by anchor choice, §3.
4. ~~(T2) the saturation engine skeleton + corpus run~~
   **DONE 2026-08-17** — §6 below.  It caught a completeness defect
   (§7): `¬¬◯⊥` is underivable in the current calculus.
5. The §7 repair: `Ax^I◯` seeds, the compound-body lifts, the
   join-variant `Υ`-restriction, soundness re-cleared; `nn_circ_bot`
   must turn `pass`.
6. The pledged visit (`minZeta`, pledged `RegWit` with tag field, the
   join trichotomy, the modal `minMod` cases) — after 5, since the
   `◯`-goal irregular case rests on the seeded rules.

## 6. (T2) results — the engine and the corpus run (2026-08-17)

`wip/frj_sat.lean`, `lean_exe frjsat`.  **Derivation-carrying**: every
database row packs its own `FRJr`/`FRJi` term, side conditions
discharged by `Decidable` instances at insertion — the engine cannot
misapply a rule (a faithfulness bug is a type error), and a hit
inhabits `Provable G` outright.  Forward saturation with subsumption
(`barren ≥ chain D ≥ blocked`; contexts by `⊇`; the one non-monotone
consumer is `⊃∉`'s `hAnot` gate, mitigated by a purged `Θ`-candidate
and flagged in the engine banner), joins bounded at premise arity 3 and
promise arity 2, `⊃∈` zone splits fully enumerated to width 10 — every
cap reported on the verdict line; none was hit on this corpus.

Result (run 2, corrected corpus): **10 of 11 PLL-underivable formulas
derived** (`pass`), **one genuine `flag`**, **4/4 PLL-derivable
controls saturate to fixpoint underived** (`control-ok`), no `FAIL`:

    neg_circ_bot     pass        rounds=3  RS=3   IS=3
    circ_imp         pass        rounds=3  RS=3   IS=3
    circ_peirce      pass        rounds=4  RS=4   IS=5   (the ◯∉ witness)
    nn_circ_bot      FLAG        rounds=2  RS=3   IS=4   (fixpoint, § 7)
    nnn_circ_bot     pass        rounds=6  RS=5   IS=8
    circ_or_split    pass        rounds=4  RS=23  IS=7   (the modal-zone keeper)
    excluded_middle  pass        rounds=3  RS=4   IS=5
    circ_and_goal    pass        rounds=3  RS=4   IS=4   (◯-goal, ◯∈)
    circ_imp_goal    pass        rounds=3  RS=3   IS=4   (compound-◯ family)
    circ_mono_atoms  pass        rounds=4  RS=8   IS=6
    godel_dummett    pass        rounds=3  RS=5   IS=7
    unit_inst        control-ok  rounds=2
    mult_inst        control-ok  rounds=2
    top              control-ok  rounds=1
    g4ill_blocker    control-ok  rounds=5  RS=20  IS=62  (fixpoint, no derivation)

The passes cover both new devices end-to-end (`circ_peirce` through
`◯∉`; `circ_or_split` keeping the modal zone through `⋈^⊥`; the
`◯`-goal family through `◯∈`), and the database sizes confirm the
top-down economics: single-digit rows for most goals, the largest
signature saturating at 82 rows in 5 rounds.

## 7. The (T2) finding — `¬¬◯⊥` is underivable in the current calculus

The corrected cell `¬¬◯⊥` (an early corpus draft had `¬¬¬◯⊥`, which
passes) saturates to fixpoint in 2 rounds at 7 rows with every
enumeration exhaustive at that size: **the current FRJ◯ cannot derive
it**, though it is PLL-underivable (every infallible model refutes it
at the root).  This is a completeness defect that neither the § 1–§ 3
design analysis nor Screen 4 caught — found only by the corpus, which
is what (T2) exists for.

**The cycle.**  `G = (¬◯⊥) ⊃ ⊥`; the signature has NO atoms, so
`Ĝ_at = ∅` and the axioms carry empty stable data.  Deriving `G` needs
a regular row `Γ ⇒ ⊥` with `¬◯⊥ ∈ Γ`; keeping `¬◯⊥ = ◯⊥ ⊃ ⊥` in a
join context needs `◯⊥ ∈ Υ`, i.e. an irregular premise with right
formula `◯⊥` AND a second zone rich enough to survive the `Θ`-
intersection.  Only `◯∉` produces a `◯`-right formula, and its zone is
bounded by `Cl` of its regular premise's context — here `Cl(∅) = ∅`,
because the world that realises the sequent (the one-world infallible
model, which forces `¬◯⊥` VACUOUSLY) is invisible to the syntactic
closure.  The premise `◯∉` needs is the very row being built.

**The measure diagnosis.**  `⊃∉` crosses from the irregular to the
regular family only with a STRICT height drop (its witness lies
properly above).  `◯∉`'s witness may be the world itself (`Rm` is
reflexive), so it adds a `t = 0 → t = 1` edge at EQUAL height — exactly
the edge the paper's `(ht(α), t, size C)` induction forbids.  The rule
is sound (pinned) and does real work where the premise context is rich
(`circ_peirce`, `nnn_circ_bot`), but it cannot SEED the `◯`-right
formulas the way `Ax^I` seeds the prime ones.

**The repair sketch (next campaign).**  Add the modal irregular axiom

    Ax^I◯ :  ⊢  [] ; Ĝ_at \ {F}, Ĝ_imp, Ĝ_◯ → ◯F,   F prime, ◯F ∈ Sf^R

sound with `Ax^I`'s own realiser — a FINAL world refutes `◯F` exactly
when it refutes `F`, its modal cone being itself.  Lift compound bodies
monotonically where sound unconditionally (`Σ;Θ → ◯A` gives
`Σ;Θ → ◯(A ∧ B)`: cone-refutation is antitone in the body); the `∨`
and `⊃` bodies need their own analysis.  One soundness constraint is
already visible and MUST be respected: a `◯`-right premise used for the
`Υ`-restriction is sound for barren joins (the new root's cone is
itself) and for suitably pledged promise joins, but NOT for fallible
joins — the fallible successor forces every body, so an `⋈^⊥` root
with `◯Y ∈ Υ` would keep implications that are false at it.  The
`Υ`-restriction therefore becomes join-variant-dependent (full for
barren, `◯`-free for `⋈^⊥`, pledge-conditioned for promise joins), and
`lemma39I` must thread the consuming join's cone data.  Verdict
discipline: `nn_circ_bot` stays a standing `flag` in the corpus until
the repair lands and turns it into a `pass`.
