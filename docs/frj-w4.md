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
5. ~~The §7 repair~~ **DONE 2026-08-17**: the mounted-world `Ax^I◯`
   (zone = the bare final world's classical theory `vacZone`, the
   realiser CONTRIBUTED via `PreModel.leaf`), soundness re-cleared
   with pins, witness cell `provable_nn_circ_bot`, engine seeds
   `seedsIC`; corpus run 3 fully green (`nn_circ_bot` `pass`,
   controls hold).  The sketched compound-body lifts and join-variant
   `Υ`-restriction were NOT needed (§7, correction).
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

Run 3 (after the §7 repair): **11 pass / 4 control-ok / 0 flags** —
`nn_circ_bot` `pass` at rounds=3 RS=3 IS=5 (the two extra IS rows are
the `Ax^I◯` seeds), every other line unchanged except `circ_peirce`
(rounds 4 → 3: the seed shortcuts a `◯∉` detour).

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

**The repair (LANDED 2026-08-17) — the mounted-world axiom `Ax^I◯`.**

    Ax^I◯ :  ⊢  [] ; vacZone(F) → ◯F,     F prime, ◯F ∈ Sf^R(G)

where `vacZone G F = nf G ((Ĝ).filter (classForce (Ĝ_at \ {F})))` and
`classForce ats` is CLASSICAL Boolean evaluation over the atom list
`ats`, with the `◯`-clause `classForce (◯A) = classForce A`.  The zone
is the classical theory (restricted to `Ĝ`) of the axiom's realiser,
and — the design's one load-bearing novelty against the ◯-free
calculus — the axiom CONTRIBUTES that realiser as a mounted world:
`preI (axIC F) = PreModel.leaf (vacZone G F)`, a single infallible
barren world.  Soundness (`lemma39I0`/`lemma39I` cases, pinned through
the FRJ audit): the leaf forces its zone because single-world forcing
IS `classForce` (`leaf_force_iff`), and it refutes `◯F` because it
refutes `F` and is its own modal cone.  Every consuming join then
finds the `◯F`-refutation witness ABOVE ITS ROOT through `RootAbove`,
fallible joins included.

**Correction of the first sketch.**  The earlier text here (a) gave
the axiom the full zone `Ĝ_at \ {F}, Ĝ_imp, Ĝ_◯` — unsound: the bare
final world does not force, e.g., `◯⊥` itself, so the zone must be its
classical THEORY, not the whole signature; and (b) claimed the
`Υ`-restriction must become join-variant-dependent (`◯`-free for
fallible joins) — wrong, withdrawn: with the witness world mounted,
`root ⊮ ◯Y` flows down from the premise's contributed model through
`RootAbove` at every join variant.  The variance worry applies only to
a WORLD-LESS axiom design, which is exactly why the world is mounted.
No compound-body lifts were needed: the corpus closes with prime
bodies only (compound `◯`-goals go through `◯∈`).

**The semantic reading (Matthew, 2026-08-17): `◯⊥` is an honorary
atom.**  The closed fragment of PLL is very large (in this repo:
RN(◯,∅) is infinite), and its first letter behaves like an atom:

    u ⊩ ◯⊥   iff   ∀ v ≥ u, ∃ f ∈ F,  v Rm f

valuation-free, `≤`-persistent, tracking hereditary `Rm`-accessibility
of the fallible region.  A maximal infallible world therefore carries
one bit beyond its `Ĝ_at`-valuation: BARE (`◯⊥` false, and `◯Y ≡ Y` on
its own cone — `classForce`'s `◯`-clause) versus DECORATED by a
fallible `Rm`-successor (`◯⊥` true, and `◯Y ≡ ⊤`).  The seed layer of
a top-down model construction must enumerate final worlds over the
EXTENDED alphabet `Ĝ_at` + the `◯⊥` bit; the fallible join has always
supplied the decorated species, and `Ax^I◯` supplies the missing bare
species — that is all the repair is.  Between the extremes, non-final
worlds realise the graded `◯`-theories through promise joins.  (The
maximal version of the reading — `◯⊥` literally in `Ĝ_at`, axioms
partitioning on it — would re-found the zone discipline; not needed at
(T2) scale, on record as the fallback if the completeness construction
stalls on exactly this.)

**Outcome.**  `FRJ/Calculus.lean` (`classForce`, `vacZone`,
`vacZone_atom`, the `axIC` constructor), `Step.lean` (`wfI` case),
`Extract.lean` (`preI := leaf`, `preI_spec` generalised to the
label-equality form, `leaf_closed`, `leaf_force_iff`), `Sound.lean`
(the two cases).  Witness cell `provable_nn_circ_bot` /
`not_PLL_nn_circ_bot_by_calculus`, pinned `[propext, Quot.sound]`.
Engine: `seedsIC` wired into the initial database.  Corpus run 3:
**11 pass / 4 control-ok / 0 flags**.

## 8. Calculus round 2 (2026-08-17) and the pledged-visit blueprint

Probe cells run BEFORE scoping the visit (per the testing mandate) found
two derivability gaps past §7, both repaired and corpus-green (17 pass /
5 control-ok / 0 flags, commit a70007e):

- **`◯(◯p⊃p)` (cell `circ_circ_imp`).**  `◯∈` consumes a regular
  premise `Γ ⇒ Z`; for `Z = A ⊃ B` such sequents exist only at roots
  FORCING `A` (`⊃∈` is the sole regular `⊃`-introduction), while a
  `◯(A⊃B)`-refuting root can have its `A`-witness strictly above.
  Repair: the MODAL JOINS `⋈^◯` / `⋈^◯,p` — conclude `Γ ⇒ ◯Z` directly
  from irregular premises with `Z ∈ Υ`; the new root is its own modal
  cone (barren) or carries a promise family pledging `Z`; the root
  refutes `Z` by the (P3) premise mechanism.  No fallible variant, since
  a fallible cone-member forces every body.
- **`¬¬◯◯⊥` (cell `nn_circ_circ_bot`).**  Prime-only `Ax^I◯` re-enters
  the `◯∉` cycle one level up (`◯◯⊥` needs an irregular premise with
  rhs `◯◯⊥`, and `F = ◯⊥` is no prime).  Repair: `Ax^I◯` generalised to
  arbitrary `F` over arbitrary classical valuations `ats ⊆ Ĝ_at` with
  side condition `classForce ats F = false`; zone `vacZoneA G ats`.

Two support devices, also landed and soundness-covered:

- **`Covers Γ W Z`** (the chain-certificate order): `Z` reachable from
  `W` by `◯`-iteration, `∧`-superformula, or `⊃`-superformula with
  antecedent in `Cl(Γ)`.  Every pledge comparison (`◯∈`, `◯∉`, promise
  components) now goes through it; `tag_cone` proves it sound via
  `covers_refutes` (a cone hereditarily refuting `W`, over a label
  forcing `Cl(Γ)`, refutes everything `W` covers).  This is what lets a
  tag born `chain W` at a join serve goals wrapped above it — the
  single-formula tag could not re-certify across `◯∈` nesting or the
  `∧`/`⊃` wraps of the visit.
- **(J7) as a restriction**: `joinCtxAtP`/`joinCtxOrP` are filtered by
  membership in EVERY `Cl(Δᵢ)` (`restrictP`); the constructor condition
  reduces to the stable zones (`hJ7s`).  The visit could never discharge
  (J7) over the fat axiom zones' second-zone junk — and never needs the
  junk kept, while `Λ*`-members always survive the filter (forced at the
  component anchors, so `Cl(Δᵢ)`-certified by Lemma 6.5).

**The pledged-visit blueprint** (for `minModP`, mutual with `minMod`,
measure `(ht, 1, size C)` shared with the regular half):

    PWit K G u D C := { ctx, t, der : FRJr G t ctx C,
      tOK : t = barren ∨ ∃ W, t = chain W ∧ (W = D ∨ Covers ctx W C),
      wld ≥ u, ¬Fal wld, cov : Λ*_wld ⊆ ctx }

with input `hcone : ∀ v, u Rm v → v ⊮ D`.  At consumption `C = D`, so
`tOK` yields exactly the `Covers`-htag (`W = D` closes by `refl`).  The
cases: ∧ recurses on the refuted conjunct (`tOK` via `andL/R`); ⊃ with
`u ⊩ A` is a local `⊃∈` (`tOK` via the `imp`-clause, `Clo ctx A` from
Lemma 6.5 at `wld`); ◯Z′ with self-`minZeta` resets the pledge to `Z′`
(the inner `tOK` feeds `◯∈`'s htag; the result re-enters `tOK` through
the `circ`-clause); prime/∨ end in joins — barren when
`circPart Λ*_anchor = []`, else promise with family = the proper
`Rm`-successors, `Ds = D`, each component `minModP` at its successor
(`hcone` TRANSPORTS along `Rm` by transitivity, and each successor is
in the cone, hence refutes `D` and is infallible).

**The open corner.**  `hcone` does NOT transport along `≤`-floats: the
pledged ⊃-case with `u ⊮ A` must anchor at a `minEta`-witness
`m ≥ u` (`m ⊩ A`, `m ⊮ B`), and if `circPart Λ*_m ≠ []` the joins at
`m` need promise components refuting some `W′` with
`Covers ctx W′ (path)`, which no transported hypothesis supplies (`⊥`
fails `Covers`; `m`'s `Rm`-successors may force everything relevant).
Every adversarial configuration attempted so far SELF-DESTRUCTS: the
refutability of the top goal forces `◯`-witnesses inside the pledging
cone, which yield alternative anchors (`≤`-above in-cone `Rm`-witnesses)
whose modal zones are dischargeable.  Conjecture: the corner is
unrealisable, and the visit needs an anchor-choice policy (prefer
`minEta` candidates above in-cone modal witnesses) rather than a
calculus round 3.  The engine is the arbiter: any corner-shaped cell
that flags at fixpoint reopens the calculus; cells that pass pin the
policy the recipe must imitate.  Status: `minMod`'s modal cases and
`minModP` are the remaining build; everything they consume (`minZeta`,
per-world Lemma 6.5, `Covers`, the modal joins, filtered promise
contexts) is landed and green.

## 9. The induction-order obstruction (2026-08-16, continuation window)

Working §8 into Lean exposed a second obstruction, prior to and independent
of the ⊃-float corner. It concerns the **irregular ◯-case** of the visit,
not the pledged visit.

**The demand.** The joins' Υ-premises and the ∨-goal cells demand irregular
wits for ◯-formulas: given `a ⊮ ◯Z`, produce `Σ ; Θ → ◯Z` with
`Λ*_a ⊆ Σ ++ Θ`. The only premise-carrying intro is ◯∉ (`circNotIn`),
whose premise is a **regular** wit `Γ ⇒ Z` at an anchor `w ≥ a` with
`w ⊮ Z` and `Λ*_a`-coverage through `Cl(Γ)`.

**The wall.** `a ⊮ ◯Z` gives (minZeta) an `e ≥ a` whose cone refutes `Z`.
If some candidate `e ≠ a` exists, the recursion floats and height drops.
But the configuration

    cone(a) = {a},  a ⊮ Z,  ∀ v > a : v ⊩ ◯Z   (a the sole candidate)

is Kripke-realisable, and there the premise anchor can only be `a` itself:
the irregular ◯Z-visit at `a` must call the regular Z-visit **at the same
world**. Under the lexicographic measure `(ht, t, |C|)` this edge increases
`t`; under size-priority `(ht, |C|, t)` the Υ-edge (regular prime-visit →
irregular cells for arbitrary-size antecedents) breaks instead. No
lexicographic reordering fixes both: the abstract call graph at a fixed
world contains the cycle

    I(◯Z) → R(Z) → I(Y) with ◯Z a subformula of Y → I(◯Z)

(realisable e.g. with `(◯Z ⊃ W) ∈ Λ*_a`, whose hJ2-coverage puts ◯Z into
Υ, or with `Y = ◯Z ∨ W` as a goal disjunct). Structural recursion on
`(height, phase, size)` cannot found this proof.

**What the engine says.** Both corner shapes were probed and PASS:

    peirce_compound   = ((◯(q⊃p) ⊃ p) ⊃ p)          rounds=3
    circ_ante_circ_goal = ◯q ⊃ ◯(◯p ⊃ p)             rounds=6

Forward saturation has no demand cycle (it derives axioms first — the
generalised Ax^I◯ supplies premise-free irregular ◯-cells — and grows
monotonically), so the calculus settles these goals; the obstruction is in
the completeness *recipe*, not the calculus. Round 3 of the calculus is
NOT indicated.

**Consequence for §8.** The pledged-visit blueprint inherits this wall in
its own ◯-cases in addition to its ⊃-float corner. Both corners are now
understood as symptoms of the same thing: formula-structural recursion
over an arbitrary countermodel is the wrong organisation for the modal
calculus.

**Recommended route (next design): completeness via saturation closure.**
Mirror the engine instead of fighting it: define the finite saturation
closure of the axiom seeds under the rules (the object `lean_exe frjsat`
already computes), prove it is a fixpoint reached in finitely many rounds,
and show by induction on the **saturation order** (not formula structure)
that every semantic demand `(Λ*_a, C)` of a countermodel is met by some
saturated row. The regress above dissolves because saturation is founded
on round-number, and the axIC seeds break the I(◯Z)/R(Z) mutual demand at
its base. This also replaces the minZeta/minEta anchor-choice policies by
the subsumption order already implemented. Statement targets (A)/(B) of §5
item 6 are unchanged; only the proof organisation moves.

**Status.** FRJ◯ completeness remains OPEN. Landed and green: calculus
round 2 with soundness (Covers, `covers_refutes`, restrictP/(J7),
generalised Ax^I◯, the modal joins), per-world Lemma 6.5, minZeta, corpus
19 pass / 5 control-ok / 0 flags. The ◯-free completeness (hcf-conditioned)
stands as before.

### §9 addendum: the corner attack survived (2026-08-17)

Two further cells were built to realise the §9 configuration as sharply
as the language allows, using the poisoned antecedent `A := p ∨ (p⊃q)`
(classically true at the empty valuation but unforced, so `A ⊃ w`
escapes every `vacZoneA` and Ax^I◯ cannot serve the demand):

    corner_poisoned_axic = (A ⊃ w) ⊃ (w ∨ ◯z)            pass, rounds=5
    corner_poisoned_ups  = (A ⊃ w) ⊃ ((◯z ⊃ w) ⊃ (w ∨ z)) flag at default
                                                           budget; PASS at
                                                           jmax=4, rounds=6

Both are PLL-underivable by hand-built 2-world countermodels (for the
second: worlds a ≤ b, a: no atoms, b: {p, w}, both Rm-loops).  The flag
was a width cap (jmax=3), not a calculus failure.  Seven corner cells
now derive; **no completeness counterexample found**.  Design datum: the
derivations succeed with Θ-zones that do NOT cover Λ*_a, so the §8/§9
demand-set (per-world Λ*-coverage) is stronger than what the calculus
needs — the saturation-closure argument should track join-time
subsumption, not per-world coverage.

## 10. Statement (B) soundness half LANDED; the remaining target

PROVED, no ◯-freeness hypothesis, pinned `[propext, Quot.sound]`
(FRJ/Complete.lean, guarded in FRJ/Audit.lean):

    provable_root_countermodel :
      Provable G → ∃ K : Kripke, ¬ K.Fal K.root ∧ ¬ K.valid G

OPEN (= FRJ◯ completeness): the converse, statement (A)

    ¬ K.Fal K.root → ¬ K.force K.root G → Provable G

via saturation-closure (§9).  Decomposition for the next window:
(1) an abstract saturated-set predicate `Sat S` (closure under the rule
schema, seeds included) with the engine's fixpoint as witness;
(2) the round-order induction: every countermodel demand is met by a
row of any `Sat`-set, with the invariant weakened per the design datum
above (join-time subsumption); (3) (A) as the corollary at the root
row.  The corpus stands at 24 pass / 5 control-ok / 0 unresolved flags.

### §10 addendum: why no structural recursion exists (2026-08-17, sharpened)

Three facts close the design question:

1. **Θ-freedom.** A join consumes its irregular premises' Θ-zones by
   intersection, so a premise with Θ = [] is always admissible and only
   shrinks the conclusion's θ-part; Λ*-material reaches the conclusion
   through the rhs-cell's Σ and the stable zones instead.  The §8
   invariant `Λ*_a ⊆ Σ ++ Θ` on every cell was therefore self-imposed:
   the calculus requires it only of the row consumed by the FINAL cov.
   Consequence: `circNotIn` may take ANY Z-refuting regular row as its
   premise, not one anchored at the demanding world.

2. **The measure dichotomy.** Even with Θ-freedom, the hJ2-cells for
   stable-implication antecedents A (with `a ⊮ A`, |A| unbounded
   relative to the goal) force irregular-before-regular phase priority
   at fixed height — the paper's (IH2) — while the ◯-body edge
   `I(◯Z) → R(Z)` at a cone-trivial sole-candidate world forces
   regular-inside-irregular at fixed height with only a size drop.  No
   lexicographic combination of (height, phase, size) satisfies both;
   the supply order that resolves a given instance depends on the model
   (which cells happen to be derivable weakly, which worlds have proper
   Rm-successors), so the induction order must be computed per instance
   — this is precisely what saturation is.

3. **Locality of the bad edge.** If the demanding world has any proper
   Rm-successor u, then `sub_mi` gives a ≤ u, u ≠ a, so ht drops and
   the regular premise anchors at u with Λ*-transport by `lamStar_mono`
   — the paper's own pattern.  The obstruction is confined to worlds
   with `cone(a) = {a}` that are sole minZeta candidates.

The §10 route (saturation closure, round-order induction) is therefore
not one option among several: it is the only organisation compatible
with fact 2.  The invariant to carry per round: every demand met by a
row THE JOIN CAN CONSUME (hJ1/hJ2/hJ5-admissible), not Λ*-coverage.

## 11. The gluing LANDED: completeness modulo two named conditions (2026-08-17)

`FRJ/Saturate.lean` now carries the whole §10 organisation, sorry-free
and `Classical.choice`-free (`[propext, Quot.sound]`, audit-guarded):

- the demand closure `AllMet` and `completeness_of_allMet`;
- the case-builder layer (`metI_atom/bot/and/or/imp/circ/circ_syn`,
  `metR_and/imp/circ/prime/or`) — each visit case with its suppliers as
  inputs, per-wit infallibility (`wfal`) replacing global infallibility;
- `minZetaNS` (non-self-preferring candidate, soleness certificate) and
  anchor weakening;
- **`visit`**, total on the paper's measure `(ht, t, |C|)`: the Υ-edges
  drop phase, every float drops height, the in-layer edges drop size,
  and the single un-orderable edge — the irregular ◯-demand at a world
  that is its own SOLE minZeta candidate — is discharged by an explicit
  supplied cell;
- `completeness_of_supply`:

      hloc : ∀ b, circPart(Λ*_b) = []      (world-wise circ-free Λ*)
      hsup : CircSupply K G                 (the sole-candidate cell)
      ─────────────────────────────────────
      ¬ K.valid G → Provable G

`CircSupply` demands, at each sole-candidate world `a` and each
`◯Z ∈ sfR`, a tagged `Z`-row whose context `Clo`-grounds `Λ*_a`
(consumed by `metI_circ_syn` — the route the engine's own derivations
of the §9 corner cells take, e.g. an `Ax^R` row grounding implications
through `Clo`'s weakening clause).

**Remaining to full (A)**: discharge or weaken `CircSupply` (the open
kernel — per-instance row existence, engine-testable), and port the
promise-mode joins to lift `hloc` (the §8 pledge machinery as builders;
its pledge-existence question would enter as a second supply, so the
kernel formulation is uniform).  The ◯-free validation
(`allMet_of_circFree` → `completeness_via_closure`) confirms the new
organisation subsumes the landed Theorem 6.2 analogue.

### §11 addendum: the kernel weakened, then discharged in two regimes
(2026-08-17, same window)

Re-examining the visit's ◯-branch: `metI_circ` needs only a
`Z`-REFUTING anchor above `a` (not a cone-refuting minZeta candidate),
and `a ⊮ ◯Z → a ⊮ Z`, so the branch floats to any proper refuter
(`minRef`).  The kernel `CircSupply` therefore fires only when

    a ⊮ ◯Z   and   every u > a forces Z

(which entails `cone(a) = {a}` and soleness).  Two discharge routes are
PROVED:

1. `circWit_of_maximal` (pins `[propext]`): at a MAXIMAL world the
   polarity-split correspondence `force_classForce` (left subformulas
   push forcing into the classical valuation of the world's `Ĝ`-atoms,
   right subformulas pull it back; maximality enters only at `⊃`/`◯`,
   infallibility only at `⊥`) makes the generalised `Ax^I◯` supply the
   wit outright: the vacuous zone of the world's classical theory
   contains `Λ*_a`, and `classForce ats Z = false` is exactly `a ⊮ Z`.

2. `metI_circ_syn`: a tagged grounding row (e.g. `Ax^R` on the atom
   complement, grounding `Λ*`-implications through `Clo`'s weakening
   clause) — the route the engine's derivations of the corner cells
   take.

Corollary landed: **`completeness_of_discrete`** — statement (A)
UNCONDITIONAL over models in which every world is maximal, the first
completeness instance for the full modal calculus (`◯` allowed on both
sides of the goal).

Remaining to full (A): (i) the kernel at NON-maximal corner worlds
(`a < u` somewhere, yet every proper extension forces `Z`; the syn
route covers the `Clo`-groundable instances, the residue needs either
a recursive grounding-row construction or a semantic argument that the
residue is empty); (ii) the promise-mode port of `metR_prime`/`metR_or`
to lift `hloc` (models whose `Λ*` carries `◯`-formulas at non-maximal
worlds).

### §11 second addendum: residue probes + the seen-mechanism (2026-08-17)

Three further probes, all PASS (corpus now 27 pass / 5 control-ok):

    corner_residue          (x⊃z) ⊃ ((◯z⊃w) ⊃ (w ∨ ◯z))   rounds=4
    corner_residue_poisoned (A⊃z) ⊃ ((◯z⊃w) ⊃ (w ∨ ◯z))   rounds=8, A = p∨(p⊃q)
    corner_selfloop         (◯z⊃z) ⊃ (w ∨ ◯z)              rounds=3

The self-loop reading is decisive: `classForce ats (◯Z⊃Z)` is a
classical tautology, so the `Ax^I◯` zone contains the self-loop
implication at EVERY valuation — the seemingly-worst instance (the
retained implication re-demanding its own ◯-cell) discharges by the
axiom, not by recursion.

**The seen-mechanism (designed, not yet implemented).**  Give `visit` a
per-world parameter `seen : List Form` of ◯-bodies whose corner case is
in flight; measure `(ht, |sfR| − |seen|, t, |C|)`.  The corner edge
`I(◯Z)@a → R(Z)@a` pushes `Z` into `seen` and drops the second
coordinate; world-floats reset `seen` under a first-coordinate drop;
all other edges leave it unchanged.  The kernel then fires only when
`Z ∈ seen` — the self-referential instance — whose Λ*-retention
demands are exactly the `(◯Z⊃W)`-shaped members, to be discharged
member-wise: tautologous ones (`W` classically entailed by `◯Z`, e.g.
`W = Z`) by the `Ax^I◯` zone, groundable ones by `Clo`, the rest by
retention inside the row under construction with their Υ-cells taken
from `seen`-aware recursion.  This is the concrete route to
discharging `CircSupply` outright; the promise-mode port for `hloc`
remains the other half.

### §11 third addendum: the stuck-member analysis + the killer probe
(2026-08-17, end of window)

Sharpening the member-wise discharge of the self-referential kernel
instance, for a retained member `(◯Z′ ⊃ W) ∈ Λ*_a` inside the
`R(Z′)@a` supply row:

1. If `a ⊩ W`: Lemma 6.5 grounds it (`W ∈ sfL`, forced ⟹ Clo-derivable
   from `Λ*_a ⊆ Γ_row`).  Stuck ⟹ `a ⊮ W`, and then the corner gives
   `∀ u > a : u ⊩ Z′ ⟹ u ⊩ ◯Z′ ⟹ u ⊩ W`: the consequent is itself
   corner-shaped.
2. NEW discharge route: `Ax^I◯` with a CHOSEN valuation `ats ⊆ Ĝ_at`
   (not the world's own): the cell lands whenever some classical
   valuation satisfies `Λ*_a` and refutes `Z′` — decidable, and blocked
   only when `Λ*_a ⊨_cl Z′` (e.g. tautologous `Z′`).
3. Attempting to build a configuration blocking EVERY route
   (tautologous `Z′` to kill 2, `W` refuted at `a` to kill 1, `W`
   built from atoms excluded from the row's zones to kill grounding)
   SELF-DESTRUCTS: refuting `W` at `a` demands a witness world above
   `a`, which the corner obliges to force `◯Z′` and hence `W` — the
   same destruction pattern as the §8 attempts.  Conjecture: the fully
   stuck configuration is semantically inconsistent, i.e. the kernel is
   dischargeable member-wise in all models.

The strongest CONSISTENT killer-attempt was probed and PASSES:

    corner_taut_body  (◯(q∨(q⊃p)) ⊃ (p∨(p⊃q))) ⊃ (w ∨ ◯(q∨(q⊃p)))
                      rounds=6; model a < b{p,q}, c{p}

Corpus: 28 pass / 5 control-ok / 0 unresolved.  Thirteen corner-family
cells, all derived; no completeness counterexample at any constructible
stratum.

**Route to unconditional (A), consolidated**: (α) the seen-mechanism
visit refactor (§11 second addendum); (β) the member-wise kernel
discharge with the four routes above + the self-destruction argument
made formal; (γ) the promise-mode port of the prime/∨ joins for `hloc`.

### §11 fourth addendum: the promise-port design pinned (2026-08-17)

Two facts fix the design of build (γ):

1. **Retention is forced.**  A `Λ*`-circ `◯Y` has `a ⊩ ◯Y, a ⊮ Y`
   (the forceStar condition), and `clo_forces` makes every Clo-member
   forced; so `Clo Γ Y` is unavailable at any realisable `Γ` and the
   circ-clause cannot cover `◯Y` — the member must be RETAINED, and
   the barren `joinCtxAt` has no θ-circ zone.  Circ-carrying worlds
   therefore genuinely require `joinAtP`/`joinOrP` (promise contexts):
   there is no retention-free route.

2. **Prime pledges are the goal.**  `Covers Γ W F` for prime `F` admits
   only `refl`, so a promise row consumable through `MRWit.tOK`
   (chain-`W` with `Covers ctx W C`) must pledge `W = F` at the prime
   base; compound goals then lift through the `Covers` clauses as in
   the landed threading.  The pledge-supply for the port is thus: at a
   circ-carrying world `a` with prime demand `F`, a component family
   `(tps, Δs)` of regular wits FOR `F` at worlds of `a`'s modal cone,
   each barren-or-chain-`Covers`-`F`, whose contexts `Clo`-contain the
   stable zones (hJ7s) and the stable circ-bodies (hJ5).  Semantic
   availability of such components — `cone(a)`-successors refuting `F`
   — is the §8 pledge-existence question in its final form, and enters
   the theorem as the second named supply (`PledgeSupply`), exactly
   parallel to `CircSupply`.

So build (γ) = the two join builders' promise branches, each taking a
`PledgeSupply`-input; `completeness_of_supply` then drops `hloc` for
`PledgeSupply`, and full unconditional (A) = the member-wise discharge
of BOTH supplies ((β), with the four routes + self-destruction).

## 12. Build (γ) LANDED: hloc eliminated (2026-08-17, continuation)

`FRJ/Saturate.lean` now carries the promise-mode joins as builders:

- `PledgeFam K G a F`: a component family deriving `F` with admissible
  tags, contexts `Clo`-containing `Λ*_a` (discharging hJ7s and, via
  `restrictP`, the conclusion filter) and grounding every
  `Λ*`-circ-body (discharging hJ5 and the θ-circ `restrictC`);
- `PledgeSupply K G`: such a family at every circ-carrying world for
  every refuted right-signature formula — the second named kernel;
- `metR_primeP` (the `⋈^At,p`, premise family enumerating
  `C :: upsPrime` so the imp-free case is covered, pledging the goal:
  the conclusion tag is `chain C`, whose `tOK` is `Covers.refl`) and
  `metR_orP` (the `⋈^∨,p`, `U = C₁ :: C₂ :: upsPrime`);
- `visit` branches per world on `circPart (Λ*_a) = []`: barren joins
  where it holds, promise joins where it fails.

**The main theorem is now**

    completeness_of_supply :
      PledgeSupply K G → CircSupply K G → ¬ K.valid G → Provable G

— statement (A) for EVERY finite Kripke model, no `hloc`, pins
`[propext, Quot.sound]`, audit-guarded.  `pledgeSupply_of_locFree`
recovers the old form; `completeness_of_discrete` re-derives through
it (both supplies discharged at discrete models).

**What remains for unconditional (A)** is exactly build (β): the
member-wise discharge of the two supplies —
`CircSupply` (four routes proved: minRef-float exhaustion means it
fires only when every proper extension forces the body; then maximal ⟹
`circWit_of_maximal`, groundable ⟹ `metI_circ_syn`, ∃-ats ⟹ chosen-
valuation `Ax^I◯`, plus the self-destruction conjecture for the rest)
and `PledgeSupply` (components for the goal over the demanding world's
cone; semantic availability is the §8 pledge-existence question).
Both are single named Props with the engine as extensional referee
(28/5/0 across thirteen corner cells).

### §12 addendum: the graded-demand refinement for build (β)

Only `metI_circ`/`metR_circ` (the `circNotIn`/`circIn` premises) consume
`tOK`; the ⊃/∧-threading preserves any tag and `Provable` accepts any
tag at the root.  So `AllMet` can be GRADED: tag-certified regular wits
only for the demands that feed `◯`-introductions, free-tagged wits
(where the FALLIBLE joins `joinAtF`/`joinOrF` are legitimate, with no
pledge needed) for everything else.  Consequences for the two kernels:

- `PledgeSupply` is only needed on the tOK-graded side, i.e. at
  circ-carrying worlds that serve as `minRef`-anchors for some
  `◯`-demand; free-graded demands at circ-carrying worlds discharge by
  the fallible joins UNCONDITIONALLY (their zone keeps the whole
  `Ĝ_◯` with no side condition, so cov is immediate).
- The component-existence analysis for the pledged side: cone-members
  witnessing each `Λ*`-circ-body Y (which exist, `a ⊩ ◯Y`) must be
  infallible and refute the pledged formula; `a ⊩ ◯Y` only guarantees
  the witness, not its `F`-refutation — the graded split means `F`
  ranges only over ◯-feeding bodies, sharpening the semantic question
  to: at a circ-carrying `minRef`-anchor `a` for body `F`, do the
  circ-body witnesses in `cone(a)` refute `F`?  (`a ⊮ F` holds at
  anchors; witnesses live in `cone(a)` where `F`-status is the §8
  pledge question.)

Next window, build order: (β1) the graded `AllMet` split with the
fallible-join builders (`metR_primeF`/`metR_orF` — unconditional,
mechanical); (β2) the pledged-side semantic analysis on the sharpened
question; (β3) `CircSupply` member-wise discharge (four routes + the
self-destruction argument).

## 13. Build (β1) LANDED: the graded visit (2026-08-17, continuation 2)

`FRWit` (tag-free regular wit), `MRWit.toFree`, free-grade threading
(`metR_andF`/`metR_impF`), and the FALLIBLE join builders
(`metR_primeF`/`metR_orF` — `⋈^At,⊥`/`⋈^∨,⊥`, whose conclusions keep
the whole modal zone with no side condition).  `SatStmt` gains grade
`t = 2` (free); the `⊃∉`-suppliers (`metI_imp.supR`) take free wits
(`impNotIn` accepts any tag); free-grade `◯`-demands route through the
certified layer (`t`-drop).  Measure `(ht, t, |C|)` with
`t ∈ {0,1,2}`; all edges legal; whole chain pins
`[propext, Quot.sound]`.

Consequence: at circ-carrying worlds the FREE grade discharges
unconditionally (fallible joins), so `PledgeSupply` is exercised only
along certified chains — the descents of ◯-bodies at minRef anchors.

### The (β2) interface refinement (analysed, next to implement)

`metI_circ` uses the anchor wit's `cov` ONLY to transport `Λ*_b` (the
DEMANDING world) into the row's `Clo`; requiring `Λ*_w ⊆ ctx` at the
anchor `w` is over-specification.  This matters: at an anchor `w` for
body `p` with `◯p ∈ Λ*_w`, full-`Λ*_w` coverage would demand retaining
`◯p` in a `p`-refuting row, whose promise components can never satisfy
hJ5 for the body `p` (`Clo`-members are forced at the components'
realisers, which refute `p`) — an unsatisfiable pledge.  But the
transport of `Λ*_b` never needs that retention: `b ⊮ ◯p` keeps `◯p`
out of `Λ*_b`; positive positions of `Λ*_b`-members are `b`-forced and
persist to `w`, so `mem_clo_lamStar` at `w` follows `b`-forced paths,
and the circ-bases it uses are `b`-forced `◯Y`s — never the demand's
own body.  Implementation: a transported-cov certified wit (cov
relative to the demanding world), with the visit's certified layer
parameterised by the demand origin; the pledged joins then retain only
the transported zone, and the `hbody`-instances range over `b`-forced
circ-bodies.  This removes the one PROVABLY-unsatisfiable
`PledgeSupply` instance and is the right statement of the certified
demand for the member-wise discharge.

### §13 addendum: the θ-riding discharge (2026-08-17, continuation 3)

Working the `OWit` layer's ⊃-case exposed and then dissolved the §13
impossibility at the row level:

- The discharged antecedent `A` need not be `Clo`-derived from
  anchor-local `Λ*` (the route that forced the impossible retention):
  `impIn`'s side condition accepts `A ∈ ctx` (base), and `A` can ride
  the θ-ZONES — every irregular cell's θ is our construction, and the
  atomic cells' zones already carry all of `Ĝ_imp` — so retention does
  not pass through the stable zones and triggers no hJ2.
- The θ-implication restriction (`restrict … (upsilon rhs)`) then
  demands `A`'s antecedent among the Υ-cells; for the critical shape
  `A = ◯P ⊃ W` at an anchor forcing `◯P`, the Υ-cell for `◯P` is
  suppliable SYNTACTICALLY by the generalised `Ax^I◯` (any valuation
  with `P` false — always available for atomic `P`), independent of
  any world's refuting `◯P`.  The §13 impossible instance is thereby
  unreachable in the θ-riding design.
- The remaining obligation of the certified row is the ORIGIN's
  `Λ*_b`-ground: its circ-members `◯Y` (with `b ⊮ Y`) still need
  retention, the barren θ has no circ zone, so the certified join at a
  ground-circ-carrying origin remains promise-mode, and the
  `hbody`/component question recurs one level up (components refuting
  the pledge with `Y`-witnesses in their contexts).  This is now THE
  single remaining semantic question of build (β2); every other
  obstruction met so far has dissolved into either a syntactic supply
  (axIC, θ-riding, grounding) or a measure legalisation (minRef,
  grades, seen).

Design consequence: the (β2) certified layer should build rows
BOTTOM-UP from the final join with explicit θ-CONTROL (fat zones
carrying the retained antecedents and the origin-transported members),
rather than threading anchor-local coverage — the visit's certified
grade becomes a fold over the descent path with a θ-obligation
accumulator.

## §14  The erasure-transfer route (2026-08-17, Matthew's redirect)

Matthew's observation (2026-08-17): when a countermodel does not depend
on `Rm` the ◯-machinery "should be redundant".  Made precise: on
◯-TRANSPARENT models (`Rm = id`, legal since `id` is a preorder inside
`≤`) forcing satisfies `force a (erase A) ↔ force a A` for the
collapse translation `erase` (`◯ := id`), so a transparent countermodel
of `G` is exactly an ordinary countermodel of the circ-free `erase G`,
which the PROVED ◯-free completeness already refutes in the calculus.
The missing content is the purely syntactic ERASURE TRANSFER

    (E)    Provable (erase G) → Provable G .

Landed (FRJ/Erase.lean, guards pinned): `erase`, `noCirc`, `erase_hcf`
(the erasure meets Minimal.lean's circ-freeness hypothesis);
`force_erase` (the semantic half — axiom-FREE);
`completeness_of_transparent_of_lift` (completeness over transparent
infallible models conditional on (E); `[propext, Quot.sound]`).

With (E) proved, the completeness map becomes: ◯-free goals (all
models) ∪ arbitrary goals over transparent models — strictly containing
the discrete corner, which is the `le = id` degenerate case — with the
supply-conditional theorem covering the genuinely modal remainder.

Per the testing mandate (E) went under extensional attack BEFORE any
proof build: `wip/frj_sat.lean` erasure-transfer block, eight
◯-decorated intuitionistic refuters (several with classically VALID
erasures, hence beyond the classical shadow; compound and nested
◯-bodies included for the zone-shift stress).  Verdict semantics
include `FAIL-CANDIDATE` = erasure derived while the G-saturation
COMPLETED below every cap without a hit (engine-certain counterexample
modulo faithfulness).

Design note for the (E) build (ahead of results): the lift is NOT
rule-homomorphic — at positions where `◯` wraps the goal formula the
erased derivation has no counterpart step, and the translation must
INSERT the irregular/regular ◯-pair (`circNotIn` then `circIn`) above
the lifted refutation of the body; contexts lift by preimage-fattening
`liftCtx Δ := (gHat G).filter (erase · ∈ Δ)`, which stays inside the
zones (preimages of zone members are zone members) and commutes with
the joins' ∪/∩/restrict algebra (preimage preserves both).
