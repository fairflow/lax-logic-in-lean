# FRJ◯ — handover for the fresh session

*2026-08-16, branch `ljf-pll`. Goal: prove completeness for LJF◯'s
refutation side. Read `docs/frjo-calculus-plan.md` first (sources +
design + W1–W6), then this file (exact state + worked analyses), then
the code in the order below. Everything compiles, zero sorries; OPEN
statements are named `def … : Prop`.*

## State per file

* `FRJO/Seq.lean` (W1, done): `Cell`, `sf`/`sfPlus` (universe),
  `determining`/`detPart` (atoms+⊥+⊃+◯ — the screened repair),
  `clB` (bounded-searcher closure, UNTRUSTED), `Reg`/`Irr`,
  `ClProps` (OPEN obligations).
* `FRJO/Calc.lean` (W2, done, **v3**): `FRJD G b : Reg G → Type` —
  `orR`, `andR1/2`, `impIn`/`impOut` (⊃∈/⊃∉), `circOut` (◯∉),
  `world` (RK's ⋈: kids + cone declaration + fallible leaf) with
  `worldOK` **v3**: universe ∧ heredity(membership) ∧
  ◯-positive(leaf ∨ cone-kid ∨ zone-membership) ∧ goal-by-SHAPE
  (atom absent / ⊥ / ◯ with cone-miss; compound = false). `rank`.
* `FRJO/Extract.lean` (W3a, done): `extract` (RK model read-off);
  `ExtractForces` (W3b) OPEN; `not_laxND_of_FRJD` pinned conditional.
* `FRJO/Complete.lean` (done): `Reconstruction b` OPEN;
  **`completenessFRJO` PROVED conditional on it alone**, pinned
  `[propext, Classical.choice, Quot.sound]`, riding
  `Reject.built_countermodel` (the (R)+T2 chain);
  `frjd_iff_not_laxND`.
* `FRJO/Reconstruct.lean`: PROVED kit — `sf_trans`, `sfPlus_closed`,
  `clB_sound`, `solo_fal_forces`; `ReconstructionSolo` OPEN (v3).

## The v2→v3 lesson (do not undo it)

The solo case was PROVED against worldOK v2 (`git show 99868db`) —
and that proof flushed out v2's unsoundness: its goal conjunct read
the bounded searcher (`clB`), so budget failures admit semantically
wrong `world` nodes and W3b is FALSE for v2. v3's conjuncts are
structural (membership + shape), which makes W3b provable and
reconstruction supply-able. Consequence: compound goals never
discharge at `world`; the solo proof needs an inner induction on the
goal. The v2 proof is the worked template — its `thRestrict`-style
zone (`(sfPlus G).filter (decide ∘ force r)`, classical) and its
conjunct-by-conjunct discharge transfer directly.

## Worked analysis — the proof to write

State ONE theorem, structural induction on `Built` (Prop-elim is fine,
the goal is `Nonempty`):

    recon {G b} : ∀ {M}, Reject.Built M → ∀ (r : M.W) (C' : PLLFormula),
      C' ∈ sfPlus G → ¬ M.force r C' →
      Nonempty (FRJD G b ⟨thRestrict G M r, C'⟩)

with `thRestrict G M r := (sfPlus G).filter (fun φ => decide (M.force r φ))`
(classical). `Reconstruction` follows (Γ ⊆ thRestrict from forcing +
`sfPlus_ctx`). CRITICAL: the cell `G` is FIXED throughout — recursive
calls vary the SEQUENT, never the cell (kids live in the same `FRJD G`).

**Solo case** (inner induction on `C'`):
∨/∧ → `orR`/`andR` (same zone); ⊃ → the only world is reflexive, so
refutation gives `A` forced ∧ `B` refuted → `impIn` (membership ✓) +
IH; ◯A → `solo_force_somehow` gives `A` refuted → `world [] [] false`
(goal-shape: `A ∉ thRestrict` ✓); atoms/⊥ → `world [] [] false`
(atom unforced → absent from the zone; solo root infallible by
`solo_fal_forces` + the refuted goal). ◯-positive conjunct: `◯B ∈
zone` → forced → `solo_force_somehow` → `B` forced → `B ∈ zone` (needs
`sfPlus_closed`, proved).

**Join case** (`M = Reject.join Mods D`, root `none`; component
IHs from `Built.rec`):

* `r = some ⟨i, a⟩`: forcing is componentwise (`join_force_comp`,
  including `◯`), so the case IS the component IH at `(Mods i, a)` —
  same zone by the same lemma. One-liner modulo transport.
* `r = none`, inner induction on `C'`:
  - ∨/∧: IH.
  - `A ⊃ B` refuted: `∃ v ≥ none` forcing `A`, refuting `B`.
    `v = none` → `impIn` + IH. `v = some ⟨i, a⟩` → component IH at
    goal `B` gives a kid over `thRestrict (Mods i) a` which contains
    `A` (forced at `v`) and all of the root zone (`force_hered`) →
    `impOut` (both sides are membership ✓).
  - `◯A` refuted: `∃ v` with cone missing `A`. `v = some ⟨i,a⟩`:
    the join adds no `Rm`-edges inside components, so the cone of a
    component world is its component cone → `◯A` refuted at `a` IN
    `Mods i` → component IH at goal `◯A` → `circOut`.
    `v = none`: the root's cone = itself + the `D.S`-declared
    components → build the `world` node (below).
  - atoms/⊥/(◯ at root): the `world` node. THE REALISER DICHOTOMY:
    for each `◯B` in the root zone with `B` not in it, `◯B`-forcing
    at the root yields a realiser `u ∈ D.S`-cone forcing `B`.
    EITHER some cone world forces ALL of `sfPlus G` — then set
    `leaf := true`, zero kids (it realises every obligation; and this
    cannot co-occur with a root-refuted `◯A` goal, since `A ∈ sfPlus`
    would be forced in the cone) — OR every needed realiser refutes
    SOMETHING in `sfPlus G`: pick it (classical `find?`), get the kid
    from the component IH at `Γ := B :: rootZone` (heredity by
    `force_hered`), cone flag true. Goal-shape conjunct for `◯A`:
    all chosen kids are `D.S`-cone worlds, which the `v = none`
    cone-miss says unforce `A` → `A` absent from their zones ✓.

**Then W3b** (`ExtractForces`): induction on the derivation; v3's
membership conjuncts are exactly what the forcing proof consumes;
Reject's `solo`/`join` forcing lemmas are the kit. **Then W4**: the
corpus screen (pattern: `wip/frjo_screen.lean`, currently pointed at
the retired `FRJO/Core.lean` RT layer — retarget it at a saturation
searcher emitting `FRJD`, or drop it until one exists).

## Pitfalls (each cost a round this session)

* Pins transcribe VERBATIM — under `open Classical`, `choice` prints
  unqualified. Verify `lake build` is error-free BEFORE committing;
  `#guard_msgs` failures are build errors.
* `List.contains` vs `∈`: go through `List.elem_iff`.
* Inside `match C, hC with | .somehow A, hC`, the ambient `C` is NOT
  substituted in things you write yourself — write the refined form
  (`⟨Γ, .somehow A⟩`), or the `cases hcl :` scrutinee won't match the
  goal and the false-branch `rfl` will mystify you.
* Section variables vanish from a `def` that stops mentioning them —
  keep `_b` explicit in `worldOK` (done) or call sites break.
* `FRJO/Core.lean` (the `RT`/`wf`/`find` layer) is RETIRED as a
  calculus — kept only as the untrusted searcher precedent. Do not
  build on it; the anti-pattern is documented in the plan.

## Suggested order

1. `recon` solo case under v3 (half a session; the v2 proof is the
   template).  2. Join case (the campaign; analysis above).
3. `Reconstruction`/`ReconstructionSolo` as corollaries; pins.
4. W3b.  5. W4 searcher + 302-cell corpus + the two flags.
Opus 5, max effort. Sorry-free + pinned or it stays OPEN.
