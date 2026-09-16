# (c) The promise join — specification, and the screen so far

*2026-08-17. Matthew's decision: go straight to the promise join, since
completeness needs it and routes (a) and (b) are detours.  Conditional on
the rule being correctly specified — so this document specifies it and
records what the extensional attack has settled, before any proof build is
scoped.*

## 0a. The check against the repo's own PLL completeness (2026-08-17, Matthew's instruction)

Before the build, the promise-join design was checked against the two
places the repository already constructs PLL countermodels.  Three
findings, one per place, and a scope correction.

**1. The frame class is aligned, exactly.**  `ConstraintModel`
(`LaxLogic/PLLKripke.lean`) demands `refl_m`, `trans_m`, `sub_mi`,
`hered_F`, `full_F`; `FinCM` (`PLLCountermodelEmit.lean`) builds the
reflexive closures of BOTH relations into `riB`/`rmB` and checks the rest
in `WellFormed`.  `FRJ.Kripke` matches field for field — `rm_refl`,
`rm_trans`, `sub_mi`, `fal_mono`, `fal_V` — so the reflexivity of `Rm`
that the witness-merging lemmas use is not an assumption of this
development but the repo's own completeness-bearing class.  What
`FRJ.Kripke` adds is `le_antisymm` (posets, i.e. REDUCED models) and
constructive finiteness; reducedness is deliberate — see finding 3.

**2. The canonical model already contains the pledge mechanism.**  The
canonical worlds of `PLLCompleteness.lean` are triples
`(val, fal, mfal)` with

    Rm T T'  :=  T.val ⊆ T'.val  ∧  T.mfal ⊆ T'.mfal

`mfal` is the set of formulas *pledged false at every `Rm`-successor*;
refuting `◯φ` at a world is exactly extending it with `φ ∈ mfal`
(consistency argument at line ~572), the pledge propagates along `Rm` by
definition, and `mfal_sub_fal` (pledged ⟹ false) is forced by
reflexivity — a world is its own `Rm`-successor.  The `Tag`/chain
mechanism of this design is the SINGLE-pledge shadow of `mfal`: `chain Z`
says "every world of the root's `Rm`-cone refutes `Z`", which is `mfal ∋ Z`
propagated down the promise chain.  The general mechanism is a pledge
SET; the emitter (`PLLCountermodelEmit.lean`) uses the same device as the
`P` component of its `(T, P)` worlds.

**3. Arity, and the honest completeness scope.**  `docs/frj-lifting.md`
§3 measured the arity of the ◯-refutation obligation (the number of
`Rm`-MAXIMAL successors) exhaustively over well-formed frames:
unbounded for full PLL (2 at n=2, 3 at n=3 — Goranko's `Alt_n`
phenomenon), but **exactly 1 on reduced confluent frames**, with the
mechanised witnesses `confluent_directed` and `rmC_le_obInv` already in
the repo.  A single promise premise per join builds models whose
`Rm`-cones are chains, i.e. the arity-1 class.  Consequently:

* **SOUNDNESS of the single-promise rules is unconditional** — every
  model built is a genuine constraint model, so every refutation
  certified is a PLL refutation;
* **COMPLETENESS of the single-promise calculus can at best hold for a
  class where arity 1 suffices** — the lifting doc's own recommendation
  ("do PCLL first") applies, and full PLL is expected to need promise
  LISTS (a rule schema) or the pledge-set generalisation of finding 2.
  One mitigation observed at Screen 2: refutations of distinct
  `◯`-formulas can be pushed to distinct `≤`-successors (the joins
  already branch in `≤`), so the per-frame arity numbers may overstate
  the per-formula need.  OPEN, deliberately.

**Consequence for the build (amended by Matthew, 2026-08-17): the
framework is built PLL-GENERAL from the outset.**  "You should not be
targeting PCLL from the outset.  That can only be a later tweak: the
general framework must be correct for PLL."  Accordingly the promise is a
FAMILY of regular premises `Δᵢ ⇒ Dᵢ` of arbitrary finite arity `k+1` —
the join declares as many modal successors as it needs, matching the
unbounded arity of full PLL; (J5) is per-formula existential (different
kept `◯Y` may be witnessed by different promise worlds), (J7) is
universal (every promise world lies above the new world), and the unary
case is `k = 0`.  PCLL/reducedness is a possible later specialisation,
never an assumption.  Soundness now; the completeness construction is
scoped separately.

## 0. Why the uniform choices go

Each uniform choice of `Rm` fixes a nucleus once and for all (`id`, `¬¬`,
`⊤`) and so fixes a proper fragment; `docs/frj-w3.md` §6a has the three
blind spots, each a theorem.  Completeness needs the countermodel's own
modal relation, which is arbitrary.  So `Rm` must become **data declared by
the derivation**, and that is what the promise join is.

## 1. The atomic change

Five parts, each unsound without the others.  This is the same list W2
gave, with part 5 now identified as the structural one.

1. `Ĝ` gains its third zone: `gHat = gAt ++ gImp ++ gCirc`, with
   `Ĝ_◯ = Sf^L(G) ∩ {◯-formulas}`.  Because `nf G l = (gHat G).filter (· ∈ l)`,
   this re-canonicalises **every** context in the development.
2. `Cl` gains the modal clause `Clo Γ X → Clo Γ (◯X)`, sound by
   `force_circ_of_force` (already proved).
3. `Λ*` gains the modal case: `α ⊩* ◯X` iff `α ⊩ ◯X` and `α ⊮ X` — exactly
   parallel to the implication case, and for the same reason (`Cl` recovers
   `◯X` from `X`, so only the non-recoverable ones are determining data).
   `forceStar_shape` becomes three-way, so `lamStar_subset_gHat` still lands
   inside `Ĝ`.
4. The context split becomes three-way: `Γ = Γ^at ++ Γ^⊃ ++ Γ^◯`
   (`atPart_union_impPart`), and both joins keep the modal part.  Dropping
   it is exactly the W1 failure: `⊃∉` admits a `◯`-formula into a zone,
   `⊃∈` shifts it into a stable set, and a join that keeps only the atomic
   and implicational parts silently loses it, breaking condition (†).
5. **`PreModel` carries `Rm` (and `Fal`) as data**, and `toKripke` uses
   them, in place of the uniform `Rm := Eq`.  The join declares the modal
   successors of the world it creates.

## 2. The rule

        σ₁ … σₙ                    Δ ⇒ D
    ──────────────────────────────────────────────────────────  ⋈^At,p
    nf G (Σ^at, Θ^at\{F}, Σ^⊃, Θ^⊃/Υ, Σ^◯, Θ^◯)  ⇒  F

`σⱼ = Σⱼ ; Θⱼ → Aⱼ` as before; `Δ ⇒ D` is the **promise premise**, a
regular sequent whose world becomes the modal successor of the new world.
(J1) containment, (J2) support, `F ∈ Prime \ Σ^at` and the blanket goal
condition are unchanged.  New:

    (J5)   ◯Y ∈ Σ^◯ ∪ Θ^◯   implies   Y ∈ Cl(Δ)
    (J7)   the conclusion context ⊆ Cl(Δ)

**(J6) of the W2 draft is redundant** and has been dropped: it asked for
`◯Y ∈ Cl(Δ)`, which follows from (J5) by the new modal clause of `Cl`
(part 2 above).

Model: the new world `ρ` gets

    Rm ρ  =  {ρ}  ∪  (the Rm-cone of the promise premise's root)

which is reflexive, transitive and contained in `≤` because the promise
component lies above `ρ`.  A join with no promise premise has
`Σ^◯ = Θ^◯ = ∅` and `Rm ρ = {ρ}`: it is the barren join of W3.

## 3. What the screen has settled

**PROVED, no axioms** (`FRJ/Basic.lean`, pinned in `FRJ/Audit.lean`):

* `Kripke.exists_common_witness` — if `w` forces `◯A` and `◯B` then a
  SINGLE modal successor of `w` forces both.  Transitivity of `Rm` chains
  the two witnesses and `Rm ⊆ ≤` carries the first forward.
* `Kripke.exists_common_witness_list` — the same for a whole finite zone:
  one modal successor forces every body.

  **This is why the rule carries ONE promise premise and not a list.**  The
  obvious worry about (J5) is that two modal formulas in the zone might
  need different witnesses, as Screen 2 of W2 shows they can at different
  WORLDS.  At a single world they cannot, and the lemma is the proof.

  It does double duty: in the completeness direction it is exactly what
  produces the promise premise, since it turns `Λ*_α`'s modal zone into one
  world forcing all its bodies.

* `Kripke.circ_and` — `◯A ∧ ◯B ⊃ ◯(A∧B)` holds in every constraint model.
  A validity the rule must not violate; standing test cell.

## 4. What must be screened before the build

1. **`◯∈` needs its index after all.**  A promise join destroys barrenness
   at the world it creates, so `FRJr` gains `b : Bool`; promise joins set
   it false, everything else passes it through, `◯∈` requires it true.
   Screen: a derivation with a promise below and `◯∈` above must be
   rejected, and the corresponding model must refute the soundness
   statement — construct that model.
2. **`⊃∉`'s side condition** `Θ ⊆ Cl(Γ) ∩ Ĝ` now admits modal formulas into
   `Θ`.  Check (†) survives with the modal zone kept by the join.
3. **The `⋈^∨` variant** — same conditions, `Θ^at` kept whole.
4. **`join_force_comp` with declared `Rm`**: the extra modal edges emanate
   from `ρ` only, so component worlds are unaffected; this needs re-proving
   structurally, the `Rm = Eq` shortcut being gone.
5. **Boundary cells**: empty modal zone (must reduce to the present join);
   `◯⊥` in the zone (forces the promise world fallible); the promise
   premise being an axiom; `Δ = ∅`.

## 5. Order of work

Parts 1–4 of §1 are syntactic and can go in one commit with the joins;
part 5 is the model-level change and is what the soundness proof will
feel.  Soundness first (the join case gains the `circ_intro` argument, and
(P2)'s secondary induction on formula size handles `◯X` because
`size X < size (◯X)`), then completeness, where `minMod` gains a modal goal
case and the promise premise comes from
`exists_common_witness_list`.

## 6. On the exponential blowup

Matthew's objection: the search space is `2^|Ĝ|` contexts, and `Ĝ` now
grows by a third zone.  That is right, and it is not fixable — `IPC` is
PSPACE-complete, so no decision procedure escapes an exponential worst
case.  What the forward method claims is about the *generated* fraction:
the contexts that actually arise are determining parts `Λ*`, not arbitrary
subsets, and derived sequents are shared across joins.  **This development
has not measured that fraction**, because `FRJ/` contains no search loop at
all.  Measuring it is a separate, well-defined piece of work and needs the
saturation procedure plus §3.3 of the paper (termination), neither of which
is mechanised.

---

## 6. BUILD OUTCOME (2026-08-17): soundness PROVED

`lake build FRJ` green, no `sorry`, all `#guard_msgs` pins pass.
What went in, as ONE atomic change (§1's list, realised):

1. `gHat = gAt ++ gImp ++ gCirc`; `nf` therefore re-canonicalises every
   context; `axI`'s zone and `lamStar_subset_axI` extended.
2. `Clo` gained the `◯`-clause (+ `cloB`/`decClo`, needed by the
   restriction filter).
3. Contexts split three ways (`atPart_union_impPart`).
4. SIX join constructors: `joinAt`/`joinOr` (barren — NEW side condition
   `Σ^◯ = ∅`, forced by (†)), `joinAtP`/`joinOrP` (promise FAMILIES,
   arity `k+1` arbitrary, (J5) existential per formula, (J7) universal
   per promise, `Θ^◯/Cl(Δ⃗)` restriction), `joinAtF`/`joinOrF` (declared
   fallible successor, whole modal zone kept, no conditions).
5. `PreModel` carries `rm`/`fal` as data; `PJRm` wires the fresh root to
   the designated promise components; `leafF` is the declared fallible
   world (label = the join's own context; the one non-p-sequent world).
6. `FRJr` indexed by `Tag` (`barren`/`chain D`/`blocked`); `◯∈` gated by
   `t ∈ {barren, chain Z}`; `tag_cone` (mutually recursive with Lemma
   3.9) proves the pledge is honoured down the whole promise chain —
   including the correction that the cone BEYOND the promise root must
   refute `Z`, which the naive Bool index missed.
7. Lemma 3.9 extended: (P2◯) via `circ_intro` with the promise root (or
   fallible leaf) as witness; the (ii) statement gained `¬ fal w`.
8. `soundness : Provable G → ¬ PLL G` — against ALL constraint models,
   the right statement for a PLL refutation calculus.

**Cells, machine-checked**: `provable_neg_circ_bot` and
`provable_circ_imp` — the calculus now refutes `¬◯⊥` and `◯p ⊃ p`
ITSELF, by `⋈^⊥`; both were provably out of reach of every infallible
extraction (`not_provable_barren_neg_circ_bot` keeps that fact).  The
`triv`/`falTop` route survives as theory but is subsumed.

**Bonus**: `Kripke.infPart` — deleting fallible worlds preserves ◯-free
forcing (the failure witnesses of `⊃` are never fallible), closing W3
open item (4); `frj_iff_countermodel` and `frj_iff_not_IPL` hold again
for ◯-free goals with the fallible extraction in play.

**OPEN (W4)**: completeness with modal goals — `Λ*` does not yet carry
the modal zone (`forceStar` unchanged; `minMod` still `hcf`-guarded), the
◯-goal case of the construction is unwritten, and the multiplicity
question (promise families vs pledge sets vs `≤`-branching) is
undecided.  Read the JLC 2021 S4 paper first (Matthew's action).
