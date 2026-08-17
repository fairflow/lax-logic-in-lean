# (c) The promise join — specification, and the screen so far

*2026-08-17. Matthew's decision: go straight to the promise join, since
completeness needs it and routes (a) and (b) are detours.  Conditional on
the rule being correctly specified — so this document specifies it and
records what the extensional attack has settled, before any proof build is
scoped.*

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
