# Step 2 of the semantic route in the subframe semantics: PROVED

2026-10-14.  Branch `subframe-layered`.  Module
`LaxLogic/PLL/SemUI/SubframeLayered.lean` (93 ledger rows, none sorried).
Context: `docs/semui-amalgamation-2026-10-14.md` §5, §6 and §9.

## 0. Status

**PROVED** (kernel-checked, axioms pinned in the module):

* `Agree.forth`, `Agree.sforth` and their mirror images: agreement on formulas
  satisfies the back-and-forth clauses of a bisimulation, one level down for
  one, respectively three, ranks of crank (§1).  This is the content of step 2,
  and it is what fails over constraint models.
* `layered_of_agree`: hence agreement at crank `3n + 1` is a layered
  bisimulation at level `n` (`[propext, Classical.choice, Quot.sound]`).
* `agree_of_layered`: the invariance lemma, a link at level `n` preserves the
  formulas of crank ≤ `n` (`[propext, Quot.sound]`).  Step 3 needs it to carry
  truth along the links of the amalgam.
* The ◯-free (IPC) instance, proved first (rule 8): `layeredI_of_agree` and
  `agreeI_of_layeredI`.
* `S_clause_needed`: the designed cell showing the `S`-clauses cannot be
  dropped (no axioms).

**OPEN**: step 3 (amalgamation) in the subframe semantics, the `∀`-side gluing,
and uniform interpolation for PLL.

Step 2 over constraint models stays REFUTED (`SemUI.layered_of_frag_agree_refuted`,
`SemUI.pair_escape_not_from_agreement`).  Nothing is superseded.

## 1. The statement

A subframe model is `(W, ≤, S, V)` with `≤` a preorder, `S ⊆ W`, `V`
hereditary, `⊥` forced nowhere, and

    x ⊩ ◯φ   ⟺   ∀ y ≥ x, y ∈ S → y ⊩ φ.

PLL is sound and complete for these models (`SubframeModel.derivable_iff_valid`,
PROVED earlier today).  Fix a finite atom set `V`.  Write

    w ≡ᵣ w'   :⟺   for every φ with crank φ ≤ r and atoms(φ) ⊆ V,
                    w ⊩ φ ⟺ w' ⊩ φ                            (`Agree`)

with `crank` the rank in which `↠` costs 1 and `◯` costs 2 (`SemUI.crank`).
**The theorem**: for `r ≥ 1`,

    w ≡_{r+1} w',  w ≤ v           ⟹   some v' ≥ w' has v ≡ᵣ v'
    w ≡_{r+3} w',  w ≤ v,  v ∈ S   ⟹   some v' ≥ w' in S' has v ≡ᵣ v'

and the mirror images from `w'` to `w`.  So the relations `≡_{3n+1}` form a
*layered bisimulation over V* (`LayeredBisim`): a family of relations `Zₙ`,
decreasing in `n`, respecting the atoms of `V`, in which a pair linked at level
`n + 1` answers every `≤`-move and every move to an `S`-point above it with a
pair linked at level `n` (`agreeBisim`, `layered_of_agree`).  Conversely a pair
linked at level `n` agrees on every formula of crank ≤ `n`
(`agree_of_layered`).

The bounds.  Write `w ⇄ₙ w'` when some layered bisimulation over `V` links `w`
and `w'` at level `n`.  As relations on pairs of worlds, linkage at level `n`
is bracketed by agreement:

    ≡_{3n+1}   ⊆   ⇄ₙ   ⊆   ≡ₙ

The factor 3 is lost in the first inclusion only:
one level for an `S`-move costs three ranks of character formula, `θ⁺ ↠ ◯θ⁻`.
For the route the size of the bound does not matter, since fragment finiteness
holds at every crank.  Two sharpenings, NOT checked in Lean:

* the `+1` pays only for the empty conjunction `⊤`; using `θ⁻` alone (or `◯θ⁻`
  alone) when `θ⁺` is empty gives `3n` in place of `3n + 1`;
* the invariance lemma spends one level on a `◯`, so a link at level `n`
  preserves every formula in which `↠` and `◯` are nested at most `n` deep,
  counting `◯` as one.

The ◯-free instance: with `≡°ᵣ` agreement on ◯-free formulas and `⇄°ₙ`
linkage by a bisimulation without the `S`-clauses (`LayeredBisimI`),

    ≡°_{n+1}   ⊆   ⇄°ₙ   ⊆   ≡°ₙ

and with the first sharpening the bracket closes, `⇄°ₙ = ≡°ₙ`, the textbook
statement for IPC.

## 2. The refutation stage

Answered from the rules, with designed cells (rule 9).

* **The constraint refutations have no subframe counterpart.**  Both are moves
  into a fallible world: in `layered_of_frag_agree_refuted` the two-point
  chain with a fallible top agrees with a single point on every atom-free
  formula of crank ≤ 1, but the `Rᵢ`-move to the fallible top has no partner;
  in `pair_escape_not_from_agreement` the fork agrees with a single point on
  every formula, but its `Rₘ`-move into its fallible branch has no partner.
  Subframe models have no fallible worlds, and `◯` has no second relation: its clause quantifies over `≤ ∩ S`, one relation, so a
  bisimulation clause for `◯` is a single forth/back step that one character
  formula can force.
* **The new clause is needed** (`S_clause_needed`, kernel-checked).  Two
  one-point models, the point in `S` in one and not in the other, are linked at
  every level by the `≤`-bisimulation, and `◯⊥` (crank 2) separates them.  So
  the bisimulation without `S`-clauses does not preserve forcing for PLL, and
  the `S`-step is visible to formulas.
* **The cost of the `S`-step is three ranks.**  The character of an `S`-move
  is `θ⁺ ↠ ◯θ⁻`; `◯θ⁻` alone is not enough, since `u ⊮ ◯θ⁻` gives an
  `S`-point above `u` refuting `θ⁻` but says nothing of `θ⁺` there.  (The
  record's §6 sketch guessed four ranks.)

No cell refuted the statement, and the proof below then went through as
sketched.

## 3. The proof

Let `L` list representatives of the formulas of crank ≤ r over `V` up to
interderivability (`SemUI.frag_reps_exist'`, PROVED 2026-07-20).
Interderivable formulas are forced at the same worlds (soundness), so
agreement on `L` is agreement at crank `r` (`agree_of_reps`).  For a world `v`
put

    θ⁺ := ⋀ { D ∈ L | v ⊩ D },      θ⁻ := ⋁ { D ∈ L | v ⊮ D }.

`v ⊩ θ⁺` and `v ⊮ θ⁻`, since `⊥` is forced nowhere.  A world forcing `θ⁺` and
refuting `θ⁻` agrees with `v` on `L` (`agree_of_char`).

* *Forth.*  If `u ≤ v` then `u ⊮ θ⁺ ↠ θ⁻`, which has crank ≤ r + 1.  If
  `u ≡_{r+1} u'` then `u' ⊮ θ⁺ ↠ θ⁻`, so some `v' ≥ u'` forces `θ⁺` and
  refutes `θ⁻`, and `v ≡ᵣ v'`.
* *S-forth.*  If `u ≤ v ∈ S` then `u ⊮ θ⁺ ↠ ◯θ⁻` (witness `v` itself), of
  crank ≤ r + 3.  If `u ≡_{r+3} u'` then some `x ≥ u'` forces `θ⁺` and some
  `y ≥ x` in `S` refutes `θ⁻`; `y` forces `θ⁺` by persistence, so `v ≡ᵣ y`.
* *Back, S-back* by symmetry of `≡`.

So `Zₙ := ≡_{3n+1}` is a layered bisimulation (`agreeBisim`); the `+1` pays for
`⋀ [] = ⊤`, of crank 1.  The converse is induction on formulas
(`LayeredBisim.force_iff`): `↠` uses forth/back, `◯` uses S-forth/S-back.

For the ◯-free instance the representatives must be ◯-free.  `eraseBox`
replaces each `◯ψ` by `⊤`; in the same model with `S` emptied (`noS`) every
`◯`-formula holds, so a formula and its erasure are forced at the same worlds,
and a ◯-free formula is forced in `noS` exactly where it is forced in the
model.  Hence an erased representative still represents
(`force_iff_eraseBox_of_interd`), and agreement on ◯-free formulas at crank
`n + 1`, as level `n`, is a ◯-free layered bisimulation (`agreeBisimI`).

## 4. What this does to the route

The route in the subframe semantics, step by step:

| step | statement | status |
|---|---|---|
| 1 | fragment finiteness up to interderivability | PROVED (`SemUI.frag_reps_exist'`; syntactic, so semantics-free) |
| 2 | agreement ⟹ layered bisimulation | PROVED today (`layered_of_agree`) |
| 3 | amalgamation from a layered link | OPEN in the subframe semantics |
| 4 | the `∀`-side gluing (Visser's push-down) | OPEN |
| 5 | assembly: semantic quantifiers definable ⟹ uniform interpolation | OPEN; completeness for subframe models is PROVED |

Step 3 needs its own proof: `LayeredAmalg.amalgamationE` is for constraint
models and consumes the escape-form link, which has no subframe analogue.  The
§6 sketch of the record: an `S`-point of the amalgam pairs an `S`-point of `M`
with a reflexive theory and refutes in place every `◯ξ` it lacks.  The level
it needs is not yet known; any level linear in the depth suffices for step 5,
since step 1 holds at every crank.  Steps 3 to 5 also need the invariance of
p-free formulas under a full subframe bisimulation, not yet stated (easy).

This is a route to uniform interpolation for PLL itself.  The formulas `∀p φ`
and `∃p φ` do not depend on the semantics: uniform interpolation is a statement
about derivability, its interpolants are unique up to interderivability, and
PLL is complete for both semantics.  What changes is the semantic
characterisation used to prove that they exist.  `IsSemEx`/`IsSemAll` in
`SemUI.lean` quantify over constraint models and `PBisim p`; the subframe
versions have the same shape (`w` forces `∃p φ` iff some p-variant of `w`
forces `φ`; `w` forces `∀p φ` iff for every `v ≥ w` every p-variant of `v`
forces `φ`), with p-variants now subframe models linked by a bisimulation over
the atoms other than `p`, `S`-clauses included.  The universal properties
(definability ⟹ uniform interpolation) go through as in `SemUI.lean`, from
soundness, completeness and the invariance lemma above.  The constraint-model
results about the old definitions (base and compositional cases, box laws,
`ofree_semAll_definable`) do not transfer automatically.  `SemExDefinable` and
`SemAllDefinable` in their constraint form stay separate questions: uniform
interpolation proved through subframe models would not make the constraint
bisimulation quantifiers definable (for IPC that is a theorem in its own
right, Visser's and Ghilardi–Zawadowski's).

## 5. Reproduce

    lake build LaxLogic.PLL.SemUI.SubframeLayered

About 15 seconds on top of the built dependencies.  The `#guard_msgs` pins
were watched failing (the pin of `S_clause_needed` first asserted
`[propext]`; the kernel reports no axioms).

## 6. Addendum: step 3 PROVED

`amalgamation` (`LaxLogic/PLL/SemUI/SubframeAmalg.lean`), level `3ν + 2`, with
the invariance lemma `PBisim.force_iff`.  Record:
`docs/subframe-step3-2026-10-14.md`.
