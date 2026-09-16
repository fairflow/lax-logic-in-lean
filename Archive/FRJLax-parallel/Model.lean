/-
# FRJ◯ — models, forcing, and (Cl1)

Section 2 of Fiorentini–Ferrari (ACM TOCL 21(3), Article 22, 2020),
continued: the model class, the forcing relation, monotonicity, validity,
countermodels, and the first closure property (Cl1), which is the one
that mentions forcing and therefore could not live in `Core.lean`.

**The model class is the decision of 2026-08-16** (`docs/frj-lax-plan.md`
§9.1): Fairtlough–Mendler *constraint models* from line one, so that the
`◯`-free results are proved once, in the structure the modal case needs.
The paper's own models are the special case in which no world is
fallible; nothing below assumes that special case.

Imports: `FRJLax.Core` and nothing else.
-/
import FRJLax.Core

namespace FRJLax

/-! ## The model class

The paper: "A *Kripke model* is a structure `K = ⟨P, ≤, ρ, V⟩`, where
`⟨P,≤⟩` is a finite poset with minimum `ρ` (the *root* of `K`) and
`V : P → 2^PV` is a function such that `α ≤ β` implies `V(α) ⊆ V(β)`."

Fairtlough–Mendler (Definition 3.1, as formalised in
`LaxLogic/PLLKripke.lean`): a constraint model carries a second
accessibility relation `R_m ⊆ R_i` and a set `F` of fallible worlds, with
`F` upward closed and every atom true at a fallible world.

This structure is both: a **rooted, antisymmetric, constructively finite
constraint model**.

Three divergences from each source, all recorded in
`docs/frj-lax-plan.md`:

* finiteness is carried as a constructive enumeration `elems`/`complete`
  rather than a `Finite` instance, because eliminating `Finite` needs
  `Fintype.ofFinite`, which costs `Classical.choice`;
* the order and the valuation are decidable, which makes forcing a
  computation rather than merely a proposition;
* `R_i` is required antisymmetric (the paper's "poset") though
  Fairtlough–Mendler ask only for a preorder.  Posets suffice for PLL, and
  `Mod(D)` will be antisymmetric by construction; the cost is that a
  `FinCM` countermodel found elsewhere must be collapsed before it can be
  fed to the completeness theorem of W4.
-/

/-- A model: a rooted finite poset `⟨W, R_i, root⟩` carrying a second
preorder `R_m ⊆ R_i`, an upward-closed set of fallible worlds, and a
monotone valuation that is full at fallible worlds. -/
structure Model where
  /-- the worlds -/
  W : Type
  /-- "finite", constructively: an enumeration of all worlds -/
  elems : List W
  complete : ∀ w, w ∈ elems
  decEq : DecidableEq W
  /-- intuitionistic accessibility, the paper's `≤` -/
  Ri : W → W → Prop
  /-- modal (constraint) accessibility -/
  Rm : W → W → Prop
  /-- the fallible worlds -/
  Fal : W → Prop
  /-- `V : P → 2^PV` -/
  V : W → String → Prop
  ri_refl : ∀ w, Ri w w
  ri_trans : ∀ {w v u}, Ri w v → Ri v u → Ri w u
  ri_antisymm : ∀ {w v}, Ri w v → Ri v w → w = v
  rm_refl : ∀ w, Rm w w
  rm_trans : ∀ {w v u}, Rm w v → Rm v u → Rm w u
  /-- the `◯`-frame is a subrelation of the `⊃`-frame -/
  sub_mi : ∀ {w v}, Rm w v → Ri w v
  /-- the root `ρ`, the minimum of the poset -/
  root : W
  root_le : ∀ w, Ri root w
  hered_F : ∀ {w v}, Ri w v → Fal w → Fal v
  /-- "`α ≤ β` implies `V(α) ⊆ V(β)`" -/
  hered_V : ∀ {w v}, Ri w v → ∀ p, V w p → V v p
  /-- `V` is full on fallible worlds -/
  full_F : ∀ {w}, Fal w → ∀ p, V w p
  decRi : ∀ w v, Decidable (Ri w v)
  decRm : ∀ w v, Decidable (Rm w v)
  decFal : ∀ w, Decidable (Fal w)
  decV : ∀ w p, Decidable (V w p)

attribute [instance] Model.decEq Model.decRi Model.decRm Model.decFal Model.decV

namespace Model

/-! ## Forcing

The paper's five clauses, with `⊥` read at the fallible worlds and the
sixth clause of Propositional Lax Logic:

    M,w ⊩ ⊥       iff  w ∈ F
    M,w ⊩ p       iff  p ∈ V(w)
    M,w ⊩ A ∧ B   iff  M,w ⊩ A and M,w ⊩ B
    M,w ⊩ A ∨ B   iff  M,w ⊩ A or M,w ⊩ B
    M,w ⊩ A ⊃ B   iff  for every v with R_i w v, M,v ⊩ A implies M,v ⊩ B
    M,w ⊩ ◯A      iff  for every v with R_i w v there is u with
                       R_m v u and M,u ⊩ A

DIVERGENCE (presentational, standard): the paper writes the `⊃`-clause as
"`K,β ⊮ A` or `K,β ⊩ B`"; the implication is the standard reading and
writing the disjunction would put excluded middle into the definition. -/

def force (M : Model) : M.W → Form → Prop
  | w, .bot => M.Fal w
  | w, .atom p => M.V w p
  | w, .and A B => force M w A ∧ force M w B
  | w, .or A B => force M w A ∨ force M w B
  | w, .imp A B => ∀ v, M.Ri w v → force M v A → force M v B
  | w, .circ A => ∀ v, M.Ri w v → ∃ u, M.Rm v u ∧ force M u A

variable (M : Model)

@[simp] theorem force_bot (w : M.W) : M.force w .bot ↔ M.Fal w := Iff.rfl
@[simp] theorem force_atom (w : M.W) (p : String) :
    M.force w (.atom p) ↔ M.V w p := Iff.rfl
@[simp] theorem force_and (w : M.W) (A B : Form) :
    M.force w (.and A B) ↔ (M.force w A ∧ M.force w B) := Iff.rfl
@[simp] theorem force_or (w : M.W) (A B : Form) :
    M.force w (.or A B) ↔ (M.force w A ∨ M.force w B) := Iff.rfl
@[simp] theorem force_imp (w : M.W) (A B : Form) :
    M.force w (.imp A B) ↔ ∀ v, M.Ri w v → M.force v A → M.force v B := Iff.rfl
@[simp] theorem force_circ (w : M.W) (A : Form) :
    M.force w (.circ A) ↔ ∀ v, M.Ri w v → ∃ u, M.Rm v u ∧ M.force u A := Iff.rfl

/-- "*Monotonicity property* holds for arbitrary formulas, i.e.
`K,α ⊩ A` and `α ≤ β` imply `K,β ⊩ A`." -/
theorem force_mono {w v : M.W} (h : M.Ri w v) :
    ∀ {A : Form}, M.force w A → M.force v A := by
  intro A
  induction A with
  | atom p => exact fun hf => M.hered_V h p hf
  | bot => exact fun hf => M.hered_F h hf
  | and A B ihA ihB => exact fun hf => ⟨ihA hf.1, ihB hf.2⟩
  | or A B ihA ihB => exact fun hf => hf.elim (Or.inl ∘ ihA) (Or.inr ∘ ihB)
  | imp A B _ _ => exact fun hf u hvu => hf u (M.ri_trans h hvu)
  | circ A _ => exact fun hf u hvu => hf u (M.ri_trans h hvu)

/-- A fallible world forces every formula.  This is the coherence check on
the structure: `full_F` is stated for atoms only, and the rest follows.
It is also what makes `⊥ ⊃ A` valid, so that the `◯`-free fragment of this
model class validates exactly IPC. -/
theorem force_of_fallible {w : M.W} (hw : M.Fal w) : ∀ A : Form, M.force w A := by
  intro A
  induction A generalizing w with
  | atom p => exact M.full_F hw p
  | bot => exact hw
  | and A B ihA ihB => exact ⟨ihA hw, ihB hw⟩
  | or A B ihA _ => exact Or.inl (ihA hw)
  | imp A B _ ihB => exact fun v hv _ => ihB (M.hered_F hv hw)
  | circ A ihA => exact fun v hv => ⟨v, M.rm_refl v, ihA (M.hered_F hv hw)⟩

/-! ### Forcing is decidable

The models are finite and carry the witnesses of that constructively, so
forcing is a COMPUTATION.  This is what lets the sets `Λ*_α` of the
completeness construction be ordinary `List.filter`s rather than
classically formed subsets, and it is the reason the development needs no
`Classical.choice`. -/

instance decForce (M : Model) : ∀ (w : M.W) (A : Form), Decidable (M.force w A)
  | w, .bot => M.decFal w
  | w, .atom p => M.decV w p
  | w, .and A B =>
      have := decForce M w A
      have := decForce M w B
      inferInstanceAs (Decidable (_ ∧ _))
  | w, .or A B =>
      have := decForce M w A
      have := decForce M w B
      inferInstanceAs (Decidable (_ ∨ _))
  | w, .imp A B =>
      have : ∀ v : M.W, Decidable (M.force v A) := fun v => decForce M v A
      have : ∀ v : M.W, Decidable (M.force v B) := fun v => decForce M v B
      have hd : Decidable (∀ v ∈ M.elems, M.Ri w v → M.force v A → M.force v B) :=
        List.decidableBAll _ _
      match hd with
      | isTrue h => isTrue (fun v hv hA => h v (M.complete v) hv hA)
      | isFalse h => isFalse (fun hf => h (fun v _ hv hA => hf v hv hA))
  | w, .circ A =>
      have : ∀ u : M.W, Decidable (M.force u A) := fun u => decForce M u A
      have hd : Decidable
          (∀ v ∈ M.elems, M.Ri w v → ∃ u ∈ M.elems, M.Rm v u ∧ M.force u A) :=
        List.decidableBAll _ _
      match hd with
      | isTrue h =>
          isTrue (fun v hv => by
            obtain ⟨u, _, hu⟩ := h v (M.complete v) hv
            exact ⟨u, hu⟩)
      | isFalse h =>
          isFalse (fun hf => h (fun v _ hv => by
            obtain ⟨u, hmu, hu⟩ := hf v hv
            exact ⟨u, M.complete u, hmu, hu⟩))

/-! ## Validity and countermodels -/

/-- "Let `Γ` be a set of formulas, by `K,α ⊩ Γ` we mean that `K,α ⊩ A` for
every `A ∈ Γ`." -/
def forces (M : Model) (w : M.W) (Γ : List Form) : Prop := ∀ A ∈ Γ, M.force w A

theorem forces_mono {M : Model} {w v : M.W} (h : M.Ri w v) {Γ : List Form}
    (hΓ : M.forces w Γ) : M.forces v Γ := fun A hA => M.force_mono h (hΓ A hA)

theorem forces_subset {M : Model} {w : M.W} {Γ Δ : List Form} (hsub : Δ ⊆ Γ)
    (hΓ : M.forces w Γ) : M.forces w Δ := fun A hA => hΓ A (hsub hA)

theorem forces_eqv {M : Model} {w : M.W} {Γ Δ : List Form} (h : Γ ≐ Δ)
    (hΓ : M.forces w Γ) : M.forces w Δ := fun A hA => hΓ A (h.2 hA)

/-- "A formula `A` is *valid* in `K` iff `K,ρ ⊩ A`." -/
def valid (M : Model) (A : Form) : Prop := M.force M.root A

end Model

/-- The valid formulas.  The paper writes `IPL` for this set over its own
model class; over constraint models it is Propositional Lax Logic, and on
`◯`-free formulas the two agree. -/
def PLL (A : Form) : Prop := ∀ M : Model, M.valid A

/-- "If `K,ρ ⊮ A`, we say that `K` is a *countermodel* for `A`." -/
def Countermodel (M : Model) (A : Form) : Prop := ¬ M.valid A

theorem not_PLL_of_countermodel {M : Model} {A : Form}
    (h : Countermodel M A) : ¬ PLL A := fun hA => h (hA M)

/-! ## (Cl1)

"(Cl1) `K,α ⊩ Γ` implies `K,α ⊩ Cl(Γ)`."

The remaining closure properties (Cl2)–(Cl6) are syntactic and are proved
in `Core.lean`.  Note which clause needs what: `∨` needs nothing, `∧`
needs nothing, and `⊃` needs monotonicity — which is exactly why `Cl`'s
`A ⊃ X` clause is sound with `A` ranging over *all* formulas. -/

theorem clo_forces {M : Model} {w : M.W} {Γ : List Form}
    (hΓ : M.forces w Γ) : ∀ {X : Form}, Clo Γ X → M.force w X := by
  intro X h
  induction h with
  | base hC => exact hΓ _ hC
  | and _ _ ihX ihY => exact ⟨ihX, ihY⟩
  | orR _ ih => exact Or.inr ih
  | orL _ ih => exact Or.inl ih
  | imp _ ih => exact fun v hv _ => M.force_mono hv ih

/-! ### The `◯` clause of `Cl`, as a candidate only

`Cl` is transcribed verbatim in `Core.lean`, without a `◯` clause,
because `Cl` occurs in the side conditions of `⊃∈` and `⊃∉` and extending
it changes the rules.  The lemma below is the whole content of the
candidate clause `X ::= … | ◯X`: it says that (Cl1) would survive the
extension, since `R_m` is reflexive.  It is proved here so that the W5
discussion has the fact in hand, and it is used nowhere. -/

theorem force_circ_of_force {M : Model} {w : M.W} {X : Form}
    (h : M.force w X) : M.force w (.circ X) :=
  fun v hv => ⟨v, M.rm_refl v, M.force_mono hv h⟩

/-! ## Axiom audit -/

/-- info: 'FRJLax.Model.force_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.force_mono

/-- info: 'FRJLax.Model.force_of_fallible' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.force_of_fallible

/-- info: 'FRJLax.Model.forces_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.forces_mono

/-- info: 'FRJLax.clo_forces' does not depend on any axioms -/
#guard_msgs in
#print axioms clo_forces

/-- info: 'FRJLax.force_circ_of_force' does not depend on any axioms -/
#guard_msgs in
#print axioms force_circ_of_force

/-- info: 'FRJLax.not_PLL_of_countermodel' does not depend on any axioms -/
#guard_msgs in
#print axioms not_PLL_of_countermodel

/-- info: 'FRJLax.Model.force' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.force

-- Forcing is decided constructively, `◯`-clause included.
/-- info: 'FRJLax.Model.decForce' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.decForce

end FRJLax
