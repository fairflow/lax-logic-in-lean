/-
# The model extracted from a derivation — the assembly kit

Section 3.1 of Fiorentini–Ferrari, "Countermodels and soundness of
FRJ(G)".  The paper's model is

    Mod(D) = ⟨PS(D), ≤, ρ, V⟩

with `PS(D)` the p-sequents of `D` (regular sequents that are axioms or
join conclusions), `σ₁ ≤ σ₂ iff σ₂ ↦* σ₁`, and `V(σ) = Lhs(σ) ∩ PV`.

Since every p-sequent has a unique p-sequent immediately below it (the
join whose premises it feeds), `PS(D)` ordered by derivation ancestry is
a finite TREE rooted at `ρ`.  We therefore build it compositionally: a
`⋈` rule places a fresh root below the disjoint union of the models
already built for its premises.  `addRoot` is that operation, and
`solo` (its empty-index instance) is the `Ax^R` leaf.

DIVERGENCE (recorded in `docs/frj-fidelity.md`): the paper takes `PS(D)`
to be the SET of p-sequents, identifying two occurrences of the same
sequent; we take occurrences.  The two agree up to the quotient that
identifies equal-labelled worlds, and soundness is insensitive to it —
`Mod(D)` is a countermodel iff its quotient is.  The identification
matters only for the minimality results of §6, which are out of scope.

A `PModel` is the extracted model together with the labelling of each
world by the left formulas of its p-sequent, and the three invariants
that the soundness proof uses at worlds other than the one under
consideration.
-/
import FRJ.Calculus

namespace FRJ

open Form

/-! ## The order on a disjoint union placed above a fresh root -/

/-- `≤` on `Option (Σ i, (M i).W)`: the fresh root `none` is below
everything, and distinct components stay incomparable. -/
inductive ARLe {ι : Type} (M : ι → Kripke) :
    Option ((i : ι) × (M i).W) → Option ((i : ι) × (M i).W) → Prop
  | root (x : Option ((i : ι) × (M i).W)) : ARLe M none x
  | comp {i : ι} {a b : (M i).W} : (M i).le a b → ARLe M (some ⟨i, a⟩) (some ⟨i, b⟩)

/-- The fresh-root construction: a new world with valuation `V₀`, below
the disjoint union of the models `M i`.  With `ι` empty this is a single
world, which is the `Ax^R` case. -/
def addRoot {ι : Type} [Finite ι] (V₀ : Finset Form) (M : ι → Kripke)
    (hV : ∀ (i : ι) (p : String), Form.atom p ∈ V₀ → (M i).V (M i).root p) :
    Kripke where
  W := Option ((i : ι) × (M i).W)
  finite := by
    have : ∀ i : ι, Finite (M i).W := fun i => (M i).finite
    infer_instance
  le := ARLe M
  le_refl := by
    rintro (_ | ⟨i, a⟩)
    · exact .root _
    · exact .comp ((M i).le_refl a)
  le_trans := by
    rintro _ _ _ (_ | ⟨hab⟩) h2
    · exact .root _
    · cases h2 with
      | comp hbc => exact .comp ((M _).le_trans hab hbc)
  le_antisymm := by
    rintro _ _ (_ | ⟨hab⟩) h2
    · cases h2 with
      | root => rfl
    · cases h2 with
      | comp hba => exact congrArg _ (Sigma.ext rfl (heq_of_eq ((M _).le_antisymm hab hba)))
  root := none
  root_le := fun _ => .root _
  V := fun x p => match x with
    | none => Form.atom p ∈ V₀
    | some ⟨i, a⟩ => (M i).V a p
  V_mono := by
    rintro _ _ (⟨(_ | ⟨i, a⟩)⟩ | ⟨hab⟩) p hp
    · exact hp
    · exact (M i).V_mono ((M i).root_le a) p (hV i p hp)
    · exact (M _).V_mono hab p hp

variable {ι : Type} [Finite ι] {V₀ : Finset Form} {M : ι → Kripke}
  {hV : ∀ (i : ι) (p : String), Form.atom p ∈ V₀ → (M i).V (M i).root p}

/-- Everything above a component world is in the same component. -/
theorem addRoot_le_comp {i : ι} {a : (M i).W} {y : (addRoot V₀ M hV).W}
    (h : (addRoot V₀ M hV).le (some ⟨i, a⟩) y) :
    ∃ b : (M i).W, (M i).le a b ∧ y = some ⟨i, b⟩ := by
  cases h with
  | comp hab => exact ⟨_, hab, rfl⟩

/-- **Forcing is preserved at component worlds.**  Each component is
upward closed in `addRoot`, so no formula changes truth value there.
This is what lets the induction treat a premise's model in isolation. -/
theorem addRoot_force_comp {i : ι} {a : (M i).W} :
    ∀ A : Form, (addRoot V₀ M hV).force (some ⟨i, a⟩) A ↔ (M i).force a A := by
  intro A
  induction A generalizing a with
  | atom p => exact Iff.rfl
  | bot => exact Iff.rfl
  | and A B ihA ihB => simp only [Kripke.force_and, ihA, ihB]
  | or A B ihA ihB => simp only [Kripke.force_or, ihA, ihB]
  | imp A B ihA ihB =>
      simp only [Kripke.force_imp]
      constructor
      · intro h b hab hA
        exact (ihB).mp (h (some ⟨i, b⟩) (.comp hab) ((ihA).mpr hA))
      · intro h y hy hA
        obtain ⟨b, hab, rfl⟩ := addRoot_le_comp hy
        exact (ihB).mpr (h b hab ((ihA).mp hA))

@[simp] theorem addRoot_root_atom (p : String) :
    (addRoot V₀ M hV).force none (.atom p) ↔ Form.atom p ∈ V₀ := Iff.rfl

/-! ## `PModel`: the extracted model with its labelling

The soundness proof reasons about worlds other than the one under
consideration — in the `⋈` case it applies the main induction hypothesis
at an arbitrary p-sequent above the join.  So the construction must
carry, for every world, the left formulas of its p-sequent together with
the facts the proof uses about them.
-/

/-- The extracted model, with each world labelled by `Lhs` of its
p-sequent, and the three invariants of Sec. 3.1. -/
structure PModel where
  K : Kripke
  /-- `Lhs(σ)` for the p-sequent `σ` at this world. -/
  lhs : K.W → Finset Form
  /-- "`V` maps `σ` to `V(σ) = Lhs(σ) ∩ PV`." -/
  val_eq : ∀ (w : K.W) (p : String), K.V w p ↔ Form.atom p ∈ lhs w
  /-- Lemma 3.4(iii): `σ₁ ↦* σ₂` implies `Lhs(σ₂) ⊆ Cl(Lhs(σ₁))`.  In the
  model order (`σ₂` above `σ₁` in the derivation means `σ₁ ≤ σ₂`) this
  reads: going up, the label of a lower world stays inside the closure. -/
  lhs_clo : ∀ {w v : K.W}, K.le w v → ∀ X ∈ lhs w, Clo (lhs v) X
  /-- Lemma 3.9(i) at every world: each p-sequent forces its own left
  formulas. -/
  forces_lhs : ∀ w : K.W, K.forces w (lhs w)

namespace PModel

/-- The `Ax^R` leaf: a single world whose label is a set of atoms. -/
def solo (Γ : Finset Form) (hΓ : ∀ X ∈ Γ, X.isPV) : PModel where
  K := addRoot (ι := Empty) Γ (fun i => i.elim) (fun i => i.elim)
  lhs := fun _ => Γ
  val_eq := by
    rintro (_ | ⟨i, _⟩) p
    · exact Iff.rfl
    · exact i.elim
  lhs_clo := fun _ X hX => .base hX
  forces_lhs := by
    rintro (_ | ⟨i, _⟩)
    · intro X hX
      have := hΓ X hX
      match X, this with
      | .atom p, _ => exact hX
    · exact i.elim

end PModel

end FRJ
