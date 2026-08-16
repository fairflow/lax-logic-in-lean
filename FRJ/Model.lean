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

What this file provides is the CONSTRUCTION only.  Lemma 3.4 (`lemma:lhs`)
and Lemma 3.9 are theorems about it and are proved as theorems, not
built in as invariants of a structure.
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
def addRoot {ι : Type} [DecidableEq ι] (ιe : List ι) (ιc : ∀ i, i ∈ ιe)
    (V₀ : List Form) (M : ι → Kripke)
    (hV : ∀ (i : ι) (p : String), Form.atom p ∈ V₀ → (M i).V (M i).root p) :
    Kripke where
  W := Option ((i : ι) × (M i).W)
  elems := none :: ιe.flatMap (fun i => ((M i).elems).map (fun a => some ⟨i, a⟩))
  complete := by
    rintro (_ | ⟨i, a⟩)
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, ιc i, ?_⟩)
      exact List.mem_map.mpr ⟨a, (M i).complete a, rfl⟩
  decEq := by
    have : ∀ i : ι, DecidableEq (M i).W := fun i => (M i).decEq
    intro x y
    exact decEq x y
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
  decLe := by
    rintro (_ | ⟨i, a⟩) y
    · exact isTrue (.root _)
    · cases y with
      | none => exact isFalse (fun h => by cases h)
      | some jb =>
          obtain ⟨j, b⟩ := jb
          by_cases hij : i = j
          · subst hij
            have : Decidable ((M i).le a b) := (M i).decLe a b
            exact decidable_of_iff ((M i).le a b)
              ⟨fun h => .comp h, fun h => by cases h; assumption⟩
          · exact isFalse (fun h => by cases h; exact hij rfl)
  decV := by
    rintro (_ | ⟨i, a⟩) p
    · exact inferInstanceAs (Decidable (Form.atom p ∈ V₀))
    · exact (M i).decV a p

variable {ι : Type} [DecidableEq ι] {ιe : List ι} {ιc : ∀ i, i ∈ ιe}
  {V₀ : List Form} {M : ι → Kripke}
  {hV : ∀ (i : ι) (p : String), Form.atom p ∈ V₀ → (M i).V (M i).root p}

/-- Everything above a component world is in the same component. -/
theorem addRoot_le_comp {i : ι} {a : (M i).W} {y : (addRoot ιe ιc V₀ M hV).W}
    (h : (addRoot ιe ιc V₀ M hV).le (some ⟨i, a⟩) y) :
    ∃ b : (M i).W, (M i).le a b ∧ y = some ⟨i, b⟩ := by
  cases h with
  | comp hab => exact ⟨_, hab, rfl⟩

/-- **Forcing is preserved at component worlds.**  Each component is
upward closed in `addRoot`, so no formula changes truth value there.
This is what lets the induction treat a premise's model in isolation. -/
theorem addRoot_force_comp {i : ι} {a : (M i).W} :
    ∀ A : Form, (addRoot ιe ιc V₀ M hV).force (some ⟨i, a⟩) A ↔ (M i).force a A := by
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
    (addRoot ιe ιc V₀ M hV).force none (.atom p) ↔ Form.atom p ∈ V₀ := Iff.rfl

/-! ## The `Ax^R` leaf

The empty-index instance of `addRoot`: a single world, which is the
model `Mod(D)` of a derivation consisting of one `Ax^R` axiom.
-/

/-- A single world whose valuation is `Γ ∩ PV`. -/
def solo (Γ : List Form) : Kripke :=
  addRoot (ι := Empty) [] (fun i => i.elim) Γ (fun i => i.elim) (fun i => i.elim)

@[simp] theorem solo_root_atom (Γ : List Form) (p : String) :
    (solo Γ).force (solo Γ).root (.atom p) ↔ Form.atom p ∈ Γ := Iff.rfl

/-- At the single world of `solo Γ`, a set of variables is forced exactly
when it is contained in `Γ` — the `V(σ) = Lhs(σ) ∩ PV` clause, in the
one case where it can be checked directly. -/
theorem solo_forces_root {Γ Δ : List Form} (hΔ : ∀ X ∈ Δ, X.isPV)
    (hsub : Δ ⊆ Γ) : (solo Γ).forces (solo Γ).root Δ := by
  intro X hX
  match X, hΔ X hX with
  | .atom p, _ => exact hsub hX

end FRJ
