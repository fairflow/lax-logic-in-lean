/-
# The corner coverage induction — brick 2 of the flight-branch closure

At a cone-trivial infallible world (which every `CircSupplyV` corner is,
by `coneTrivial_of_corner`), the STRICT round-2 calculus's kept chain
covers everything the flight-branch join needs.  With a Υ/base/pool
triple adequate for the world (hypotheses below — in the assembly they
are discharged by the thin premise family: `Ax^I` rows for refuted
atoms, `⊃∉` floats for imps refuted only above, pushes/floats for fresh
`◯`s), the two halves close by ONE plain size induction:

    (F)  X ∈ Sf^L(G),  a ⊩ X   ⟹  Clo (base ++ keptOf Υ base pool) X
    (R)  Y ∈ Sf^R(G),  a ⊮ Y   ⟹  RefAt true Υ (base ++ keptOf …) Y

The mutual knot — a forced implication with refuted antecedent must be
KEPT, and kept membership needs `RefAt` of the antecedent over the
final context — is cut by `keptOf_saturated` (brick 1): the greedy
chain is a fixpoint, so `RefAt` over `base ++ keptOf …` IS kept
membership.  Size founds everything: `(F)` at `A ⊃ B` calls `(R)` at
`A` (a proper subformula, on the OTHER polarity — `sfL_imp`), and the
cone-triviality clause makes forced `◯X'` descend to forced `X'`.

Corollary `corner_lamStar_clo`: `Λ*_a` is `Clo`-covered — exactly the
`hTh` obligation of the `◯∉` cell the flight branch must build.  The
remaining assembly (next): the thin premise family discharging the
Υ-adequacy hypotheses inside `minModS`, replacing the guard.
-/
import FRJ.Complete
import FRJ.RefAt

namespace FRJ

open Form

/-- The Υ/base/pool adequacy at a world — what the thin premise family
supplies.  `base` holds the forced `Sf^L`-atoms; `pool` offers every
forceStar implication; `Υ` covers the refuted `Sf^R`-formulas that the
`RefAt` clauses cannot decompose: atoms, implications without a local
counter-witness, and `◯`s whose body the world forces. -/
structure CornerSupply (K : Kripke) (G : Form) (a : K.W)
    (Υ base pool : List Form) : Prop where
  hat : ∀ p : String, Form.atom p ∈ sfL G → K.force a (.atom p) →
    Form.atom p ∈ base
  hpool : ∀ A B : Form, Form.imp A B ∈ sfL G → K.force a (.imp A B) →
    ¬ K.force a A → Form.imp A B ∈ pool
  hUat : ∀ p : String, Form.atom p ∈ sfR G → ¬ K.force a (.atom p) →
    Form.atom p ∈ Υ
  hUimp : ∀ A B : Form, Form.imp A B ∈ sfR G → ¬ K.force a (.imp A B) →
    (¬ K.force a A ∨ K.force a B) → Form.imp A B ∈ Υ
  hUcirc : ∀ Z : Form, Form.circ Z ∈ sfR G → ¬ K.force a (.circ Z) →
    K.force a Z → Form.circ Z ∈ Υ

/-- **The corner coverage induction.**  At a cone-trivial infallible
world with an adequate Υ/base/pool triple, forced left subformulas are
`Clo`-derivable and refuted right subformulas are `RefAt`-refutable,
both over `base ++ keptOf Υ base pool`. -/
theorem corner_coverage {K : Kripke} {G : Form} {a : K.W}
    {Υ base pool : List Form}
    (hcone : K.ConeTrivial a) (hinf : ¬ K.Fal a)
    (hs : CornerSupply K G a Υ base pool) :
    ∀ n : Nat,
      (∀ X, X.size ≤ n → X ∈ sfL G → K.force a X →
        Clo (base ++ keptOf Υ base pool) X) ∧
      (∀ Y, Y.size ≤ n → Y ∈ sfR G → ¬ K.force a Y →
        RefAt true Υ (base ++ keptOf Υ base pool) Y) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro X hX
        exfalso; cases X <;> (simp only [Form.size] at hX; omega)
      · intro Y hY
        exfalso; cases Y <;> (simp only [Form.size] at hY; omega)
  | succ k ih =>
      obtain ⟨ihF, ihR⟩ := ih
      constructor
      · -- (F): forced left subformulas are Clo-derivable
        intro X hX hmem hf
        cases X with
        | atom p =>
            exact .base (List.mem_append_left _ (hs.hat p hmem hf))
        | bot => exact absurd hf hinf
        | and X₁ X₂ =>
            obtain ⟨h1, h2⟩ := sfL_and hmem
            have hsz1 : X₁.size ≤ k := by
              simp only [Form.size] at hX; omega
            have hsz2 : X₂.size ≤ k := by
              simp only [Form.size] at hX; omega
            exact .and (ihF X₁ hsz1 h1 hf.1) (ihF X₂ hsz2 h2 hf.2)
        | or X₁ X₂ =>
            obtain ⟨h1, h2⟩ := sfL_or hmem
            have hsz1 : X₁.size ≤ k := by
              simp only [Form.size] at hX; omega
            have hsz2 : X₂.size ≤ k := by
              simp only [Form.size] at hX; omega
            rcases hf with hf | hf
            · exact .orL (ihF X₁ hsz1 h1 hf)
            · exact .orR (ihF X₂ hsz2 h2 hf)
        | imp A B =>
            obtain ⟨hA, hB⟩ := sfL_imp hmem
            have hsz1 : A.size ≤ k := by
              simp only [Form.size] at hX; omega
            have hsz2 : B.size ≤ k := by
              simp only [Form.size] at hX; omega
            obtain hfB | hfB := Decidable.em (K.force a B)
            · exact .imp (ihF B hsz2 hB hfB)
            · have hnA : ¬ K.force a A :=
                fun hfA => hfB (hf a (K.le_refl a) hfA)
              exact .base (List.mem_append_right _
                (keptOf_saturated (hs.hpool A B hmem hf hnA)
                  (ihR A hsz1 hA hnA)))
        | circ X' =>
            have hsz : X'.size ≤ k := by
              simp only [Form.size] at hX; omega
            have hf' : K.force a X' := by
              obtain ⟨c, hrc, hc⟩ := hf a (K.le_refl a)
              exact (hcone c hrc) ▸ hc
            exact .circ (ihF X' hsz (sfL_circ hmem) hf')
      · -- (R): refuted right subformulas are RefAt-refutable
        intro Y hY hmem hnf
        cases Y with
        | atom p => exact .ups (hs.hUat p hmem hnf)
        | bot => exact .bot
        | and Y₁ Y₂ =>
            obtain ⟨h1, h2⟩ := sfR_and hmem
            have hsz1 : Y₁.size ≤ k := by
              simp only [Form.size] at hY; omega
            have hsz2 : Y₂.size ≤ k := by
              simp only [Form.size] at hY; omega
            obtain hf1 | hf1 := Decidable.em (K.force a Y₁)
            · exact .andR (ihR Y₂ hsz2 h2 (fun h => hnf ⟨hf1, h⟩))
            · exact .andL (ihR Y₁ hsz1 h1 hf1)
        | or Y₁ Y₂ =>
            obtain ⟨h1, h2⟩ := sfR_or hmem
            have hsz1 : Y₁.size ≤ k := by
              simp only [Form.size] at hY; omega
            have hsz2 : Y₂.size ≤ k := by
              simp only [Form.size] at hY; omega
            exact .or (ihR Y₁ hsz1 h1 (fun h => hnf (Or.inl h)))
              (ihR Y₂ hsz2 h2 (fun h => hnf (Or.inr h)))
        | imp A B =>
            obtain ⟨hA, hB⟩ := sfR_imp hmem
            have hsz1 : A.size ≤ k := by
              simp only [Form.size] at hY; omega
            have hsz2 : B.size ≤ k := by
              simp only [Form.size] at hY; omega
            obtain hfA | hfA := Decidable.em (K.force a A)
            · obtain hfB | hfB := Decidable.em (K.force a B)
              · exact .ups (hs.hUimp A B hmem hnf (Or.inr hfB))
              · exact .imp (ihF A hsz1 hA hfA) (ihR B hsz2 hB hfB)
            · exact .ups (hs.hUimp A B hmem hnf (Or.inl hfA))
        | circ Z =>
            have hsz : Z.size ≤ k := by
              simp only [Form.size] at hY; omega
            obtain hfZ | hfZ := Decidable.em (K.force a Z)
            · exact .ups (hs.hUcirc Z hmem hnf hfZ)
            · exact .circ rfl (ihR Z hsz (sfR_circ hmem) hfZ)

/-- (F), packaged. -/
theorem corner_coverage_forced {K : Kripke} {G : Form} {a : K.W}
    {Υ base pool : List Form}
    (hcone : K.ConeTrivial a) (hinf : ¬ K.Fal a)
    (hs : CornerSupply K G a Υ base pool) :
    ∀ X ∈ sfL G, K.force a X → Clo (base ++ keptOf Υ base pool) X :=
  fun X hmem hf =>
    (corner_coverage hcone hinf hs X.size).1 X (Nat.le_refl _) hmem hf

/-- (R), packaged. -/
theorem corner_coverage_refuted {K : Kripke} {G : Form} {a : K.W}
    {Υ base pool : List Form}
    (hcone : K.ConeTrivial a) (hinf : ¬ K.Fal a)
    (hs : CornerSupply K G a Υ base pool) :
    ∀ Y ∈ sfR G, ¬ K.force a Y → RefAt true Υ (base ++ keptOf Υ base pool) Y :=
  fun Y hmem hnf =>
    (corner_coverage hcone hinf hs Y.size).2 Y (Nat.le_refl _) hmem hnf

/-- **`Λ*` is `Clo`-covered at the corner** — the `hTh` obligation of
the flight branch's `◯∉` cell, discharged from the coverage. -/
theorem corner_lamStar_clo {K : Kripke} {G : Form} {a : K.W}
    {Υ base pool : List Form}
    (hcone : K.ConeTrivial a) (hinf : ¬ K.Fal a)
    (hs : CornerSupply K G a Υ base pool) :
    ∀ X ∈ lamStar K a G, Clo (base ++ keptOf Υ base pool) X := by
  intro X hX
  obtain ⟨hsf, hstar⟩ := mem_lamStar.mp hX
  exact corner_coverage_forced hcone hinf hs X hsf (K.forceStar_force hstar)

/-- info: 'FRJ.corner_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms corner_coverage

/-- info: 'FRJ.keptOf_saturated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms keptOf_saturated

/-- info: 'FRJ.corner_lamStar_clo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms corner_lamStar_clo

end FRJ
