/-
BiLax round 2 — MODEL EXISTENCE: a saturated open branch IS a
countermodel.

This is the disproof engine the whole build exists for.  A `Hintikka`
structure is a finite saturated open branch of `BiLaxL` presented as
data: worlds `Fin n`, the three relations and fallibility as decidable
predicates, and the left/right labelled-formula assignments, subject to
(i) the frame laws of `BiModel`, (ii) one saturation condition per
rule, (iii) openness.

`Hintikka.truth` is the truth lemma — left formulas are forced, right
formulas are refuted — and `Hintikka.not_biLaxND` converts a Hintikka
structure into CERTIFIED NON-DERIVABILITY, via `biLaxND_sound` alone:
no cut admissibility, no ND↔labelled equivalence needed.  For PLL
sequents `BiLax.Refute` (next file) composes this with `bforce_emb`.

Note what this buys over battery search: the object is the FAILED
PROOF SEARCH STATE, so its size is driven by the formula, not by an
enumeration of all models below some world-count.
-/
import BiLax.Labelled

namespace BiLax

/-- **A finite saturated open branch**, as data. -/
structure Hintikka where
  n : Nat
  ri : Fin n → Fin n → Prop
  rm : Fin n → Fin n → Prop
  rc : Fin n → Fin n → Prop
  fal : Fin n → Prop
  L : Fin n → BiForm → Prop
  R : Fin n → BiForm → Prop
  -- (i) the frame laws
  ri_refl : ∀ x, ri x x
  ri_trans : ∀ {x y z}, ri x y → ri y z → ri x z
  rm_refl : ∀ x, rm x x
  rm_trans : ∀ {x y z}, rm x y → rm y z → rm x z
  sub_mi : ∀ {x y}, rm x y → ri x y
  fal_hered : ∀ {x y}, ri x y → fal x → fal y
  square_c : ∀ {w u v}, rc w u → ri u v → ∃ w', ri w w' ∧ rc w' v
  counit_c : ∀ {w u}, rc w u → ∃ v, ri w v ∧ ∀ y, rm v y → ri y u
  serial_c : ∀ v, ∃ u, rm v u ∧ rc v u
  -- (ii) openness and the atomic conditions
  open_lr : ∀ {x A}, L x A → R x A → False
  prop_hered : ∀ {x y a}, ri x y → L x (.prop a) → L y (.prop a)
  fal_no_prop : ∀ {x a}, fal x → R x (.prop a) → False
  fal_no_bot : ∀ {x}, fal x → R x .bot → False
  bot_left : ∀ {x}, L x .bot → fal x
  -- (iii) saturation, one pair per connective
  sat_andL : ∀ {x A B}, L x (.and A B) → L x A ∧ L x B
  sat_andR : ∀ {x A B}, R x (.and A B) → R x A ∨ R x B
  sat_orL : ∀ {x A B}, L x (.or A B) → L x A ∨ L x B
  sat_orR : ∀ {x A B}, R x (.or A B) → R x A ∧ R x B
  sat_impL : ∀ {x y A B}, L x (A ⇾ B) → ri x y → R y A ∨ L y B
  sat_impR : ∀ {x A B}, R x (A ⇾ B) → ∃ y, ri x y ∧ L y A ∧ R y B
  sat_coimpL : ∀ {x A B}, L x (A ⤙ B) → ∃ y, ri y x ∧ L y A ∧ R y B
  sat_coimpR : ∀ {x y A B}, R x (A ⤙ B) → ri y x → R y A ∨ L y B
  sat_laxL : ∀ {x y A}, L x (◯∀A) → ri x y → ∃ u, rm y u ∧ L u A
  sat_laxR : ∀ {x A}, R x (◯∀A) → ∃ y, ri x y ∧ ∀ u, rm y u → R u A
  sat_colaxL : ∀ {x A}, L x (◯∃A) → ∃ u, rc u x ∧ L u A
  sat_colaxR : ∀ {x u A}, R x (◯∃A) → rc u x → R u A

namespace Hintikka

variable (H : Hintikka)

/-- The extracted model. -/
def toModel : BiModel where
  W := Fin H.n
  Ri := H.ri
  Rm := H.rm
  Rc := H.rc
  F := {x | H.fal x}
  V a := {x | H.L x (.prop a) ∨ H.fal x}
  refl_i := H.ri_refl
  trans_i := H.ri_trans
  refl_m := H.rm_refl
  trans_m := H.rm_trans
  sub_mi := H.sub_mi
  hered_F := fun h hx => H.fal_hered h hx
  hered_V := by
    rintro a x y h (hL | hF)
    · exact .inl (H.prop_hered h hL)
    · exact .inr (H.fal_hered h hF)
  full_F := fun hx => .inr hx
  square_c := H.square_c
  counit_c := H.counit_c
  serial_c := H.serial_c

/-- **The truth lemma**: left formulas are forced at their label,
right formulas are refuted there. -/
theorem truth (A : BiForm) :
    ∀ x : Fin H.n,
      (H.L x A → bforce H.toModel x A) ∧
      (H.R x A → ¬ bforce H.toModel x A) := by
  induction A with
  | prop a =>
      intro x
      refine ⟨fun h => .inl h, fun h hf => ?_⟩
      rcases hf with hL | hF
      · exact H.open_lr hL h
      · exact H.fal_no_prop hF h
  | bot =>
      intro x
      exact ⟨fun h => H.bot_left h, fun h hf => H.fal_no_bot hf h⟩
  | and A B ihA ihB =>
      intro x
      constructor
      · intro h
        exact ⟨(ihA x).1 (H.sat_andL h).1, (ihB x).1 (H.sat_andL h).2⟩
      · intro h hf
        rcases H.sat_andR h with hA | hB
        · exact (ihA x).2 hA hf.1
        · exact (ihB x).2 hB hf.2
  | or A B ihA ihB =>
      intro x
      constructor
      · intro h
        rcases H.sat_orL h with hA | hB
        · exact .inl ((ihA x).1 hA)
        · exact .inr ((ihB x).1 hB)
      · intro h hf
        rcases hf with hA | hB
        · exact (ihA x).2 (H.sat_orR h).1 hA
        · exact (ihB x).2 (H.sat_orR h).2 hB
  | imp A B ihA ihB =>
      intro x
      constructor
      · intro h v hv hA
        rcases H.sat_impL h hv with hR | hL
        · exact absurd hA ((ihA v).2 hR)
        · exact (ihB v).1 hL
      · intro h hf
        obtain ⟨y, hy, hA, hB⟩ := H.sat_impR h
        exact (ihB y).2 hB (hf y hy ((ihA y).1 hA))
  | coimp A B ihA ihB =>
      intro x
      constructor
      · intro h
        obtain ⟨y, hy, hA, hB⟩ := H.sat_coimpL h
        exact ⟨y, hy, (ihA y).1 hA, (ihB y).2 hB⟩
      · rintro h ⟨v, hv, hA, hnB⟩
        rcases H.sat_coimpR h hv with hR | hL
        · exact (ihA v).2 hR hA
        · exact hnB ((ihB v).1 hL)
  | lax A ih =>
      intro x
      constructor
      · intro h v hv
        obtain ⟨u, hu, hA⟩ := H.sat_laxL h hv
        exact ⟨u, hu, (ih u).1 hA⟩
      · intro h hf
        obtain ⟨y, hy, hall⟩ := H.sat_laxR h
        obtain ⟨u, hu, hA⟩ := hf y hy
        exact (ih u).2 (hall u hu) hA
  | colax A ih =>
      intro x
      constructor
      · intro h
        obtain ⟨u, hu, hA⟩ := H.sat_colaxL h
        exact ⟨u, hu, (ih u).1 hA⟩
      · rintro h ⟨u, hu, hA⟩
        exact (ih u).2 (H.sat_colaxR h hu) hA

/-- **The refutation theorem**: a Hintikka structure carrying `Γ` on
the left and `φ` on the right of one label CERTIFIES that the bi-lax
sequent is not derivable — through soundness of `BiLaxND` alone. -/
theorem not_biLaxND {Γ : List BiForm} {φ : BiForm} (x : Fin H.n)
    (hΓ : ∀ A ∈ Γ, H.L x A) (hφ : H.R x φ) : BiLaxND Γ φ → False := by
  intro p
  exact (H.truth φ x).2 hφ
    (biLaxND_sound p H.toModel x
      (fun A hA => (H.truth A x).1 (hΓ A hA)))

/-- The same, as underivability of the plain consequence. -/
theorem not_biConsequence {Γ : List BiForm} {φ : BiForm} (x : Fin H.n)
    (hΓ : ∀ A ∈ Γ, H.L x A) (hφ : H.R x φ) : ¬ BiConsequence Γ φ := by
  intro hc
  exact (H.truth φ x).2 hφ
    (hc H.toModel x (fun A hA => (H.truth A x).1 (hΓ A hA)))

end Hintikka

/-! ## Pins -/

/--
info: 'BiLax.Hintikka.truth' does not depend on any axioms
-/
#guard_msgs in
#print axioms Hintikka.truth

/--
info: 'BiLax.Hintikka.not_biLaxND' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hintikka.not_biLaxND

end BiLax
