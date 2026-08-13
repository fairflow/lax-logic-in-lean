/-
BiLax round 1 — models and the semantic theorems.

`BiModel` = a Fairtlough–Mendler constraint model carrying the two
RETROSPECTIVE frame laws, both EXACT (derived by the
largest-upset-avoiding-`u` argument during round-0 planning, verified
by the screens in BiLax/Screens.lean):

* `square`  (`Rm ; Ri ⊆ Ri ; Rm`): exactly what makes `◯∃`
  persistent — necessity via the upset `↑w`.
* `counit_law` (every `Rm`-predecessor `w` of `u` has an
  `Ri`-successor all of whose `Rm`-successors are `Ri`-below `u`):
  exactly what makes the counit `◯∃◯∀A ⊢ A` sound — necessity via the
  largest upset avoiding `u`.

The unit needs only reflexive `Rm` (inherited).  NOTE the repo's
`ConstraintModel` class does NOT satisfy `counit_law` in general (a
2-world countermodel exists), so `BiModel` is a genuinely smaller
class; every lifting statement carries these laws as side conditions.

Fallibility: `force_of_fallible` holds for the FORWARD fragment only —
`ff = ⊤ ⤙ ⊤` is forced nowhere (`bforce_ff`), separating the absolute
falsum from PLL's local falsum `⊥` (= F).  See docs/bilax-plan.md
§4(b).
-/
import BiLax.Syntax
import LaxLogic.PLLKripke

namespace BiLax
open PLLND

/-- **Bi-lax constraint models**: constraint models with the two
retrospective frame laws. -/
structure BiModel extends ConstraintModel where
  square : ∀ {w u v : W}, Rm w u → Ri u v → ∃ w', Ri w w' ∧ Rm w' v
  counit_law : ∀ {w u : W}, Rm w u → ∃ v, Ri w v ∧ ∀ y, Rm v y → Ri y u

/-- Forcing for bi-lax formulas.  The forward clauses are PLL's;
`⤙` and `◯∃` look backward. -/
def bforce (M : BiModel) : M.W → BiForm → Prop
  | w, .prop a => w ∈ M.V a
  | w, .bot => w ∈ M.F
  | w, .and A B => bforce M w A ∧ bforce M w B
  | w, .or A B => bforce M w A ∨ bforce M w B
  | w, .imp A B => ∀ v, M.Ri w v → bforce M v A → bforce M v B
  | w, .coimp A B => ∃ v, M.Ri v w ∧ bforce M v A ∧ ¬ bforce M v B
  | w, .lax A => ∀ v, M.Ri w v → ∃ u, M.Rm v u ∧ bforce M u A
  | w, .colax A => ∃ u, M.Rm u w ∧ bforce M u A

/-- **Persistence**: every bi-lax connective is hereditary along `Ri`
— the retrospective ones via transitivity (`⤙`) and the `square`
(`◯∃`). -/
theorem bforce_hered (M : BiModel) {A : BiForm} :
    ∀ {w v : M.W}, M.Ri w v → bforce M w A → bforce M v A := by
  induction A with
  | prop a => exact fun h hw => M.hered_V h hw
  | bot => exact fun h hw => M.hered_F h hw
  | and A B ihA ihB => exact fun h hw => ⟨ihA h hw.1, ihB h hw.2⟩
  | or A B ihA ihB =>
      exact fun h hw =>
        hw.elim (fun x => .inl (ihA h x)) (fun x => .inr (ihB h x))
  | imp A B ihA ihB =>
      exact fun h hw u hvu hu => hw u (M.trans_i h hvu) hu
  | coimp A B ihA ihB =>
      rintro w v h ⟨u, huw, hA, hnB⟩
      exact ⟨u, M.trans_i huw h, hA, hnB⟩
  | lax A ih =>
      exact fun h hw u hvu => hw u (M.trans_i h hvu)
  | colax A ih =>
      rintro w v h ⟨u, huw, hA⟩
      obtain ⟨u', huu', hu'v⟩ := M.square huw h
      exact ⟨u', hu'v, ih huu' hA⟩

/-- The embedding agrees with PLL forcing. -/
theorem bforce_emb (M : BiModel) (φ : PLLFormula) :
    ∀ w : M.W, bforce M w (emb φ) ↔ M.force w φ := by
  induction φ with
  | prop a => exact fun w => Iff.rfl
  | falsePLL => exact fun w => Iff.rfl
  | and φ ψ ihφ ihψ => exact fun w => and_congr (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ => exact fun w => or_congr (ihφ w) (ihψ w)
  | ifThen φ ψ ihφ ihψ =>
      intro w
      constructor
      · intro h v hv hφ
        exact (ihψ v).mp (h v hv ((ihφ v).mpr hφ))
      · intro h v hv hφ
        exact (ihψ v).mpr (h v hv ((ihφ v).mp hφ))
  | somehow φ ih =>
      intro w
      constructor
      · intro h v hv
        obtain ⟨u, hu, hφ⟩ := h v hv
        exact ⟨u, hu, (ih u).mp hφ⟩
      · intro h v hv
        obtain ⟨u, hu, hφ⟩ := h v hv
        exact ⟨u, hu, (ih u).mpr hφ⟩

/-- **Fragment-relative fallibility**: fallible worlds force every
FORWARD formula.  (Not every formula: see `bforce_ff`.) -/
theorem bforce_of_fallible_forward (M : BiModel) {A : BiForm}
    (hA : IsForward A) : ∀ {w : M.W}, w ∈ M.F → bforce M w A := by
  induction A with
  | prop a => exact fun hw => M.full_F hw
  | bot => exact fun hw => hw
  | and A B ihA ihB => exact fun hw => ⟨ihA hA.1 hw, ihB hA.2 hw⟩
  | or A B ihA _ => exact fun hw => .inl (ihA hA.1 hw)
  | imp A B _ ihB =>
      exact fun hw v hv _ => ihB hA.2 (M.hered_F hv hw)
  | coimp A B _ _ => exact absurd hA not_false
  | lax A ih =>
      exact fun hw v hv => ⟨v, M.refl_m v, ih hA (M.hered_F hv hw)⟩
  | colax A _ => exact absurd hA not_false

/-- **The absolute falsum is forced nowhere**: `ff = ⊤ ⤙ ⊤` needs a
predecessor refuting `⊤`. -/
theorem bforce_ff (M : BiModel) (w : M.W) : ¬ bforce M w BiForm.ff := by
  rintro ⟨v, _, _, hnt⟩
  exact hnt (fun u _ h => h)

/-! ## The adjunction ◯∃ ⊣ ◯∀, unit, counit, co-residuation -/

/-- Unit: `A ⊢ ◯∀◯∃A` (needs only reflexive `Rm` and persistence). -/
theorem bforce_unit (M : BiModel) (A : BiForm) {w : M.W}
    (hA : bforce M w A) : bforce M w (◯∀(◯∃A)) := by
  intro v hv
  exact ⟨v, M.refl_m v, v, M.refl_m v, bforce_hered M hv hA⟩

/-- Counit: `◯∃◯∀A ⊢ A` (exactly `counit_law`). -/
theorem bforce_counit (M : BiModel) (A : BiForm) {w : M.W}
    (h : bforce M w (◯∃(◯∀A))) : bforce M w A := by
  obtain ⟨u, huw, hlax⟩ := h
  obtain ⟨v, huv, hall⟩ := M.counit_law huw
  obtain ⟨y, hvy, hy⟩ := hlax v huv
  exact bforce_hered M (hall y hvy) hy

/-- **The modal adjunction** at the level of consequence on a model. -/
theorem bforce_adjunction (M : BiModel) (A B : BiForm) :
    (∀ w, bforce M w (◯∃A) → bforce M w B) ↔
    (∀ w, bforce M w A → bforce M w (◯∀B)) := by
  constructor
  · intro h w hA v hv
    exact ⟨v, M.refl_m v,
      h v ⟨v, M.refl_m v, bforce_hered M hv hA⟩⟩
  · intro h w hcol
    obtain ⟨u, huw, hA⟩ := hcol
    obtain ⟨v, huv, hall⟩ := M.counit_law huw
    obtain ⟨y, hvy, hy⟩ := h u hA v huv
    exact bforce_hered M (hall y hvy) hy

/-- **Co-residuation**: `⤙` is left adjoint to `∨`. -/
theorem bforce_coresiduation (M : BiModel) (A B C : BiForm) :
    (∀ w, bforce M w A → bforce M w (.or B C)) ↔
    (∀ w, bforce M w (A ⤙ B) → bforce M w C) := by
  classical
  constructor
  · rintro h w ⟨v, hvw, hA, hnB⟩
    rcases h v hA with hB | hC
    · exact absurd hB hnB
    · exact bforce_hered M hvw hC
  · intro h w hA
    by_cases hB : bforce M w B
    · exact .inl hB
    · exact .inr (h w ⟨w, M.refl_i w, hA, hB⟩)

end BiLax
