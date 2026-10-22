import LaxLogic.PLL.SubTab.Model

/-!
# The subframe tableau: completeness

2026-10-15.  Every formula has a closed tableau (`yes`) or a
finite subframe countermodel (`no`).  The countermodel is read off the
open tree (`SubTab/Model.lean`) as tables by `extract`, which turns any
finite decidable subframe model refuting `φ` into a `SubCM` that `no.check`
accepts.

Fragment first (CLAUDE.md rule 8): `complete_boxFree` (◯-free), then
`complete` (PLL).
-/

open PLLFormula

namespace PLLND
namespace SubTab

open SubframeModel.CF

/-- The atoms of a formula. -/
def atomsOf (φ : PLLFormula) : List String :=
  (subs φ).filterMap fun | .prop a => some a | _ => none

theorem prop_mem_atomsOf {φ : PLLFormula} {a : String} (h : PLLFormula.prop a ∈ subs φ) :
    a ∈ atomsOf φ :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

section Extract
variable (M : SubframeModel) [FinDec M] (x : M.W) (φ : PLLFormula)

/-- The worlds, with `x` first. -/
def worldsL : List M.W := x :: FinDec.elems (M := M)

/-- **A finite decidable model as tables** (atoms restricted to those of `φ`). -/
def extract : SubCM where
  n := (worldsL M x).length
  root := 0
  le := (worldsL M x).map fun u => (worldsL M x).map fun v => decide (M.le u v)
  S := (worldsL M x).map fun u => decide (u ∈ M.S)
  val := (worldsL M x).map fun u => (atomsOf φ).filter fun a => decide (u ∈ M.V a)

variable {M x φ}

theorem extract_n : (extract M x φ).n = (worldsL M x).length := rfl

theorem leB_eq {i j : Nat} (hi : i < (worldsL M x).length) (hj : j < (worldsL M x).length) :
    (extract M x φ).leB i j = decide (M.le (worldsL M x)[i] (worldsL M x)[j]) := by
  simp only [SubCM.leB, extract, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.map_some,
    Option.getD_some]

theorem SB_eq {i : Nat} (hi : i < (worldsL M x).length) :
    (extract M x φ).SB i = decide ((worldsL M x)[i] ∈ M.S) := by
  simp only [SubCM.SB, extract, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

theorem val_eq {i : Nat} (hi : i < (worldsL M x).length) :
    (extract M x φ).val.getD i [] =
      (atomsOf φ).filter fun a => decide ((worldsL M x)[i] ∈ M.V a) := by
  simp only [extract, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

theorem vB_iff {a : String} {i : Nat} (hi : i < (worldsL M x).length) :
    (extract M x φ).vB a i = true ↔ a ∈ atomsOf φ ∧ (worldsL M x)[i] ∈ M.V a := by
  simp only [SubCM.vB, val_eq hi, List.contains_iff_mem, List.mem_filter, decide_eq_true_eq]

theorem mem_worldsL (v : M.W) : ∃ j, ∃ hj : j < (worldsL M x).length, (worldsL M x)[j] = v :=
  List.mem_iff_getElem.mp (List.mem_cons_of_mem _ (FinDec.complete v))

theorem extract_ok : (extract M x φ).okB = true := by
  simp only [SubCM.okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    extract_n]
  refine ⟨⟨⟨Nat.succ_pos _, fun i hi => ?_⟩, fun i hi j hj k hk => ?_⟩, fun i hi j hj => ?_⟩
  · rw [leB_eq hi hi]; exact decide_eq_true (M.refl _)
  · rw [leB_eq hi hj, leB_eq hj hk, leB_eq hi hk]
    cases h₁ : decide (M.le (worldsL M x)[i] (worldsL M x)[j]) <;>
      cases h₂ : decide (M.le (worldsL M x)[j] (worldsL M x)[k]) <;> simp only [Bool.and_false,
        Bool.and_true, Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or]
    exact decide_eq_true (M.trans (of_decide_eq_true h₁) (of_decide_eq_true h₂))
  · rw [leB_eq hi hj]
    cases h : decide (M.le (worldsL M x)[i] (worldsL M x)[j]) <;>
      simp only [Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, List.all_eq_true]
    intro a ha
    rw [val_eq hi] at ha
    obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
    exact (vB_iff hj).mpr ⟨ha1, M.hered (of_decide_eq_true h) (of_decide_eq_true ha2)⟩

theorem all_range_iff {n : Nat} {g : Nat → Bool} :
    (List.range n).all g = true ↔ ∀ j, j < n → g j = true := by
  simp only [List.all_eq_true, List.mem_range]

/-- The tables force what the model forces, on the subformulas of `φ`. -/
theorem forceB_iff_force : ∀ (ψ : PLLFormula), ψ ∈ subs φ →
    ∀ (i : Nat) (hi : i < (worldsL M x).length),
      (extract M x φ).forceB i ψ = true ↔ M.force (worldsL M x)[i] ψ
  | .prop a, hψ, i, hi => by
      rw [SubCM.forceB, vB_iff hi]
      exact ⟨fun h => h.2, fun h => ⟨prop_mem_atomsOf hψ, h⟩⟩
  | .falsePLL, _, i, hi => ⟨fun h => absurd h Bool.false_ne_true, False.elim⟩
  | .and A B, hψ, i, hi => by
      obtain ⟨hA, hB⟩ := (subs_closed φ).and A B hψ
      simp only [SubCM.forceB, Bool.and_eq_true]
      exact and_congr (forceB_iff_force A hA i hi) (forceB_iff_force B hB i hi)
  | .or A B, hψ, i, hi => by
      obtain ⟨hA, hB⟩ := (subs_closed φ).or A B hψ
      simp only [SubCM.forceB, Bool.or_eq_true]
      exact or_congr (forceB_iff_force A hA i hi) (forceB_iff_force B hB i hi)
  | .ifThen A B, hψ, i, hi => by
      obtain ⟨hA, hB⟩ := (subs_closed φ).imp A B hψ
      rw [SubCM.forceB, all_range_iff]
      constructor
      · intro h v hv hAv
        obtain ⟨j, hj, rfl⟩ := mem_worldsL (x := x) v
        have := h j hj
        rw [leB_eq hi hj, decide_eq_true hv, (forceB_iff_force A hA j hj).mpr hAv] at this
        simp only [Bool.not_true, Bool.false_or] at this
        exact (forceB_iff_force B hB j hj).mp this
      · intro h j hj
        rw [leB_eq hi hj]
        cases hl : decide (M.le (worldsL M x)[i] (worldsL M x)[j]) <;>
          simp only [Bool.not_false, Bool.true_or, Bool.not_true, Bool.false_or]
        cases hf : (extract M x φ).forceB j A <;>
          simp only [Bool.not_false, Bool.true_or, Bool.not_true, Bool.false_or]
        exact (forceB_iff_force B hB j hj).mpr
          (h _ (of_decide_eq_true hl) ((forceB_iff_force A hA j hj).mp hf))
  | .somehow A, hψ, i, hi => by
      have hA := (subs_closed φ).box A hψ
      rw [SubCM.forceB, all_range_iff]
      constructor
      · intro h v hv hvS
        obtain ⟨j, hj, rfl⟩ := mem_worldsL (x := x) v
        have := h j hj
        rw [leB_eq hi hj, decide_eq_true hv, SB_eq hj, decide_eq_true hvS] at this
        simp only [Bool.not_true, Bool.false_or] at this
        exact (forceB_iff_force A hA j hj).mp this
      · intro h j hj
        rw [leB_eq hi hj, SB_eq hj]
        cases hl : decide (M.le (worldsL M x)[i] (worldsL M x)[j]) <;>
          simp only [Bool.not_false, Bool.true_or, Bool.not_true, Bool.false_or]
        cases hs : decide ((worldsL M x)[j] ∈ M.S) <;>
          simp only [Bool.not_false, Bool.true_or, Bool.not_true, Bool.false_or]
        exact (forceB_iff_force A hA j hj).mpr
          (h _ (of_decide_eq_true hl) (of_decide_eq_true hs))

/-- **A finite decidable model refuting `φ` at `x` gives tables that the no
side accepts.** -/
theorem extract_refutes (hx : ¬ M.force x φ) : (extract M x φ).refutes φ = true := by
  simp only [SubCM.refutes, extract_ok, Bool.true_and, Bool.not_eq_true']
  have h0 : 0 < (worldsL M x).length := Nat.succ_pos _
  cases h : (extract M x φ).forceB (extract M x φ).root φ
  · rfl
  · exact absurd ((forceB_iff_force φ (self_mem_subs φ) 0 h0).mp h) hx

end Extract

/-- **Completeness, ◯-free instance.**  A ◯-free formula has a closed tableau
or a finite subframe countermodel. -/
theorem complete_boxFree (φ : PLLFormula) (hφ : NoBox (subs φ)) :
    (∃ c, yes.check φ c = true) ∨ (∃ m, no.check φ m = true) := by
  rcases dich_boxFree (subs φ) (subs_closed φ) hφ _ ⟨false, [], [φ]⟩ rfl
      (fun _ h => absurd h List.not_mem_nil) (all_one (self_mem_subs φ)) with
    ⟨c, hc⟩ | ⟨t, hg, hcov⟩
  · exact .inl ⟨c, hc⟩
  · exact .inr ⟨extract (model t hg) (rootW t hg) φ,
      extract_refutes ((root_refutes t hg hcov).2.2 φ List.mem_cons_self)⟩


/-- **Completeness of the subframe tableau.**  Every formula has a closed
tableau or a finite subframe countermodel; with `yes.sound` and `no.sound`
the tableau is a decision procedure for PLL, with certificates on both
sides. -/
theorem complete (φ : PLLFormula) :
    (∃ c, yes.check φ c = true) ∨ (∃ m, no.check φ m = true) := by
  rcases dich (subs φ) (subs_closed φ) _ ⟨false, [], [φ]⟩ rfl
      (fun _ h => absurd h List.not_mem_nil) (all_one (self_mem_subs φ)) with
    ⟨c, hc⟩ | ⟨t, hg, hcov⟩
  · exact .inl ⟨c, hc⟩
  · exact .inr ⟨extract (model t hg) (rootW t hg) φ,
      extract_refutes ((root_refutes t hg hcov).2.2 φ List.mem_cons_self)⟩

end SubTab
end PLLND

#axioms_within PLLND.SubTab.extract_refutes [propext, Quot.sound]
#axioms_within PLLND.SubTab.complete_boxFree [propext, Quot.sound]
#axioms_within PLLND.SubTab.complete [propext, Quot.sound]
