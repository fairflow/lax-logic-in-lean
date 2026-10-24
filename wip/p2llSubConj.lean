import LaxLogic.PLL.Semantics.CountermodelEmit
import LaxLogic.PLL.G4.G4Space
import Meta.Audit

/-!
# A ◯-clause for `∃p`: one direction holds, the other fails

This tests the sub-conjecture proposed in `docs/second-order-pll-survey.md`
§3.5 as a candidate ◯-clause for a Pitts-style computation of `∃p`,

    ∃p (Γ, ◯φ)  ≡  ∃p Γ ∧ ◯∃p (Γ, φ),

with the context read as the conjunction of its members.  The direction `⊢`
holds for every `Γ` and `φ` (`subconj_forward`); the direction `⊣` fails at
`Γ = ◯p ↠ q`, `φ = p` (`subconj_cell`, `subconj_false_at`, `subconj_false`).
Both are stated for ANY operator meeting the specification `ExSpec` of a
uniform `∃`-interpolant (`p`-free, implied by its argument, and below every
`p`-free consequence of it), so they say nothing about whether such
operators exist.

At the cell, `∃p (Γ ∧ ◯p) ⊢ q` by the minimality clause, since
`(◯p ↠ q) ∧ ◯p ⊢ q`, while `∃p Γ ∧ ◯∃p (Γ ∧ p) ⊬ q`.  The countermodel `M₀`
has worlds `0 ≤ 1` with `Rₘ = Rᵢ`, `F = ∅`, `q` true at `1` only and `p`
nowhere; `M₁` is its `p`-variant with `p` true at `1`.  `∃p Γ` holds at `0` in
`M₀` because `Γ` does; `∃p (Γ ∧ p)` holds at `1` in `M₁`, hence at `1` in `M₀`
since it is `p`-free (`forceB_val_congr`), hence `◯∃p (Γ ∧ p)` holds at `0`;
`q` fails at `0`.  The models are `FinCM` data, checked by `decide`; the
abstract formulas are evaluated through `FinCM.force_iff` and `soundness`.
-/

open PLLFormula

namespace PLLND
namespace P2LLSubConj

/-- `ψ` meets the specification of a uniform `∃p`-interpolant of `φ`:
`p`-free, `φ ⊢ ψ`, and `ψ ⊢ χ` for every `p`-free `χ` with `φ ⊢ χ`. -/
def ExSpec (p : String) (φ ψ : PLLFormula) : Prop :=
  p ∉ ψ.atoms ∧ Nonempty ([] ⊢ φ ↠ ψ) ∧
    ∀ χ : PLLFormula, p ∉ χ.atoms → Nonempty ([] ⊢ φ ↠ χ) → Nonempty ([] ⊢ ψ ↠ χ)

theorem pfree_and {p : String} {a b : PLLFormula} (ha : p ∉ a.atoms) (hb : p ∉ b.atoms) :
    p ∉ (a.and b).atoms := fun h => (mem_atoms_and.mp h).elim ha hb

/-! ## The cell -/

/-- `Γ = ◯p ↠ q`. -/
abbrev gam : PLLFormula := .ifThen (.somehow (.prop "p")) (.prop "q")

/-- `Γ, ◯φ` with `φ = p`: `(◯p ↠ q) ∧ ◯p`. -/
abbrev gamO : PLLFormula := .and gam (.somehow (.prop "p"))

/-- `Γ, φ` with `φ = p`: `(◯p ↠ q) ∧ p`. -/
abbrev gamP : PLLFormula := .and gam (.prop "p")

/-- `(◯p ↠ q) ∧ ◯p ⊢ q`. -/
theorem gamO_q : Nonempty ([] ⊢ gamO ↠ .prop "q") :=
  ⟨.impIntro (.impElim (.andElim1 (.iden (List.mem_cons_self ..)))
    (.andElim2 (.iden (List.mem_cons_self ..))))⟩

theorem p_not_in_q : "p" ∉ (prop "q").atoms := fun h =>
  absurd (Finset.mem_singleton.mp h) (by decide)

/-! ## The models -/

/-- Worlds `0 ≤ 1`, `Rₘ = Rᵢ`, `F = ∅`, `q` at `1`, `p` nowhere. -/
def M₀ : FinCM :=
  { n := 2, ri := [(0, 1)], rm := [(0, 1)], fall := [], val := [(1, "q")] }

/-- The `p`-variant of `M₀` with `p` true at `1`. -/
def M₁ : FinCM := { M₀ with val := (1, "p") :: M₀.val }

theorem wf₀ : M₀.WellFormed := FinCM.wellFormed_of_wellB (by decide)

theorem wf₁ : M₁.WellFormed := FinCM.wellFormed_of_wellB (by decide)

/-- `Γ` holds at `0` in `M₀`. -/
theorem gam_at_0 : M₀.forceB 0 gam = true := by decide

/-- `Γ ∧ p` holds at `1` in `M₁`. -/
theorem gamP_at_1 : M₁.forceB 1 gamP = true := by decide

/-- `q` fails at `0` in `M₀`. -/
theorem q_at_0 : M₀.forceB 0 (.prop "q") = false := by decide

/-- `1` is `Rₘ`-reachable from both worlds. -/
theorem rm_to_1 : ∀ v, v < 2 → M₀.rmB v 1 = true := by decide

/-! ## Evaluating abstract formulas -/

/-- A derivable implication transfers forcing in a well-formed `FinCM`
(constraint-model soundness, through `FinCM.force_iff`). -/
theorem forceB_of_der {M : FinCM} (wf : M.WellFormed) {φ ψ : PLLFormula}
    (d : [] ⊢ φ ↠ ψ) {w : Nat} (hw : w < M.n) (h : M.forceB w φ = true) :
    M.forceB w ψ = true := by
  have hs := PLLND.soundness d (M.toModel wf) ⟨w, hw⟩ (fun _ h => absurd h List.not_mem_nil)
  exact (M.force_iff wf ψ ⟨w, hw⟩).mp
    (hs ⟨w, hw⟩ ((M.toModel wf).refl_i _) ((M.force_iff wf φ ⟨w, hw⟩).mpr h))

/-- **Changing the valuation off the atoms of `φ` does not change `forceB`.** -/
theorem forceB_val_congr (M : FinCM) (val' : List (Nat × String)) :
    ∀ φ : PLLFormula,
      (∀ a ∈ φ.atoms, ∀ v, M.valB v a = ({ M with val := val' } : FinCM).valB v a) →
      ∀ w, M.forceB w φ = ({ M with val := val' } : FinCM).forceB w φ
  | .prop a, h, w => h a (Finset.mem_singleton_self a) w
  | .falsePLL, _, _ => rfl
  | .and φ ψ, h, w => by
      have e₁ := forceB_val_congr M val' φ (fun a ha => h a (mem_atoms_and.mpr (.inl ha)))
      have e₂ := forceB_val_congr M val' ψ (fun a ha => h a (mem_atoms_and.mpr (.inr ha)))
      simp only [FinCM.forceB, e₁, e₂]
  | .or φ ψ, h, w => by
      have e₁ := forceB_val_congr M val' φ (fun a ha => h a (mem_atoms_or.mpr (.inl ha)))
      have e₂ := forceB_val_congr M val' ψ (fun a ha => h a (mem_atoms_or.mpr (.inr ha)))
      simp only [FinCM.forceB, e₁, e₂]
  | .ifThen φ ψ, h, w => by
      have e₁ := forceB_val_congr M val' φ (fun a ha => h a (mem_atoms_ifThen.mpr (.inl ha)))
      have e₂ := forceB_val_congr M val' ψ (fun a ha => h a (mem_atoms_ifThen.mpr (.inr ha)))
      simp only [FinCM.forceB, e₁, e₂]
      rfl
  | .somehow φ, h, w => by
      have e := forceB_val_congr M val' φ h
      simp only [FinCM.forceB, e]
      rfl

/-- `M₀` and `M₁` agree on every atom other than `p`. -/
theorem valB_off_p {a : String} (ha : a ≠ "p") (v : Nat) :
    M₀.valB v a = ({ M₀ with val := M₁.val } : FinCM).valB v a := by
  have hmem : (v, a) ∈ M₀.val ↔ (v, a) ∈ (1, "p") :: M₀.val :=
    ⟨List.mem_cons_of_mem _,
      fun h => (List.mem_cons.mp h).resolve_left fun e => ha (congrArg Prod.snd e)⟩
  show (decide ((v, a) ∈ M₀.val) || M₀.fallB v) =
    (decide ((v, a) ∈ (1, "p") :: M₀.val) || M₀.fallB v)
  rw [decide_eq_decide.mpr hmem]

/-- A `p`-free formula forced at `1` in `M₁` is forced at `1` in `M₀`. -/
theorem transfer_at_1 {χ : PLLFormula} (hχ : "p" ∉ χ.atoms) (h : M₁.forceB 1 χ = true) :
    M₀.forceB 1 χ = true := by
  rw [forceB_val_congr M₀ M₁.val χ
    (fun a ha v => valB_off_p (fun e => hχ (e ▸ ha)) v) 1]
  exact h

/-- `◯χ` holds at `0` in `M₀` when `χ` holds at `1`. -/
theorem somehow_at_0 {χ : PLLFormula} (h : M₀.forceB 1 χ = true) :
    M₀.forceB 0 (.somehow χ) = true := by
  show ((List.range 2).all fun v => !(M₀.riB 0 v) ||
    (List.range 2).any fun u => M₀.rmB v u && M₀.forceB u χ) = true
  refine List.all_eq_true.mpr fun v hv => ?_
  have hu : ((List.range 2).any fun u => M₀.rmB v u && M₀.forceB u χ) = true :=
    List.any_eq_true.mpr ⟨1, List.mem_range.mpr (by decide), by
      simp only [rm_to_1 v (List.mem_range.mp hv), h, Bool.and_self]⟩
  rw [hu, Bool.or_true]

/-! ## The two directions -/

/-- **The direction `⊣` fails at `Γ = ◯p ↠ q`, `φ = p`, for all `e₁`, `e₂`,
`e₃` meeting the specification:**

    ∃p Γ ∧ ◯∃p (Γ ∧ p)  ⊬  ∃p (Γ ∧ ◯p). -/
theorem subconj_cell {e₁ e₂ e₃ : PLLFormula}
    (h₁ : ExSpec "p" gamO e₁) (h₂ : ExSpec "p" gam e₂) (h₃ : ExSpec "p" gamP e₃) :
    ¬ Nonempty ([] ⊢ .and e₂ (.somehow e₃) ↠ e₁) := by
  rintro ⟨d⟩
  obtain ⟨d₂⟩ := h₂.2.1
  obtain ⟨d₃⟩ := h₃.2.1
  obtain ⟨dq⟩ := h₁.2.2 (.prop "q") p_not_in_q gamO_q
  have hw₂ : M₀.forceB 0 e₂ = true := forceB_of_der wf₀ d₂ (by decide) gam_at_0
  have hu₃ : M₀.forceB 1 e₃ = true :=
    transfer_at_1 h₃.1 (forceB_of_der wf₁ d₃ (by decide) gamP_at_1)
  have hw : M₀.forceB 0 (.and e₂ (.somehow e₃)) = true := by
    show (M₀.forceB 0 e₂ && M₀.forceB 0 (.somehow e₃)) = true
    rw [hw₂, somehow_at_0 hu₃, Bool.and_self]
  have hq := forceB_of_der wf₀ dq (by decide) (forceB_of_der wf₀ d (by decide) hw)
  rw [q_at_0] at hq
  exact Bool.false_ne_true hq

/-- **The direction `⊢` holds for every `Γ` and `φ`:**

    ∃p (Γ ∧ ◯φ)  ⊢  ∃p Γ ∧ ◯∃p (Γ ∧ φ). -/
theorem subconj_forward {p : String} {Γ φ e₁ e₂ e₃ : PLLFormula}
    (h₁ : ExSpec p (.and Γ (.somehow φ)) e₁) (h₂ : ExSpec p Γ e₂)
    (h₃ : ExSpec p (.and Γ φ) e₃) :
    Nonempty ([] ⊢ e₁ ↠ .and e₂ (.somehow e₃)) := by
  obtain ⟨d₂⟩ := h₂.2.1
  obtain ⟨d₃⟩ := h₃.2.1
  refine h₁.2.2 (.and e₂ (.somehow e₃)) (pfree_and h₂.1 h₃.1)
    ⟨.impIntro (.andIntro ?_ ?_)⟩
  · exact .impElim (d₂.weaken _) (.andElim1 (.iden (List.mem_cons_self ..)))
  · exact .laxElim (.andElim2 (.iden (List.mem_cons_self ..)))
      (.laxIntro (.impElim ((d₃.weaken _).weaken _)
        (.andIntro (.andElim1 (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
          (.iden (List.mem_cons_self ..)))))

/-- **For any operator `E` meeting the specification, the equivalence fails
at the cell:**

    ¬ (E p (Γ ∧ ◯φ)  ⊣⊢  E p Γ ∧ ◯E p (Γ ∧ φ)),   Γ = ◯p ↠ q,  φ = p. -/
theorem subconj_false_at (E : String → PLLFormula → PLLFormula)
    (hE : ∀ p ψ, ExSpec p ψ (E p ψ)) :
    ¬ (Nonempty ([] ⊢ E "p" gamO ↠ .and (E "p" gam) (.somehow (E "p" gamP))) ∧
        Nonempty ([] ⊢ .and (E "p" gam) (.somehow (E "p" gamP)) ↠ E "p" gamO)) :=
  fun h => subconj_cell (hE "p" gamO) (hE "p" gam) (hE "p" gamP) h.2

/-- **The schema is false for every such operator.** -/
theorem subconj_false (E : String → PLLFormula → PLLFormula)
    (hE : ∀ p ψ, ExSpec p ψ (E p ψ)) :
    ¬ ∀ (p : String) (Γ φ : PLLFormula),
      Nonempty ([] ⊢ E p (.and Γ (.somehow φ)) ↠ .and (E p Γ) (.somehow (E p (.and Γ φ)))) ∧
        Nonempty ([] ⊢ .and (E p Γ) (.somehow (E p (.and Γ φ))) ↠ E p (.and Γ (.somehow φ))) :=
  fun h => subconj_false_at E hE (h "p" gam (.prop "p"))

end P2LLSubConj
end PLLND

/-! ## Axiom audit (pinned)

Exact pins, transcribed from the build, and the bound `[propext, Quot.sound]`.
The bound was watched failing (`[propext]` on `subconj_cell`, `[Quot.sound]`
on `subconj_false`); the negative test at the end keeps one failing bound in
the build. -/

/-- info: 'PLLND.P2LLSubConj.subconj_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.P2LLSubConj.subconj_cell

/-- info: 'PLLND.P2LLSubConj.subconj_forward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.P2LLSubConj.subconj_forward

/-- info: 'PLLND.P2LLSubConj.subconj_false_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.P2LLSubConj.subconj_false_at

/-- info: 'PLLND.P2LLSubConj.subconj_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.P2LLSubConj.subconj_false

/-- info: 'PLLND.P2LLSubConj.forceB_val_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.P2LLSubConj.forceB_val_congr

#axioms_within PLLND.P2LLSubConj.subconj_cell [propext, Quot.sound]
#axioms_within PLLND.P2LLSubConj.subconj_forward [propext, Quot.sound]
#axioms_within PLLND.P2LLSubConj.subconj_false_at [propext, Quot.sound]
#axioms_within PLLND.P2LLSubConj.subconj_false [propext, Quot.sound]
#axioms_within PLLND.P2LLSubConj.forceB_val_congr [propext, Quot.sound]

/-- error: 'PLLND.P2LLSubConj.subconj_cell' depends on Quot.sound, which the bound does not allow.
  declared: [propext]
Locate the entry with:  #axiom_path Quot.sound PLLND.P2LLSubConj.subconj_cell -/
#guard_msgs in
#axioms_within PLLND.P2LLSubConj.subconj_cell [propext]
