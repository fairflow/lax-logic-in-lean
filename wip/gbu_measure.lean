/-
# Settling the measure for `Gbu◯(G)`

The three `◯`-obligations of `docs/gbu-circ-seams.md` determine three
new steps of backward search:

    Ψ, Z ⇒g ◯C            Ψ ⇒g Z             Ω ⇒g Z
    ───────────── L◯      ──────── R◯        ────────── R◯ₙᵢ
    Ψ, ◯Z ⇒g ◯C           Ψ ⇒g ◯Z            Ω →g ◯Z

`R◯ₙᵢ` releases focus (its `FRJ` counterpart `circNotIn` has a REGULAR
premise, and no focus-preserving variant can exist).  This file settles
what that does to termination.  Two results.

**1.  The paper's weight cannot be repaired.**  `Wg = ⟨unclosed, tp,
size⟩` and every variant of it are functions of the sequent alone, and
the extended step relation has a two-cycle:

    (Ω ⇒g Z)  --L⊃ on ◯Z ⊃ B ∈ Ω-->  (Ω →g ◯Z)  --R◯ₙᵢ-->  (Ω ⇒g Z)

so `¬ WellFounded (StepC G)` for EVERY `G` (`not_wf_stepC`).  No measure
on sequents can decrease along both steps: the `L⊃` left premise keeps
the context and may enlarge the goal, and `R◯ₙᵢ` keeps the context and
turns an irregular sequent back into a regular one.  The conjecture
recorded in `docs/gbu-circ-seams.md` — that a reordering of `Wg` might
work — is therefore REFUTED.

**2.  A store settles it.**  The cycle turns on re-focusing the SAME
implication of the SAME context, so backward search must remember which
implications it has already focused on.  Carrying that set `U` in the
state, the measure

    Wg◯(τ, U) = ⟨ |Sf^L(G) ∖ Cl(Ψ)| , Σ_{X∈Ψ} |X| , |Ψ^⊃ ∖ U| , |C| ⟩

lexicographic, decreases on all twenty steps (`wgo_step`), hence
`StepU` is well-founded (`stepU_wf`).

Two things are worth recording about that measure.

* **`tp` disappears.**  In the paper `tp` exists for exactly one step,
  the left premise of `L⊃`, where the goal may grow; `|Ψ^⊃ ∖ U|` covers
  that step instead.  And `tp` CANNOT be retained: it is what `R◯ₙᵢ`
  increases.
* **`ctxSize` is new and load-bearing.**  It is what the context-shrinking
  left rules decrease, which is what frees `|Ψ^⊃ ∖ U|` to be reset
  whenever the context changes — `L∧` can expose implications that were
  not in `Ψ^⊃` before, so the store count is not monotone on its own.
-/
import wip.gbu

namespace FRJ.Gbu

open FRJ Form

/-! ## 1.  The naive extension is not well-founded -/

/-- The step relation of `Gbu◯(G)` on sequents alone: `Step` plus the
three `◯` steps.  `lcirc` is `L◯` (goal `◯`-shaped), `rcirc` is `R◯`,
`rcircNI` is `R◯ₙᵢ` — note it goes irregular → REGULAR. -/
inductive StepC (G : Form) : (Bool × List Form × Form) →
    (Bool × List Form × Form) → Prop
  | old {p q} (h : Step G p q) : StepC G p q
  | lcirc {Ψ Z C} :
      StepC G (true, Z :: Ψ, .circ C) (true, .circ Z :: Ψ, .circ C)
  | rcirc {Ψ Z} : StepC G (true, Ψ, Z) (true, Ψ, .circ Z)
  | rcircNI {Ψ Z} : StepC G (true, Ψ, Z) (false, Ψ, .circ Z)

/-- A well-founded relation has no two-cycle. -/
theorem no_two_cycle {α : Type} {r : α → α → Prop} (hwf : WellFounded r)
    {a b : α} (hab : r a b) (hba : r b a) : False := by
  have key : ∀ z, Acc r z → ∀ y, r z y → r y z → False := by
    intro z hz
    induction hz with
    | intro w _ ih => exact fun y hwy hyw => ih y hyw w hyw hwy
  exact key a (hwf.apply a) b hab hba

/-- **The naive `◯`-extension of backward search does not terminate.**
Take any `Z`, `B`, `Ψ` and put `Γ = ◯Z ⊃ B, Ψ`.  Then

    Γ →g ◯Z   is a premise of   Γ ⇒g Z     by `L⊃` on `◯Z ⊃ B`,
    Γ ⇒g Z    is a premise of   Γ →g ◯Z    by `R◯ₙᵢ`,

a two-cycle.  Consequently NO function of the sequent — no reordering or
refinement of `Wg` — can serve as a termination measure. -/
theorem not_wf_stepC (G : Form) :
    ¬ WellFounded (fun p q : Bool × List Form × Form => StepC G p q) := by
  intro hwf
  exact no_two_cycle (a := (false, Form.imp (.circ (.atom "z")) .bot :: [],
      Form.circ (.atom "z")))
    (b := (true, Form.imp (.circ (.atom "z")) .bot :: [], Form.atom "z"))
    hwf (.old .limpL1) .rcircNI

/-- **No measure on sequents can work**, into any well-founded order
whatsoever.  This is the sharp form of `not_wf_stepC`, and it is what
closes the conjecture recorded in `docs/gbu-circ-seams.md`: reordering or
refining `Wg` is not merely hard, it is impossible.  (The statement is
about the STEP RELATION, which is exactly what the paper's Theorem 7 and
our `step_wf` are about; a measure allowed to consult the database `D`
is not excluded, but neither Lemma 8 nor the recursion of Theorem 8
has access to one.) -/
theorem no_measure_stepC (G : Form) {β : Type}
    (m : (Bool × List Form × Form) → β) {lt : β → β → Prop}
    (hwf : WellFounded lt)
    (hm : ∀ p q, StepC G p q → lt (m p) (m q)) : False :=
  not_wf_stepC G (Subrelation.wf (fun {p q} h => hm p q h) (InvImage.wf m hwf))

/-! ## 2.  The store, and the measure that works -/

/-- The state of backward search in `Gbu◯(G)`: a sequent together with
the set `U` of implications of the context already focused on at this
context. -/
abbrev SeqU := Bool × List Form × Form × List Form

/-- `Σ_{X ∈ Ψ} |X|`: what the context-shrinking left rules decrease. -/
def ctxSize (Ψ : List Form) : Nat := (Ψ.map Form.size).sum

/-- `|Ψ^⊃ ∖ U|`: the implications of the context still available for
`L⊃`.  Replaces the paper's `tp`. -/
def usedCount (Ψ U : List Form) : Nat :=
  Ψ.countP (fun X => X.isImp && !decide (X ∈ U))

/-- `Wg◯`. -/
def wgo (G : Form) (s : SeqU) : Nat × Nat × Nat × Nat :=
  (unclosed G s.2.1, ctxSize s.2.1, usedCount s.2.1 s.2.2.2, s.2.2.1.size)

/-- The lexicographic order on quadruples, written out. -/
def WgoLt (x y : Nat × Nat × Nat × Nat) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧
    (x.2.2.1 < y.2.2.1 ∨ (x.2.2.1 = y.2.2.1 ∧ x.2.2.2 < y.2.2.2)))))

private def accWgo (a b c d : Nat) : Acc WgoLt (a, b, c, d) :=
  .intro _ (by
    rintro ⟨a', b', c', d'⟩ h
    exact accWgo a' b' c' d')
termination_by (a, b, c, d)
decreasing_by
  rcases h with h | ⟨he, h | ⟨he2, h | ⟨he3, h⟩⟩⟩
  · exact Prod.Lex.left _ _ h
  · subst he
    exact Prod.Lex.right _ (Prod.Lex.left _ _ h)
  · subst he; subst he2
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ h))
  · subst he; subst he2; subst he3
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ h))

theorem wgoLt_wf : WellFounded WgoLt :=
  ⟨fun x => by obtain ⟨a, b, c, d⟩ := x; exact accWgo a b c d⟩

/-! ### The step relation with the store

One constructor per (rule, premise) pair, as in `Step`, plus the three
`◯` steps.  The store is UNCONSTRAINED (`U'`) on every step that shrinks
the context or the unclosed count, since those sit above it; it is
carried unchanged on the goal-only steps; and `limpL1` extends it with
the implication it focuses on, which must not already be there. -/
inductive StepU (G : Form) : SeqU → SeqU → Prop
  | landL {Ψ A B C U U'} :
      StepU G (true, A :: B :: Ψ, C, U') (true, .and A B :: Ψ, C, U)
  | randR1 {Ψ A B U} : StepU G (true, Ψ, A, U) (true, Ψ, .and A B, U)
  | randR2 {Ψ A B U} : StepU G (true, Ψ, B, U) (true, Ψ, .and A B, U)
  | lorL1 {Ψ A B C U U'} :
      StepU G (true, A :: Ψ, C, U') (true, .or A B :: Ψ, C, U)
  | lorL2 {Ψ A B C U U'} :
      StepU G (true, B :: Ψ, C, U') (true, .or A B :: Ψ, C, U)
  | rorR1 {Ψ C₁ C₂ U} : StepU G (false, Ψ, C₁, U) (true, Ψ, .or C₁ C₂, U)
  | rorR2 {Ψ C₁ C₂ U} : StepU G (false, Ψ, C₂, U) (true, Ψ, .or C₁ C₂, U)
  /-- The left premise of `L⊃`: the context is unchanged, the goal may
  GROW, and the focused implication is banked. -/
  | limpL1 {Ψ A B C U} (hnU : Form.imp A B ∉ U) :
      StepU G (false, .imp A B :: Ψ, A, .imp A B :: U)
        (true, .imp A B :: Ψ, C, U)
  | limpL2 {Ψ A B C U U'} :
      StepU G (true, B :: Ψ, C, U') (true, .imp A B :: Ψ, C, U)
  | rimpI {Ψ A B U} : StepU G (true, Ψ, B, U) (true, Ψ, .imp A B, U)
  | rimpNI {Ψ A B U U'} (hA : A ∈ sfL G) (hnc : ¬ Clo Ψ A) :
      StepU G (true, A :: Ψ, B, U') (true, Ψ, .imp A B, U)
  | randI1 {Ψ A B U} : StepU G (false, Ψ, A, U) (false, Ψ, .and A B, U)
  | randI2 {Ψ A B U} : StepU G (false, Ψ, B, U) (false, Ψ, .and A B, U)
  | rorI1 {Ψ C₁ C₂ U} : StepU G (false, Ψ, C₁, U) (false, Ψ, .or C₁ C₂, U)
  | rorI2 {Ψ C₁ C₂ U} : StepU G (false, Ψ, C₂, U) (false, Ψ, .or C₁ C₂, U)
  | rimpII {Ψ A B U} : StepU G (false, Ψ, B, U) (false, Ψ, .imp A B, U)
  | rimpNII {Ψ A B U U'} (hA : A ∈ sfL G) (hnc : ¬ Clo Ψ A) :
      StepU G (true, A :: Ψ, B, U') (false, Ψ, .imp A B, U)
  /-- `L◯` — the goal must be `◯`-shaped (unrestricted it is unsound). -/
  | lcirc {Ψ Z C U U'} :
      StepU G (true, Z :: Ψ, .circ C, U') (true, .circ Z :: Ψ, .circ C, U)
  /-- `R◯`. -/
  | rcirc {Ψ Z U} : StepU G (true, Ψ, Z, U) (true, Ψ, .circ Z, U)
  /-- `R◯ₙᵢ` — focus is released, so the phase goes UP; the goal is what
  decreases. -/
  | rcircNI {Ψ Z U} : StepU G (true, Ψ, Z, U) (false, Ψ, .circ Z, U)

/-! ### `ctxSize`, `usedCount` -/

theorem ctxSize_cons {Ψ : List Form} {X : Form} :
    ctxSize (X :: Ψ) = X.size + ctxSize Ψ := by
  show ((X :: Ψ).map Form.size).sum = X.size + (Ψ.map Form.size).sum
  rw [List.map_cons, List.sum_cons]

/-- `Cl(◯Z, Ψ) ⊆ Cl(Z, Ψ)`: the unit again, and what makes `L◯` safe for
the `unclosed` component. -/
theorem clo_circ_cons {Ψ : List Form} {Z : Form} :
    ∀ {X : Form}, Clo (.circ Z :: Ψ) X → Clo (Z :: Ψ) X := by
  intro X h
  induction h with
  | @base C hC =>
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact .circ (.base List.mem_cons_self)
      · exact .base (List.mem_cons_of_mem _ hC')
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih
  | circ _ ih => exact .circ ih

/-- Banking one unbanked implication of the context strictly shrinks the
pool. -/
theorem usedCount_lt {Ψ U : List Form} {A B : Form}
    (hnU : Form.imp A B ∉ U) :
    usedCount (.imp A B :: Ψ) (.imp A B :: U)
      < usedCount (.imp A B :: Ψ) U := by
  refine countP_lt_countP (fun X _ hX => ?_) (b := Form.imp A B)
    List.mem_cons_self ?_ ?_
  · rcases Bool.and_eq_true_iff.mp hX with ⟨h1, h2⟩
    refine Bool.and_eq_true_iff.mpr ⟨h1, ?_⟩
    have hX' : ¬ (X ∈ Form.imp A B :: U) := by
      intro hc
      rw [decide_eq_true hc] at h2
      exact Bool.noConfusion h2
    have : decide (X ∈ U) = false :=
      decide_eq_false (fun hc => hX' (List.mem_cons_of_mem _ hc))
    rw [this]
    rfl
  · rw [decide_eq_false hnU]
    rfl
  · rw [decide_eq_true (show Form.imp A B ∈ Form.imp A B :: U from
      List.mem_cons_self)]
    rfl

/-! ### Lemma 8 for `Wg◯` -/

private theorem wgoDrop {G : Form} {s t : SeqU}
    (h : unclosed G s.2.1 < unclosed G t.2.1) : WgoLt (wgo G s) (wgo G t) :=
  Or.inl h

private theorem wgoCtx {G : Form} {s t : SeqU}
    (hcl : ∀ X ∈ t.2.1, Clo s.2.1 X) (hs : ctxSize s.2.1 < ctxSize t.2.1) :
    WgoLt (wgo G s) (wgo G t) := by
  have hmono : unclosed G s.2.1 ≤ unclosed G t.2.1 :=
    unclosed_mono (fun _ hX => clo_trans hcl hX)
  rcases Nat.lt_or_ge (unclosed G s.2.1) (unclosed G t.2.1) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨Nat.le_antisymm hmono h, Or.inl hs⟩

private theorem wgoUsed {G : Form} {s t : SeqU} (hΨ : s.2.1 = t.2.1)
    (hu : usedCount s.2.1 s.2.2.2 < usedCount t.2.1 t.2.2.2) :
    WgoLt (wgo G s) (wgo G t) := by
  refine Or.inr ⟨?_, Or.inr ⟨?_, Or.inl hu⟩⟩
  · show unclosed G s.2.1 = unclosed G t.2.1
    rw [hΨ]
  · show ctxSize s.2.1 = ctxSize t.2.1
    rw [hΨ]

private theorem wgoGoal {G : Form} {s t : SeqU} (hΨ : s.2.1 = t.2.1)
    (hU : s.2.2.2 = t.2.2.2) (hg : s.2.2.1.size < t.2.2.1.size) :
    WgoLt (wgo G s) (wgo G t) := by
  refine Or.inr ⟨?_, Or.inr ⟨?_, Or.inr ⟨?_, hg⟩⟩⟩
  · show unclosed G s.2.1 = unclosed G t.2.1
    rw [hΨ]
  · show ctxSize s.2.1 = ctxSize t.2.1
    rw [hΨ]
  · show usedCount s.2.1 s.2.2.2 = usedCount t.2.1 t.2.2.2
    rw [hΨ, hU]

/-- **Lemma 8 for `Gbu◯(G)`**: `Wg◯` strictly decreases on every step of
backward search. -/
theorem wgo_step {G : Form} {s t : SeqU} (h : StepU G s t) :
    WgoLt (wgo G s) (wgo G t) := by
  have goal : ∀ {A B : Form}, A.size < A.size + B.size + 1 :=
    fun {_ _} => Nat.lt_succ_of_le (Nat.le_add_right _ _)
  have goal' : ∀ {A B : Form}, B.size < A.size + B.size + 1 :=
    fun {_ _} => Nat.lt_succ_of_le (Nat.le_add_left _ _)
  cases h with
  | @landL Ψ A B C _ _ =>
      refine wgoCtx (fun X hX => ?_) ?_
      · rcases List.mem_cons.mp hX with rfl | hX'
        · exact .and (.base List.mem_cons_self)
            (.base (List.mem_cons_of_mem _ List.mem_cons_self))
        · exact .base (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hX'))
      · show ctxSize (A :: B :: Ψ) < ctxSize (Form.and A B :: Ψ)
        rw [ctxSize_cons, ctxSize_cons, ctxSize_cons]
        show A.size + (B.size + ctxSize Ψ) < (A.size + B.size + 1) + ctxSize Ψ
        omega
  | randR1 => exact wgoGoal rfl rfl goal
  | randR2 => exact wgoGoal rfl rfl goal'
  | @lorL1 Ψ A B C _ _ =>
      refine wgoCtx (fun X hX => ?_) ?_
      · rcases List.mem_cons.mp hX with rfl | hX'
        · exact .orL (.base List.mem_cons_self)
        · exact .base (List.mem_cons_of_mem _ hX')
      · show ctxSize (A :: Ψ) < ctxSize (Form.or A B :: Ψ)
        rw [ctxSize_cons, ctxSize_cons]
        show A.size + ctxSize Ψ < (A.size + B.size + 1) + ctxSize Ψ
        omega
  | @lorL2 Ψ A B C _ _ =>
      refine wgoCtx (fun X hX => ?_) ?_
      · rcases List.mem_cons.mp hX with rfl | hX'
        · exact .orR (.base List.mem_cons_self)
        · exact .base (List.mem_cons_of_mem _ hX')
      · show ctxSize (B :: Ψ) < ctxSize (Form.or A B :: Ψ)
        rw [ctxSize_cons, ctxSize_cons]
        show B.size + ctxSize Ψ < (A.size + B.size + 1) + ctxSize Ψ
        omega
  | rorR1 => exact wgoGoal rfl rfl goal
  | rorR2 => exact wgoGoal rfl rfl goal'
  | limpL1 hnU => exact wgoUsed rfl (usedCount_lt hnU)
  | @limpL2 Ψ A B C _ _ =>
      refine wgoCtx (fun X hX => ?_) ?_
      · rcases List.mem_cons.mp hX with rfl | hX'
        · exact .imp (.base List.mem_cons_self)
        · exact .base (List.mem_cons_of_mem _ hX')
      · show ctxSize (B :: Ψ) < ctxSize (Form.imp A B :: Ψ)
        rw [ctxSize_cons, ctxSize_cons]
        show B.size + ctxSize Ψ < (A.size + B.size + 1) + ctxSize Ψ
        omega
  | rimpI => exact wgoGoal rfl rfl goal'
  | rimpNI hA hnc => exact wgoDrop (unclosed_lt hA hnc)
  | randI1 => exact wgoGoal rfl rfl goal
  | randI2 => exact wgoGoal rfl rfl goal'
  | rorI1 => exact wgoGoal rfl rfl goal
  | rorI2 => exact wgoGoal rfl rfl goal'
  | rimpII => exact wgoGoal rfl rfl goal'
  | rimpNII hA hnc => exact wgoDrop (unclosed_lt hA hnc)
  | @lcirc Ψ Z C _ _ =>
      refine wgoCtx (fun X hX => ?_) ?_
      · rcases List.mem_cons.mp hX with rfl | hX'
        · exact .circ (.base List.mem_cons_self)
        · exact .base (List.mem_cons_of_mem _ hX')
      · show ctxSize (Z :: Ψ) < ctxSize (Form.circ Z :: Ψ)
        rw [ctxSize_cons, ctxSize_cons]
        show Z.size + ctxSize Ψ < (Z.size + 1) + ctxSize Ψ
        omega
  | @rcirc Ψ Z _ =>
      exact wgoGoal rfl rfl (show Z.size < Z.size + 1 from Nat.lt_succ_self _)
  | @rcircNI Ψ Z _ =>
      exact wgoGoal rfl rfl (show Z.size < Z.size + 1 from Nat.lt_succ_self _)

/-- **Termination of backward proof-search in `Gbu◯(G)`.** -/
theorem stepU_wf (G : Form) :
    WellFounded (fun s t : SeqU => StepU G s t) :=
  Subrelation.wf (fun {_ _} h => wgo_step h)
    (InvImage.wf (fun s : SeqU => wgo G s) wgoLt_wf)

/-! ### Fidelity: the store is bookkeeping, not a change of rules

Every `StepU` step erases to a `StepC` step.  So `StepU` is the SAME
backward search, with a record of which implications have already been
focused on; the only thing the store does is forbid re-focusing one
(`limpL1`'s `hnU`), which is exactly the move the two-cycle repeats. -/

theorem stepC_of_stepU {G : Form} {s t : SeqU} (h : StepU G s t) :
    StepC G (s.1, s.2.1, s.2.2.1) (t.1, t.2.1, t.2.2.1) := by
  cases h with
  | landL => exact .old .landL
  | randR1 => exact .old .randR1
  | randR2 => exact .old .randR2
  | lorL1 => exact .old .lorL1
  | lorL2 => exact .old .lorL2
  | rorR1 => exact .old .rorR1
  | rorR2 => exact .old .rorR2
  | limpL1 _ => exact .old .limpL1
  | limpL2 => exact .old .limpL2
  | rimpI => exact .old .rimpI
  | rimpNI hA hnc => exact .old (.rimpNI hA hnc)
  | randI1 => exact .old .randI1
  | randI2 => exact .old .randI2
  | rorI1 => exact .old .rorI1
  | rorI2 => exact .old .rorI2
  | rimpII => exact .old .rimpII
  | rimpNII hA hnc => exact .old (.rimpNII hA hnc)
  | lcirc => exact .lcirc
  | rcirc => exact .rcirc
  | rcircNI => exact .rcircNI

/-! ## Axiom pins -/

/-- info: 'FRJ.Gbu.not_wf_stepC' does not depend on any axioms -/
#guard_msgs in
#print axioms not_wf_stepC

/-- info: 'FRJ.Gbu.wgo_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wgo_step

/-- info: 'FRJ.Gbu.stepU_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepU_wf

/-- info: 'FRJ.Gbu.no_measure_stepC' does not depend on any axioms -/
#guard_msgs in
#print axioms no_measure_stepC

/-- info: 'FRJ.Gbu.stepC_of_stepU' does not depend on any axioms -/
#guard_msgs in
#print axioms stepC_of_stepU

end FRJ.Gbu
