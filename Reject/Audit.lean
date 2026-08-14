/-
ADVERSARIAL PASS on the ◯ rules (`Reject/Build.lean`).

Not a re-statement of soundness — an attack on SCOPE and on the
degenerate cases, per the repo's testing doctrine (boundary cells
first, branch coverage, fail only on a certificate).  Five questions
were put to the rules; three answers are good, two are findings that
constrain the join rule (T1).

  Q1  Are `boxRefuteHere`'s premises VACUOUS, or over-strong?
      → `boxRefuteHere_exact`: they are EXACTLY the semantic
        condition.  Neither.
  Q2  Is `S = ∅` legal, and does it break anything?
      → `emptyS` is a lawful `RootData`; the rule stays sound (it is
        an instance of Q1).  Documented, not a defect.
  Q3  Does `addRoot` preserve REDUCEDNESS?
      → YES, `addRoot_reduced`.
  Q4  Does `addRoot` preserve CONFLUENCE?
      → **NO** — `addRoot_not_confluent`, a machine-checked
        counterexample.  THIS MATTERS: the unary-arity licence for the
        ◯-rule (docs/frj-lifting.md §3) holds on reduced AND confluent
        frames, so a calculus that leaves the confluent class loses
        it.  The join rule must carry a confluence side condition, or
        the ◯-rule must be given its general (list-of-premises) form.
  Q5  Do the rules COMPOSE to a real result, or only to the two demo
      facts?
      → `boxp_not_p`: the repo landmark `◯p ⊬ p` derived by
        construction, using `boxHolds` and `not_laxND_of_root`.

Also found and fixed: `boxHolds` was INCOMPLETE — it could only
witness `◯A` at the root through a PROPER `Rm`-successor, missing the
reflexive case where the root itself forces `A`.  `boxHoldsRoot`
supplies it.
-/
import Reject.Build
import LaxLogic.PLLFrames

namespace Reject

open PLLND

variable {M : ConstraintModel}

/-! ## Q1 — the premises of `boxRefuteHere` are exactly right -/

/-- **Anti-vacuity / anti-overstrength**: the two premises of
`boxRefuteHere` are EQUIVALENT to "no `Rm`-successor of the root
forces `A`", which is precisely the `◯∈` refutation condition.  So the
rule is neither vacuously satisfiable nor stronger than the semantics
demands. -/
theorem boxRefuteHere_exact (D : RootData M) (A : PLLFormula) :
    (¬ (addRoot M D).force none A ∧ ∀ u : M.W, D.S u → ¬ M.force u A) ↔
    (∀ u : (addRoot M D).W, (addRoot M D).Rm none u →
      ¬ (addRoot M D).force u A) := by
  constructor
  · rintro ⟨h1, h2⟩ (_ | u) hu hf
    · exact h1 hf
    · exact h2 u hu ((addRoot_force_some D A u).mp hf)
  · intro h
    refine ⟨h none True.intro, fun u hu hf => ?_⟩
    exact h (some u) hu ((addRoot_force_some D A u).mpr hf)

/-! ## Q2 — the empty modal cone is lawful -/

/-- `S = ∅` is a legal choice: the root's only `Rm`-successor is
itself.  `boxRefuteHere`'s second premise is then vacuous, and by Q1
the rule is still exactly the semantic condition — the root refutes
`◯A` iff it refutes `A`. -/
def emptyS (M : ConstraintModel) : RootData M where
  S _ := False
  S_up h _ := absurd h not_false
  At _ := False
  At_hered h := absurd h not_false

theorem emptyS_box_iff (A : PLLFormula) :
    (¬ (addRoot M (emptyS M)).force none (.somehow A)) ↔
    (¬ (addRoot M (emptyS M)).force none A ∨
      ∃ a : M.W, ∀ u : M.W, M.Rm a u → ¬ M.force u A) := by
  classical
  constructor
  · intro h
    by_cases hr : (addRoot M (emptyS M)).force none A
    · refine .inr ?_
      by_contra hc
      push_neg at hc
      refine h ?_
      rintro (_ | v) _
      · exact ⟨none, True.intro, hr⟩
      · obtain ⟨u, hu, hA⟩ := hc v
        exact ⟨some u, hu, (addRoot_force_some _ A u).mpr hA⟩
    · exact .inl hr
  · rintro (hr | ⟨a, ha⟩)
    · exact boxRefuteHere _ hr (fun u hu => absurd hu not_false)
    · exact boxRefuteAbove _ a ha

/-! ## Q3 — reducedness IS preserved -/

/-- A model is reduced when `Ri` is antisymmetric (a partial order,
not a preorder).  Matthew's canonical-form condition; the arity probe
shows it is what makes the ◯-rule unary. -/
def Reduced (C : ConstraintModel) : Prop :=
  ∀ {x y : C.W}, C.Ri x y → C.Ri y x → x = y

theorem addRoot_reduced (D : RootData M) (h : Reduced M) :
    Reduced (addRoot M D) := by
  rintro (_ | a) (_ | b) h1 h2
  · rfl
  · exact absurd h2 not_false
  · exact absurd h1 not_false
  · exact congrArg some (h h1 h2)

/-! ## Q4 — confluence is NOT preserved (the certificate) -/

/-- Two incomparable worlds, all relations the identity.  Mutually
confluent and reduced. -/
def twoM : ConstraintModel where
  W := Bool
  Ri x y := x = y
  Rm x y := x = y
  F _ := False
  V _ _ := False
  refl_i _ := rfl
  trans_i h1 h2 := h1.trans h2
  refl_m _ := rfl
  trans_m h1 h2 := h1.trans h2
  sub_mi h := h
  hered_F _ hx := hx
  hered_V _ hx := hx
  full_F hx := absurd hx not_false

theorem twoM_confluent : MutuallyConfluent twoM := by
  intro x w v h1 h2
  cases h1; cases h2
  exact ⟨x, rfl, rfl⟩

/-- The root's modal cone is `{true}` — upward closed, since `Rm` is
the identity. -/
def twoD : RootData twoM where
  S u := u = true
  S_up := by
    rintro u v hu rfl
    exact hu
  At _ := False
  At_hered h := absurd h not_false

/-- **`addRoot` does NOT preserve mutual confluence.**  `Rm root (some
true)` and `Ri root (some false)` have no common completion: the only
`Ri`-successor of `some true` is itself, and `some false` is not
`Rm`-below it. -/
theorem addRoot_not_confluent :
    ¬ MutuallyConfluent (addRoot twoM twoD) := by
  intro h
  obtain ⟨(_ | u), h1, h2⟩ :=
    @h none (some true) (some false) rfl True.intro
  · exact absurd h1 not_false
  · -- h1 : true = u  (Ri in twoM),  h2 : false = u  (Rm in twoM)
    have e1 : true = u := h1
    have e2 : false = u := h2
    exact Bool.noConfusion (e1.trans e2.symm)

/-! ## Q5 — the rules compose: the repo landmark, by construction -/

/-- One world where every atom holds. -/
def pW : ConstraintModel :=
  solo (fun _ => True) False (fun h => absurd h not_false)

def pD : RootData pW where
  S _ := True
  S_up _ _ := True.intro
  At _ := False
  At_hered h := absurd h not_false

/-- The root forces `◯p` (by `boxHolds`). -/
theorem pRoot_forces_boxP :
    (addRoot pW pD).force none (.somehow (.prop "p")) :=
  boxHolds pD ⟨(), True.intro, True.intro⟩
    (fun a => ⟨a, True.intro, True.intro⟩)

/-- **`◯p ⊬ p` — the repo landmark, derived by construction.** -/
theorem boxp_not_p :
    ¬ Nonempty (LaxND [.somehow (.prop "p")] (.prop "p")) := by
  refine not_laxND_of_root (N := addRoot pW pD) (w := none) ?_ (fun h => h)
  intro χ hχ
  simp only [List.mem_singleton] at hχ
  subst hχ
  exact pRoot_forces_boxP

/-! ## The fix: `boxHolds` was incomplete -/

/-- **The missing ◯-positive case**: the root may witness `◯A`
through ITSELF (`Rm` is reflexive), which `boxHolds` could not
express — it demanded a PROPER `Rm`-successor. -/
theorem boxHoldsRoot (D : RootData M) {A : PLLFormula}
    (hroot : (addRoot M D).force none A)
    (habove : ∀ a : M.W, ∃ u : M.W, M.Rm a u ∧ M.force u A) :
    (addRoot M D).force none (.somehow A) := by
  rintro (_ | v) _
  · exact ⟨none, True.intro, hroot⟩
  · obtain ⟨u, hu, hA⟩ := habove v
    exact ⟨some u, hu, (addRoot_force_some D A u).mpr hA⟩

/-! ## Pins -/

/--
info: 'Reject.boxRefuteHere_exact' does not depend on any axioms
-/
#guard_msgs in
#print axioms boxRefuteHere_exact

/--
info: 'Reject.addRoot_reduced' does not depend on any axioms
-/
#guard_msgs in
#print axioms addRoot_reduced

/--
info: 'Reject.addRoot_not_confluent' does not depend on any axioms
-/
#guard_msgs in
#print axioms addRoot_not_confluent

/--
info: 'Reject.boxp_not_p' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms boxp_not_p

end Reject
