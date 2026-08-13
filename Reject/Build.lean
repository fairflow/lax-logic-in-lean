/-
A FORWARD, MODEL-GENERATING REFUTATION CALCULUS FOR PLL — the ◯ rules.

Design taken from Fiorentini–Ferrari: FRJ(G) (TABLEAUX 2017 / TOCL
2020, appendix read at source) and "A forward internal calculus for
model generation in S4" (JLC 31(3), 2021), whose abstract states the
principle we follow — *an internal calculus to check SATISFIABILITY of
a set of formulas, supporting model extraction, whose forward
proof-search is a top-down construction of a model*.

So the rules ARE model constructors and each rule's soundness is a
forcing lemma about the construction.  A derivation is a construction
term; its conclusion is read off the root.  Nothing here is a failed
proof search: a refutation is built, forwards, from smaller
refutations.

**The one constructor.**  `addRoot M D` adds a NEW ROOT below an
existing model.  This is the safe direction (contrast `addTop` in
BiLax/Internal.lean, which was UNSOUND because a fallible top makes
`◯φ` true everywhere): forcing only ever looks upward along `Ri`/`Rm`,
so adding a world strictly below changes nothing above it —
`addRoot_force_some`.

**The ◯ rules.**  Refuting `◯A` at the new root means: some
`Ri`-successor of the root has no `Rm`-successor forcing `A`.  The two
cases mirror FRJ's `⊃∈` / `⊃∉`:

* `boxRefuteHere` (◯∈) — the witness is the root itself: the root
  refutes `A` and so does every world in the root's chosen `Rm`-cone
  `D.S`.  ONE premise per member of the cone; by the arity probe
  (docs/frj-lifting.md §3) that cone has a single maximum on reduced
  confluent frames, so the rule is UNARY there.
* `boxRefuteAbove` (◯∉) — the witness is a world `a` of the premise
  model with no `Rm`-successor forcing `A`.

Both are proved below, and `not_laxND_of_root` turns a root that
forces `Γ` and refutes `ψ` into certified PLL-underivability.
-/
import LaxLogic.PLLKripke

namespace Reject

open PLLND

/-- The data a `addRoot` step chooses: which worlds become the new
root's proper `Rm`-successors, and which atoms hold at the root. -/
structure RootData (M : ConstraintModel) where
  /-- the root's proper `Rm`-successors; `Rm`-upward closed so that
  `Rm` stays transitive -/
  S : M.W → Prop
  S_up : ∀ {u v : M.W}, S u → M.Rm u v → S v
  /-- atoms forced at the root; hereditary, so forced everywhere -/
  At : String → Prop
  At_hered : ∀ {a : String}, At a → ∀ w : M.W, w ∈ M.V a

variable {M : ConstraintModel}

/-- **The constructor**: a new root below `M`. -/
def addRoot (M : ConstraintModel) (D : RootData M) : ConstraintModel where
  W := Option M.W
  Ri x y := match x, y with
    | none, _ => True
    | some _, none => False
    | some a, some b => M.Ri a b
  Rm x y := match x, y with
    | none, none => True
    | none, some u => D.S u
    | some _, none => False
    | some a, some b => M.Rm a b
  F x := match x with
    | none => False
    | some a => a ∈ M.F
  V a x := match x with
    | none => D.At a
    | some b => b ∈ M.V a
  refl_i x := by cases x with
    | none => exact True.intro
    | some a => exact M.refl_i a
  trans_i := by
    rintro (_ | a) (_ | b) (_ | c) h1 h2 <;> first
      | exact True.intro
      | exact absurd h1 not_false
      | exact absurd h2 not_false
      | exact M.trans_i h1 h2
  refl_m x := by cases x with
    | none => exact True.intro
    | some a => exact M.refl_m a
  trans_m := by
    rintro (_ | a) (_ | b) (_ | c) h1 h2
    · exact True.intro
    · exact h2
    · exact True.intro
    · exact D.S_up h1 h2
    · exact absurd h1 not_false
    · exact absurd h1 not_false
    · exact absurd h2 not_false
    · exact M.trans_m h1 h2
  sub_mi := by
    rintro (_ | a) (_ | b) h <;> first
      | exact True.intro
      | exact absurd h not_false
      | exact M.sub_mi h
  hered_F := by
    rintro (_ | a) (_ | b) h hx <;> first
      | exact absurd hx not_false
      | exact absurd h not_false
      | exact M.hered_F h hx
  hered_V := by
    rintro c (_ | a) (_ | b) h hx
    · exact hx
    · exact D.At_hered hx b
    · exact absurd h not_false
    · exact M.hered_V h hx
  full_F := by
    rintro c (_ | a) hx
    · exact absurd hx not_false
    · exact M.full_F hx

/-- **Forcing is unchanged above the new root** — the reason adding a
root is the safe direction. -/
theorem addRoot_force_some (D : RootData M) (φ : PLLFormula) :
    ∀ a : M.W, (addRoot M D).force (some a) φ ↔ M.force a φ := by
  induction φ with
  | prop a => exact fun w => Iff.rfl
  | falsePLL => exact fun w => Iff.rfl
  | and φ ψ ihφ ihψ => exact fun w => and_congr (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ => exact fun w => or_congr (ihφ w) (ihψ w)
  | ifThen φ ψ ihφ ihψ =>
      intro a
      constructor
      · intro h v hv hφ
        exact (ihψ v).mp (h (some v) hv ((ihφ v).mpr hφ))
      · rintro h (_ | v) hv hφ
        · exact absurd hv not_false
        · exact (ihψ v).mpr (h v hv ((ihφ v).mp hφ))
  | somehow φ ih =>
      intro a
      constructor
      · intro h v hv
        obtain ⟨(_ | u), hu, hφ⟩ := h (some v) hv
        · exact absurd hu not_false
        · exact ⟨u, hu, (ih u).mp hφ⟩
      · rintro h (_ | v) hv
        · exact absurd hv not_false
        · obtain ⟨u, hu, hφ⟩ := h v hv
          exact ⟨some u, hu, (ih u).mpr hφ⟩

/-! ## The ◯-refutation rules -/

/-- **`◯∈` — refute `◯A` at the root itself.**  Premises: the root
refutes `A`, and every world in the root's chosen `Rm`-cone refutes
`A`.  (On reduced confluent frames that cone has a single maximum, so
this is a UNARY rule; see docs/frj-lifting.md §3.) -/
theorem boxRefuteHere (D : RootData M) {A : PLLFormula}
    (hroot : ¬ (addRoot M D).force none A)
    (hcone : ∀ u : M.W, D.S u → ¬ M.force u A) :
    ¬ (addRoot M D).force none (.somehow A) := by
  intro h
  obtain ⟨(_ | u), hu, hA⟩ := h none True.intro
  · exact hroot hA
  · exact hcone u hu ((addRoot_force_some D A u).mp hA)

/-- **`◯∉` — refute `◯A` at a world above the root.**  Premise: some
world `a` of the premise model has NO `Rm`-successor forcing `A`. -/
theorem boxRefuteAbove (D : RootData M) {A : PLLFormula} (a : M.W)
    (ha : ∀ u : M.W, M.Rm a u → ¬ M.force u A) :
    ¬ (addRoot M D).force none (.somehow A) := by
  intro h
  obtain ⟨(_ | u), hu, hA⟩ := h (some a) True.intro
  · exact absurd hu not_false
  · exact ha u hu ((addRoot_force_some D A u).mp hA)

/-- **The ◯-POSITIVE rule**, needed to carry `◯A` in the root's
context: the root forces `◯A` when its own `Rm`-cone realises `A` and
every world above does too. -/
theorem boxHolds (D : RootData M) {A : PLLFormula}
    (hroot : ∃ u : M.W, D.S u ∧ M.force u A)
    (habove : ∀ a : M.W, ∃ u : M.W, M.Rm a u ∧ M.force u A) :
    (addRoot M D).force none (.somehow A) := by
  rintro (_ | v) _
  · obtain ⟨u, hSu, hA⟩ := hroot
    exact ⟨some u, hSu, (addRoot_force_some D A u).mpr hA⟩
  · obtain ⟨u, hu, hA⟩ := habove v
    exact ⟨some u, hu, (addRoot_force_some D A u).mpr hA⟩

/-! ## Reading the conclusion off the root -/

/-- **A root that forces `Γ` and refutes `ψ` certifies PLL
underivability.** -/
theorem not_laxND_of_root {N : ConstraintModel} {w : N.W}
    {Γ : List PLLFormula} {ψ : PLLFormula}
    (hΓ : ∀ χ ∈ Γ, N.force w χ) (hψ : ¬ N.force w ψ) :
    ¬ Nonempty (LaxND Γ ψ) := by
  rintro ⟨p⟩
  exact hψ (soundness p N w hΓ)

/-! ## The base constructor: a single world -/

/-- One world, no proper successors: `Ri = Rm = {(w,w)}`. -/
def solo (V₀ : String → Prop) (fal : Prop) (hfull : fal → ∀ a, V₀ a) :
    ConstraintModel where
  W := Unit
  Ri _ _ := True
  Rm _ _ := True
  F _ := fal
  V a _ := V₀ a
  refl_i _ := True.intro
  trans_i _ _ := True.intro
  refl_m _ := True.intro
  trans_m _ _ := True.intro
  sub_mi _ := True.intro
  hered_F _ hx := hx
  hered_V _ hx := hx
  full_F {a} {_} hx := hfull hx a

/-- At a solo world `◯` is the identity: the only `Rm`-successor is
the world itself.  This is the calculus's atomic modal fact. -/
theorem solo_force_somehow (V₀ : String → Prop) (fal : Prop)
    (hfull : fal → ∀ a, V₀ a) (φ : PLLFormula) :
    (solo V₀ fal hfull).force () (.somehow φ) ↔
      (solo V₀ fal hfull).force () φ := by
  constructor
  · intro h
    obtain ⟨u, _, hφ⟩ := h () True.intro
    cases u
    exact hφ
  · intro h _ _
    exact ⟨(), True.intro, h⟩

/-! ## Pins -/

/--
info: 'Reject.addRoot_force_some' does not depend on any axioms
-/
#guard_msgs in
#print axioms addRoot_force_some

/--
info: 'Reject.boxRefuteHere' does not depend on any axioms
-/
#guard_msgs in
#print axioms boxRefuteHere

/--
info: 'Reject.boxRefuteAbove' does not depend on any axioms
-/
#guard_msgs in
#print axioms boxRefuteAbove

/--
info: 'Reject.not_laxND_of_root' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms not_laxND_of_root

end Reject
