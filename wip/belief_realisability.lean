import LaxLogic.PLLFrames

/-!
# Route B: realisability constraint models for PLL (ladder rungs 1–2, + bite (i))

Implements `docs/route-b-model.md` §§1, 6: a Fairtlough–Mendler constraint frame
with **evidence at each world** from a partial applicative structure, and the two
realisability relations

* `realU` (`⊩ᵘ`, uniform evidence): evidence for `◯φ` is one fixed element,
  carried to the constraint-witness;
* `realS` (`⊩ˢ`, strategy evidence): evidence for `◯φ` is a function which, given
  (the code of) any information-future `v`, returns evidence for `φ` at some
  constraint-witness of `v`.

Proved here (rung 2), for both relations:

* heredity — `w Rᵢ v` and `a ⊩_w φ` imply `a ⊩_v φ` (**belief increases along
  the branching order**; the realiser-level `force_hered`);
* fallible saturation — at `w ∈ F` every element realises every formula
  (the realiser-level `force_of_fallible`).

And the first piece of the separation triptych (`route-b-model.md` §5(a)):

* `bite_uniform_split` — in the split model (`modelOrSplit`) with full evidence,
  the root **truth-forces** `◯(A ∨ B)` yet **no element `⊩ᵘ`-realises it**: a
  uniform realiser is one tagged pair, and its tag would have to decide disjunct
  `A` at world `a` and disjunct `B` at world `b`.  (This uses only the pairing
  structure, so it is stated over the ℕ-pairing instance `natPca`; the argument
  is application-independent.)

No combinatory laws (`k`, `s`) are assumed yet — they enter at soundness
(rung 5), where the validity class is genuine PCAs.
-/

open PLLFormula

namespace PLLND
namespace BeliefReal

/-- A partial applicative structure with total pairing and tag decoding.
Application is partial (`Option`); `untag` is **total** — every element decodes
as a tagged value (as in Kleene's first algebra under Cantor pairing).  No
combinatory laws are required at this stage. -/
structure Pca where
  Carrier : Type
  app : Carrier → Carrier → Option Carrier
  pair : Carrier → Carrier → Carrier
  fst : Carrier → Carrier
  snd : Carrier → Carrier
  tag : Bool → Carrier → Carrier
  untag : Carrier → Bool × Carrier
  fst_pair : ∀ a b, fst (pair a b) = a
  snd_pair : ∀ a b, snd (pair a b) = b
  untag_tag : ∀ i a, untag (tag i a) = (i, a)

/-- Evidence over a constraint frame: for each atom and world, the set of
elements evidencing that atom there — hereditary along `Rᵢ` and full on the
fallible worlds. -/
structure Evidence (P : Pca) (C : ConstraintModel) where
  E : String → C.W → Set P.Carrier
  hered_E : ∀ {s : String} {w v : C.W}, C.Ri w v → E s w ⊆ E s v
  full_E : ∀ {s : String} {w : C.W}, w ∈ C.F → ∀ x : P.Carrier, x ∈ E s w

/-- `⊩ᵘ` — **uniform-evidence** realisability.  Every world-quantified clause
carries the fallibility guard, mirroring `force_of_fallible`.  The `◯`-clause
carries the *same* element to the constraint-witness. -/
def realU (P : Pca) {C : ConstraintModel} (Ev : Evidence P C) :
    PLLFormula → P.Carrier → C.W → Prop
  | .prop s, x, w => w ∈ C.F ∨ x ∈ Ev.E s w
  | .falsePLL, _x, w => w ∈ C.F
  | .and φ ψ, x, w =>
      w ∈ C.F ∨ (realU P Ev φ (P.fst x) w ∧ realU P Ev ψ (P.snd x) w)
  | .or φ ψ, x, w =>
      w ∈ C.F ∨ ((P.untag x).1 = false ∧ realU P Ev φ (P.untag x).2 w)
             ∨ ((P.untag x).1 = true ∧ realU P Ev ψ (P.untag x).2 w)
  | .ifThen φ ψ, x, w =>
      ∀ v, C.Ri w v → v ∈ C.F ∨
        (∀ b, realU P Ev φ b v → ∃ y, P.app x b = some y ∧ realU P Ev ψ y v)
  | .somehow φ, x, w =>
      ∀ v, C.Ri w v → v ∈ C.F ∨ (∃ u, C.Rm v u ∧ realU P Ev φ x u)

/-- `⊩ˢ` — **strategy** realisability, relative to a world-coding
`κ : W → Carrier`.  Evidence for `◯φ` is a function: applied to the code of any
information-future `v`, it returns (under `snd`) evidence for `φ` at some
constraint-witness of `v`.  The strategy needs no foreknowledge of the frame —
the future is its *input*; the side conditions `Rₘ` and realisation are checked
in the semantics, not by the realiser. -/
def realS (P : Pca) {C : ConstraintModel} (Ev : Evidence P C) (κ : C.W → P.Carrier) :
    PLLFormula → P.Carrier → C.W → Prop
  | .prop s, x, w => w ∈ C.F ∨ x ∈ Ev.E s w
  | .falsePLL, _x, w => w ∈ C.F
  | .and φ ψ, x, w =>
      w ∈ C.F ∨ (realS P Ev κ φ (P.fst x) w ∧ realS P Ev κ ψ (P.snd x) w)
  | .or φ ψ, x, w =>
      w ∈ C.F ∨ ((P.untag x).1 = false ∧ realS P Ev κ φ (P.untag x).2 w)
             ∨ ((P.untag x).1 = true ∧ realS P Ev κ ψ (P.untag x).2 w)
  | .ifThen φ ψ, x, w =>
      ∀ v, C.Ri w v → v ∈ C.F ∨
        (∀ b, realS P Ev κ φ b v → ∃ y, P.app x b = some y ∧ realS P Ev κ ψ y v)
  | .somehow φ, x, w =>
      ∀ v, C.Ri w v → v ∈ C.F ∨
        (∃ y, P.app x (κ v) = some y ∧ ∃ u, C.Rm v u ∧ realS P Ev κ φ (P.snd y) u)

/-! ## Rung 2: heredity (increasing belief) and fallible saturation -/

/-- **Heredity for `⊩ᵘ`** — belief increases along the branching order. -/
theorem realU_hered (P : Pca) {C : ConstraintModel} (Ev : Evidence P C)
    (φ : PLLFormula) :
    ∀ {w v : C.W} {x : P.Carrier},
      C.Ri w v → realU P Ev φ x w → realU P Ev φ x v := by
  induction φ with
  | prop s =>
      intro w v x h hx
      simp only [realU] at hx ⊢
      exact hx.elim (fun hF => .inl (C.hered_F h hF)) (fun hE => .inr (Ev.hered_E h hE))
  | falsePLL =>
      intro w v x h hx
      exact C.hered_F h hx
  | and φ ψ ihφ ihψ =>
      intro w v x h hx
      simp only [realU] at hx ⊢
      rcases hx with hF | ⟨h1, h2⟩
      · exact .inl (C.hered_F h hF)
      · exact .inr ⟨ihφ h h1, ihψ h h2⟩
  | or φ ψ ihφ ihψ =>
      intro w v x h hx
      simp only [realU] at hx ⊢
      rcases hx with hF | ⟨ht, h1⟩ | ⟨ht, h1⟩
      · exact .inl (C.hered_F h hF)
      · exact .inr (.inl ⟨ht, ihφ h h1⟩)
      · exact .inr (.inr ⟨ht, ihψ h h1⟩)
  | ifThen φ ψ ihφ ihψ =>
      intro w v x h hx
      simp only [realU] at hx ⊢
      intro v' hv'
      exact hx v' (C.trans_i h hv')
  | somehow φ ih =>
      intro w v x h hx
      simp only [realU] at hx ⊢
      intro v' hv'
      exact hx v' (C.trans_i h hv')

/-- **Heredity for `⊩ˢ`**. -/
theorem realS_hered (P : Pca) {C : ConstraintModel} (Ev : Evidence P C)
    (κ : C.W → P.Carrier) (φ : PLLFormula) :
    ∀ {w v : C.W} {x : P.Carrier},
      C.Ri w v → realS P Ev κ φ x w → realS P Ev κ φ x v := by
  induction φ with
  | prop s =>
      intro w v x h hx
      simp only [realS] at hx ⊢
      exact hx.elim (fun hF => .inl (C.hered_F h hF)) (fun hE => .inr (Ev.hered_E h hE))
  | falsePLL =>
      intro w v x h hx
      exact C.hered_F h hx
  | and φ ψ ihφ ihψ =>
      intro w v x h hx
      simp only [realS] at hx ⊢
      rcases hx with hF | ⟨h1, h2⟩
      · exact .inl (C.hered_F h hF)
      · exact .inr ⟨ihφ h h1, ihψ h h2⟩
  | or φ ψ ihφ ihψ =>
      intro w v x h hx
      simp only [realS] at hx ⊢
      rcases hx with hF | ⟨ht, h1⟩ | ⟨ht, h1⟩
      · exact .inl (C.hered_F h hF)
      · exact .inr (.inl ⟨ht, ihφ h h1⟩)
      · exact .inr (.inr ⟨ht, ihψ h h1⟩)
  | ifThen φ ψ ihφ ihψ =>
      intro w v x h hx
      simp only [realS] at hx ⊢
      intro v' hv'
      exact hx v' (C.trans_i h hv')
  | somehow φ ih =>
      intro w v x h hx
      simp only [realS] at hx ⊢
      intro v' hv'
      exact hx v' (C.trans_i h hv')

/-- **Fallible saturation for `⊩ᵘ`**: at a fallible world every element realises
every formula. -/
theorem realU_of_fallible (P : Pca) {C : ConstraintModel} (Ev : Evidence P C)
    (φ : PLLFormula) :
    ∀ {w : C.W} {x : P.Carrier}, w ∈ C.F → realU P Ev φ x w := by
  induction φ with
  | prop s => intro w x hF; exact .inl hF
  | falsePLL => intro w x hF; exact hF
  | and φ ψ ihφ ihψ => intro w x hF; exact .inl hF
  | or φ ψ ihφ ihψ => intro w x hF; exact .inl hF
  | ifThen φ ψ ihφ ihψ =>
      intro w x hF v hv
      exact .inl (C.hered_F hv hF)
  | somehow φ ih =>
      intro w x hF v hv
      exact .inl (C.hered_F hv hF)

/-- **Fallible saturation for `⊩ˢ`**. -/
theorem realS_of_fallible (P : Pca) {C : ConstraintModel} (Ev : Evidence P C)
    (κ : C.W → P.Carrier) (φ : PLLFormula) :
    ∀ {w : C.W} {x : P.Carrier}, w ∈ C.F → realS P Ev κ φ x w := by
  induction φ with
  | prop s => intro w x hF; exact .inl hF
  | falsePLL => intro w x hF; exact hF
  | and φ ψ ihφ ihψ => intro w x hF; exact .inl hF
  | or φ ψ ihφ ihψ => intro w x hF; exact .inl hF
  | ifThen φ ψ ihφ ihψ =>
      intro w x hF v hv
      exact .inl (C.hered_F hv hF)
  | somehow φ ih =>
      intro w x hF v hv
      exact .inl (C.hered_F hv hF)

/-! ## The ℕ-pairing instance and full evidence -/

/-- The ℕ instance: Cantor pairing, tags in the first component.  Application is
left trivial — the bite theorem below is application-independent. -/
def natPca : Pca where
  Carrier := ℕ
  app _ _ := none
  pair := Nat.pair
  fst n := n.unpair.1
  snd n := n.unpair.2
  tag i a := Nat.pair (cond i 1 0) a
  untag n := (n.unpair.1 == 1, n.unpair.2)
  fst_pair a b := by rw [Nat.unpair_pair]
  snd_pair a b := by rw [Nat.unpair_pair]
  untag_tag i a := by cases i <;> (rw [Nat.unpair_pair]; rfl)

/-- Full evidence over a constraint model: every element evidences every atom
true at a world. -/
def fullEvidence (P : Pca) (C : ConstraintModel) : Evidence P C where
  E s w := {_a | w ∈ C.V s}
  hered_E h _a ha := C.hered_V h ha
  full_E hF _x := C.full_F hF

/-! ## The evidential bite, piece (i) of the separation triptych -/

/-- **The bite** (`route-b-model.md` §5(a)): in the split model the root
truth-forces `◯(A ∨ B)`, but no element `⊩ᵘ`-realises it — the uniform tag would
have to decide disjunct `A` at world `a` and disjunct `B` at world `b`. -/
theorem bite_uniform_split :
    modelOrSplit.force W3.r (somehow ((prop "A").or (prop "B"))) ∧
    ∀ x : ℕ,
      ¬ realU natPca (fullEvidence natPca modelOrSplit)
          (somehow ((prop "A").or (prop "B"))) x W3.r := by
  refine ⟨by decide, ?_⟩
  intro x hx
  simp only [realU] at hx
  have ha := hx W3.a (Or.inr rfl)
  have hb := hx W3.b (Or.inr rfl)
  rcases ha with hFa | ⟨u, hau, hu⟩
  · exact hFa.elim
  rcases hau with rfl | habs
  · -- the witness of world `a` is `a` itself: the tag must be `false`
    rcases hu with hF | ⟨htf, _hA⟩ | ⟨htt, hB⟩
    · exact hF.elim
    · -- tag = false; world `b` now demands tag = true
      rcases hb with hFb | ⟨u', hbu, hu'⟩
      · exact hFb.elim
      rcases hbu with rfl | habs'
      · rcases hu' with hF' | ⟨htf', hA'⟩ | ⟨htt', _hB'⟩
        · exact hF'.elim
        · -- disjunct `A` at world `b`: no evidence for `A` there
          rcases hA' with hF'' | hmem
          · exact hF''.elim
          · have hVA : W3.b ∈ vSplit "A" := hmem
            exact absurd hVA (by decide)
        · -- tags clash: `false = true`
          rw [htf] at htt'
          exact absurd htt' (by decide)
      · exact absurd habs' (by decide)
    · -- disjunct `B` at world `a`: no evidence for `B` there
      rcases hB with hF'' | hmem
      · exact hF''.elim
      · have hVB : W3.a ∈ vSplit "B" := hmem
        exact absurd hVB (by decide)
  · exact absurd habs (by decide)

end BeliefReal
end PLLND

#print axioms PLLND.BeliefReal.realU
#print axioms PLLND.BeliefReal.realS
#print axioms PLLND.BeliefReal.realU_hered
#print axioms PLLND.BeliefReal.realS_hered
#print axioms PLLND.BeliefReal.realU_of_fallible
#print axioms PLLND.BeliefReal.realS_of_fallible
#print axioms PLLND.BeliefReal.natPca
#print axioms PLLND.BeliefReal.fullEvidence
#print axioms PLLND.BeliefReal.bite_uniform_split
