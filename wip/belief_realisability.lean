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

/-! ## Rung 3: the belief operator is a stable local nucleus

`ob` is the `∀∃` clause as an operator on `α`-valued semantic propositions
(hereditary along `Rᵢ`, saturated on `F`).  The five laws of `route-b-model.md`
§2 (O2): stability, inflation, idempotence, monotonicity, and the meet law by
**sequential composition** — no confluence anywhere.  `realU_somehow_mem` ties
the operator back to the `⊩ᵘ` clause. -/

/-- A semantic proposition: hereditary and fallible-saturated. -/
structure HProp (α : Type) (C : ConstraintModel) where
  pred : C.W → Set α
  hered : ∀ {w v : C.W}, C.Ri w v → pred w ⊆ pred v
  satF : ∀ {w : C.W}, w ∈ C.F → ∀ x : α, x ∈ pred w

/-- The belief operator on `α`-valued propositions: the `∀∃` clause. -/
def ob (C : ConstraintModel) {α : Type} (Q : C.W → Set α) : C.W → Set α :=
  fun w => {x | ∀ v, C.Ri w v → v ∈ C.F ∨ (∃ u, C.Rm v u ∧ x ∈ Q u)}

/-- **Stability**: `◯` maps semantic propositions to semantic propositions
(heredity by `trans_i`, saturation by `hered_F`). -/
def obH {α : Type} {C : ConstraintModel} (A : HProp α C) : HProp α C where
  pred := ob C A.pred
  hered := fun h _x hx v' hv' => hx v' (C.trans_i h hv')
  satF := fun hF _x _v hv => Or.inl (C.hered_F hv hF)

/-- **Inflation** `P ≤ ◯P` — uses heredity of `P` and `refl_m`. -/
theorem ob_infl {α : Type} {C : ConstraintModel} (A : HProp α C) (w : C.W) :
    A.pred w ⊆ ob C A.pred w :=
  fun _x hx v hv => Or.inr ⟨v, C.refl_m v, A.hered hv hx⟩

/-- **Monotonicity**. -/
theorem ob_mono {α : Type} {C : ConstraintModel} {Q R : C.W → Set α}
    (h : ∀ w, Q w ⊆ R w) (w : C.W) : ob C Q w ⊆ ob C R w :=
  fun _x hx v hv => (hx v hv).imp id (fun ⟨u, hm, hu⟩ => ⟨u, hm, h u hu⟩)

/-- **Idempotence** `◯◯P ≤ ◯P` — `trans_m`, with saturation absorbing a
fallible intermediate witness. -/
theorem ob_idem {α : Type} {C : ConstraintModel} (A : HProp α C) (w : C.W) :
    ob C (ob C A.pred) w ⊆ ob C A.pred w := by
  intro x hx v hv
  rcases hx v hv with hF | ⟨u₁, hm₁, hu₁⟩
  · exact Or.inl hF
  · rcases hu₁ u₁ (C.refl_i u₁) with hF₁ | ⟨u₂, hm₂, hu₂⟩
    · exact Or.inr ⟨u₁, hm₁, A.satF hF₁ x⟩
    · exact Or.inr ⟨u₂, C.trans_m hm₁ hm₂, hu₂⟩

/-- Pairing meet of semantic propositions. -/
def hmeet (P : Pca) {C : ConstraintModel} (A B : HProp P.Carrier C) :
    HProp P.Carrier C where
  pred w := {x | P.fst x ∈ A.pred w ∧ P.snd x ∈ B.pred w}
  hered := fun h _x hx => ⟨A.hered h hx.1, B.hered h hx.2⟩
  satF := fun hF x => ⟨A.satF hF (P.fst x), B.satF hF (P.snd x)⟩

/-- **The meet law, by sequential composition** (`◯P ⊓ ◯Q ≤ ◯(P ⊓ Q)`): the
second constraint is discharged **at the world the first produced** — `sub_mi`,
`trans_m`, heredity; **no confluence**. -/
theorem ob_strength (P : Pca) {C : ConstraintModel} (A B : HProp P.Carrier C)
    (w : C.W) (x : P.Carrier)
    (h1 : P.fst x ∈ ob C A.pred w) (h2 : P.snd x ∈ ob C B.pred w) :
    x ∈ ob C (hmeet P A B).pred w := by
  intro v hv
  rcases h1 v hv with hF | ⟨u₁, hm₁, hP⟩
  · exact Or.inl hF
  · have hwu₁ : C.Ri w u₁ := C.trans_i hv (C.sub_mi hm₁)
    rcases h2 u₁ hwu₁ with hF₁ | ⟨u₂, hm₂, hQ⟩
    · exact Or.inr ⟨u₁, hm₁, ⟨hP, B.satF hF₁ _⟩⟩
    · exact Or.inr ⟨u₂, C.trans_m hm₁ hm₂, ⟨A.hered (C.sub_mi hm₂) hP, hQ⟩⟩

/-- The `⊩ᵘ` clause for `◯φ` *is* membership in `ob` of the realisability
predicate of `φ`: the modality is interpreted by the belief operator. -/
theorem realU_somehow_mem (P : Pca) {C : ConstraintModel} (Ev : Evidence P C)
    (φ : PLLFormula) (x : P.Carrier) (w : C.W) :
    realU P Ev (.somehow φ) x w ↔
      x ∈ ob C (fun u => {y | realU P Ev φ y u}) w :=
  Iff.rfl

/-! ## The double-negation believer (the continuation reading)

Reading PLL as a logic of **inhabitation**, every strong monad interprets the
proof theory — idempotence `◯◯M ⊣⊢ ◯M` is inter-derivability, never a
computational identity.  The propositional shadow of the continuation monad is
`◯M = ¬¬M`, and in the constraint semantics this believer is exactly the model
in which **every information step counts as constraint discharge**: -/

/-- **The double-negation believer.**  In any constraint model with `Rₘ = Rᵢ`
and no fallible worlds, `◯M` is forced exactly where `¬¬M` is: the continuation
reading `◯ = ¬¬` is the `Rₘ = Rᵢ` instance of the constraint semantics. -/
theorem force_somehow_iff_notnot (C : ConstraintModel)
    (hRm : ∀ {w v : C.W}, C.Rm w v ↔ C.Ri w v) (hF : C.F = ∅)
    (M : PLLFormula) (w : C.W) :
    C.force w (somehow M) ↔ C.force w (notPLL (notPLL M)) := by
  constructor
  · intro h v hv hneg
    rcases h v hv with ⟨u, hmu, hu⟩
    have huF : u ∈ C.F := hneg u (hRm.mp hmu) hu
    rw [hF] at huF
    exact huF.elim
  · intro h v hv
    by_contra hcon
    push Not at hcon
    have hnegM : C.force v (notPLL M) := by
      intro u hu hM
      exact absurd hM (hcon u (hRm.mpr hu))
    have hvF : v ∈ C.F := h v hv hnegM
    rw [hF] at hvF
    exact hvF

/-! ## Triptych (ii): the uniform clause validates `◯(φ∨ψ) ⊃ (◯φ ∨ ◯ψ)`

Over any structure with an identity combinator (`skk` in a genuine PCA), the
identity realises `∨`-distribution **at every world of every model**, for
arbitrary `φ, ψ`: a uniform realiser of `◯(φ∨ψ)` is one fixed tagged pair, and
its fixed tag already decides the disjunct at every constraint-witness.  With
`not_provable_somehow_or_dist` (`PLLFrames`) this makes PLL sound but
**incomplete** for `⊩ᵘ`: `PLLᵘ` is a proper extension. -/

/-- **Universal `⊩ᵘ`-realiser for `∨`-distribution.** -/
theorem uniform_dist_valid (P : Pca) {C : ConstraintModel} (Ev : Evidence P C)
    (I : P.Carrier) (hI : ∀ b, P.app I b = some b) (φ ψ : PLLFormula) (w : C.W) :
    realU P Ev ((somehow (φ.or ψ)).ifThen ((somehow φ).or (somehow ψ))) I w := by
  simp only [realU]
  intro v _hv
  refine Or.inr fun b hb => ⟨b, hI b, ?_⟩
  rcases Bool.eq_false_or_eq_true (P.untag b).1 with ht | ht
  · refine Or.inr (Or.inr ⟨ht, fun v' hv' => ?_⟩)
    rcases hb v' hv' with hF | ⟨u, hm, hu⟩
    · exact Or.inl hF
    · rcases hu with hFu | ⟨htt, _⟩ | ⟨_, hc⟩
      · exact Or.inr ⟨u, hm, realU_of_fallible P Ev ψ hFu⟩
      · rw [ht] at htt; exact absurd htt (by decide)
      · exact Or.inr ⟨u, hm, hc⟩
  · refine Or.inr (Or.inl ⟨ht, fun v' hv' => ?_⟩)
    rcases hb v' hv' with hF | ⟨u, hm, hu⟩
    · exact Or.inl hF
    · rcases hu with hFu | ⟨_, hc⟩ | ⟨htt, _⟩
      · exact Or.inr ⟨u, hm, realU_of_fallible P Ev φ hFu⟩
      · exact Or.inr ⟨u, hm, hc⟩
      · rw [ht] at htt; exact absurd htt (by decide)

/-! ## Triptych (iv): the collapse stops at implication

Over the chain countermodel `modelNoImpDist` (`r ≤ a ≤ b`, `Rₘ` reflexive plus
`a Rₘ b`, `A` at `{a,b}`, `B` at `{b}`, `F = ∅`) with full evidence:
`(◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)` has **no** `⊩ᵘ`-realiser at the root, for any structure
with an identity combinator.  So `◯(A⊃B)` does not reduce to `◯A ⊃ ◯B` in
`PLLᵘ` — the "push `◯` to the atoms" normal form fails at `⊃`. -/

section ImpDist

variable (P : Pca)

private abbrev EvChain (P : Pca) : Evidence P modelNoImpDist :=
  fullEvidence P modelNoImpDist

/-- No element evidences `B` at world `a`. -/
theorem no_evidence_B_at_a (y : P.Carrier) :
    ¬ realU P (EvChain P) (prop "B") y W3.a := by
  rintro (hF | hmem)
  · exact hF.elim
  · exact absurd (show W3.a ∈ vChain "B" from hmem) (by decide)

/-- No element realises `A ⊃ B` at the root. -/
theorem no_realU_impAB_at_root (y : P.Carrier) :
    ¬ realU P (EvChain P) ((prop "A").ifThen (prop "B")) y W3.r := by
  intro hy
  rcases hy W3.a (Or.inr (Or.inl rfl)) with hF | himp
  · exact hF.elim
  · obtain ⟨y', _, hy'⟩ :=
      himp y (Or.inr (show W3.a ∈ vChain "A" by decide))
    exact no_evidence_B_at_a P y' hy'

/-- No element realises `◯(A ⊃ B)` at the root: the only `Rₘ`-witness of `r` is
`r` itself. -/
theorem no_realU_obImpAB_at_root (y : P.Carrier) :
    ¬ realU P (EvChain P) (somehow ((prop "A").ifThen (prop "B"))) y W3.r := by
  intro hy
  rcases hy W3.r (Or.inl rfl) with hF | ⟨u, hmu, hu⟩
  · exact hF.elim
  · rcases hmu with rfl | ⟨habs, _⟩
    · exact no_realU_impAB_at_root P y hu
    · exact absurd habs (by decide)

/-- No element realises `◯A` at the root (the only witness is `r`, where `A`
has no evidence). -/
theorem no_realU_obA_at_root (b : P.Carrier) :
    ¬ realU P (EvChain P) (somehow (prop "A")) b W3.r := by
  intro hb
  rcases hb W3.r (Or.inl rfl) with hF | ⟨u, hmu, hu⟩
  · exact hF.elim
  · rcases hmu with rfl | ⟨habs, _⟩
    · rcases hu with hF | hmem
      · exact hF.elim
      · exact absurd (show W3.r ∈ vChain "A" from hmem) (by decide)
    · exact absurd habs (by decide)

/-- Every element realises `◯B` at worlds `a` and `b` (the witness is `b`). -/
theorem realU_obB_above (b' : P.Carrier) (v : W3) (hv : v ≠ W3.r) :
    realU P (EvChain P) (somehow (prop "B")) b' v := by
  intro v' hv'
  refine Or.inr ⟨W3.b, ?_, Or.inr (show W3.b ∈ vChain "B" by decide)⟩
  -- `v' Rₘ b`: from `a` via the step `a Rₘ b`, from `b` by reflexivity
  cases v' with
  | r =>
      -- `v'` is `Rᵢ`-above `v ≠ r`, so `v' = r` is impossible
      cases v with
      | r => exact absurd rfl hv
      | a => rcases hv' with h | h | ⟨_, h⟩ <;> simp_all
      | b => rcases hv' with h | h | ⟨h, _⟩ <;> simp_all
  | a => exact Or.inr ⟨rfl, rfl⟩
  | b => exact Or.inl rfl

/-- The identity realises `◯A ⊃ ◯B` at the root: vacuously at `r` (no realiser
of `◯A` there), and via the `b`-witness above `r`. -/
theorem id_realises_obA_imp_obB (I : P.Carrier) (hI : ∀ b, P.app I b = some b) :
    realU P (EvChain P) ((somehow (prop "A")).ifThen (somehow (prop "B"))) I
      W3.r := by
  intro v _hv
  refine Or.inr fun b' hb' => ⟨b', hI b', ?_⟩
  cases v with
  | r => exact absurd hb' (no_realU_obA_at_root P b')
  | a => exact realU_obB_above P b' W3.a (by decide)
  | b => exact realU_obB_above P b' W3.b (by decide)

/-- **The `⊃`-barrier (triptych (iv)).**  `(◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)` has no
`⊩ᵘ`-realiser at the root of the chain model — for any structure with an
identity combinator (`skk` in a genuine PCA).  With `uniform_dist_valid`, the
`PLLᵘ`-collapse of `◯` goes through `∧` and `∨` but **stops at implication**. -/
theorem impdist_not_uniform (I : P.Carrier) (hI : ∀ b, P.app I b = some b)
    (e : P.Carrier) :
    ¬ realU P (EvChain P)
        (((somehow (prop "A")).ifThen (somehow (prop "B"))).ifThen
          (somehow ((prop "A").ifThen (prop "B")))) e W3.r := by
  intro he
  rcases he W3.r (Or.inl rfl) with hF | himp
  · exact hF.elim
  · obtain ⟨y, _, hy⟩ := himp I (id_realises_obA_imp_obB P I hI)
    exact no_realU_obImpAB_at_root P y hy

end ImpDist

/-! ## Triptych (iii): the strategy clause refutes `∨`-distribution

Under `⊩ˢ` the split-model countermodel **survives**: a case-splitting strategy
realises `◯(A∨B)` at the root (so the refutation is not vacuous — and the bite
of `bite_uniform_split` vanishes), while any realiser of `◯A ∨ ◯B` must commit
its tag at the root and dies on the opposite branch.  This is the first point
in the development where a realiser is a genuine **program** (a case-split on
the presented future) rather than an identity/pairing combinator.  The strategy
element is hypothesised by its two application equations, keeping the theorem
class-robust: in a genuine PCA (`K₁`) such an element exists by combinatory
completeness (a decidable case-split on numeral codes). -/

section StrategyDist

variable (P : Pca) (κ : W3 → P.Carrier)

/-- A case-splitting strategy realises `◯(A∨B)` at the root: futures `r`, `a`
are answered with disjunct `A` (tag `false`), future `b` with disjunct `B`
(tag `true`).  Under `⊩ˢ` the root's belief in the disjunction is evidenced. -/
theorem strategy_realises_obAB (b₀ : P.Carrier)
    (h_r : ∃ y, P.app b₀ (κ W3.r) = some y ∧ (P.untag (P.snd y)).1 = false)
    (h_a : ∃ y, P.app b₀ (κ W3.a) = some y ∧ (P.untag (P.snd y)).1 = false)
    (h_b : ∃ y, P.app b₀ (κ W3.b) = some y ∧ (P.untag (P.snd y)).1 = true) :
    realS P (fullEvidence P modelOrSplit) κ
      (somehow ((prop "A").or (prop "B"))) b₀ W3.r := by
  intro v _hv
  refine Or.inr ?_
  cases v with
  | r =>
      obtain ⟨y, hy, ht⟩ := h_r
      exact ⟨y, hy, W3.a, Or.inr rfl,
        Or.inr (Or.inl ⟨ht, Or.inr (show W3.a ∈ vSplit "A" by decide)⟩)⟩
  | a =>
      obtain ⟨y, hy, ht⟩ := h_a
      exact ⟨y, hy, W3.a, Or.inl rfl,
        Or.inr (Or.inl ⟨ht, Or.inr (show W3.a ∈ vSplit "A" by decide)⟩)⟩
  | b =>
      obtain ⟨y, hy, ht⟩ := h_b
      exact ⟨y, hy, W3.b, Or.inl rfl,
        Or.inr (Or.inr ⟨ht, Or.inr (show W3.b ∈ vSplit "B" by decide)⟩)⟩

/-- **Triptych (iii).**  Under `⊩ˢ`, `◯(A∨B) ⊃ (◯A ∨ ◯B)` has no realiser at
the split-model root: whatever the candidate returns must commit one tag at
`r`, and whichever disjunct it commits has no evidence at the opposite maximal
world. -/
theorem strategy_dist_refuted (b₀ : P.Carrier)
    (h_r : ∃ y, P.app b₀ (κ W3.r) = some y ∧ (P.untag (P.snd y)).1 = false)
    (h_a : ∃ y, P.app b₀ (κ W3.a) = some y ∧ (P.untag (P.snd y)).1 = false)
    (h_b : ∃ y, P.app b₀ (κ W3.b) = some y ∧ (P.untag (P.snd y)).1 = true)
    (e : P.Carrier) :
    ¬ realS P (fullEvidence P modelOrSplit) κ
        ((somehow ((prop "A").or (prop "B"))).ifThen
          ((somehow (prop "A")).or (somehow (prop "B")))) e W3.r := by
  intro he
  rcases he W3.r (Or.inl rfl) with hF | himp
  · exact hF.elim
  · obtain ⟨y, _, hy⟩ := himp b₀ (strategy_realises_obAB P κ b₀ h_r h_a h_b)
    rcases hy with hF | ⟨_, hA⟩ | ⟨_, hB⟩
    · exact hF.elim
    · rcases hA W3.b (Or.inr rfl) with hFb | ⟨y', _, u, hmu, hu⟩
      · exact hFb.elim
      · rcases hmu with rfl | habs
        · rcases hu with hF' | hmem
          · exact hF'.elim
          · exact absurd (show W3.b ∈ vSplit "A" from hmem) (by decide)
        · exact absurd habs (by decide)
    · rcases hB W3.a (Or.inr rfl) with hFa | ⟨y', _, u, hmu, hu⟩
      · exact hFa.elim
      · rcases hmu with rfl | habs
        · rcases hu with hF' | hmem
          · exact hF'.elim
          · exact absurd (show W3.a ∈ vSplit "B" from hmem) (by decide)
        · exact absurd habs (by decide)

end StrategyDist

/-- A concrete instance: carrier `ℕ`, application implementing exactly the
case-split on the world codes `r ↦ 0, a ↦ 1, b ↦ 2`.  (Not a combinatorially
complete PCA — it witnesses that the hypotheses of the theorems above are
satisfiable; in `K₁` they hold by combinatory completeness.) -/
@[reducible] def splitPca : Pca where
  Carrier := ℕ
  app _ x := some (Nat.pair 0 (Nat.pair (if x = 2 then 1 else 0) 0))
  pair := Nat.pair
  fst n := n.unpair.1
  snd n := n.unpair.2
  tag i a := Nat.pair (cond i 1 0) a
  untag n := (n.unpair.1 == 1, n.unpair.2)
  fst_pair a b := by rw [Nat.unpair_pair]
  snd_pair a b := by rw [Nat.unpair_pair]
  untag_tag i a := by cases i <;> (rw [Nat.unpair_pair]; rfl)

/-- World coding for the split model. -/
def splitCode : W3 → ℕ
  | .r => 0
  | .a => 1
  | .b => 2

/-- **The bite vanishes under `⊩ˢ`**: the strategy `0` realises `◯(A∨B)` at the
root of the split model (contrast `bite_uniform_split`). -/
theorem strategy_realises_obAB_split :
    realS splitPca (fullEvidence splitPca modelOrSplit) splitCode
      (somehow ((prop "A").or (prop "B"))) 0 W3.r :=
  strategy_realises_obAB splitPca splitCode 0
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair]⟩
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair]⟩
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair]⟩

/-- **Triptych (iii), unconditional instance**: under `⊩ˢ` the split model
refutes `◯(A∨B) ⊃ (◯A ∨ ◯B)` at the root — the truth countermodel survives the
strategy clause. -/
theorem strategy_dist_refuted_split (e : ℕ) :
    ¬ realS splitPca (fullEvidence splitPca modelOrSplit) splitCode
        ((somehow ((prop "A").or (prop "B"))).ifThen
          ((somehow (prop "A")).or (somehow (prop "B")))) e W3.r :=
  strategy_dist_refuted splitPca splitCode 0
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair]⟩
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair]⟩
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair]⟩ e

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
#print axioms PLLND.BeliefReal.obH
#print axioms PLLND.BeliefReal.ob_infl
#print axioms PLLND.BeliefReal.ob_mono
#print axioms PLLND.BeliefReal.ob_idem
#print axioms PLLND.BeliefReal.ob_strength
#print axioms PLLND.BeliefReal.realU_somehow_mem
#print axioms PLLND.BeliefReal.force_somehow_iff_notnot
#print axioms PLLND.BeliefReal.uniform_dist_valid
#print axioms PLLND.BeliefReal.no_realU_obA_at_root
#print axioms PLLND.BeliefReal.id_realises_obA_imp_obB
#print axioms PLLND.BeliefReal.impdist_not_uniform
#print axioms PLLND.BeliefReal.strategy_realises_obAB
#print axioms PLLND.BeliefReal.strategy_dist_refuted
#print axioms PLLND.BeliefReal.strategy_realises_obAB_split
#print axioms PLLND.BeliefReal.strategy_dist_refuted_split
