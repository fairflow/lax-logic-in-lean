import LaxLogic.PLLFrames
import LaxLogic.PLLCountermodelEmit
import LaxLogic.PLLEvidence

/-!
# Uniform and strategy realisability: the separations and the obstruction

The `⊩ᵘ`/`⊩ˢ` half of the realisability development (design:
`docs/route-b-model.md`; the completeness-grade `⊩ᵖ` relation and the
decoration theorems live in `LaxLogic/PLLEvidence.lean`).  Source of the
belief paper's §5 and of the extraction results of its §7.

Contents:

* `realU` (`⊩ᵘ`, uniform evidence): evidence for `◯φ` is one fixed element,
  carried to the constraint-witness; `realS` (`⊩ˢ`, strategy evidence):
  evidence for `◯φ` is a function which, given (the code of) any
  information-future `v`, returns evidence for `φ` at some
  constraint-witness of `v`.  For both: heredity along `Rᵢ` and fallible
  saturation (`realU_hered`, `realS_hered`, `realU_of_fallible`,
  `realS_of_fallible`).
* The four separations: the bite `bite_uniform_split` (truth outruns
  uniform evidence at `◯(A ∨ B)`); `uniform_dist_valid` (`⊩ᵘ` validates
  the distribution scheme PLL refutes); `strategy_realises_obAB` /
  `strategy_dist_refuted` (`⊩ˢ` removes the bite and refutes the scheme);
  `impdist_not_uniform` (the `⊃`-barrier).
* The local operator `ob` on hereditary predicates, with its closure laws
  `ob_infl`, `ob_mono`, `ob_idem` and the meet law `ob_strength`.
* The double-negation reading: `force_somehow_iff_notnot` (with `Rₘ = Rᵢ`
  and no fallible worlds, `◯` is forced exactly where `¬¬` is).
* Combinatory completeness for partial applicative structures with `k`/`s`
  (`Poly.abs_spec`), and evidence extraction from natural deduction:
  `extract_sound` (uniform) and `extractS_sound` (strategy).
* **The fullness obstruction** `realS_fullness_obstruction`: on a
  three-world frame no evidence assignment is both atom-adequate and full
  for `⊩ˢ`, for any applicative structure with finite tables against the
  world-coding — the machine-checked reason the `⊃`-clause of `⊩ᵖ` is
  presented the evaluation world.
-/

open PLLFormula

namespace PLLND
namespace BeliefReal

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
information-future `v`, it returns a package naming a constraint-witness `u`
(under `fst`, as `κ u`) together with evidence for `φ` at `u` (under `snd`).
The strategy needs no foreknowledge of the frame — the future is its *input*;
the side conditions (`Rₘ`, and that the named world realises) are checked in
the semantics.  The witness is **named** rather than semantic (`fst y = κ u`)
because strategy-soundness requires it: the `laxElim` composite must apply the
continuation at the witness's code. -/
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
        (∃ y, P.app x (κ v) = some y ∧
          ∃ u, C.Rm v u ∧ P.fst y = κ u ∧ realS P Ev κ φ (P.snd y) u)

/-- `x ⊩ᵘ[Ev, w] φ` — `x` uniformly realises `φ` at world `w` (evidence `Ev`). -/
scoped notation:50 x:51 " ⊩ᵘ[" Ev ", " w "] " φ:51 => realU _ Ev φ x w

/-- `x ⊩ˢ[Ev, κ, w] φ` — `x` strategy-realises `φ` at `w` (coding `κ`). -/
scoped notation:50 x:51 " ⊩ˢ[" Ev ", " κ ", " w "] " φ:51 => realS _ Ev κ φ x w

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
    (h_r : ∃ y, P.app b₀ (κ W3.r) = some y ∧ P.fst y = κ W3.a ∧
      (P.untag (P.snd y)).1 = false)
    (h_a : ∃ y, P.app b₀ (κ W3.a) = some y ∧ P.fst y = κ W3.a ∧
      (P.untag (P.snd y)).1 = false)
    (h_b : ∃ y, P.app b₀ (κ W3.b) = some y ∧ P.fst y = κ W3.b ∧
      (P.untag (P.snd y)).1 = true) :
    realS P (fullEvidence P modelOrSplit) κ
      (somehow ((prop "A").or (prop "B"))) b₀ W3.r := by
  intro v _hv
  refine Or.inr ?_
  cases v with
  | r =>
      obtain ⟨y, hy, hw, ht⟩ := h_r
      exact ⟨y, hy, W3.a, Or.inr rfl, hw,
        Or.inr (Or.inl ⟨ht, Or.inr (show W3.a ∈ vSplit "A" by decide)⟩)⟩
  | a =>
      obtain ⟨y, hy, hw, ht⟩ := h_a
      exact ⟨y, hy, W3.a, Or.inl rfl, hw,
        Or.inr (Or.inl ⟨ht, Or.inr (show W3.a ∈ vSplit "A" by decide)⟩)⟩
  | b =>
      obtain ⟨y, hy, hw, ht⟩ := h_b
      exact ⟨y, hy, W3.b, Or.inl rfl, hw,
        Or.inr (Or.inr ⟨ht, Or.inr (show W3.b ∈ vSplit "B" by decide)⟩)⟩

/-- **Triptych (iii).**  Under `⊩ˢ`, `◯(A∨B) ⊃ (◯A ∨ ◯B)` has no realiser at
the split-model root: whatever the candidate returns must commit one tag at
`r`, and whichever disjunct it commits has no evidence at the opposite maximal
world. -/
theorem strategy_dist_refuted (b₀ : P.Carrier)
    (h_r : ∃ y, P.app b₀ (κ W3.r) = some y ∧ P.fst y = κ W3.a ∧
      (P.untag (P.snd y)).1 = false)
    (h_a : ∃ y, P.app b₀ (κ W3.a) = some y ∧ P.fst y = κ W3.a ∧
      (P.untag (P.snd y)).1 = false)
    (h_b : ∃ y, P.app b₀ (κ W3.b) = some y ∧ P.fst y = κ W3.b ∧
      (P.untag (P.snd y)).1 = true)
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
    · rcases hA W3.b (Or.inr rfl) with hFb | ⟨y', _, u, hmu, _, hu⟩
      · exact hFb.elim
      · rcases hmu with rfl | habs
        · rcases hu with hF' | hmem
          · exact hF'.elim
          · exact absurd (show W3.b ∈ vSplit "A" from hmem) (by decide)
        · exact absurd habs (by decide)
    · rcases hB W3.a (Or.inr rfl) with hFa | ⟨y', _, u, hmu, _, hu⟩
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
  app _ x := some (Nat.pair (if x = 2 then 2 else 1)
    (Nat.pair (if x = 2 then 1 else 0) 0))
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
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair], by simp [splitCode, Nat.unpair_pair]⟩
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair], by simp [splitCode, Nat.unpair_pair]⟩
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair], by simp [splitCode, Nat.unpair_pair]⟩

/-- **Triptych (iii), unconditional instance**: under `⊩ˢ` the split model
refutes `◯(A∨B) ⊃ (◯A ∨ ◯B)` at the root — the truth countermodel survives the
strategy clause. -/
theorem strategy_dist_refuted_split (e : ℕ) :
    ¬ realS splitPca (fullEvidence splitPca modelOrSplit) splitCode
        ((somehow ((prop "A").or (prop "B"))).ifThen
          ((somehow (prop "A")).or (somehow (prop "B")))) e W3.r :=
  strategy_dist_refuted splitPca splitCode 0
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair], by simp [splitCode, Nat.unpair_pair]⟩
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair], by simp [splitCode, Nat.unpair_pair]⟩
    ⟨_, rfl, by simp [splitCode, Nat.unpair_pair], by simp [splitCode, Nat.unpair_pair]⟩ e

/-! ## Rung 5 groundwork: genuine PCAs and combinatory completeness

`PcaKS` is a genuine partial combinatory algebra: `Pca` plus `k`, `s` with the
standard laws (`k·a` defined with `k·a·b = a`; `s·a`, `s·a·b` defined with
`s·a·b·c ≃ a·c·(b·c)`).  `Poly` is the language of polynomials over the algebra
(variables, constants, formal application); `Poly.abs` is bracket abstraction,
and `abs_spec` is **combinatory completeness**: an abstraction always denotes,
and applying it computes substitution.  This is the engine for O3: the realiser
extracted from a `LaxND` derivation will be a closed polynomial. -/

/-- A genuine PCA: `k`, `s` with the standard partial-application laws. -/
structure PcaKS extends Pca where
  k : Carrier
  s : Carrier
  k_app : ∀ a : Carrier, ∃ ka, app k a = some ka ∧ ∀ b, app ka b = some a
  s_app : ∀ a b : Carrier, ∃ sa sab, app s a = some sa ∧ app sa b = some sab ∧
      ∀ c, app sab c =
        (app a c).bind fun ac => (app b c).bind fun bc => app ac bc

section Combinatory

variable (Q : PcaKS)

/-- Polynomials over the algebra (variables are plain ℕ names; well-scopedness
is an invariant of the extraction, not of the syntax). -/
inductive Poly (Q : PcaKS) : Type where
  | var : ℕ → Poly Q
  | const : Q.Carrier → Poly Q
  | app : Poly Q → Poly Q → Poly Q

/-- Evaluation of a polynomial in an environment (partial, via `Option`). -/
def Poly.eval : Poly Q → (ℕ → Q.Carrier) → Option Q.Carrier
  | .var i, ρ => some (ρ i)
  | .const c, _ => some c
  | .app f a, ρ =>
      (Poly.eval f ρ).bind fun f' => (Poly.eval a ρ).bind fun a' => Q.app f' a'

/-- Extend an environment with a value for variable `0`. -/
def extendEnv {α : Type} (a : α) (ρ : ℕ → α) : ℕ → α
  | 0 => a
  | j + 1 => ρ j

/-- Bracket abstraction: `abs t` behaves as `λx₀. t`. -/
def Poly.abs : Poly Q → Poly Q
  | .var 0 => .app (.app (.const Q.s) (.const Q.k)) (.const Q.k)
  | .var (j + 1) => .app (.const Q.k) (.var j)
  | .const c => .app (.const Q.k) (.const c)
  | .app f a => .app (.app (.const Q.s) (Poly.abs f)) (Poly.abs a)

/-- **Combinatory completeness.**  A bracket abstraction always denotes, and
applying it evaluates the body in the extended environment:
`(λx₀. t)·a ≃ t[x₀ := a]`. -/
theorem Poly.abs_spec (t : Poly Q) (ρ : ℕ → Q.Carrier) :
    ∃ g, Poly.eval Q (Poly.abs Q t) ρ = some g ∧
      ∀ a, Q.app g a = Poly.eval Q t (extendEnv a ρ) := by
  induction t with
  | var i =>
      cases i with
      | zero =>
          obtain ⟨sk, skk, h1, h2, h3⟩ := Q.s_app Q.k Q.k
          refine ⟨skk, by simp [Poly.abs, Poly.eval, h1, h2], fun a => ?_⟩
          obtain ⟨ka, hka, hkab⟩ := Q.k_app a
          simp [Poly.eval, extendEnv, h3, hka, hkab]
      | succ j =>
          obtain ⟨ka, hka, hkab⟩ := Q.k_app (ρ j)
          refine ⟨ka, by simp [Poly.abs, Poly.eval, hka], fun a => ?_⟩
          simp [Poly.eval, extendEnv, hkab]
  | const c =>
      obtain ⟨ka, hka, hkab⟩ := Q.k_app c
      exact ⟨ka, by simp [Poly.abs, Poly.eval, hka],
        fun a => by simp [Poly.eval, hkab]⟩
  | app f b ihf ihb =>
      obtain ⟨gf, hf, hfa⟩ := ihf
      obtain ⟨gb, hb, hba⟩ := ihb
      obtain ⟨sa, sab, h1, h2, h3⟩ := Q.s_app gf gb
      refine ⟨sab, by simp [Poly.abs, Poly.eval, hf, hb, h1, h2], fun a => ?_⟩
      rw [h3 a, hfa a, hba a]
      simp [Poly.eval]

end Combinatory

/-! ## Rung 5 (O3): evidence extraction — soundness with an extracted realiser

`extract` maps every `LaxND` derivation to a polynomial; `extract_sound` shows
its value realises the conclusion (uniform clause `⊩ᵘ`) in every realisability
model **without fallible worlds**, under any environment realising the context.
The `F = ∅` scoping is the standard Kleene-style one: at fallible worlds the
`F`-guards make hypothesis-realisers non-strict, so application may diverge;
lifting this needs a strictness discipline and is left OPEN
(`route-b-model.md` §4).

The internal structural combinators (`pairE`, `fstE`, `sndE`, `tagE`, `caseE`)
are the element-level versions of the pairing/tag structure; in `K₁` all are
definable.  Note the lax cases: `laxIntro` extracts to the **identity** and
`laxElim` to a **let** — under uniform evidence the `◯`-monad's computational
shadow is the identity monad, which is precisely the rigidity that the
incompleteness theorem (§5) detects. -/

/-- A PCA with internal pairing, tagging and case analysis (all definable in
`K₁` by combinatory completeness). -/
structure PcaFull extends PcaKS where
  pairE : Carrier
  fstE : Carrier
  sndE : Carrier
  tagE : Bool → Carrier
  caseE : Carrier
  pairE_app : ∀ a : Carrier, ∃ pa, app pairE a = some pa ∧
      ∀ b, app pa b = some (pair a b)
  fstE_app : ∀ a : Carrier, app fstE a = some (fst a)
  sndE_app : ∀ a : Carrier, app sndE a = some (snd a)
  tagE_app : ∀ (i : Bool) (a : Carrier), app (tagE i) a = some (tag i a)
  caseE_app : ∀ x : Carrier, ∃ c₁, app caseE x = some c₁ ∧
      ∀ l, ∃ c₂, app c₁ l = some c₂ ∧
        ∀ r, app c₂ r =
          bif (untag x).1 then app r (untag x).2 else app l (untag x).2

/-- Index of a hypothesis, by decidable search (a membership *proof* is a
`Prop` and cannot compute the index). -/
def memIdx : (Γ : List PLLFormula) → (φ : PLLFormula) → φ ∈ Γ → ℕ
  | [], _, h => absurd h (by simp)
  | a :: Γ', φ, h =>
      if heq : φ = a then 0
      else memIdx Γ' φ ((List.mem_cons.mp h).resolve_left heq) + 1

theorem memIdx_get : ∀ (Γ : List PLLFormula) (φ : PLLFormula) (h : φ ∈ Γ),
    Γ[memIdx Γ φ h]? = some φ := by
  intro Γ
  induction Γ with
  | nil => intro φ h; exact absurd h (by simp)
  | cons a Γ' ih =>
      intro φ h
      by_cases heq : φ = a
      · subst heq; simp [memIdx]
      · simp only [memIdx, dif_neg heq, List.getElem?_cons_succ]
        exact ih φ _

/-- An environment of realisers for a context at a world. -/
def EnvReal (P : Pca) {C : ConstraintModel} (Ev : Evidence P C)
    (Γ : List PLLFormula) (ρ : ℕ → P.Carrier) (w : C.W) : Prop :=
  ∀ i ψ, Γ[i]? = some ψ → realU P Ev ψ (ρ i) w

theorem envReal_hered {P : Pca} {C : ConstraintModel} {Ev : Evidence P C}
    {Γ : List PLLFormula} {ρ : ℕ → P.Carrier} {w v : C.W}
    (h : C.Ri w v) (hρ : EnvReal P Ev Γ ρ w) : EnvReal P Ev Γ ρ v :=
  fun i ψ hi => realU_hered P Ev ψ h (hρ i ψ hi)

theorem envReal_cons {P : Pca} {C : ConstraintModel} {Ev : Evidence P C}
    {Γ : List PLLFormula} {ρ : ℕ → P.Carrier} {w : C.W} {φ : PLLFormula}
    {a : P.Carrier} (hρ : EnvReal P Ev Γ ρ w) (ha : realU P Ev φ a w) :
    EnvReal P Ev (φ :: Γ) (extendEnv a ρ) w := by
  intro i ψ hi
  cases i with
  | zero =>
      simp only [List.getElem?_cons_zero] at hi
      have hψ : φ = ψ := Option.some.inj hi
      subst hψ
      exact ha
  | succ j =>
      simp only [List.getElem?_cons_succ] at hi
      exact hρ j ψ hi

section Extraction

variable (Q : PcaFull)

/-- **The extraction**: from a derivation to a polynomial.  `iden` is a
variable, `impIntro` a bracket abstraction, `laxIntro` the identity,
`laxElim` a `let`. -/
def extract : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxND Γ φ → Poly Q.toPcaKS
  | Γ, _, .iden h => .var (memIdx Γ _ h)
  | _, _, .falsoElim _ p => extract p
  | _, _, .impIntro p => Poly.abs Q.toPcaKS (extract p)
  | _, _, .impElim p₁ p₂ => .app (extract p₁) (extract p₂)
  | _, _, .andIntro p₁ p₂ =>
      .app (.app (.const Q.pairE) (extract p₁)) (extract p₂)
  | _, _, .andElim1 p => .app (.const Q.fstE) (extract p)
  | _, _, .andElim2 p => .app (.const Q.sndE) (extract p)
  | _, _, .orIntro1 p => .app (.const (Q.tagE false)) (extract p)
  | _, _, .orIntro2 p => .app (.const (Q.tagE true)) (extract p)
  | _, _, .orElim p₀ p₁ p₂ =>
      .app (.app (.app (.const Q.caseE) (extract p₀))
        (Poly.abs Q.toPcaKS (extract p₁))) (Poly.abs Q.toPcaKS (extract p₂))
  | _, _, .laxIntro p => extract p
  | _, _, .laxElim p₁ p₂ =>
      .app (Poly.abs Q.toPcaKS (extract p₂)) (extract p₁)

/-- **O3, soundness with evidence extraction** (models without fallible
worlds): the extracted polynomial evaluates, and its value `⊩ᵘ`-realises the
conclusion, under any environment realising the context. -/
theorem extract_sound {C : ConstraintModel} (Ev : Evidence Q.toPca C)
    (hF : ∀ u : C.W, u ∉ C.F) :
    ∀ {Γ : List PLLFormula} {φ : PLLFormula} (p : LaxND Γ φ)
      (w : C.W) (ρ : ℕ → Q.Carrier),
      EnvReal Q.toPca Ev Γ ρ w →
      ∃ g, Poly.eval Q.toPcaKS (extract Q p) ρ = some g ∧
        realU Q.toPca Ev φ g w := by
  intro Γ φ p
  induction p with
  | @iden Γ φ h =>
      intro w ρ hρ
      exact ⟨ρ (memIdx Γ φ h), by simp [extract, Poly.eval],
        hρ _ _ (memIdx_get Γ φ h)⟩
  | @falsoElim Γ φ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      exact (hF w hr).elim
  | @impIntro Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hga⟩ := Poly.abs_spec Q.toPcaKS (extract Q p) ρ
      refine ⟨g, by simpa [extract] using hg, ?_⟩
      simp only [realU]
      intro v hv
      refine Or.inr fun b hb => ?_
      obtain ⟨y, hey, hry⟩ :=
        ih v (extendEnv b ρ) (envReal_cons (envReal_hered hv hρ) hb)
      exact ⟨y, by rw [hga b]; exact hey, hry⟩
  | @impElim Γ φ ψ p₁ p₂ ih₁ ih₂ =>
      intro w ρ hρ
      obtain ⟨g₁, hg₁, hr₁⟩ := ih₁ w ρ hρ
      obtain ⟨g₂, hg₂, hr₂⟩ := ih₂ w ρ hρ
      simp only [realU] at hr₁
      rcases hr₁ w (C.refl_i w) with hF' | himp
      · exact (hF w hF').elim
      · obtain ⟨y, happ, hry⟩ := himp g₂ hr₂
        exact ⟨y, by simp [extract, Poly.eval, hg₁, hg₂, happ], hry⟩
  | @andIntro Γ φ ψ p₁ p₂ ih₁ ih₂ =>
      intro w ρ hρ
      obtain ⟨g₁, hg₁, hr₁⟩ := ih₁ w ρ hρ
      obtain ⟨g₂, hg₂, hr₂⟩ := ih₂ w ρ hρ
      obtain ⟨pa, hpa, hpab⟩ := Q.pairE_app g₁
      refine ⟨Q.pair g₁ g₂,
        by simp [extract, Poly.eval, hg₁, hg₂, hpa, hpab g₂], ?_⟩
      simp only [realU]
      exact Or.inr ⟨by rw [Q.fst_pair]; exact hr₁, by rw [Q.snd_pair]; exact hr₂⟩
  | @andElim1 Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      simp only [realU] at hr
      rcases hr with hF' | ⟨h1, _⟩
      · exact (hF w hF').elim
      · exact ⟨Q.fst g, by simp [extract, Poly.eval, hg, Q.fstE_app], h1⟩
  | @andElim2 Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      simp only [realU] at hr
      rcases hr with hF' | ⟨_, h2⟩
      · exact (hF w hF').elim
      · exact ⟨Q.snd g, by simp [extract, Poly.eval, hg, Q.sndE_app], h2⟩
  | @orIntro1 Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      refine ⟨Q.tag false g,
        by simp [extract, Poly.eval, hg, Q.tagE_app], ?_⟩
      simp only [realU]
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · rw [Q.untag_tag]
      · rw [Q.untag_tag]; exact hr
  | @orIntro2 Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      refine ⟨Q.tag true g,
        by simp [extract, Poly.eval, hg, Q.tagE_app], ?_⟩
      simp only [realU]
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [Q.untag_tag]
      · rw [Q.untag_tag]; exact hr
  | @orElim Γ φ ψ χ p₀ p₁ p₂ ih₀ ih₁ ih₂ =>
      intro w ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih₀ w ρ hρ
      obtain ⟨l, hl, hla⟩ := Poly.abs_spec Q.toPcaKS (extract Q p₁) ρ
      obtain ⟨r, hr', hra⟩ := Poly.abs_spec Q.toPcaKS (extract Q p₂) ρ
      obtain ⟨c₁, hc₁, hc₁l⟩ := Q.caseE_app x
      obtain ⟨c₂, hc₂, hc₂r⟩ := hc₁l l
      simp only [realU] at hrx
      rcases hrx with hF' | ⟨ht, hpay⟩ | ⟨ht, hpay⟩
      · exact (hF w hF').elim
      · -- tag false: left branch
        obtain ⟨y, hey, hry⟩ :=
          ih₁ w (extendEnv (Q.untag x).2 ρ) (envReal_cons hρ hpay)
        refine ⟨y, ?_, hry⟩
        simp [extract, Poly.eval, hx, hl, hr', hc₁, hc₂]
        rw [hc₂r r, ht]
        simpa [hla ((Q.untag x).2)] using hey
      · -- tag true: right branch
        obtain ⟨y, hey, hry⟩ :=
          ih₂ w (extendEnv (Q.untag x).2 ρ) (envReal_cons hρ hpay)
        refine ⟨y, ?_, hry⟩
        simp [extract, Poly.eval, hx, hl, hr', hc₁, hc₂]
        rw [hc₂r r, ht]
        simpa [hra ((Q.untag x).2)] using hey
  | @laxIntro Γ φ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      refine ⟨g, by simpa [extract] using hg, ?_⟩
      simp only [realU]
      intro v hv
      exact Or.inr ⟨v, C.refl_m v, realU_hered Q.toPca Ev φ hv hr⟩
  | @laxElim Γ φ ψ p₁ p₂ ih₁ ih₂ =>
      intro w ρ hρ
      obtain ⟨g₁, hg₁, hr₁⟩ := ih₁ w ρ hρ
      obtain ⟨l, hl, hla⟩ := Poly.abs_spec Q.toPcaKS (extract Q p₂) ρ
      simp only [realU] at hr₁
      rcases hr₁ w (C.refl_i w) with hF' | ⟨u₀, hm₀, hφ₀⟩
      · exact (hF w hF').elim
      · obtain ⟨g, hgeval, _hgOb⟩ :=
          ih₂ u₀ (extendEnv g₁ ρ)
            (envReal_cons (envReal_hered (C.sub_mi hm₀) hρ) hφ₀)
        refine ⟨g, ?_, ?_⟩
        · simp [extract, Poly.eval, hl, hg₁]
          rw [hla g₁]; exact hgeval
        · simp only [realU]
          intro v hv
          rcases hr₁ v hv with hF' | ⟨u, hm, hφ⟩
          · exact Or.inl hF'
          · obtain ⟨y, hyeval, hyOb⟩ :=
              ih₂ u (extendEnv g₁ ρ)
                (envReal_cons (envReal_hered (C.trans_i hv (C.sub_mi hm)) hρ) hφ)
            have hyg : y = g := Option.some.inj (hyeval.symm.trans hgeval)
            subst hyg
            simp only [realU] at hyOb
            rcases hyOb u (C.refl_i u) with hFu | ⟨u₂, hm₂, hψ⟩
            · exact (hF u hFu).elim
            · exact Or.inr ⟨u₂, C.trans_m hm hm₂, hψ⟩

end Extraction

/-- Shift every variable up by one — the de Bruijn `bump`. -/
def Poly.bump {Q : PcaKS} : Poly Q → Poly Q
  | .var i => .var (i + 1)
  | .const c => .const c
  | .app f a => .app (Poly.bump f) (Poly.bump a)

theorem Poly.eval_bump {Q : PcaKS} (t : Poly Q) (a : Q.Carrier) (ρ : ℕ → Q.Carrier) :
    Poly.eval Q (Poly.bump t) (extendEnv a ρ) = Poly.eval Q t ρ := by
  induction t with
  | var i => rfl
  | const c => rfl
  | app f b ihf ihb => simp only [Poly.bump, Poly.eval, ihf, ihb]

/-- Strategy-realiser environment for a context at a world. -/
def EnvRealS (P : Pca) {C : ConstraintModel} (Ev : Evidence P C)
    (κ : C.W → P.Carrier) (Γ : List PLLFormula) (ρ : ℕ → P.Carrier) (w : C.W) : Prop :=
  ∀ i ψ, Γ[i]? = some ψ → realS P Ev κ ψ (ρ i) w

theorem envRealS_hered {P : Pca} {C : ConstraintModel} {Ev : Evidence P C}
    {κ : C.W → P.Carrier} {Γ : List PLLFormula} {ρ : ℕ → P.Carrier} {w v : C.W}
    (h : C.Ri w v) (hρ : EnvRealS P Ev κ Γ ρ w) : EnvRealS P Ev κ Γ ρ v :=
  fun i ψ hi => realS_hered P Ev κ ψ h (hρ i ψ hi)

theorem envRealS_cons {P : Pca} {C : ConstraintModel} {Ev : Evidence P C}
    {κ : C.W → P.Carrier} {Γ : List PLLFormula} {ρ : ℕ → P.Carrier} {w : C.W}
    {φ : PLLFormula} {a : P.Carrier} (hρ : EnvRealS P Ev κ Γ ρ w)
    (ha : realS P Ev κ φ a w) : EnvRealS P Ev κ (φ :: Γ) (extendEnv a ρ) w := by
  intro i ψ hi
  cases i with
  | zero =>
      simp only [List.getElem?_cons_zero] at hi
      obtain rfl := Option.some.inj hi; exact ha
  | succ j => simp only [List.getElem?_cons_succ] at hi; exact hρ j ψ hi

section StrategyExtraction

variable (Q : PcaFull)

/-- **Strategy extraction**: like `extract`, but the two lax rules thread the
future.  `laxIntro` becomes `λc. ⟨c, ·⟩` (name the future as the witness code);
`laxElim` becomes `λc. (⌜run p₂⌝ · snd(s₁·c)) · fst(s₁·c)` — apply `p₁`'s
strategy to the future, run `p₂` with the produced evidence, then apply the
resulting `◯ψ`-strategy at the *named* witness code `fst(s₁·c)`. -/
def extractS : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxND Γ φ → Poly Q.toPcaKS
  | Γ, _, .iden h => .var (memIdx Γ _ h)
  | _, _, .falsoElim _ p => extractS p
  | _, _, .impIntro p => Poly.abs Q.toPcaKS (extractS p)
  | _, _, .impElim p₁ p₂ => .app (extractS p₁) (extractS p₂)
  | _, _, .andIntro p₁ p₂ =>
      .app (.app (.const Q.pairE) (extractS p₁)) (extractS p₂)
  | _, _, .andElim1 p => .app (.const Q.fstE) (extractS p)
  | _, _, .andElim2 p => .app (.const Q.sndE) (extractS p)
  | _, _, .orIntro1 p => .app (.const (Q.tagE false)) (extractS p)
  | _, _, .orIntro2 p => .app (.const (Q.tagE true)) (extractS p)
  | _, _, .orElim p₀ p₁ p₂ =>
      .app (.app (.app (.const Q.caseE) (extractS p₀))
        (Poly.abs Q.toPcaKS (extractS p₁))) (Poly.abs Q.toPcaKS (extractS p₂))
  | _, _, .laxIntro p =>
      Poly.abs Q.toPcaKS
        (.app (.app (.const Q.pairE) (.var 0)) (Poly.bump (extractS p)))
  | _, _, .laxElim p₁ p₂ =>
      Poly.abs Q.toPcaKS
        (.app
          (.app (Poly.bump (Poly.abs Q.toPcaKS (extractS p₂)))
            (.app (.const Q.sndE) (.app (Poly.bump (extractS p₁)) (.var 0))))
          (.app (.const Q.fstE) (.app (Poly.bump (extractS p₁)) (.var 0))))

/-- **O3ˢ, strategy soundness with evidence extraction** (models without
fallible worlds): the extracted polynomial evaluates, and its value
`⊩ˢ`-realises the conclusion, under any environment `⊩ˢ`-realising the context.
The `◯`-cases exhibit belief-evidence as a genuine *constraint-discharge
program*: a function on presented futures returning `(⌜witness⌝, evidence)`. -/
theorem extractS_sound {C : ConstraintModel} (Ev : Evidence Q.toPca C)
    (κ : C.W → Q.Carrier) (hF : ∀ u : C.W, u ∉ C.F) :
    ∀ {Γ : List PLLFormula} {φ : PLLFormula} (p : LaxND Γ φ)
      (w : C.W) (ρ : ℕ → Q.Carrier),
      EnvRealS Q.toPca Ev κ Γ ρ w →
      ∃ g, Poly.eval Q.toPcaKS (extractS Q p) ρ = some g ∧
        realS Q.toPca Ev κ φ g w := by
  intro Γ φ p
  induction p with
  | @iden Γ φ h =>
      intro w ρ hρ
      exact ⟨ρ (memIdx Γ φ h), by simp [extractS, Poly.eval],
        hρ _ _ (memIdx_get Γ φ h)⟩
  | @falsoElim Γ φ p ih =>
      intro w ρ hρ; obtain ⟨g, _, hr⟩ := ih w ρ hρ; exact (hF w hr).elim
  | @impIntro Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hga⟩ := Poly.abs_spec Q.toPcaKS (extractS Q p) ρ
      refine ⟨g, by simpa [extractS] using hg, ?_⟩
      simp only [realS]; intro v hv
      refine Or.inr fun b hb => ?_
      obtain ⟨y, hey, hry⟩ :=
        ih v (extendEnv b ρ) (envRealS_cons (envRealS_hered hv hρ) hb)
      exact ⟨y, by rw [hga b]; exact hey, hry⟩
  | @impElim Γ φ ψ p₁ p₂ ih₁ ih₂ =>
      intro w ρ hρ
      obtain ⟨g₁, hg₁, hr₁⟩ := ih₁ w ρ hρ
      obtain ⟨g₂, hg₂, hr₂⟩ := ih₂ w ρ hρ
      simp only [realS] at hr₁
      rcases hr₁ w (C.refl_i w) with hF' | himp
      · exact (hF w hF').elim
      · obtain ⟨y, happ, hry⟩ := himp g₂ hr₂
        exact ⟨y, by simp [extractS, Poly.eval, hg₁, hg₂, happ], hry⟩
  | @andIntro Γ φ ψ p₁ p₂ ih₁ ih₂ =>
      intro w ρ hρ
      obtain ⟨g₁, hg₁, hr₁⟩ := ih₁ w ρ hρ
      obtain ⟨g₂, hg₂, hr₂⟩ := ih₂ w ρ hρ
      obtain ⟨pa, hpa, hpab⟩ := Q.pairE_app g₁
      refine ⟨Q.pair g₁ g₂,
        by simp [extractS, Poly.eval, hg₁, hg₂, hpa, hpab g₂], ?_⟩
      simp only [realS]
      exact Or.inr ⟨by rw [Q.fst_pair]; exact hr₁, by rw [Q.snd_pair]; exact hr₂⟩
  | @andElim1 Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      simp only [realS] at hr
      rcases hr with hF' | ⟨h1, _⟩
      · exact (hF w hF').elim
      · exact ⟨Q.fst g, by simp [extractS, Poly.eval, hg, Q.fstE_app], h1⟩
  | @andElim2 Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      simp only [realS] at hr
      rcases hr with hF' | ⟨_, h2⟩
      · exact (hF w hF').elim
      · exact ⟨Q.snd g, by simp [extractS, Poly.eval, hg, Q.sndE_app], h2⟩
  | @orIntro1 Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      refine ⟨Q.tag false g, by simp [extractS, Poly.eval, hg, Q.tagE_app], ?_⟩
      simp only [realS]
      exact Or.inr (Or.inl ⟨by rw [Q.untag_tag], by rw [Q.untag_tag]; exact hr⟩)
  | @orIntro2 Γ φ ψ p ih =>
      intro w ρ hρ
      obtain ⟨g, hg, hr⟩ := ih w ρ hρ
      refine ⟨Q.tag true g, by simp [extractS, Poly.eval, hg, Q.tagE_app], ?_⟩
      simp only [realS]
      exact Or.inr (Or.inr ⟨by rw [Q.untag_tag], by rw [Q.untag_tag]; exact hr⟩)
  | @orElim Γ φ ψ χ p₀ p₁ p₂ ih₀ ih₁ ih₂ =>
      intro w ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih₀ w ρ hρ
      obtain ⟨l, hl, hla⟩ := Poly.abs_spec Q.toPcaKS (extractS Q p₁) ρ
      obtain ⟨r, hr', hra⟩ := Poly.abs_spec Q.toPcaKS (extractS Q p₂) ρ
      obtain ⟨c₁, hc₁, hc₁l⟩ := Q.caseE_app x
      obtain ⟨c₂, hc₂, hc₂r⟩ := hc₁l l
      simp only [realS] at hrx
      rcases hrx with hF' | ⟨ht, hpay⟩ | ⟨ht, hpay⟩
      · exact (hF w hF').elim
      · obtain ⟨y, hey, hry⟩ :=
          ih₁ w (extendEnv (Q.untag x).2 ρ) (envRealS_cons hρ hpay)
        refine ⟨y, ?_, hry⟩
        simp only [extractS, Poly.eval, hx, hl, hr', hc₁, hc₂, Option.bind_some]
        rw [hc₂r r, ht]; simpa [hla ((Q.untag x).2)] using hey
      · obtain ⟨y, hey, hry⟩ :=
          ih₂ w (extendEnv (Q.untag x).2 ρ) (envRealS_cons hρ hpay)
        refine ⟨y, ?_, hry⟩
        simp only [extractS, Poly.eval, hx, hl, hr', hc₁, hc₂, Option.bind_some]
        rw [hc₂r r, ht]; simpa [hra ((Q.untag x).2)] using hey
  | @laxIntro Γ φ p ih =>
      intro w ρ hρ
      obtain ⟨gp, hgp, hrp⟩ := ih w ρ hρ
      obtain ⟨g, hg, hga⟩ := Poly.abs_spec Q.toPcaKS
        (.app (.app (.const Q.pairE) (.var 0)) (Poly.bump (extractS Q p))) ρ
      refine ⟨g, by simpa [extractS] using hg, ?_⟩
      simp only [realS]; intro v hv
      obtain ⟨pa, hpa, hpab⟩ := Q.pairE_app (κ v)
      refine Or.inr ⟨Q.pair (κ v) gp, ?_, v, C.refl_m v, ?_, ?_⟩
      · rw [hga (κ v)]
        simp only [Poly.eval, Option.bind_some, extendEnv, Poly.eval_bump, hgp,
          hpa, hpab gp]
      · rw [Q.fst_pair]
      · rw [Q.snd_pair]; exact realS_hered Q.toPca Ev κ φ hv hrp
  | @laxElim Γ φ ψ p₁ p₂ ih₁ ih₂ =>
      intro w ρ hρ
      obtain ⟨s₁, hs₁, hr₁⟩ := ih₁ w ρ hρ
      obtain ⟨rp₂, hrp₂, hrp₂a⟩ := Poly.abs_spec Q.toPcaKS (extractS Q p₂) ρ
      obtain ⟨g, hg, hga⟩ := Poly.abs_spec Q.toPcaKS
        (.app
          (.app (Poly.bump (Poly.abs Q.toPcaKS (extractS Q p₂)))
            (.app (.const Q.sndE) (.app (Poly.bump (extractS Q p₁)) (.var 0))))
          (.app (.const Q.fstE) (.app (Poly.bump (extractS Q p₁)) (.var 0)))) ρ
      refine ⟨g, by simpa [extractS] using hg, ?_⟩
      -- g realises ◯ψ at w: for each future v, run p₁'s strategy then p₂'s.
      simp only [realS]; intro v hv
      -- p₁'s strategy at future v
      simp only [realS] at hr₁
      rcases hr₁ v hv with hF' | ⟨y₁, hy₁, u, hmu, hfu, hφu⟩
      · exact Or.inl hF'
      -- run p₂ at u with the produced φ-evidence (snd y₁)
      have hwu : C.Ri w u := C.trans_i hv (C.sub_mi hmu)
      obtain ⟨g₂, hg₂, hr₂⟩ :=
        ih₂ u (extendEnv (Q.snd y₁) ρ)
          (envRealS_cons (envRealS_hered hwu hρ) hφu)
      -- apply g₂ (a ◯ψ-strategy at u) at the named witness code fst y₁ = κ u
      simp only [realS] at hr₂
      rcases hr₂ u (C.refl_i u) with hFu | ⟨y₂, hy₂, u₂, hmu₂, hfu₂, hψu₂⟩
      · exact (hF u hFu).elim
      refine Or.inr ⟨y₂, ?_, u₂, C.trans_m hmu hmu₂, hfu₂, hψu₂⟩
      -- evaluate: g·(κ v) = (rp₂ · snd y₁) · (fst y₁) = g₂ · (κ u) = y₂
      rw [hga (κ v)]
      have hg₂eq : Q.app rp₂ (Q.snd y₁) = some g₂ := by rw [hrp₂a]; exact hg₂
      rw [← hfu] at hy₂
      simp only [Poly.eval, Option.bind_some, extendEnv, Poly.eval_bump, hs₁, hy₁,
        Q.sndE_app, Q.fstE_app, hrp₂, hg₂eq, hy₂]

end StrategyExtraction

/-! ## The ⊃-barrier blocks fullness for `⊩ˢ` — the obstruction to §6

*Fullness* (every forced formula has a realiser) is one half of the mutual
induction any completeness-by-decoration proof needs (the other half,
*adequacy* — realised implies forced — consumes it at the `⊃` clause).  The
theorem below shows fullness is **unachievable** for `⊩ˢ`: on a three-world
frame there is **no** evidence assignment that is atom-adequate (evidence only
where the atom holds) and full — for *every* PCA that can implement finite
tables against the world-coding `κ`.

The failure is **`◯`-essential**.  For a purely intuitionistic antecedent,
world-tagged atom evidence would let a table-building PCA rescue fullness
(forcing a disjunction at a branch point already commits to a disjunct, by
heredity).  The unrescuable case is an antecedent whose realisers cannot carry
world-marks — and strategies are exactly that: one finite table realises
`◯t` at *both* incomparable futures simultaneously.  Feeding that single
strategy to a would-be realiser of `◯t ⊃ (p ∨ q)` at the root forces one
answer `y` for two futures that demand opposite tags.

Frame: `0 ≤ 1`, `0 ≤ 2`; `Rₘ` reflexive only; `t` at both leaves, `p` only
at `1`, `q` only at `2`.  Then `◯t ⊃ (p ∨ q)` is truth-forced at the root
(vacuously there — `◯t` fails at `0` — and via the local atom at each leaf),
but fullness would hand it a realiser, which the tag-clash refutes.

This is why the §6 completeness construction moves to the *presented* clause
family `⊩ᵖ`, where the `⊃` clause, like the `◯` clause, receives the code of
the evaluation world. -/

section FullnessObstruction

/-- The three-world obstruction frame, as checker data. -/
abbrev obsM : FinCM :=
  { n := 3, ri := [(0, 1), (0, 2)], rm := [], fall := [],
    val := [(1, "p"), (2, "q"), (1, "t"), (2, "t")] }

theorem obsM_wf : obsM.WellFormed := FinCM.wellFormed_of_wellB (by decide)

/-- The obstruction model. -/
abbrev obsC : ConstraintModel := obsM.toModel obsM_wf

/-- No world of the obstruction model is fallible. -/
theorem obsC_no_fallible : ∀ w : obsC.W, w ∉ obsC.F := by
  intro w hw
  have h : FinCM.fallB obsM w.1 = true := hw
  simp [FinCM.fallB, obsM] at h

/-- **Fullness is unachievable for `⊩ˢ`**: no evidence on the obstruction
model is both atom-adequate and full, for any PCA with finite tables against
the coding `κ`. -/
theorem realS_fullness_obstruction (P : Pca) (κ : obsC.W → P.Carrier)
    (htab : ∀ g : obsC.W → P.Carrier, ∃ s, ∀ i, P.app s (κ i) = some (g i)) :
    ¬ ∃ Ev : Evidence P obsC,
      (∀ (a : String) (w : obsC.W), ∀ x ∈ Ev.E a w, w ∈ obsC.V a) ∧
      (∀ (φ : PLLFormula) (w : obsC.W), obsC.force w φ →
        ∃ x, x ⊩ˢ[Ev, κ, w] φ) := by
  rintro ⟨Ev, hA, hF⟩
  -- Fullness at the atom `t` hands over tokens at both leaves.
  obtain ⟨m₁, hm₁⟩ := hF (prop "t") (1 : Fin 3)
    ((obsM.force_iff obsM_wf (prop "t") (1 : Fin 3)).mpr (by decide))
  obtain ⟨m₂, hm₂⟩ := hF (prop "t") (2 : Fin 3)
    ((obsM.force_iff obsM_wf (prop "t") (2 : Fin 3)).mpr (by decide))
  simp only [realS] at hm₁ hm₂
  have hm₁' : m₁ ∈ Ev.E "t" (1 : Fin 3) :=
    hm₁.resolve_left (obsC_no_fallible _)
  have hm₂' : m₂ ∈ Ev.E "t" (2 : Fin 3) :=
    hm₂.resolve_left (obsC_no_fallible _)
  -- Only-reflexive narrowing of the frame relations, decided once.
  have key1 : ∀ n, n < 3 → FinCM.riB obsM 1 n = true → n = 1 := by decide
  have key2 : ∀ n, n < 3 → FinCM.riB obsM 2 n = true → n = 2 := by decide
  -- The single strategy table serving both leaves.
  obtain ⟨s, hs⟩ := htab fun i =>
    if i.1 = 1 then P.pair (κ (1 : Fin 3)) m₁
    else P.pair (κ (2 : Fin 3)) m₂
  have hsval₁ : P.app s (κ (1 : Fin 3)) = some (P.pair (κ (1 : Fin 3)) m₁) := by
    simpa using hs (1 : Fin 3)
  have hsval₂ : P.app s (κ (2 : Fin 3)) = some (P.pair (κ (2 : Fin 3)) m₂) := by
    simpa using hs (2 : Fin 3)
  -- `s` realises `◯t` at leaf 1 …
  have hs₁ : realS P Ev κ (somehow (prop "t")) s (1 : Fin 3) := by
    simp only [realS]
    intro v hv
    right
    have hveq : v = (1 : Fin 3) := Fin.ext (key1 v.1 v.2 hv)
    subst hveq
    refine ⟨P.pair (κ (1 : Fin 3)) m₁, hsval₁,
      (1 : Fin 3), ?_, P.fst_pair .., ?_⟩
    · show FinCM.rmB obsM 1 1 = true
      decide
    · rw [P.snd_pair]
      exact .inr hm₁'
  -- … and at leaf 2.
  have hs₂ : realS P Ev κ (somehow (prop "t")) s (2 : Fin 3) := by
    simp only [realS]
    intro v hv
    right
    have hveq : v = (2 : Fin 3) := Fin.ext (key2 v.1 v.2 hv)
    subst hveq
    refine ⟨P.pair (κ (2 : Fin 3)) m₂, hsval₂,
      (2 : Fin 3), ?_, P.fst_pair .., ?_⟩
    · show FinCM.rmB obsM 2 2 = true
      decide
    · rw [P.snd_pair]
      exact .inr hm₂'
  -- Fullness at the implication, fed the common strategy at both leaves.
  obtain ⟨x, hx⟩ := hF ((somehow (prop "t")).ifThen ((prop "p").or (prop "q")))
    (0 : Fin 3)
    ((obsM.force_iff obsM_wf _ (0 : Fin 3)).mpr (by decide))
  simp only [realS] at hx
  have h1 := (hx (1 : Fin 3)
    (show FinCM.riB obsM 0 1 = true by decide)).resolve_left
    (obsC_no_fallible _)
  have h2 := (hx (2 : Fin 3)
    (show FinCM.riB obsM 0 2 = true by decide)).resolve_left
    (obsC_no_fallible _)
  obtain ⟨y, happ₁, hy₁⟩ := h1 s hs₁
  obtain ⟨y', happ₂, hy₂⟩ := h2 s hs₂
  have hyy : y = y' := by
    rw [happ₁] at happ₂
    exact Option.some.inj happ₂
  subst hyy
  -- The tag clash.
  rcases hy₁.resolve_left (obsC_no_fallible _) with ⟨htag, hmem⟩ | ⟨htag, hmem⟩
  · -- tag `false` at leaf 1; leaf 2 then demands `true` or `p`-evidence at 2.
    rcases hy₂.resolve_left (obsC_no_fallible _) with ⟨_, hmem'⟩ | ⟨htag', _⟩
    · have hp := hA "p" (2 : Fin 3) _
        (hmem'.resolve_left (obsC_no_fallible _))
      have hb : FinCM.valB obsM 2 "p" = true := hp
      exact absurd hb (by decide)
    · rw [htag] at htag'
      exact Bool.false_ne_true htag'
  · -- tag `true` at leaf 1 needs `q`-evidence at 1: refuted by atom-adequacy.
    have hq := hA "q" (1 : Fin 3) _
      (hmem.resolve_left (obsC_no_fallible _))
    have hb : FinCM.valB obsM 1 "q" = true := hq
    exact absurd hb (by decide)

end FullnessObstruction



end BeliefReal
end PLLND

/-! ### Axiom audit — measured on promotion (2026-07-18) and pinned -/

/-- info: 'PLLND.BeliefReal.realU' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.realU

/-- info: 'PLLND.BeliefReal.realS' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.realS

/-- info: 'PLLND.BeliefReal.realU_hered' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.realU_hered

/-- info: 'PLLND.BeliefReal.realS_hered' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.realS_hered

/-- info: 'PLLND.BeliefReal.realU_of_fallible' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.realU_of_fallible

/-- info: 'PLLND.BeliefReal.realS_of_fallible' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.realS_of_fallible

/--
info: 'PLLND.BeliefReal.natPca' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.natPca

/-- info: 'PLLND.BeliefReal.fullEvidence' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.fullEvidence

/--
info: 'PLLND.BeliefReal.bite_uniform_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.bite_uniform_split

/-- info: 'PLLND.BeliefReal.obH' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.obH

/-- info: 'PLLND.BeliefReal.ob_infl' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.ob_infl

/-- info: 'PLLND.BeliefReal.ob_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.ob_mono

/-- info: 'PLLND.BeliefReal.ob_idem' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.ob_idem

/-- info: 'PLLND.BeliefReal.ob_strength' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.ob_strength

/-- info: 'PLLND.BeliefReal.realU_somehow_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.realU_somehow_mem

/--
info: 'PLLND.BeliefReal.force_somehow_iff_notnot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.force_somehow_iff_notnot

/-- info: 'PLLND.BeliefReal.uniform_dist_valid' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.BeliefReal.uniform_dist_valid

/--
info: 'PLLND.BeliefReal.no_realU_obA_at_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.no_realU_obA_at_root

/--
info: 'PLLND.BeliefReal.id_realises_obA_imp_obB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.id_realises_obA_imp_obB

/--
info: 'PLLND.BeliefReal.impdist_not_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.impdist_not_uniform

/--
info: 'PLLND.BeliefReal.strategy_realises_obAB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.strategy_realises_obAB

/--
info: 'PLLND.BeliefReal.strategy_dist_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.strategy_dist_refuted

/--
info: 'PLLND.BeliefReal.strategy_realises_obAB_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.strategy_realises_obAB_split

/--
info: 'PLLND.BeliefReal.strategy_dist_refuted_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.strategy_dist_refuted_split

/-- info: 'PLLND.BeliefReal.Poly.abs_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.BeliefReal.Poly.abs_spec

/-- info: 'PLLND.BeliefReal.extract' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.BeliefReal.extract

/--
info: 'PLLND.BeliefReal.extract_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.extract_sound

/-- info: 'PLLND.BeliefReal.Poly.eval_bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.BeliefReal.Poly.eval_bump

/-- info: 'PLLND.BeliefReal.extractS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.BeliefReal.extractS

/--
info: 'PLLND.BeliefReal.extractS_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.extractS_sound

/--
info: 'PLLND.BeliefReal.realS_fullness_obstruction' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BeliefReal.realS_fullness_obstruction
