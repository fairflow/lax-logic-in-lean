/-
# `LaxLogic.QLL.PaperSemantics` — the CLP paper's own models, and Theorem 3.6

Stage 0 of `docs/qll-clp-implementation-plan.md`.  The paper is the 10 September
1997 draft of Fairtlough, Mendler and Walton.  Its Definition 3.2 gives a
*Kripke constraint model* with **one** modal relation, and its Definition 3.3
reads the modality as

    α ⊨ ◯M   iff   for all β with α Ri β there is γ with β Rm γ and γ ⊨ M

which is the `◯∃` clause of `Kripke.lean` exactly.  Its `∀`, `∃` and `⊃`
clauses are ours too, over frames with `Rm ⊆ Ri`, increasing domains and
`Ri`-closed fallible worlds.  So the paper's logic is this development's logic
at `q = .ex`, and the point of this file is to say that in a form the kernel
checks rather than in prose: `CModel` and `CModel.force` are written out
independently, and `CModel.force_iff` proves the agreement.

**One departure from the printed Definition 3.3, and it is the draft's slip
rather than a choice.**  The printed atomic clause is

    α ⊨ P(t₁,…,tₙ)  iff  (σ(t₁),…,σ(tₙ)) ∈ Iα(Pₙ)

with no disjunct for fallibility, which would leave a fallible world failing to
satisfy an atom even though it satisfies `false`.  The paper's own translation
into `[S4,S4]` has `P° = □i P ∨ □i f`, so the disjunct is intended; `force`
carries it, and `CModel.force` below carries it too.

**What this buys.**  Their Theorem 3.6 is proved in the paper by Gödel
translation into a classical bimodal theory, with the details referred to
`[FW97]`, which we do not have.  Here it is `thm_3_6`, obtained from
`Prv.sound` and `completeness1` — the canonical model of `Complete1.lean` read
as one of the paper's models, which it is once `Rm` is taken to be `RE`.
-/
import LaxLogic.QLL.Complete1

namespace LaxLogic.QLL

/-! ## The fragment the paper speaks about

One modality, ours being two.  `OnlyEx` picks out the formulas on which the
two developments have the same subject matter. -/

/-- Every modality in the formula is `◯∃`, the paper's `◯`. -/
def Form.OnlyEx : Form → Prop
  | .top | .bot | .pred _ _ => True
  | .and A B | .or A B | .imp A B => A.OnlyEx ∧ B.OnlyEx
  | .circ q A => q = .ex ∧ A.OnlyEx
  | .forall_ A | .exists_ A => A.OnlyEx

/-! ## Definition 3.2 -/

/-- A Kripke constraint model: `⟨W, Ri, Rm, I, F⟩` with `Rm ⊆ Ri`, domains
increasing along `Ri`, and `F` closed under `Ri`.  Conditions (ii) and (iii) of
the paper — that constants agree and function interpretations grow along `Ri` —
are met here by taking the interpretation of the function symbols to be the same
at every state, which is their strictest instance. -/
structure CModel where
  /-- `W`. -/
  S : Type
  /-- The individuals. -/
  D : Type
  /-- `|α|`, the universe at `α`. -/
  Dom : S → D → Prop
  /-- The intuitionistic pre-order. -/
  Ri : S → S → Prop
  /-- The modal pre-order. -/
  Rm : S → S → Prop
  /-- `F`, the fallible worlds. -/
  F : S → Prop
  /-- `Iα` on function symbols. -/
  fn : String → List D → D
  /-- `Iα` on predicate symbols. -/
  I : S → String → List D → Prop
  refl_i : ∀ s, Ri s s
  trans_i : ∀ {s v u}, Ri s v → Ri v u → Ri s u
  refl_m : ∀ s, Rm s s
  trans_m : ∀ {s v u}, Rm s v → Rm v u → Rm s u
  /-- `Rm ⊆ Ri`. -/
  m_sub_i : ∀ {s v}, Rm s v → Ri s v
  /-- `α Ri β` and `α ∈ F` implies `β ∈ F`. -/
  hered_F : ∀ {s v}, Ri s v → F s → F v
  /-- Condition (i): `α Ri β → |α| ⊆ |β|`. -/
  dom_mono : ∀ {s v d}, Ri s v → Dom s d → Dom v d
  /-- Condition (iv): `Iα(Pₙ) ⊆ Iβ(Pₙ)`. -/
  hered_I : ∀ {s v P ds}, Ri s v → I s P ds → I v P ds
  /-- Universes are closed under the function symbols. -/
  fn_dom : ∀ {s : S} {f : String} {ds : List D}, (∀ d ∈ ds, Dom s d) → Dom s (fn f ds)
  /-- Universes are non-empty, uniformly. -/
  d₀ : D
  dom_d₀ : ∀ s, Dom s d₀

/-- A constraint model is a `KModel` whose two modal relations coincide. -/
def CModel.toKModel (C : CModel) : KModel where
  S := C.S
  D := C.D
  Dom := C.Dom
  Ri := C.Ri
  RA := C.Rm
  RE := C.Rm
  Fl := C.F
  refl_i := C.refl_i
  trans_i := C.trans_i
  refl_A := C.refl_m
  trans_A := C.trans_m
  sub_A := C.m_sub_i
  refl_E := C.refl_m
  trans_E := C.trans_m
  sub_E := C.m_sub_i
  dom_mono := C.dom_mono
  d₀ := C.d₀
  dom_d₀ := C.dom_d₀
  hered_Fl := C.hered_F
  fn := C.fn
  I := C.I
  hered_I := C.hered_I
  fn_dom := C.fn_dom

/-! ## Definition 3.3

Written out as the paper writes it, with the one repair noted in the header.
Term evaluation is not in dispute and is taken from `Kripke.lean`. -/

/-- `C, α ⊨σ M`. -/
def CModel.force (C : CModel) : Form → C.S → (String → C.D) → List C.D → Prop
  | .top,       _, _, _ => True
  | .bot,       s, _, _ => C.F s
  | .pred P ts, s, ρ, β => C.F s ∨ C.I s P (C.toKModel.evTms ρ β ts)
  | .and A B,   s, ρ, β => C.force A s ρ β ∧ C.force B s ρ β
  | .or A B,    s, ρ, β => C.force A s ρ β ∨ C.force B s ρ β
  | .imp A B,   s, ρ, β => ∀ v, C.Ri s v → C.force A v ρ β → C.force B v ρ β
  | .circ _ A,  s, ρ, β => ∀ v, C.Ri s v → ∃ u, C.Rm v u ∧ C.force A u ρ β
  | .forall_ A, s, ρ, β => ∀ v, C.Ri s v → ∀ d, C.Dom v d → C.force A v ρ (d :: β)
  | .exists_ A, s, ρ, β => ∃ d, C.Dom s d ∧ C.force A s ρ (d :: β)

/-- **The agreement.**  On the fragment the paper speaks about, its Definition
3.3 and our `force` are the same relation. -/
theorem CModel.force_iff (C : CModel) : ∀ (A : Form), A.OnlyEx →
    ∀ (s : C.S) (ρ : String → C.D) (β : List C.D),
      (C.force A s ρ β ↔ C.toKModel.force A s ρ β) := by
  intro A
  induction A with
  | top | bot | pred _ _ => intro _ _ _ _; exact Iff.rfl
  | and _ _ ih₁ ih₂ =>
      intro h s ρ β; exact and_congr (ih₁ h.1 s ρ β) (ih₂ h.2 s ρ β)
  | or _ _ ih₁ ih₂ =>
      intro h s ρ β; exact or_congr (ih₁ h.1 s ρ β) (ih₂ h.2 s ρ β)
  | imp _ _ ih₁ ih₂ =>
      intro h s ρ β
      exact forall_congr' fun v => imp_congr Iff.rfl
        (imp_congr (ih₁ h.1 v ρ β) (ih₂ h.2 v ρ β))
  | circ q _ ih =>
      intro h s ρ β
      rcases h.1 with rfl
      exact forall_congr' fun v => imp_congr Iff.rfl
        (exists_congr fun u => and_congr Iff.rfl (ih h.2 u ρ β))
  | forall_ _ ih =>
      intro h s ρ β
      exact forall_congr' fun v => imp_congr Iff.rfl
        (forall_congr' fun d => imp_congr Iff.rfl (ih h v ρ (d :: β)))
  | exists_ _ ih =>
      intro h s ρ β
      exact exists_congr fun d => and_congr Iff.rfl (ih h s ρ (d :: β))

/-! ## The canonical model, read as one of the paper's

`Complete1.canon` has two modal relations.  Forgetting the `◯∀` one leaves a
model of Definition 3.2, and on `OnlyEx` formulas it forces exactly what the
canonical model forces — the `◯∀` clause being the only place `RA` is read. -/

/-- The canonical model with `Rm := RE`. -/
def canonC : CModel where
  S := canon.S
  D := canon.D
  Dom := canon.Dom
  Ri := canon.Ri
  Rm := canon.RE
  F := canon.Fl
  fn := canon.fn
  I := canon.I
  refl_i := canon.refl_i
  trans_i := canon.trans_i
  refl_m := canon.refl_E
  trans_m := canon.trans_E
  m_sub_i := canon.sub_E
  hered_F := canon.hered_Fl
  dom_mono := canon.dom_mono
  hered_I := canon.hered_I
  fn_dom := canon.fn_dom
  d₀ := canon.d₀
  dom_d₀ := canon.dom_d₀

/-! Term evaluation reads only the function symbols and `d₀`, on which the two
models agree; but they are different terms, so it needs saying. -/

mutual
theorem canonC_evTm : ∀ (t : Tm) (ρ : String → canon.D) (β : List canon.D),
    canonC.toKModel.evTm ρ β t = canon.evTm ρ β t
  | .bvar _,  _, _ => rfl
  | .fvar _,  _, _ => rfl
  | .fn f ts, ρ, β => by
      show canon.fn f (canonC.toKModel.evTms ρ β ts) = canon.fn f (canon.evTms ρ β ts)
      rw [canonC_evTms ts ρ β]
theorem canonC_evTms : ∀ (ts : List Tm) (ρ : String → canon.D) (β : List canon.D),
    canonC.toKModel.evTms ρ β ts = canon.evTms ρ β ts
  | [],      _, _ => rfl
  | t :: ts, ρ, β => by
      show canonC.toKModel.evTm ρ β t :: canonC.toKModel.evTms ρ β ts
        = canon.evTm ρ β t :: canon.evTms ρ β ts
      rw [canonC_evTm t ρ β, canonC_evTms ts ρ β]
      rfl
end

theorem canonC_force_iff : ∀ (A : Form), A.OnlyEx →
    ∀ (s : canonC.S) (ρ : String → canonC.D) (β : List canonC.D),
      (canonC.force A s ρ β ↔ canon.force A s ρ β) := by
  intro A
  induction A with
  | top | bot => intro _ _ _ _; exact Iff.rfl
  | pred P ts =>
      intro _ s ρ β
      show (canon.Fl s ∨ canon.I s P (canonC.toKModel.evTms ρ β ts)) ↔
           (canon.Fl s ∨ canon.I s P (canon.evTms ρ β ts))
      rw [canonC_evTms ts ρ β]
  | and _ _ ih₁ ih₂ =>
      intro h s ρ β; exact and_congr (ih₁ h.1 s ρ β) (ih₂ h.2 s ρ β)
  | or _ _ ih₁ ih₂ =>
      intro h s ρ β; exact or_congr (ih₁ h.1 s ρ β) (ih₂ h.2 s ρ β)
  | imp _ _ ih₁ ih₂ =>
      intro h s ρ β
      exact forall_congr' fun v => imp_congr Iff.rfl
        (imp_congr (ih₁ h.1 v ρ β) (ih₂ h.2 v ρ β))
  | circ q _ ih =>
      intro h s ρ β
      rcases h.1 with rfl
      exact forall_congr' fun v => imp_congr Iff.rfl
        (exists_congr fun u => and_congr Iff.rfl (ih h.2 u ρ β))
  | forall_ _ ih =>
      intro h s ρ β
      exact forall_congr' fun v => imp_congr Iff.rfl
        (forall_congr' fun d => imp_congr Iff.rfl (ih h v ρ (d :: β)))
  | exists_ _ ih =>
      intro h s ρ β
      exact exists_congr fun d => and_congr Iff.rfl (ih h s ρ (d :: β))

/-! ## Theorem 3.6 -/

/-- Consequence over the paper's models. -/
def CConsequence (Γ : List Form) (A : Form) : Prop :=
  ∀ (C : CModel) (s : C.S) (ρ : String → C.D),
    (∀ x ∈ ctxFv Γ ++ A.fv, C.Dom s (ρ x)) →
    (∀ B ∈ Γ, C.force B s ρ []) → C.force A s ρ []

/-- **Theorem 3.6**, over the paper's own Definition 3.2 and 3.3, for the
natural deduction system of its Figure 2. -/
theorem thm_3_6 {Γ : List Form} {A : Form}
    (hΓlc : ∀ B ∈ Γ, Form.lc B) (hAlc : Form.lc A)
    (hΓex : ∀ B ∈ Γ, B.OnlyEx) (hAex : A.OnlyEx) :
    Γ ⊢ A ↔ CConsequence Γ A := by
  constructor
  · intro hd C s ρ hass hΓ
    refine (C.force_iff A hAex s ρ []).mpr ?_
    refine Prv.sound hd C.toKModel s ρ hass (fun B hB => ?_)
    exact (C.force_iff B (hΓex B hB) s ρ []).mp (hΓ B hB)
  · intro h
    by_contra hn
    obtain ⟨w, hass, hΓf, hAf⟩ := exists_countermodel hΓlc hAlc hn
    refine hAf ((canonC_force_iff A hAex w canonρ []).mp ?_)
    refine h canonC w canonρ hass (fun B hB => ?_)
    exact (canonC_force_iff B (hΓex B hB) w canonρ []).mpr (hΓf B hB)

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.CModel.force_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms CModel.force_iff

/-- info: 'LaxLogic.QLL.thm_3_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms thm_3_6

end LaxLogic.QLL
