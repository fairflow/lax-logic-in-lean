import LaxLogic.PLL.SubTab.Semantics
import LeanCertify

/-!
# The subframe tableau as a certified decider: certificates and soundness

2026-10-15.  Statements approved by Matthew before the proofs (lean-certify
R10).

* **Yes side.**  A closed tableau `TCert`, checked by the structural
  `check`; `check_sound`: no world of a finite decidable subframe model
  refutes a sequent with a closed tableau; `yes` packages it as a
  `Certify.Certifier` for `Holds φ := Nonempty ([] ⊢ φ)`, through
  `completeness`.
* **No side.**  A finite subframe countermodel `SubCM` as tables, no
  fallible world; `refutes_sound` through `soundness`; `no` packages it.
-/

open PLLFormula

namespace PLLND
namespace SubTab

open SubframeModel.CF

/-- The property decided. -/
def Holds (φ : PLLFormula) : Prop := Nonempty ([] ⊢ φ)

/-- A signed sequent at one world: `ant` true there, `suc` false there;
`isS` records that the world is an S-point. -/
structure SSeq where
  isS : Bool
  ant : List PLLFormula
  suc : List PLLFormula

/-- A world of a subframe model refutes the sequent. -/
def Refutes (M : SubframeModel) (x : M.W) (s : SSeq) : Prop :=
  (s.isS = true → x ∈ M.S) ∧ (∀ γ ∈ s.ant, M.force x γ) ∧ (∀ δ ∈ s.suc, ¬ M.force x δ)

/-- A closed tableau, as data: one constructor per rule, formulas named by
value. -/
inductive TCert where
  | bot
  | ax (A : PLLFormula)
  | andL (A B : PLLFormula) (c : TCert)
  | orL (A B : PLLFormula) (c₁ c₂ : TCert)
  | impL (A B : PLLFormula) (c₁ c₂ : TCert)
  | boxL (A : PLLFormula) (c : TCert)
  | andR (A B : PLLFormula) (c₁ c₂ : TCert)
  | orR (A B : PLLFormula) (c : TCert)
  | impLoc (A B : PLLFormula) (c : TCert)
  | boxLoc (A : PLLFormula) (c : TCert)
  | impR (A B : PLLFormula) (c : TCert)
  | boxR (A : PLLFormula) (c : TCert)
  deriving Repr, Inhabited

/-- Membership, as a Boolean. -/
def mem (A : PLLFormula) (l : List PLLFormula) : Bool := decide (A ∈ l)

/-- The checker, structural in the certificate. -/
def check : SSeq → TCert → Bool
  | s, .bot => mem .falsePLL s.ant
  | s, .ax A => mem A s.ant && mem A s.suc
  | s, .andL A B c => mem (.and A B) s.ant && check ⟨s.isS, s.ant ++ [A, B], s.suc⟩ c
  | s, .orL A B c₁ c₂ => mem (.or A B) s.ant &&
      check ⟨s.isS, s.ant ++ [A], s.suc⟩ c₁ && check ⟨s.isS, s.ant ++ [B], s.suc⟩ c₂
  | s, .impL A B c₁ c₂ => mem (.ifThen A B) s.ant &&
      check ⟨s.isS, s.ant, s.suc ++ [A]⟩ c₁ && check ⟨s.isS, s.ant ++ [B], s.suc⟩ c₂
  | s, .boxL A c => s.isS && mem (.somehow A) s.ant && check ⟨s.isS, s.ant ++ [A], s.suc⟩ c
  | s, .andR A B c₁ c₂ => mem (.and A B) s.suc &&
      check ⟨s.isS, s.ant, s.suc ++ [A]⟩ c₁ && check ⟨s.isS, s.ant, s.suc ++ [B]⟩ c₂
  | s, .orR A B c => mem (.or A B) s.suc && check ⟨s.isS, s.ant, s.suc ++ [A, B]⟩ c
  | s, .impLoc A B c => mem (.ifThen A B) s.suc && mem A s.ant &&
      check ⟨s.isS, s.ant, s.suc ++ [B]⟩ c
  | s, .boxLoc A c => s.isS && mem (.somehow A) s.suc && check ⟨s.isS, s.ant, s.suc ++ [A]⟩ c
  | s, .impR A B c => mem (.ifThen A B) s.suc && check ⟨false, s.ant ++ [A], [B]⟩ c
  | s, .boxR A c => mem (.somehow A) s.suc && check ⟨true, s.ant, [A]⟩ c

section
variable {P : PLLFormula → Prop}

theorem all_app {l : List PLLFormula} (h : ∀ a ∈ l, P a) {as : List PLLFormula}
    (h' : ∀ a ∈ as, P a) : ∀ a ∈ l ++ as, P a := fun a ha =>
  (List.mem_append.mp ha).elim (h a) (h' a)

theorem all_one {A : PLLFormula} (h : P A) : ∀ a ∈ [A], P a := fun a ha => by
  rw [List.mem_singleton.mp ha]; exact h

theorem all_two {A B : PLLFormula} (hA : P A) (hB : P B) : ∀ a ∈ [A, B], P a := fun a ha => by
  rcases List.mem_cons.mp ha with e | ha
  · rw [e]; exact hA
  · rw [List.mem_singleton.mp ha]; exact hB
end

theorem mem_of {A : PLLFormula} {l : List PLLFormula} (h : mem A l = true) : A ∈ l :=
  of_decide_eq_true h

/-- **Soundness of closed tableaux.**  No world of a finite decidable
subframe model refutes a sequent that has a closed tableau. -/
theorem check_sound (c : TCert) : ∀ (s : SSeq), check s c = true →
    ∀ (M : SubframeModel) [FinDec M] (x : M.W), ¬ Refutes M x s := by
  induction c with
  | bot =>
    intro s h M _ x hr
    exact hr.2.1 _ (mem_of h)
  | ax A =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    exact hr.2.2 _ (mem_of h.2) (hr.2.1 _ (mem_of h.1))
  | andL A B c ih =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    have hAB := hr.2.1 _ (mem_of h.1)
    exact ih _ h.2 M x ⟨hr.1, all_app hr.2.1 (all_two hAB.1 hAB.2), hr.2.2⟩
  | orL A B c₁ c₂ ih₁ ih₂ =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    rcases hr.2.1 _ (mem_of h.1.1) with hA | hB
    · exact ih₁ _ h.1.2 M x ⟨hr.1, all_app hr.2.1 (all_one hA), hr.2.2⟩
    · exact ih₂ _ h.2 M x ⟨hr.1, all_app hr.2.1 (all_one hB), hr.2.2⟩
  | impL A B c₁ c₂ ih₁ ih₂ =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    have himp := hr.2.1 _ (mem_of h.1.1)
    rcases Decidable.em (M.force x A) with hA | hA
    · exact ih₂ _ h.2 M x
        ⟨hr.1, all_app hr.2.1 (all_one (himp x (M.refl x) hA)), hr.2.2⟩
    · exact ih₁ _ h.1.2 M x ⟨hr.1, hr.2.1, all_app hr.2.2 (all_one hA)⟩
  | boxL A c ih =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    have hbox := hr.2.1 _ (mem_of h.1.2)
    exact ih _ h.2 M x
      ⟨hr.1, all_app hr.2.1 (all_one (hbox x (M.refl x) (hr.1 h.1.1))), hr.2.2⟩
  | andR A B c₁ c₂ ih₁ ih₂ =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    have hn := hr.2.2 _ (mem_of h.1.1)
    rcases Decidable.em (M.force x A) with hA | hA
    · exact ih₂ _ h.2 M x
        ⟨hr.1, hr.2.1, all_app hr.2.2 (all_one fun hB => hn ⟨hA, hB⟩)⟩
    · exact ih₁ _ h.1.2 M x ⟨hr.1, hr.2.1, all_app hr.2.2 (all_one hA)⟩
  | orR A B c ih =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    have hn := hr.2.2 _ (mem_of h.1)
    exact ih _ h.2 M x ⟨hr.1, hr.2.1,
      all_app hr.2.2 (all_two (fun hA => hn (.inl hA)) (fun hB => hn (.inr hB)))⟩
  | impLoc A B c ih =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    have hn := hr.2.2 _ (mem_of h.1.1)
    exact ih _ h.2 M x ⟨hr.1, hr.2.1, all_app hr.2.2 (all_one fun hB =>
      hn fun v hv _ => SubframeModel.force_mono M B hv hB)⟩
  | boxLoc A c ih =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    have hn := hr.2.2 _ (mem_of h.1.2)
    exact ih _ h.2 M x ⟨hr.1, hr.2.1, all_app hr.2.2 (all_one fun hA =>
      hn fun v hv _ => SubframeModel.force_mono M A hv hA)⟩
  | impR A B c ih =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨v, hxv, hA, hB⟩ := exists_of_not_force_imp (hr.2.2 _ (mem_of h.1))
    exact ih _ h.2 M v ⟨fun e => absurd e Bool.false_ne_true,
      all_app (fun γ hγ => SubframeModel.force_mono M γ hxv (hr.2.1 γ hγ)) (all_one hA),
      all_one hB⟩
  | boxR A c ih =>
    intro s h M _ x hr
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨v, hxv, hvS, hA⟩ := exists_of_not_force_box (hr.2.2 _ (mem_of h.1))
    exact ih _ h.2 M v ⟨fun _ => hvS,
      fun γ hγ => SubframeModel.force_mono M γ hxv (hr.2.1 γ hγ), all_one hA⟩

/-- A closed tableau for `⊢ φ` proves `φ`. -/
theorem holds_of_check {φ : PLLFormula} {c : TCert} (h : check ⟨false, [], [φ]⟩ c = true) :
    Holds φ :=
  SubframeModel.CF.completeness fun M _ x => Decidable.byContradiction fun hn =>
    check_sound c _ h M x ⟨fun e => absurd e Bool.false_ne_true,
      fun _ hγ => absurd hγ List.not_mem_nil, all_one hn⟩

/-- **The yes side**: closed tableaux, certifying `Nonempty ([] ⊢ φ)`. -/
def yes : Certify.Certifier PLLFormula TCert Holds where
  check φ c := check ⟨false, [], [φ]⟩ c
  sound _ _ h := holds_of_check h

/-! ## The no side: finite subframe countermodels -/

/-- A finite subframe model as tables: worlds `0 … n-1`, no fallible world. -/
structure SubCM where
  n : Nat
  root : Nat
  le : List (List Bool)
  S : List Bool
  val : List (List String)
  deriving Repr

namespace SubCM

variable (m : SubCM)

def leB (i j : Nat) : Bool := (m.le.getD i []).getD j false
def SB (i : Nat) : Bool := m.S.getD i false
def vB (a : String) (i : Nat) : Bool := (m.val.getD i []).contains a

/-- The frame conditions: root in range, a preorder, a persistent valuation. -/
def okB : Bool :=
  decide (m.root < m.n) &&
  (List.range m.n).all (fun i => m.leB i i) &&
  (List.range m.n).all (fun i => (List.range m.n).all fun j => (List.range m.n).all fun k =>
    !(m.leB i j && m.leB j k) || m.leB i k) &&
  (List.range m.n).all (fun i => (List.range m.n).all fun j =>
    !(m.leB i j) || (m.val.getD i []).all fun a => m.vB a j)

/-- Forcing, structural in the formula. -/
def forceB : Nat → PLLFormula → Bool
  | i, .prop a => m.vB a i
  | _, .falsePLL => false
  | i, .and A B => forceB i A && forceB i B
  | i, .or A B => forceB i A || forceB i B
  | i, .ifThen A B => (List.range m.n).all fun j => !(m.leB i j) || !(forceB j A) || forceB j B
  | i, .somehow A => (List.range m.n).all fun j => !(m.leB i j) || !(m.SB j) || forceB j A

/-- The certificate check: a model, refuting `φ` at its root. -/
def refutes (φ : PLLFormula) : Bool := m.okB && !(m.forceB m.root φ)

variable {m}

theorem ok_parts (h : m.okB = true) :
    m.root < m.n ∧ (∀ i, i < m.n → m.leB i i = true) ∧
    (∀ i j k, i < m.n → j < m.n → k < m.n → m.leB i j = true → m.leB j k = true →
      m.leB i k = true) ∧
    (∀ i j, i < m.n → j < m.n → m.leB i j = true → ∀ a, m.vB a i = true → m.vB a j = true) := by
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hr, hrefl⟩, htrans⟩, hher⟩ := h
  refine ⟨hr, hrefl, fun i j k hi hj hk hij hjk => ?_, fun i j hi hj hij a ha => ?_⟩
  · have := htrans i hi j hj k hk
    simp only [hij, hjk, Bool.and_self, Bool.not_true, Bool.false_or] at this
    exact this
  · have := hher i hi j hj
    simp only [hij, Bool.not_true, Bool.false_or, List.all_eq_true] at this
    exact this a (List.contains_iff_mem.mp ha)

/-- The model the tables denote. -/
abbrev toModel (h : m.okB = true) : SubframeModel where
  W := {i : Nat // i < m.n}
  le a b := m.leB a.1 b.1 = true
  S := {a | m.SB a.1 = true}
  V x := {a | m.vB x a.1 = true}
  refl a := (ok_parts h).2.1 a.1 a.2
  trans {u v w} h₁ h₂ := (ok_parts h).2.2.1 u.1 v.1 w.1 u.2 v.2 w.2 h₁ h₂
  hered {a u v} h₁ h₂ := (ok_parts h).2.2.2 u.1 v.1 u.2 v.2 h₁ a h₂

instance (h : m.okB = true) : FinDec (m.toModel h) where
  elems := (List.range m.n).attach.map fun i => ⟨i.1, List.mem_range.mp i.2⟩
  complete a := List.mem_map.mpr ⟨⟨a.1, List.mem_range.mpr a.2⟩, List.mem_attach _ _, rfl⟩
  decLe a b := inferInstanceAs (Decidable (m.leB a.1 b.1 = true))
  decS a := inferInstanceAs (Decidable (m.SB a.1 = true))
  decV x a := inferInstanceAs (Decidable (m.vB x a.1 = true))

/-- The Boolean forcing agrees with forcing in the model. -/
theorem forceB_iff (h : m.okB = true) :
    ∀ (φ : PLLFormula) (a : (m.toModel h).W), m.forceB a.1 φ = true ↔ (m.toModel h).force a φ
  | .prop x, a => Iff.rfl
  | .falsePLL, a => ⟨fun e => absurd e Bool.false_ne_true, False.elim⟩
  | .and A B, a => by
      simp only [forceB, Bool.and_eq_true]
      exact and_congr (forceB_iff h A a) (forceB_iff h B a)
  | .or A B, a => by
      simp only [forceB, Bool.or_eq_true]
      exact or_congr (forceB_iff h A a) (forceB_iff h B a)
  | .ifThen A B, a => by
      simp only [forceB, List.all_eq_true, List.mem_range]
      constructor
      · intro hall b hab hA
        have := hall b.1 b.2
        simp only [show m.leB a.1 b.1 = true from hab, (forceB_iff h A b).mpr hA,
          Bool.not_true, Bool.false_or] at this
        exact (forceB_iff h B b).mp this
      · intro hall j hj
        cases hl : m.leB a.1 j <;> simp only [Bool.not_false, Bool.true_or, Bool.not_true,
          Bool.false_or]
        cases hf : m.forceB j A <;> simp only [Bool.not_false, Bool.true_or, Bool.not_true,
          Bool.false_or]
        exact (forceB_iff h B ⟨j, hj⟩).mpr (hall ⟨j, hj⟩ hl ((forceB_iff h A ⟨j, hj⟩).mp hf))
  | .somehow A, a => by
      simp only [forceB, List.all_eq_true, List.mem_range]
      constructor
      · intro hall b hab hbS
        have := hall b.1 b.2
        simp only [show m.leB a.1 b.1 = true from hab, show m.SB b.1 = true from hbS,
          Bool.not_true, Bool.false_or] at this
        exact (forceB_iff h A b).mp this
      · intro hall j hj
        cases hl : m.leB a.1 j <;> simp only [Bool.not_false, Bool.true_or, Bool.not_true,
          Bool.false_or]
        cases hs : m.SB j <;> simp only [Bool.not_false, Bool.true_or, Bool.not_true,
          Bool.false_or]
        exact (forceB_iff h A ⟨j, hj⟩).mpr (hall ⟨j, hj⟩ hl hs)

/-- **Soundness of the countermodel check.** -/
theorem refutes_sound {φ : PLLFormula} (h : m.refutes φ = true) : Holds φ → False := by
  intro ⟨d⟩
  simp only [refutes, Bool.and_eq_true, Bool.not_eq_true'] at h
  have hr := (ok_parts h.1).1
  have hf := SubframeModel.CF.soundness d (m.toModel h.1) ⟨m.root, hr⟩ fun _ hχ => absurd hχ List.not_mem_nil
  have := (forceB_iff h.1 φ ⟨m.root, hr⟩).mpr hf
  rw [h.2] at this
  exact Bool.false_ne_true this

end SubCM

/-- **The no side**: finite subframe countermodels. -/
def no : Certify.Certifier PLLFormula SubCM (fun φ => Holds φ → False) where
  check φ m := m.refutes φ
  sound _ _ h := SubCM.refutes_sound h

end SubTab
end PLLND

#axioms_within PLLND.SubTab.check_sound [propext, Quot.sound]
#axioms_within PLLND.SubTab.holds_of_check [propext, Quot.sound]
#axioms_within PLLND.SubTab.SubCM.refutes_sound [propext, Quot.sound]
#axioms_within PLLND.SubTab.yes [propext, Quot.sound]
#axioms_within PLLND.SubTab.no [propext, Quot.sound]

/-! ## Lean certify gates (R2, R3) -/

#certify_structural PLLND.SubTab.yes
#certify_statement PLLND.SubTab.yes
#certify_structural PLLND.SubTab.no
#certify_statement PLLND.SubTab.no
