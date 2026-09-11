/-
# `LaxLogic.QLL.Herbrand` — Lloyd's least Herbrand model, inside the Kripke semantics

Stage H2 of `docs/qll-herbrand-horn-plan.md`: the `◯`-free instance (CLAUDE.md
rule 8) of what `HerbrandLLP.lean` will do for Definition 5.1 programs.

**The Herbrand universe** is the locally closed terms, with free names counted
as constants (the plan's D3, extended): under the valuation `x ↦ .fvar x` every
such term evaluates to itself, so free names need no bookkeeping.  This is the
device of the canonical model in `Complete1.lean`.

**A Herbrand model is a `KModel`.**  `HFrame.model` puts the Herbrand universe,
as a constant domain, on any preorder of worlds, with the function symbols
interpreted as themselves; `herbrand1 I` is the one-world case, Lloyd's
Herbrand interpretation `I`, and `HTrue I A` is forcing there.  No new
semantics is introduced: truth in a Herbrand interpretation *is* `force`.

**The least Herbrand model** `LHM R P` is an inductive predicate, relative to
built-in relations `R` (empty here; the constraint relations of §7 later).  It
is not `OrderHom.lfp`: Mathlib's `lfp_le`/`map_lfp` on `Set` depend on
`Classical.choice`, an inductive predicate on no axioms, and its induction
principle is the proof extraction below.  The clause rule ignores the modal
flag, so for a program with modal heads `LHM` is the least model of the program
with `◯` stripped: the draft's `Π¹`.

For a closed Horn program `P` (`Horn.WF`) and a closed Σ-formula `S`:

    Tp R P (LHM R P) p us ↔ LHM R P p us              -- a fixpoint of T_P
    (∀ p us, Tp R P I p us → I p us) → LHM R P ≤ I    -- the least pre-fixpoint
    HTrue (LHM R P) h.form   (h ∈ P)                  -- a model of P

and, when `P` has no modal heads and `R` is empty,

    P.forms ⊢q S  ↔  HTrue (LHM P) S  ↔  P.forms ⊫ S

For atoms this is van Emden and Kowalski's characterisation of the least
Herbrand model, with `⊫` the Kripke consequence of `Kripke.lean`.  Its
`⊫ → ⊢q` half is completeness for this fragment by Lloyd's route: instantiate
the consequence at the least Herbrand model, then read a derivation off the
inductive definition, with terms of the model as the witnesses for `∃`.  No
Lindenbaum construction is involved.

Two designed cells show the restrictions are needed: excluded middle for an
atom holds in the empty Herbrand interpretation and is not provable (queries
must be Σ), and `P ∨ Q` has no least Herbrand model (programs must be Horn).
-/
import LaxLogic.QLL.Horn

namespace LaxLogic.QLL

/-! ## Local closedness, through instantiation and selection -/

theorem Tm.lcAtList_of_forall {k : Nat} :
    ∀ {ts : List Tm}, (∀ t ∈ ts, Tm.lcAt k t) → Tm.lcAtList k ts
  | [],     _ => trivial
  | t :: _, h => ⟨h t (List.mem_cons.2 (Or.inl rfl)),
      Tm.lcAtList_of_forall fun u hu => h u (List.mem_cons.2 (Or.inr hu))⟩

theorem Tm.lcAtList_nil {k : Nat} : Tm.lcAtList k [] := trivial

/-- Instantiating the argument list of a clause head. -/
def Tm.instAllList : List Tm → List Tm → List Tm
  | [],      us => us
  | t :: ts, us => Tm.instAllList ts (Tm.openAtList ts.length t us)

theorem Form.instAll_pred : ∀ (ts : List Tm) (P : String) (us : List Tm),
    Form.instAll ts (.pred P us) = .pred P (Tm.instAllList ts us)
  | [],      _, _  => rfl
  | t :: ts, P, us => Form.instAll_pred ts P (Tm.openAtList ts.length t us)

theorem Tm.lcAtList_instAllList : ∀ (ts us : List Tm), (∀ t ∈ ts, Tm.lcAt 0 t) →
    Tm.lcAtList ts.length us → Tm.lcAtList 0 (Tm.instAllList ts us)
  | [],      _,  _,   h => h
  | t :: ts, us, hts, h =>
      Tm.lcAtList_instAllList ts _ (fun u hu => hts u (List.mem_cons.2 (Or.inr hu)))
        (Tm.lcAtList_openAtList ts.length t
          (Tm.lcAt_mono (Nat.zero_le _) t (hts t (List.mem_cons.2 (Or.inl rfl)))) us h)

theorem Form.lcAt_instAll : ∀ (ts : List Tm) (A : Form), (∀ t ∈ ts, Tm.lcAt 0 t) →
    Form.lcAt ts.length A → Form.lcAt 0 (Form.instAll ts A)
  | [],      _, _,   h => h
  | t :: ts, A, hts, h =>
      Form.lcAt_instAll ts _ (fun u hu => hts u (List.mem_cons.2 (Or.inr hu)))
        (Form.lcAt_openAt A ts.length t
          (Tm.lcAt_mono (Nat.zero_le _) t (hts t (List.mem_cons.2 (Or.inl rfl)))) h)

theorem Form.lcAt_sel : ∀ (A : Form) (g : Idx) (k : Nat), Form.lcAt k A → Form.lcAt k (sel A g)
  | .top, g, _, h => by rw [sel_top]; exact h
  | .bot, g, _, h => by cases g <;> exact h
  | .pred P ts, g, _, h => by rw [sel_pred]; exact h
  | .and A B, g, k, h => by
      cases g with
      | pair g₁ g₂ => exact ⟨Form.lcAt_sel A g₁ k h.1, Form.lcAt_sel B g₂ k h.2⟩
      | _ => exact h
  | .or A B, g, k, h => by
      cases g with
      | inl g => exact Form.lcAt_sel A g k h.1
      | inr g => exact Form.lcAt_sel B g k h.2
      | _ => exact h
  | .imp _ _, g, _, h => by cases g <;> exact h
  | .circ _ _, g, _, h => by cases g <;> exact h
  | .forall_ _, g, _, h => by cases g <;> exact h
  | .exists_ A, g, k, h => by
      cases g with
      | ex g => exact Form.lcAt_sel A g (k + 1) h
      | _ => exact h

theorem IsPP.openAt {A : Form} (h : IsPP A) : ∀ (k : Nat) (t : Tm), IsPP (A.openAt k t) := by
  induction h with
  | top => intro _ _; exact .top
  | pred P _ => intro _ _; exact .pred P _
  | and _ _ ih₁ ih₂ => intro k t; exact .and (ih₁ k t) (ih₂ k t)
  | ex _ ih => intro k t; exact .ex (ih (k + 1) t)

theorem IsPP.instAll : ∀ (ts : List Tm) {A : Form}, IsPP A → IsPP (Form.instAll ts A)
  | [],      _, h => h
  | t :: ts, _, h => IsPP.instAll ts (h.openAt _ t)

/-- `∀x̃`-elimination at a list of terms: the `Prv` twin of `Derives.allEs`. -/
theorem Prv.allEs : ∀ (ts : List Tm) {Γ : List Form} {A : Form}, (∀ t ∈ ts, Tm.lcAt 0 t) →
    Prv Γ (Form.foralls ts.length A) → Prv Γ (Form.instAll ts A)
  | [],      _, _, _,   h => h
  | t :: ts, _, A, hts, h => by
      have h' := Prv.allE t (hts t (List.mem_cons.2 (Or.inl rfl))) h
      rw [Form.openAt_foralls, Nat.zero_add] at h'
      exact Prv.allEs ts (fun u hu => hts u (List.mem_cons.2 (Or.inr hu))) h'

/-! ## Herbrand models are Kripke models -/

/-- A preorder of worlds with an upward-closed set of fallible ones. -/
structure HFrame where
  W : Type
  le : W → W → Prop
  refl : ∀ w, le w w
  trans : ∀ {u v w}, le u v → le v w → le u w
  Fl : W → Prop
  hered_Fl : ∀ {w v}, le w v → Fl w → Fl v

/-- The Kripke model on a Herbrand frame: the locally closed terms as a constant
domain, every function symbol interpreted as itself, and all three
accessibility relations the frame's order.  The last makes `◯∀` and `◯∃`
coincide, which is why the modal results built on it are for one modality at a
time. -/
def HFrame.model (F : HFrame) (I : F.W → String → List Tm → Prop)
    (hI : ∀ {w v : F.W} {p : String} {ts : List Tm}, F.le w v → I w p ts → I v p ts) :
    KModel where
  S := F.W
  D := Tm
  Dom _ t := Tm.lcAt 0 t
  Ri := F.le
  RA := F.le
  RE := F.le
  Fl := F.Fl
  refl_i := F.refl
  trans_i := F.trans
  refl_A := F.refl
  trans_A := F.trans
  sub_A h := h
  refl_E := F.refl
  trans_E := F.trans
  sub_E h := h
  dom_mono _ h := h
  d₀ := .fn "c" []
  dom_d₀ _ := trivial
  hered_Fl := F.hered_Fl
  fn f ds := .fn f ds
  I := I
  hered_I := hI
  fn_dom h := Tm.lcAtList_of_forall h

section
variable (F : HFrame) (I : F.W → String → List Tm → Prop)
  (hI : ∀ {w v : F.W} {p : String} {ts : List Tm}, F.le w v → I w p ts → I v p ts)

mutual
/-- Under `x ↦ .fvar x`, a locally closed term denotes itself. -/
theorem HFrame.evTm_lc (β : List Tm) :
    ∀ t : Tm, Tm.lcAt 0 t → (F.model I hI).evTm Tm.fvar β t = t
  | .bvar i,   h => absurd h (Nat.not_lt_zero i)
  | .fvar _,   _ => rfl
  | .fn f ts,  h => congrArg (Tm.fn f) (HFrame.evTms_lc β ts h)
theorem HFrame.evTms_lc (β : List Tm) :
    ∀ ts : List Tm, Tm.lcAtList 0 ts → (F.model I hI).evTms Tm.fvar β ts = ts
  | [],      _ => rfl
  | t :: ts, h => by
      show (F.model I hI).evTm Tm.fvar β t :: (F.model I hI).evTms Tm.fvar β ts = t :: ts
      rw [HFrame.evTm_lc β t h.1, HFrame.evTms_lc β ts h.2]
      rfl
end
end

/-- One world, nothing fallible. -/
def HFrame.one : HFrame where
  W := Unit
  le _ _ := True
  refl _ := trivial
  trans _ _ := trivial
  Fl _ := False
  hered_Fl _ h := h

/-- Lloyd's Herbrand interpretation `I`, as a one-world Kripke model. -/
abbrev herbrand1 (I : String → List Tm → Prop) : KModel :=
  HFrame.one.model (fun _ => I) (fun _ h => h)

/-- Truth of a formula in a Herbrand interpretation: forcing in `herbrand1`. -/
def HTrue (I : String → List Tm → Prop) (A : Form) : Prop :=
  (herbrand1 I).force A () Tm.fvar []

theorem herbrand1_evTm (I : String → List Tm → Prop) (t : Tm) (h : Tm.lcAt 0 t) :
    (herbrand1 I).evTm Tm.fvar [] t = t :=
  HFrame.evTm_lc HFrame.one (fun _ => I) (fun _ h => h) [] t h

theorem herbrand1_evTms (I : String → List Tm → Prop) (us : List Tm) (h : Tm.lcAtList 0 us) :
    (herbrand1 I).evTms Tm.fvar [] us = us :=
  HFrame.evTms_lc HFrame.one (fun _ => I) (fun _ h => h) [] us h

/-! ## Truth in a Herbrand interpretation, connective by connective -/

section
variable {I : String → List Tm → Prop}

theorem HTrue_pred {p : String} {us : List Tm} (h : Tm.lcAtList 0 us) :
    HTrue I (.pred p us) ↔ I p us := by
  show False ∨ I p ((herbrand1 I).evTms Tm.fvar [] us) ↔ I p us
  rw [herbrand1_evTms I us h]
  exact ⟨fun h => h.resolve_left id, Or.inr⟩

theorem HTrue_and {A B : Form} : HTrue I (.and A B) ↔ HTrue I A ∧ HTrue I B := Iff.rfl

theorem HTrue_or {A B : Form} : HTrue I (.or A B) ↔ HTrue I A ∨ HTrue I B := Iff.rfl

theorem HTrue_imp {A B : Form} : HTrue I (.imp A B) ↔ (HTrue I A → HTrue I B) :=
  ⟨fun h ha => h () trivial ha, fun h _ _ ha => h ha⟩

/-- One world: both lax modalities collapse. -/
theorem HTrue_circ {q : Q} {A : Form} : HTrue I (.circ q A) ↔ HTrue I A := by
  cases q
  · exact ⟨fun h => (h () trivial).elim fun _ hu => hu.2, fun h _ _ => ⟨(), trivial, h⟩⟩
  · exact ⟨fun h => (h () trivial).elim fun _ hu => hu.2, fun h _ _ => ⟨(), trivial, h⟩⟩

theorem HTrue_exists {A : Form} :
    HTrue I (.exists_ A) ↔ ∃ t, Tm.lcAt 0 t ∧ HTrue I (A.openAt 0 t) := by
  constructor
  · rintro ⟨t, ht, h⟩
    have e := (herbrand1 I).force_openAt Tm.fvar t ht A () []
    rw [herbrand1_evTm I t ht] at e
    exact ⟨t, ht, e.2 h⟩
  · rintro ⟨t, ht, h⟩
    have e := (herbrand1 I).force_openAt Tm.fvar t ht A () []
    rw [herbrand1_evTm I t ht] at e
    exact ⟨t, ht, e.1 h⟩

theorem HTrue_forall {A : Form} :
    HTrue I (.forall_ A) ↔ ∀ t, Tm.lcAt 0 t → HTrue I (A.openAt 0 t) := by
  constructor
  · intro h t ht
    have e := (herbrand1 I).force_openAt Tm.fvar t ht A () []
    rw [herbrand1_evTm I t ht] at e
    exact e.2 (h () trivial t ht)
  · intro h _ _ t ht
    have e := (herbrand1 I).force_openAt Tm.fvar t ht A () []
    rw [herbrand1_evTm I t ht] at e
    exact e.1 (h t ht)

theorem HTrue_foralls : ∀ (m : Nat) (A : Form),
    HTrue I (Form.foralls m A) ↔
      ∀ ts : List Tm, ts.length = m → (∀ t ∈ ts, Tm.lcAt 0 t) → HTrue I (Form.instAll ts A)
  | 0, A => by
      constructor
      · intro h ts hl _
        cases ts with
        | nil => exact h
        | cons _ _ => exact absurd hl (Nat.succ_ne_zero _)
      · intro h
        exact h [] rfl fun _ h => nomatch h
  | m + 1, A => by
      show HTrue I (.forall_ (Form.foralls m A)) ↔ _
      rw [HTrue_forall]
      constructor
      · intro h ts hl hts
        cases ts with
        | nil => exact absurd hl.symm (Nat.succ_ne_zero m)
        | cons t ts =>
            have hl' : ts.length = m := Nat.succ.inj hl
            have h' := h t (hts t (List.mem_cons.2 (Or.inl rfl)))
            rw [Form.openAt_foralls, Nat.zero_add, HTrue_foralls m] at h'
            have h'' := h' ts hl' fun u hu => hts u (List.mem_cons.2 (Or.inr hu))
            show HTrue I (Form.instAll ts (A.openAt ts.length t))
            rw [hl']
            exact h''
      · intro h t ht
        rw [Form.openAt_foralls, Nat.zero_add, HTrue_foralls m]
        intro ts hl hts
        have h' := h (t :: ts) (by rw [List.length_cons, hl]) fun u hu => by
          rcases List.mem_cons.1 hu with rfl | hu
          · exact ht
          · exact hts u hu
        have e : Form.instAll (t :: ts) A = Form.instAll ts (A.openAt m t) := by
          show Form.instAll ts (A.openAt ts.length t) = _
          rw [hl]
        rw [e] at h'
        exact h'

theorem HTrue_instAll_headForm (h : Horn) (ts : List Tm) :
    HTrue I (Form.instAll ts h.headForm) ↔ HTrue I (Form.instAll ts h.headAtom) := by
  unfold Horn.headForm
  cases h.modal
  · show HTrue I (Form.instAll ts h.headAtom) ↔ _
    exact Iff.rfl
  · show HTrue I (Form.instAll ts (.circ h.q h.headAtom)) ↔ _
    rw [Form.instAll_circ]
    exact HTrue_circ

end

/-! ## The least Herbrand model -/

/-- No built-in relations. -/
def RNone : String → List Tm → Prop := fun _ _ => False

/-- A Horn clause is closed: its body and head arguments mention only its own
`arity` bound variables. -/
def Horn.WF (h : Horn) : Prop := Form.lcAt h.arity h.body ∧ Tm.lcAtList h.arity h.args

/-- Truth in the least Herbrand model of `P` over the built-in relations `R`, for
the formulas that can be true there: atoms, and the primitive positive formulas
built from them.  `fire` is the immediate consequence operator read as a rule;
it ignores the modal flag (see the module header). -/
inductive Holds (R : String → List Tm → Prop) (P : List Horn) : Form → Prop
  | base {p : String} {us : List Tm} : R p us → Holds R P (.pred p us)
  | top : Holds R P .top
  | and {A B : Form} : Holds R P A → Holds R P B → Holds R P (.and A B)
  | ex {A : Form} (t : Tm) : Tm.lcAt 0 t → Holds R P (A.openAt 0 t) → Holds R P (.exists_ A)
  | fire {h : Horn} {ts : List Tm} : h ∈ P → ts.length = h.arity → (∀ t ∈ ts, Tm.lcAt 0 t) →
      Holds R P (Form.instAll ts h.body) → Holds R P (.pred h.head (Tm.instAllList ts h.args))

/-- The least Herbrand model `M_P`, as a Herbrand interpretation. -/
def LHM (R : String → List Tm → Prop) (P : List Horn) : String → List Tm → Prop :=
  fun p us => Holds R P (.pred p us)

/-- The immediate consequence operator `T_P`, relative to `R`. -/
def Tp (R : String → List Tm → Prop) (P : List Horn) (I : String → List Tm → Prop) :
    String → List Tm → Prop :=
  fun p us => R p us ∨ ∃ h ∈ P, ∃ ts : List Tm, ts.length = h.arity ∧ (∀ t ∈ ts, Tm.lcAt 0 t) ∧
    HTrue I (Form.instAll ts h.body) ∧ p = h.head ∧ us = Tm.instAllList ts h.args

section
variable {R : String → List Tm → Prop} {P : List Horn}

/-- What holds is true in the least Herbrand model. -/
theorem Holds.toHTrue (hR : ∀ p us, R p us → Tm.lcAtList 0 us) (hP : ∀ h ∈ P, h.WF)
    {φ : Form} (d : Holds R P φ) : HTrue (LHM R P) φ := by
  induction d with
  | base hr => exact (HTrue_pred (hR _ _ hr)).2 (.base hr)
  | top => trivial
  | and _ _ ih₁ ih₂ => exact HTrue_and.2 ⟨ih₁, ih₂⟩
  | ex t ht _ ih => exact HTrue_exists.2 ⟨t, ht, ih⟩
  | @fire h ts hh hlen hts hb _ =>
      exact (HTrue_pred (Tm.lcAtList_instAllList ts h.args hts
        (by rw [hlen]; exact (hP h hh).2))).2 (.fire hh hlen hts hb)

theorem Holds.of_HTrue_aux : ∀ (n : Nat) {φ : Form}, φ.size < n → IsPP φ → Form.lcAt 0 φ →
    HTrue (LHM R P) φ → Holds R P φ
  | 0, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, hn, hφ, hc, h => by
      cases hφ with
      | top => exact .top
      | pred p us => exact (HTrue_pred hc).1 h
      | @and A B h₁ h₂ =>
          exact .and (Holds.of_HTrue_aux n (Form.size_lt_left hn) h₁ hc.1 (HTrue_and.1 h).1)
            (Holds.of_HTrue_aux n (Form.size_lt_right hn) h₂ hc.2 (HTrue_and.1 h).2)
      | @ex A hA =>
          obtain ⟨t, ht, h⟩ := HTrue_exists.1 h
          exact .ex t ht (Holds.of_HTrue_aux n
            (by rw [Form.size_openAt]; exact Nat.lt_of_succ_lt_succ hn)
            (hA.openAt 0 t) (Form.lcAt_openAt A 0 t ht hc) h)

/-- A closed primitive positive formula true in the least Herbrand model holds. -/
theorem Holds.of_HTrue {φ : Form} (hφ : IsPP φ) (hc : Form.lcAt 0 φ)
    (h : HTrue (LHM R P) φ) : Holds R P φ :=
  Holds.of_HTrue_aux _ (Nat.lt_succ_self _) hφ hc h

theorem LHM_lc (hR : ∀ p us, R p us → Tm.lcAtList 0 us) (hP : ∀ h ∈ P, h.WF)
    {p : String} {us : List Tm} (hl : LHM R P p us) : Tm.lcAtList 0 us := by
  cases hl with
  | base hr => exact hR _ _ hr
  | @fire h ts hh hlen hts _ =>
      exact Tm.lcAtList_instAllList ts h.args hts (by rw [hlen]; exact (hP h hh).2)

/-- The least Herbrand model is a model of the program. -/
theorem HTrue_LHM_form (hP : ∀ h ∈ P, h.WF) {h : Horn} (hh : h ∈ P) :
    HTrue (LHM R P) h.form := by
  show HTrue _ (Form.foralls h.arity (.imp h.body h.headForm))
  refine (HTrue_foralls h.arity _).2 fun ts hlen hts => ?_
  rw [Form.instAll_imp]
  refine HTrue_imp.2 fun hb => ?_
  have hb' : Holds R P (Form.instAll ts h.body) :=
    Holds.of_HTrue (h.body_pp.instAll ts)
      (Form.lcAt_instAll ts _ hts (by rw [hlen]; exact (hP h hh).1)) hb
  refine (HTrue_instAll_headForm h ts).2 ?_
  show HTrue _ (Form.instAll ts (.pred h.head h.args))
  rw [Form.instAll_pred]
  exact (HTrue_pred (Tm.lcAtList_instAllList ts _ hts
    (by rw [hlen]; exact (hP h hh).2))).2 (.fire hh hlen hts hb')

/-- `T_P(M_P) = M_P`. -/
theorem Tp_LHM (hR : ∀ p us, R p us → Tm.lcAtList 0 us) (hP : ∀ h ∈ P, h.WF)
    (p : String) (us : List Tm) : Tp R P (LHM R P) p us ↔ LHM R P p us := by
  constructor
  · rintro (hr | ⟨h, hh, ts, hlen, hts, hb, rfl, rfl⟩)
    · exact .base hr
    · exact .fire hh hlen hts (Holds.of_HTrue (h.body_pp.instAll ts)
        (Form.lcAt_instAll ts _ hts (by rw [hlen]; exact (hP h hh).1)) hb)
  · intro hl
    cases hl with
    | base hr => exact Or.inl hr
    | @fire h ts hh hlen hts hb =>
        exact Or.inr ⟨h, hh, ts, hlen, hts, Holds.toHTrue hR hP hb, rfl, rfl⟩

/-- `M_P` is below every pre-fixpoint of `T_P`. -/
theorem LHM_least (hR : ∀ p us, R p us → Tm.lcAtList 0 us) (hP : ∀ h ∈ P, h.WF)
    {I : String → List Tm → Prop} (hI : ∀ p us, Tp R P I p us → I p us)
    (p : String) (us : List Tm) (hl : LHM R P p us) : I p us := by
  have key : ∀ {φ : Form}, Holds R P φ → HTrue I φ := by
    intro φ d
    induction d with
    | base hr => exact (HTrue_pred (hR _ _ hr)).2 (hI _ _ (Or.inl hr))
    | top => trivial
    | and _ _ ih₁ ih₂ => exact HTrue_and.2 ⟨ih₁, ih₂⟩
    | ex t ht _ ih => exact HTrue_exists.2 ⟨t, ht, ih⟩
    | @fire h ts hh hlen hts _ ih =>
        exact (HTrue_pred (Tm.lcAtList_instAllList ts h.args hts
          (by rw [hlen]; exact (hP h hh).2))).2 (hI _ _ (Or.inr ⟨h, hh, ts, hlen, hts, ih, rfl, rfl⟩))
  exact (HTrue_pred (LHM_lc hR hP hl)).1 (key (φ := .pred p us) hl)

end

/-! ## Lloyd's theorem, over the Kripke consequence relation -/

section
variable {P : List Horn}

/-- Proof extraction: what holds in the least Herbrand model of a program with
no modal heads is derivable from it. -/
theorem Holds.prv (hm : ∀ h ∈ P, h.modal = false) {φ : Form} (d : Holds RNone P φ) :
    Prv (P.map Horn.form) φ := by
  induction d with
  | base hr => exact (hr : False).elim
  | top => exact .topI
  | and _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | ex t ht _ ih => exact .exI t ht ih
  | @fire h ts hh hlen hts _ ih =>
      have hf : Prv (P.map Horn.form) (Form.foralls ts.length (.imp h.body h.headForm)) := by
        rw [hlen]; exact .var (List.mem_map.2 ⟨h, hh, rfl⟩)
      have hi := Prv.allEs ts hts hf
      rw [Form.instAll_imp] at hi
      have e : Form.instAll ts h.headForm = .pred h.head (Tm.instAllList ts h.args) := by
        unfold Horn.headForm
        rw [hm h hh]
        exact Form.instAll_pred ts h.head h.args
      rw [← e]
      exact .impE hi ih

theorem prv_of_HTrue_LHM (hm : ∀ h ∈ P, h.modal = false) {S : Form} (hS : IsSigma S)
    (hc : Form.lcAt 0 S) (h : HTrue (LHM RNone P) S) : Prv (P.map Horn.form) S := by
  obtain ⟨g, hg, h⟩ := ((herbrand1 (LHM RNone P)).force_iff_sel hS () Tm.fvar []).1 h
  exact Prv.of_sel hS hg (Holds.prv hm (Holds.of_HTrue (hS.pp_sel hg) (Form.lcAt_sel S g 0 hc) h))

theorem HTrue_of_consequence (hP : ∀ h ∈ P, h.WF) {S : Form}
    (h : Consequence (P.map Horn.form) S) : HTrue (LHM RNone P) S :=
  h (herbrand1 (LHM RNone P)) () Tm.fvar (fun _ _ => trivial) fun B hB => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hB
    exact HTrue_LHM_form hP hc

/-- Lloyd: a closed Σ-query follows from a closed Horn program exactly when it is
true in the least Herbrand model. -/
theorem lloyd_prv_iff (hP : ∀ h ∈ P, h.WF) (hm : ∀ h ∈ P, h.modal = false) {S : Form}
    (hS : IsSigma S) (hc : Form.lcAt 0 S) :
    Prv (P.map Horn.form) S ↔ HTrue (LHM RNone P) S :=
  ⟨fun h => HTrue_of_consequence hP (Prv.sound h), prv_of_HTrue_LHM hm hS hc⟩

/-- Completeness for Horn programs and Σ-queries, by Lloyd's route. -/
theorem lloyd_completeness (hP : ∀ h ∈ P, h.WF) (hm : ∀ h ∈ P, h.modal = false) {S : Form}
    (hS : IsSigma S) (hc : Form.lcAt 0 S) (h : Consequence (P.map Horn.form) S) :
    Prv (P.map Horn.form) S :=
  prv_of_HTrue_LHM hm hS hc (HTrue_of_consequence hP h)

theorem lloyd_consequence_iff (hP : ∀ h ∈ P, h.WF) (hm : ∀ h ∈ P, h.modal = false)
    {S : Form} (hS : IsSigma S) (hc : Form.lcAt 0 S) :
    Consequence (P.map Horn.form) S ↔ Prv (P.map Horn.form) S :=
  ⟨lloyd_completeness hP hm hS hc, Prv.sound⟩

/-- van Emden and Kowalski: the least Herbrand model is the set of atoms that
follow from the program. -/
theorem vanEmden_Kowalski (hP : ∀ h ∈ P, h.WF) (hm : ∀ h ∈ P, h.modal = false)
    {p : String} {us : List Tm} (hus : Tm.lcAtList 0 us) :
    LHM RNone P p us ↔ Consequence (P.map Horn.form) (.pred p us) := by
  rw [lloyd_consequence_iff hP hm (.pred p us) hus, lloyd_prv_iff hP hm (.pred p us) hus,
    HTrue_pred hus]

end

/-! ## Why the restrictions: two designed cells -/

/-- Two worlds `false ≤ true`, nothing fallible. -/
def HFrame.two : HFrame where
  W := Bool
  le a b := a = false ∨ b = true
  refl a := by cases a; exact Or.inl rfl; exact Or.inr rfl
  trans := fun h₁ h₂ => by
    rcases h₁ with rfl | rfl
    · exact Or.inl rfl
    · rcases h₂ with h | rfl
      · exact (Bool.noConfusion h : False).elim
      · exact Or.inr rfl
  Fl _ := False
  hered_Fl _ h := h

/-- `P` true at the top world only. -/
def lemModel : KModel :=
  HFrame.two.model (fun w _ _ => w = true) fun h hw => by
    rcases h with rfl | rfl
    · exact (Bool.false_ne_true hw).elim
    · rfl

/-- Excluded middle for an atom is true in the empty Herbrand interpretation... -/
theorem lem_HTrue : HTrue RNone (.or (.pred "P" []) (.imp (.pred "P" []) .bot)) :=
  Or.inr (HTrue_imp.2 fun h => ((HTrue_pred Tm.lcAtList_nil).1 h : False).elim)

/-- ...and not derivable: so queries are restricted to Σ-formulas. -/
theorem lem_not_prv : ¬ Prv [] (.or (.pred "P" []) (.imp (.pred "P" []) .bot)) := by
  intro h
  have h' := Prv.sound h lemModel false Tm.fvar (fun _ _ => trivial) (fun _ hB => nomatch hB)
  rcases h' with h₁ | h₂
  · rcases h₁ with h₁ | h₁
    · exact h₁
    · exact Bool.false_ne_true h₁
  · exact h₂ true (Or.inl rfl) (Or.inr rfl)

/-- `P ∨ Q` has no least Herbrand model: so programs are restricted to Horn clauses. -/
theorem or_no_least_model : ¬ ∃ I : String → List Tm → Prop,
    HTrue I (.or (.pred "P" []) (.pred "Q" [])) ∧
    ∀ J : String → List Tm → Prop, HTrue J (.or (.pred "P" []) (.pred "Q" [])) →
      ∀ p us, I p us → J p us := by
  rintro ⟨I, hI, hmin⟩
  have hP := hmin (fun p _ => p = "P") (Or.inl ((HTrue_pred Tm.lcAtList_nil).2 rfl))
  have hQ := hmin (fun p _ => p = "Q") (Or.inr ((HTrue_pred Tm.lcAtList_nil).2 rfl))
  rcases hI with h | h
  · exact absurd (hQ _ _ ((HTrue_pred Tm.lcAtList_nil).1 h)) (by decide)
  · exact absurd (hP _ _ ((HTrue_pred Tm.lcAtList_nil).1 h)) (by decide)

/-! ## Axioms

Nothing here uses choice.  The completeness half, `lloyd_completeness`,
instantiates the consequence at `herbrand1 (LHM RNone P)` and reads the
derivation off `Holds`; the soundness half is `Prv.sound`, which is free of
choice since `freshFor_notMem` (`Kit.lean`) was re-proved by byte size. -/

/-- info: 'LaxLogic.QLL.HFrame.evTm_lc' depends on axioms: [propext] -/
#guard_msgs in #print axioms HFrame.evTm_lc

/-- info: 'LaxLogic.QLL.HTrue_foralls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms HTrue_foralls

/-- info: 'LaxLogic.QLL.Holds.of_HTrue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Holds.of_HTrue

/-- info: 'LaxLogic.QLL.HTrue_LHM_form' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms HTrue_LHM_form

/-- info: 'LaxLogic.QLL.Tp_LHM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Tp_LHM

/-- info: 'LaxLogic.QLL.LHM_least' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms LHM_least

/-- info: 'LaxLogic.QLL.Holds.prv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Holds.prv

/-- info: 'LaxLogic.QLL.lloyd_completeness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lloyd_completeness

/-- info: 'LaxLogic.QLL.lloyd_prv_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lloyd_prv_iff

/-- info: 'LaxLogic.QLL.lloyd_consequence_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lloyd_consequence_iff

/-- info: 'LaxLogic.QLL.vanEmden_Kowalski' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vanEmden_Kowalski

/-- info: 'LaxLogic.QLL.lem_HTrue' depends on axioms: [propext] -/
#guard_msgs in #print axioms lem_HTrue

/-- info: 'LaxLogic.QLL.lem_not_prv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lem_not_prv

/-- info: 'LaxLogic.QLL.or_no_least_model' depends on axioms: [propext] -/
#guard_msgs in #print axioms or_no_least_model

end LaxLogic.QLL
