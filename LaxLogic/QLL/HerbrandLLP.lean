/-
# `LaxLogic.QLL.HerbrandLLP` — §7 of the CLP draft, worlds 0 and 1

Stage H3 of `docs/qll-herbrand-horn-plan.md`.

A program `Θ` of Definition 5.1 is split into Horn clauses (`Horn.lean`), and
two least Herbrand models are taken (`Herbrand.lean`):

* `llpI0 Θ`, of `Θ.horn0`: the modal clauses dropped.  This is the draft's `Π⁰`,
  which replaces every `◯P` by `true`.
* `llpI1 Θ`, of `Θ.horn`: every clause, `◯` read as the identity.  This is the
  draft's `Π¹`, which replaces `◯P` by `P`.

`llpModel Θ` puts them on two worlds `0 = false ≤ 1 = true`, all arrows modal,
nothing fallible: the draft's four-world canonical frame `0 ⇢ 1, 0 ⇢ 2 ⇢ 3`
restricted to `{0, 1}`.  World 2 needs the refinement of stage 4 and waits for
stage 5.

For a closed program (`Clause.WF`) and a closed Σ-formula `S`, Theorem 7.5 at
`i = 0, 1`:

    Θ.forms ⊢q S       ↔  0 ⊨ S  ↔  HTrue (llpI0 Θ) S
    Θ.forms ⊢q ◯_q S   ↔  1 ⊨ S  ↔  HTrue (llpI1 Θ) S     (every modal clause of Θ carries q)

and the completeness halves `Θ.forms ⊫ S → Θ.forms ⊢q S` and
`Θ.forms ⊫ ◯_q S → Θ.forms ⊢q ◯_q S` by Lloyd's route.  The extraction for
`◯_q S` is made of the stage 2 rules, at the level of `Prv`: `∧◯`, `∃◯` and
`val(⋆)` assemble `◯` of a clause body from `◯` of its atoms, then `⊃◯` fires a
modal clause and `impCirc` (CLP.lean) a non-modal one under `◯`.  So the Fig. 3
calculus is complete for `◯`-queries against Definition 5.1 programs.

The one-modality condition is needed (decision D5 of the plan): the model has
`RA = RE`, and `circAll_not_circEx` shows `◯∀ P ⊬ ◯∃ P`.

`llpCModel Θ` is the same model as one of the draft's own Kripke constraint
models (Definition 3.2), and agrees with `llpModel Θ` on `◯∃`-formulas by
`CModel.force_iff`.
-/
import LaxLogic.QLL.Herbrand
import LaxLogic.QLL.PaperSemantics

namespace LaxLogic.QLL

/-! ## The least model grows with the program -/

theorem Holds.mono {R : String → List Tm → Prop} {P P' : List Horn} (hPP : ∀ h ∈ P, h ∈ P')
    {φ : Form} (d : Holds R P φ) : Holds R P' φ := by
  induction d with
  | base hr => exact .base hr
  | top => exact .top
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | ex t ht _ ih => exact .ex t ht ih
  | fire hh hlen hts _ ih => exact .fire (hPP _ hh) hlen hts ih

/-! ## Forcing in a Herbrand frame -/

section
variable (F : HFrame) (I : F.W → String → List Tm → Prop)
  (hI : ∀ {w v : F.W} {p : String} {ts : List Tm}, F.le w v → I w p ts → I v p ts)

mutual
/-- All Herbrand models evaluate terms alike. -/
theorem HFrame.evTm_eq (G : HFrame) (J : G.W → String → List Tm → Prop)
    (hJ : ∀ {w v : G.W} {p : String} {ts : List Tm}, G.le w v → J w p ts → J v p ts)
    (ρ : String → Tm) (β : List Tm) :
    ∀ t : Tm, (F.model I hI).evTm ρ β t = (G.model J hJ).evTm ρ β t
  | .bvar _  => rfl
  | .fvar _  => rfl
  | .fn f ts => congrArg (Tm.fn f) (HFrame.evTms_eq G J hJ ρ β ts)
theorem HFrame.evTms_eq (G : HFrame) (J : G.W → String → List Tm → Prop)
    (hJ : ∀ {w v : G.W} {p : String} {ts : List Tm}, G.le w v → J w p ts → J v p ts)
    (ρ : String → Tm) (β : List Tm) :
    ∀ ts : List Tm, (F.model I hI).evTms ρ β ts = (G.model J hJ).evTms ρ β ts
  | []      => rfl
  | t :: ts => by
      show (F.model I hI).evTm ρ β t :: (F.model I hI).evTms ρ β ts = _
      rw [HFrame.evTm_eq G J hJ ρ β t, HFrame.evTms_eq G J hJ ρ β ts]
      rfl
end

/-- Σ-formulas are forced locally: at a world that is not fallible, exactly
when they are true in that world's Herbrand interpretation. -/
theorem HFrame.force_sigma {S : Form} (hS : IsSigma S) :
    ∀ (w : F.W) (β : List Tm), ¬ F.Fl w →
      ((F.model I hI).force S w Tm.fvar β ↔ (herbrand1 (I w)).force S () Tm.fvar β) := by
  induction hS with
  | top => intro _ _ _; exact Iff.rfl
  | pred P ts =>
      intro w β hw
      show F.Fl w ∨ I w P ((F.model I hI).evTms Tm.fvar β ts)
        ↔ False ∨ I w P ((herbrand1 (I w)).evTms Tm.fvar β ts)
      rw [HFrame.evTms_eq F I hI HFrame.one (fun _ => I w) (fun _ h => h) Tm.fvar β ts]
      exact ⟨fun h => h.imp (fun h => hw h) id, fun h => h.imp False.elim id⟩
  | and _ _ ih₁ ih₂ => intro w β hw; exact and_congr (ih₁ w β hw) (ih₂ w β hw)
  | or _ _ ih₁ ih₂ => intro w β hw; exact or_congr (ih₁ w β hw) (ih₂ w β hw)
  | ex _ ih => intro w β hw; exact exists_congr fun d => and_congr Iff.rfl (ih w (d :: β) hw)

theorem HFrame.force_forall {A : Form} {w : F.W} :
    (F.model I hI).force (.forall_ A) w Tm.fvar [] ↔
      ∀ v, F.le w v → ∀ t, Tm.lcAt 0 t → (F.model I hI).force (A.openAt 0 t) v Tm.fvar [] := by
  constructor
  · intro h v hv t ht
    have e := (F.model I hI).force_openAt Tm.fvar t ht A v []
    have ev : (F.model I hI).evTm Tm.fvar [] t = t := HFrame.evTm_lc F I hI [] t ht
    rw [ev] at e
    exact e.2 (h v hv t ht)
  · intro h v hv t ht
    have e := (F.model I hI).force_openAt Tm.fvar t ht A v []
    have ev : (F.model I hI).evTm Tm.fvar [] t = t := HFrame.evTm_lc F I hI [] t ht
    rw [ev] at e
    exact e.1 (h v hv t ht)

theorem HFrame.force_foralls : ∀ (m : Nat) (A : Form) (w : F.W),
    (F.model I hI).force (Form.foralls m A) w Tm.fvar [] ↔
      ∀ v, F.le w v → ∀ ts : List Tm, ts.length = m → (∀ t ∈ ts, Tm.lcAt 0 t) →
        (F.model I hI).force (Form.instAll ts A) v Tm.fvar []
  | 0, A, w => by
      constructor
      · intro h v hv ts hl _
        cases ts with
        | nil => exact (F.model I hI).hered A Tm.fvar [] hv h
        | cons _ _ => exact absurd hl (Nat.succ_ne_zero _)
      · intro h
        exact h w (F.refl w) [] rfl fun _ h => nomatch h
  | m + 1, A, w => by
      show (F.model I hI).force (.forall_ (Form.foralls m A)) w Tm.fvar [] ↔ _
      rw [HFrame.force_forall]
      constructor
      · intro h v hv ts hl hts
        cases ts with
        | nil => exact absurd hl.symm (Nat.succ_ne_zero m)
        | cons t ts =>
            have hl' : ts.length = m := Nat.succ.inj hl
            have h' := h v hv t (hts t (List.mem_cons.2 (Or.inl rfl)))
            rw [Form.openAt_foralls, Nat.zero_add, HFrame.force_foralls m] at h'
            have h'' := h' v (F.refl v) ts hl' fun u hu => hts u (List.mem_cons.2 (Or.inr hu))
            show (F.model I hI).force (Form.instAll ts (A.openAt ts.length t)) v Tm.fvar []
            rw [hl']
            exact h''
      · intro h v hv t ht
        rw [Form.openAt_foralls, Nat.zero_add, HFrame.force_foralls m]
        intro u hu ts hl hts
        have h' := h u (F.trans hv hu) (t :: ts) (by rw [List.length_cons, hl]) fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ht
          · exact hts x hx
        have e : Form.instAll (t :: ts) A = Form.instAll ts (A.openAt m t) := by
          show Form.instAll ts (A.openAt ts.length t) = _
          rw [hl]
        rw [e] at h'
        exact h'

end

/-! ## Programs of Definition 5.1, as Horn programs -/

/-- A clause is closed: its body mentions only its own bound variables. -/
def Clause.WF (c : Clause) : Prop := Form.lcAt c.arity c.body

theorem headVars_lc (m : Nat) : Tm.lcAtList m (headVars m) :=
  Tm.lcAtList_of_forall fun t ht => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ht
    exact List.mem_range.1 (List.mem_reverse.1 hi)

theorem Clause.toHorn_WF {c : Clause} (hc : c.WF) {h : Horn} (hh : h ∈ c.toHorn) : h.WF := by
  obtain ⟨⟨g, _⟩, _, rfl⟩ := List.mem_map.1 hh
  exact ⟨Form.lcAt_sel c.body g c.arity hc, headVars_lc c.arity⟩

theorem Clause.toHorn_fields {c : Clause} {h : Horn} (hh : h ∈ c.toHorn) :
    h.modal = c.modal ∧ h.q = c.q := by
  obtain ⟨⟨g, _⟩, _, rfl⟩ := List.mem_map.1 hh
  exact ⟨rfl, rfl⟩

/-- The clause formulas: the program as a context of `Prv`. -/
def Program.forms (Θ : Program) : List Form := Θ.map Clause.form

/-- All the Horn clauses of the program, `◯` kept (read by `Holds` as `Π¹`). -/
def Program.horn (Θ : Program) : List Horn := Θ.flatMap Clause.toHorn

/-- The Horn clauses of the non-modal clauses: the draft's `Π⁰`. -/
def Program.horn0 (Θ : Program) : List Horn :=
  Θ.flatMap fun c => bif c.modal then [] else c.toHorn

/-- Every modal clause carries the modality `q`. -/
def Program.OnlyQ (Θ : Program) (q : Q) : Prop := ∀ c ∈ Θ, c.modal = true → c.q = q

section
variable {Θ : Program}

theorem Program.mem_horn {h : Horn} : h ∈ Θ.horn ↔ ∃ c ∈ Θ, h ∈ c.toHorn := List.mem_flatMap

theorem Program.mem_horn0 {h : Horn} (hh : h ∈ Θ.horn0) :
    ∃ c ∈ Θ, c.modal = false ∧ h ∈ c.toHorn := by
  obtain ⟨c, hc, hh⟩ := List.mem_flatMap.1 hh
  cases hm : c.modal with
  | false => rw [hm] at hh; exact ⟨c, hc, hm, hh⟩
  | true => rw [hm] at hh; exact nomatch (hh : h ∈ ([] : List Horn))

theorem Program.mem_horn0_of {c : Clause} (hc : c ∈ Θ) (hm : c.modal = false) {h : Horn}
    (hh : h ∈ c.toHorn) : h ∈ Θ.horn0 :=
  List.mem_flatMap.2 ⟨c, hc, by rw [hm]; exact hh⟩

theorem Program.horn0_sub {h : Horn} (hh : h ∈ Θ.horn0) : h ∈ Θ.horn := by
  obtain ⟨c, hc, -, hhc⟩ := Program.mem_horn0 hh
  exact Program.mem_horn.2 ⟨c, hc, hhc⟩

theorem Program.horn0_nonmodal : ∀ h ∈ Θ.horn0, h.modal = false := fun h hh => by
  obtain ⟨c, _, hm, hhc⟩ := Program.mem_horn0 hh
  rw [(Clause.toHorn_fields hhc).1]
  exact hm

/-- Each Horn clause of the program follows from the program. -/
theorem Program.prv_horn {h : Horn} (hh : h ∈ Θ.horn) : Prv Θ.forms h.form := by
  obtain ⟨c, hc, hhc⟩ := Program.mem_horn.1 hh
  exact (Clause.prv_toHorn c hhc).weaken fun B hB => by
    rcases List.mem_cons.1 hB with rfl | hB
    · exact List.mem_map.2 ⟨c, hc, rfl⟩
    · exact nomatch hB

end

/-! ## The model -/

/-- The interpretation at worlds `0 = false` and `1 = true`. -/
def I01 (I₀ I₁ : String → List Tm → Prop) : Bool → String → List Tm → Prop
  | false => I₀
  | true  => I₁

theorem I01_hered {I₀ I₁ : String → List Tm → Prop} (h01 : ∀ p us, I₀ p us → I₁ p us) :
    ∀ {w v : HFrame.two.W} {p : String} {ts : List Tm},
      HFrame.two.le w v → I01 I₀ I₁ w p ts → I01 I₀ I₁ v p ts := fun {w v _ _} hwv hI => by
  rcases hwv with rfl | rfl
  · cases v
    · exact hI
    · exact h01 _ _ hI
  · cases w
    · exact h01 _ _ hI
    · exact hI

/-- Two worlds `0 ≤ 1`, all arrows modal, nothing fallible. -/
abbrev herbrand2 (I₀ I₁ : String → List Tm → Prop) (h01 : ∀ p us, I₀ p us → I₁ p us) : KModel :=
  HFrame.two.model (I01 I₀ I₁) (I01_hered h01)

/-- World 0: the least Herbrand model of `Π⁰`. -/
abbrev llpI0 (Θ : Program) : String → List Tm → Prop := LHM RNone Θ.horn0

/-- World 1: the least Herbrand model of `Π¹`. -/
abbrev llpI1 (Θ : Program) : String → List Tm → Prop := LHM RNone Θ.horn

theorem llpI0_le (Θ : Program) : ∀ p us, llpI0 Θ p us → llpI1 Θ p us :=
  fun _ _ h => Holds.mono (fun _ hh => Program.horn0_sub hh) h

/-- The LLP Herbrand model: §7's canonical frame on the worlds `{0, 1}`. -/
abbrev llpModel (Θ : Program) : KModel := herbrand2 (llpI0 Θ) (llpI1 Θ) (llpI0_le Θ)

section
variable {Θ : Program}

theorem llpModel_sigma {S : Form} (hS : IsSigma S) (w : Bool) :
    (llpModel Θ).force S w Tm.fvar [] ↔ HTrue (I01 (llpI0 Θ) (llpI1 Θ) w) S :=
  HFrame.force_sigma HFrame.two (I01 (llpI0 Θ) (llpI1 Θ)) (I01_hered (llpI0_le Θ)) hS w [] id

/-- At world 0, `◯_q S` is `S` at world 1. -/
theorem llpModel_circ {q : Q} {S : Form} (hS : IsSigma S) :
    (llpModel Θ).force (.circ q S) false Tm.fvar [] ↔ HTrue (llpI1 Θ) S := by
  have hloc := llpModel_sigma (Θ := Θ) hS true
  cases q
  · constructor
    · intro h
      obtain ⟨u, hu, hSu⟩ := h true (Or.inl rfl)
      rcases hu with hu | rfl
      · exact absurd hu (by decide)
      · exact hloc.1 hSu
    · intro h _ _
      exact ⟨true, Or.inr rfl, hloc.2 h⟩
  · constructor
    · intro h
      obtain ⟨u, hu, hSu⟩ := h true (Or.inl rfl)
      rcases hu with hu | rfl
      · exact absurd hu (by decide)
      · exact hloc.1 hSu
    · intro h _ _
      exact ⟨true, Or.inr rfl, hloc.2 h⟩

/-- Lemma 7.2 on the worlds `{0, 1}`: world 0 forces every clause. -/
theorem llpModel_clause (hΘ : ∀ c ∈ Θ, c.WF) {c : Clause} (hc : c ∈ Θ) :
    (llpModel Θ).force c.form false Tm.fvar [] := by
  show (llpModel Θ).force (Form.foralls c.arity (.imp c.body c.headForm)) false Tm.fvar []
  refine (HFrame.force_foralls HFrame.two (I01 (llpI0 Θ) (llpI1 Θ)) (I01_hered (llpI0_le Θ))
    c.arity _ false).2 fun v _ ts hlen hts => ?_
  rw [Form.instAll_imp]
  intro v' _ hb
  have hb' := (llpModel_sigma (c.body_sigma.instAll ts) v').1 hb
  obtain ⟨g, hg, hbg⟩ :=
    ((herbrand1 _).force_iff_sel (c.body_sigma.instAll ts) () Tm.fvar []).1 hb'
  rw [ind_instAll] at hg
  rw [sel_instAll] at hbg
  have hh : (⟨c.arity, sel c.body g, c.body_sigma.pp_sel hg, c.head, headVars c.arity,
      c.modal, c.q⟩ : Horn) ∈ c.toHorn :=
    List.mem_map.2 ⟨⟨g, hg⟩, List.mem_attach _ _, rfl⟩
  have hlc : Form.lcAt 0 (Form.instAll ts (sel c.body g)) :=
    Form.lcAt_instAll ts _ hts (by rw [hlen]; exact Form.lcAt_sel _ _ _ (hΘ c hc))
  have hargs : Tm.lcAtList 0 (Tm.instAllList ts (headVars c.arity)) :=
    Tm.lcAtList_instAllList ts _ hts (by rw [hlen]; exact headVars_lc _)
  have hpp : IsPP (Form.instAll ts (sel c.body g)) := (c.body_sigma.pp_sel hg).instAll ts
  have hbody1 : Holds RNone Θ.horn (Form.instAll ts (sel c.body g)) := by
    cases v'
    · exact Holds.mono (fun _ hh => Program.horn0_sub hh)
        (Holds.of_HTrue (R := RNone) (P := Θ.horn0) hpp hlc hbg)
    · exact Holds.of_HTrue (R := RNone) (P := Θ.horn) hpp hlc hbg
  have hfire1 : llpI1 Θ c.head (Tm.instAllList ts (headVars c.arity)) :=
    Holds.fire (Program.mem_horn.2 ⟨c, hc, hh⟩) hlen hts hbody1
  unfold Clause.headForm
  cases hm : c.modal
  · show (llpModel Θ).force (Form.instAll ts (.pred c.head (headVars c.arity))) v' Tm.fvar []
    rw [Form.instAll_pred]
    refine (llpModel_sigma (.pred _ _) v').2 ((HTrue_pred hargs).2 ?_)
    cases v'
    · have hh0 := Program.mem_horn0_of hc hm hh
      exact Holds.fire hh0 hlen hts (Holds.of_HTrue (R := RNone) (P := Θ.horn0) hpp hlc hbg)
    · exact hfire1
  · show (llpModel Θ).force
      (Form.instAll ts (.circ c.q (.pred c.head (headVars c.arity)))) v' Tm.fvar []
    rw [Form.instAll_circ, Form.instAll_pred]
    have hat := (llpModel_sigma (Θ := Θ) (.pred c.head (Tm.instAllList ts (headVars c.arity))) true).2
      ((HTrue_pred hargs).2 hfire1)
    cases c.q
    · exact fun _ _ => ⟨true, Or.inr rfl, hat⟩
    · exact fun _ _ => ⟨true, Or.inr rfl, hat⟩

theorem llp_sat (hΘ : ∀ c ∈ Θ, c.WF) : ∀ B ∈ Θ.forms, (llpModel Θ).force B false Tm.fvar [] :=
  fun B hB => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hB
    exact llpModel_clause hΘ hc

/-! ## Extraction -/

/-- What holds in `Π¹`'s least model holds under `◯_q`, provided every modal
clause carries `q`.  Each case is a derived rule of Fig. 3. -/
theorem Holds.prv_circ {q : Q} (hq : Θ.OnlyQ q) {φ : Form} (d : Holds RNone Θ.horn φ) :
    Prv Θ.forms (.circ q φ) := by
  induction d with
  | base hr => exact (hr : False).elim
  | top => exact .circI .topI
  | and _ _ ih₁ ih₂ =>
      refine .circE ih₁ (.circE (ih₂.weaken fun _ h => List.mem_cons.2 (Or.inr h))
        (.circI (.andI (.var ?_) (.var ?_))))
      · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      · exact List.mem_cons.2 (Or.inl rfl)
  | ex t ht _ ih => exact .circE ih (.circI (.exI t ht (.var (List.mem_cons.2 (Or.inl rfl)))))
  | @fire h ts hh hlen hts _ ih =>
      have hf : Prv Θ.forms (Form.foralls ts.length (.imp h.body h.headForm)) := by
        rw [hlen]; exact Program.prv_horn hh
      have hi := Prv.allEs ts hts hf
      rw [Form.instAll_imp] at hi
      have hi' : Prv (Form.instAll ts h.body :: Θ.forms) (Form.instAll ts h.headForm) :=
        .impE (hi.weaken fun _ h => List.mem_cons.2 (Or.inr h)) (.var (List.mem_cons.2 (Or.inl rfl)))
      have e : Form.instAll ts h.headAtom = .pred h.head (Tm.instAllList ts h.args) :=
        Form.instAll_pred ts h.head h.args
      refine .circE ih ?_
      obtain ⟨c, hc, hhc⟩ := Program.mem_horn.1 hh
      obtain ⟨hmod, hqq⟩ := Clause.toHorn_fields hhc
      unfold Horn.headForm at hi'
      cases hm : h.modal
      · rw [hm] at hi'
        have hi'' : Prv (Form.instAll ts h.body :: Θ.forms) (Form.instAll ts h.headAtom) := hi'
        rw [e] at hi''
        exact .circI hi''
      · rw [hm] at hi'
        have hi'' : Prv (Form.instAll ts h.body :: Θ.forms)
            (Form.instAll ts (.circ h.q h.headAtom)) := hi'
        rw [Form.instAll_circ, e, hqq, hq c hc (hmod ▸ hm)] at hi''
        exact hi''

/-! ## Theorem 7.5 at worlds 0 and 1 -/

theorem llp_prv_of_HTrue0 {S : Form} (hS : IsSigma S) (hc : Form.lcAt 0 S)
    (h : HTrue (llpI0 Θ) S) : Prv Θ.forms S := by
  obtain ⟨g, hg, h⟩ := ((herbrand1 _).force_iff_sel hS () Tm.fvar []).1 h
  have d := Holds.prv Program.horn0_nonmodal
    (Holds.of_HTrue (R := RNone) (P := Θ.horn0) (hS.pp_sel hg) (Form.lcAt_sel S g 0 hc) h)
  refine Prv.of_sel hS hg (Prv.cutAll (fun A hA => ?_) d)
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hA
  exact Program.prv_horn (Program.horn0_sub hh)

theorem llp_prv_circ_of_HTrue1 {q : Q} (hq : Θ.OnlyQ q) {S : Form} (hS : IsSigma S)
    (hc : Form.lcAt 0 S) (h : HTrue (llpI1 Θ) S) : Prv Θ.forms (.circ q S) := by
  obtain ⟨g, hg, h⟩ := ((herbrand1 _).force_iff_sel hS () Tm.fvar []).1 h
  have d := Holds.prv_circ hq
    (Holds.of_HTrue (R := RNone) (P := Θ.horn) (hS.pp_sel hg) (Form.lcAt_sel S g 0 hc) h)
  exact .circE d (.circI (Prv.of_sel hS hg (.var (List.mem_cons.2 (Or.inl rfl)))))

/-- Completeness for Σ-queries, by Lloyd's route. -/
theorem llp_completeness0 (hΘ : ∀ c ∈ Θ, c.WF) {S : Form} (hS : IsSigma S)
    (hc : Form.lcAt 0 S) (h : Consequence Θ.forms S) : Prv Θ.forms S :=
  llp_prv_of_HTrue0 hS hc ((llpModel_sigma hS false).1
    (h (llpModel Θ) false Tm.fvar (fun _ _ => trivial) (llp_sat hΘ)))

/-- Completeness for `◯`-queries, by Lloyd's route. -/
theorem llp_completeness1 (hΘ : ∀ c ∈ Θ, c.WF) {q : Q} (hq : Θ.OnlyQ q) {S : Form}
    (hS : IsSigma S) (hc : Form.lcAt 0 S) (h : Consequence Θ.forms (.circ q S)) :
    Prv Θ.forms (.circ q S) :=
  llp_prv_circ_of_HTrue1 hq hS hc ((llpModel_circ hS).1
    (h (llpModel Θ) false Tm.fvar (fun _ _ => trivial) (llp_sat hΘ)))

/-- **Theorem 7.5, `i = 0`**: `S` is a 0-consequence iff `0 ⊨ S`. -/
theorem thm_7_5_world0 (hΘ : ∀ c ∈ Θ, c.WF) {S : Form} (hS : IsSigma S) (hc : Form.lcAt 0 S) :
    Prv Θ.forms S ↔ (llpModel Θ).force S false Tm.fvar [] :=
  ⟨fun h => Prv.sound h (llpModel Θ) false Tm.fvar (fun _ _ => trivial) (llp_sat hΘ),
   fun h => llp_prv_of_HTrue0 hS hc ((llpModel_sigma hS false).1 h)⟩

/-- **Theorem 7.5, `i = 1`**: `S` is a 1-consequence iff `1 ⊨ S`. -/
theorem thm_7_5_world1 (hΘ : ∀ c ∈ Θ, c.WF) {q : Q} (hq : Θ.OnlyQ q) {S : Form}
    (hS : IsSigma S) (hc : Form.lcAt 0 S) :
    Prv Θ.forms (.circ q S) ↔ (llpModel Θ).force S true Tm.fvar [] :=
  ⟨fun h => (llpModel_sigma hS true).2 ((llpModel_circ hS).1
      (Prv.sound h (llpModel Θ) false Tm.fvar (fun _ _ => trivial) (llp_sat hΘ))),
   fun h => llp_prv_circ_of_HTrue1 hq hS hc ((llpModel_sigma hS true).1 h)⟩

end

/-! ## The same model in the draft's own terms -/

/-- `llpModel Θ` as one of the draft's Kripke constraint models (Definition 3.2):
one modal relation, here equal to `Ri`. -/
def llpCModel (Θ : Program) : CModel where
  S := Bool
  D := Tm
  Dom _ t := Tm.lcAt 0 t
  Ri := HFrame.two.le
  Rm := HFrame.two.le
  F _ := False
  fn f ds := .fn f ds
  I := I01 (llpI0 Θ) (llpI1 Θ)
  refl_i := HFrame.two.refl
  trans_i := HFrame.two.trans
  refl_m := HFrame.two.refl
  trans_m := HFrame.two.trans
  m_sub_i h := h
  hered_F _ h := h
  dom_mono _ h := h
  hered_I := I01_hered (llpI0_le Θ)
  fn_dom h := Tm.lcAtList_of_forall h
  d₀ := .fn "c" []
  dom_d₀ _ := trivial

/-- Definition 3.3 in `llpCModel Θ` is forcing in `llpModel Θ`, on `◯∃`-formulas. -/
theorem llpCModel_force_iff {Θ : Program} {A : Form} (hA : A.OnlyEx) (w : Bool) :
    (llpCModel Θ).force A w Tm.fvar [] ↔ (llpModel Θ).force A w Tm.fvar [] :=
  (llpCModel Θ).force_iff A hA w Tm.fvar []

/-! ## Why one modality -/

/-- Two states `false ≤ true`: `RA` the order, `RE` equality, `P` true at `true`. -/
def mixedModel : KModel where
  S := Bool
  D := Unit
  Dom _ _ := True
  Ri s v := s = false ∨ v = true
  RA s v := s = false ∨ v = true
  RE s v := s = v
  Fl _ := False
  refl_i := HFrame.two.refl
  trans_i := HFrame.two.trans
  refl_A := HFrame.two.refl
  trans_A := HFrame.two.trans
  sub_A h := h
  refl_E _ := rfl
  trans_E h₁ h₂ := h₁.trans h₂
  sub_E h := by subst h; exact HFrame.two.refl _
  dom_mono _ _ := trivial
  d₀ := ()
  dom_d₀ _ := trivial
  hered_Fl _ h := h
  fn _ _ := ()
  I s _ _ := s = true
  hered_I h hs := by
    rcases h with rfl | rfl
    · exact (Bool.false_ne_true hs).elim
    · rfl
  fn_dom _ := trivial

/-- `◯∀ P ⊬ ◯∃ P`: the two lax modalities are not interchangeable, so the
extraction for `◯_q`-queries needs every modal clause to carry `q`. -/
theorem circAll_not_circEx : ¬ Prv [.circ .all (.pred "P" [])] (.circ .ex (.pred "P" [])) := by
  intro h
  have hA : mixedModel.force (.circ .all (.pred "P" [])) false (fun _ => ()) [] :=
    fun _ _ => ⟨true, Or.inr rfl, Or.inr rfl⟩
  have hE := Prv.sound h mixedModel false (fun _ => ()) (fun _ _ => trivial) fun B hB => by
    rcases List.mem_cons.1 hB with rfl | hB
    · exact hA
    · exact nomatch hB
  obtain ⟨u, hu, hP⟩ := hE false (Or.inl rfl)
  cases hu
  rcases hP with h | h
  · exact h
  · exact Bool.false_ne_true h

/-! ## Axioms

Both completeness halves use no choice; `thm_7_5_world0/1` take it in only
through `Prv.sound`, as in `Herbrand.lean`. -/

/-- info: 'LaxLogic.QLL.HFrame.force_sigma' depends on axioms: [propext] -/
#guard_msgs in #print axioms HFrame.force_sigma

/-- info: 'LaxLogic.QLL.HFrame.force_foralls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms HFrame.force_foralls

/-- info: 'LaxLogic.QLL.llpModel_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms llpModel_clause

/-- info: 'LaxLogic.QLL.Holds.prv_circ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Holds.prv_circ

/-- info: 'LaxLogic.QLL.llp_completeness0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms llp_completeness0

/-- info: 'LaxLogic.QLL.llp_completeness1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms llp_completeness1

/-- info: 'LaxLogic.QLL.thm_7_5_world0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms thm_7_5_world0

/-- info: 'LaxLogic.QLL.thm_7_5_world1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms thm_7_5_world1

/-- info: 'LaxLogic.QLL.llpCModel_force_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms llpCModel_force_iff

/-- info: 'LaxLogic.QLL.circAll_not_circEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms circAll_not_circEx

end LaxLogic.QLL
