/-
# `LaxLogic.QLL.Kripke` — Kripke semantics for QLL

The *other* semantics.  `Interp.lean` reads a formula as a refinement type and
a proof term as a constraint refining it; that reading is into Lean's own logic
and is finer than the calculus — it separates `◯∀` from `◯∃`, which no rule of
Fig. 5 can.  This file gives the model theory of the abstract logic instead:
states, an intuitionistic order, and one reachability relation per modality.

## The frame

Fairtlough–Mendler constraint frames (`PLLKripke.lean`, Definition 3.1),
extended in two ways.

**Two modal relations.**  Fig. 5's `◯E` requires the same `Q` in both premises
and the conclusion — the figure permits no mixing — so the calculus never
connects the modalities at all: QLL is first-order intuitionistic logic with
*two independent* lax modalities.  A semantics with one relation would validate
`◯∀A ⊣⊢ ◯∃A`, which is not derivable, so each gets its own.  The *clause* is
the same for both; only the relation differs.

**Varying domains.**  One domain `D` with a monotone local domain
`Dom : S → D → Prop`, rather than a family of types indexed by states.  Same
data — take the union one way, the fibres the other — but an assignment is then
a plain function and moving one to a successor needs no coercion.  Increasing,
not constant: constant domains validate `∀x(A ∨ B x) ⊃ A ∨ ∀x B x`, which is
not intuitionistically valid.

The `∀` clause ranges over the domain of the **successor**, not of the current
state.  With the domain taken at the current state satisfaction is not
hereditary.

**Fallible states.**  Not a device introduced here: `◯⊥` is consistent — no
rule of Fig. 5 derives `⊥` from it — so the semantics needs a state reachable
by `Rm` at which `⊥` holds, and such a state must then force everything.
Explosion at `∃` is what forces every *local* domain to be non-empty.

## Two environments

The syntax is locally nameless, so satisfaction carries two: `ρ` for the named
free individuals and `β` for the de Bruijn indices, innermost first.  Only the
quantifier clauses touch `β`; only the eigenvariable rules touch `ρ`.  This is
the same split `Refines` uses, so the two semantics line up.
-/
import LaxLogic.QLL.Lc

namespace LaxLogic.QLL

/-- A constraint frame with varying domains and one reachability relation per
modality. -/
structure QFrame where
  /-- States. -/
  S : Type
  /-- The domain of individuals, globally. -/
  D : Type
  /-- The local domain at a state. -/
  Dom : S → D → Prop
  /-- Intuitionistic accessibility. -/
  Ri : S → S → Prop
  /-- Reachability for `◯∀`. -/
  RA : S → S → Prop
  /-- Reachability for `◯∃`. -/
  RE : S → S → Prop
  /-- Fallible states. -/
  Fl : S → Prop
  refl_i : ∀ s, Ri s s
  trans_i : ∀ {s v u}, Ri s v → Ri v u → Ri s u
  refl_A : ∀ s, RA s s
  trans_A : ∀ {s v u}, RA s v → RA v u → RA s u
  sub_A : ∀ {s v}, RA s v → Ri s v
  refl_E : ∀ s, RE s s
  trans_E : ∀ {s v u}, RE s v → RE v u → RE s u
  sub_E : ∀ {s v}, RE s v → Ri s v
  /-- Domains increase. -/
  dom_mono : ∀ {s v d}, Ri s v → Dom s d → Dom v d
  /-- A distinguished individual, in every local domain.  It makes explosion
  work at `∃`, and it is the value a loose index takes — which cannot arise for
  a locally closed formula, but must be *some* fixed thing if changing the
  valuation off a formula's free names is to leave forcing alone. -/
  d₀ : D
  dom_d₀ : ∀ s, Dom s d₀
  hered_Fl : ∀ {s v}, Ri s v → Fl s → Fl v

/-- A frame together with an interpretation of the signature.  Function
symbols are rigid; predicate symbols are hereditary in the state. -/
structure KModel extends QFrame where
  /-- Interpretation of the function symbols, the same at every state. -/
  fn : String → List D → D
  /-- Interpretation of the predicate symbols. -/
  I : S → String → List D → Prop
  hered_I : ∀ {s v P ds}, Ri s v → I s P ds → I v P ds
  /-- Local domains are closed under the function symbols. -/
  fn_dom : ∀ {s : S} {f : String} {ds : List D}, (∀ d ∈ ds, Dom s d) → Dom s (fn f ds)

namespace KModel

variable (M : KModel)

/-! ## Terms -/

mutual
/-- The value of a term: `β` for the indices, `ρ` for the names. -/
def evTm (ρ : String → M.D) (β : List M.D) : Tm → M.D
  | .bvar i  => β[i]?.getD M.d₀
  | .fvar x  => ρ x
  | .fn f ts => M.fn f (evTms ρ β ts)
/-- `evTm` on an argument list. -/
def evTms (ρ : String → M.D) (β : List M.D) : List Tm → List M.D
  | []      => []
  | t :: ts => evTm ρ β t :: evTms ρ β ts
end

/-! ## Forcing -/

/-- `M ⊨ A` at a state, under an assignment.  Atoms explode at a fallible
state; `⊥` holds exactly there. -/
def force : Form → M.S → (String → M.D) → List M.D → Prop
  | .top,         _, _, _ => True
  | .bot,         s, _, _ => M.Fl s
  | .pred P ts,   s, ρ, β => M.Fl s ∨ M.I s P (M.evTms ρ β ts)
  | .and A B,     s, ρ, β => force A s ρ β ∧ force B s ρ β
  | .or A B,      s, ρ, β => force A s ρ β ∨ force B s ρ β
  | .imp A B,     s, ρ, β => ∀ v, M.Ri s v → force A v ρ β → force B v ρ β
  | .circ .all A, s, ρ, β => ∀ v, M.Ri s v → ∃ u, M.RA v u ∧ force A u ρ β
  | .circ .ex A,  s, ρ, β => ∀ v, M.Ri s v → ∃ u, M.RE v u ∧ force A u ρ β
  | .forall_ A,   s, ρ, β => ∀ v, M.Ri s v → ∀ d, M.Dom v d → force A v ρ (d :: β)
  | .exists_ A,   s, ρ, β => ∃ d, M.Dom s d ∧ force A s ρ (d :: β)

@[inherit_doc] notation:50 M " ; " s ", " ρ ", " β " ⊩ " A => KModel.force M A s ρ β

/-! ## The two structural facts -/

/-- Heredity: forcing survives passage to a successor. -/
theorem hered : ∀ (A : Form) {s v : M.S} (ρ : String → M.D) (β : List M.D),
    M.Ri s v → M.force A s ρ β → M.force A v ρ β := by
  intro A
  induction A with
  | top => intro _ _ _ _ _ _; trivial
  | bot => intro _ _ _ _ h hs; exact M.hered_Fl h hs
  | pred _ _ => intro _ _ _ _ h hs; exact hs.imp (M.hered_Fl h) (M.hered_I h)
  | and _ _ ih₁ ih₂ => intro _ _ ρ β h hs; exact ⟨ih₁ ρ β h hs.1, ih₂ ρ β h hs.2⟩
  | or _ _ ih₁ ih₂ => intro _ _ ρ β h hs; exact hs.imp (ih₁ ρ β h) (ih₂ ρ β h)
  | imp _ _ _ _ => intro _ _ _ _ h hs u hu; exact hs u (M.trans_i h hu)
  | circ q _ _ =>
      cases q <;> intro _ _ _ _ h hs u hu <;> exact hs u (M.trans_i h hu)
  | forall_ _ _ => intro _ _ _ _ h hs u hu; exact hs u (M.trans_i h hu)
  | exists_ _ ih =>
      intro _ _ ρ β h hs
      obtain ⟨d, hd, hA⟩ := hs
      exact ⟨d, M.dom_mono h hd, ih ρ (d :: β) h hA⟩

/-- Explosion: a fallible state forces everything. -/
theorem force_of_fallible : ∀ (A : Form) {s : M.S} (ρ : String → M.D) (β : List M.D),
    M.Fl s → M.force A s ρ β := by
  intro A
  induction A with
  | top => intro _ _ _ _; trivial
  | bot => intro _ _ _ h; exact h
  | pred _ _ => intro _ _ _ h; exact Or.inl h
  | and _ _ ih₁ ih₂ => intro _ ρ β h; exact ⟨ih₁ ρ β h, ih₂ ρ β h⟩
  | or _ _ ih₁ _ => intro _ ρ β h; exact Or.inl (ih₁ ρ β h)
  | imp _ _ _ ih₂ => intro _ ρ β h v hv _; exact ih₂ ρ β (M.hered_Fl hv h)
  | circ q _ ih =>
      cases q <;>
        · intro _ ρ β h v hv
          exact ⟨v, by first | exact M.refl_A v | exact M.refl_E v,
                 ih ρ β (M.hered_Fl hv h)⟩
  | forall_ _ ih => intro _ ρ β h v hv d _; exact ih ρ (d :: β) (M.hered_Fl hv h)
  | exists_ _ ih =>
      intro s ρ β h
      exact ⟨M.d₀, M.dom_d₀ s, ih ρ (M.d₀ :: β) h⟩

/-! ## Values stay in the local domain

An assignment is *at* a state when every name it uses is in that state's
domain; the same for the index environment.  Terms then evaluate into the
domain, which is what `∀E` needs to instantiate. -/

/-- Every name is interpreted in the local domain. -/
def Assign (s : M.S) (ρ : String → M.D) : Prop := ∀ x, M.Dom s (ρ x)

theorem Assign.mono {s v : M.S} {ρ : String → M.D} (h : M.Ri s v) (hρ : M.Assign s ρ) :
    M.Assign v ρ := fun x => M.dom_mono h (hρ x)

mutual
theorem evTm_dom {s : M.S} {ρ : String → M.D} {β : List M.D}
    (hρ : M.Assign s ρ) (hβ : ∀ d ∈ β, M.Dom s d) :
    ∀ t : Tm, M.Dom s (M.evTm ρ β t)
  | .bvar i => by
      show M.Dom s (β[i]?.getD M.d₀)
      cases h : β[i]? with
      | none => simpa using M.dom_d₀ s
      | some d => simpa using hβ d (List.mem_of_getElem? h)
  | .fvar x => hρ x
  | .fn _ ts => M.fn_dom (evTms_dom hρ hβ ts)
theorem evTms_dom {s : M.S} {ρ : String → M.D} {β : List M.D}
    (hρ : M.Assign s ρ) (hβ : ∀ d ∈ β, M.Dom s d) :
    ∀ ts : List Tm, ∀ d ∈ M.evTms ρ β ts, M.Dom s d
  | [],      _, h => by simp [KModel.evTms] at h
  | t :: ts, d, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact evTm_dom hρ hβ t
      · exact evTms_dom hρ hβ ts d h
end

/-! ## Changing the valuation off a formula's free names -/

mutual
theorem evTm_congr {ρ ρ' : String → M.D} {β : List M.D} :
    ∀ (t : Tm), (∀ x ∈ Tm.fv t, ρ x = ρ' x) → M.evTm ρ β t = M.evTm ρ' β t
  | .bvar _,  _ => rfl
  | .fvar x,  h => h x (by simp [Tm.fv])
  | .fn _ ts, h => by simp [KModel.evTm, evTms_congr ts h]
theorem evTms_congr {ρ ρ' : String → M.D} {β : List M.D} :
    ∀ (ts : List Tm), (∀ x ∈ Tm.fvList ts, ρ x = ρ' x) → M.evTms ρ β ts = M.evTms ρ' β ts
  | [],      _ => rfl
  | t :: ts, h => by
      simp [KModel.evTms, evTm_congr t (fun x hx => h x (by simp [Tm.fvList, hx])),
            evTms_congr ts (fun x hx => h x (by simp [Tm.fvList, hx]))]
end

theorem force_congr : ∀ (A : Form) (s : M.S) (ρ ρ' : String → M.D) (β : List M.D),
    (∀ x ∈ A.fv, ρ x = ρ' x) → (M.force A s ρ β ↔ M.force A s ρ' β) := by
  intro A
  induction A with
  | top | bot => intro _ _ _ _ _; exact Iff.rfl
  | pred _ ts =>
      intro s ρ ρ' β h
      show (M.Fl s ∨ _) ↔ (M.Fl s ∨ _)
      rw [M.evTms_congr ts h]
  | and _ _ ih₁ ih₂ =>
      intro s ρ ρ' β h
      exact and_congr (ih₁ s ρ ρ' β (fun x hx => h x (by simp [Form.fv, hx])))
                      (ih₂ s ρ ρ' β (fun x hx => h x (by simp [Form.fv, hx])))
  | or _ _ ih₁ ih₂ =>
      intro s ρ ρ' β h
      exact or_congr (ih₁ s ρ ρ' β (fun x hx => h x (by simp [Form.fv, hx])))
                     (ih₂ s ρ ρ' β (fun x hx => h x (by simp [Form.fv, hx])))
  | imp _ _ ih₁ ih₂ =>
      intro s ρ ρ' β h
      exact forall_congr' fun v => imp_congr Iff.rfl
        (imp_congr (ih₁ v ρ ρ' β (fun x hx => h x (by simp [Form.fv, hx])))
                   (ih₂ v ρ ρ' β (fun x hx => h x (by simp [Form.fv, hx]))))
  | circ q _ ih =>
      intro s ρ ρ' β h
      cases q <;>
        exact forall_congr' fun v => imp_congr Iff.rfl
          (exists_congr fun u => and_congr Iff.rfl (ih u ρ ρ' β h))
  | forall_ _ ih =>
      intro s ρ ρ' β h
      exact forall_congr' fun v => imp_congr Iff.rfl
        (forall_congr' fun d => imp_congr Iff.rfl (ih v ρ ρ' (d :: β) h))
  | exists_ _ ih =>
      intro s ρ ρ' β h
      exact exists_congr fun d => and_congr Iff.rfl (ih s ρ ρ' (d :: β) h)

/-! ## Opening

Substituting a closed term for the outermost bound individual is the same as
extending the index environment with its value.  Stated at the environments
soundness uses — the opened variable last — so that past the end of `β` both
sides are out of range and answer `d₀`; no local closedness of the *formula* is
then needed. -/

theorem getElem?_snoc {α : Type} (β : List α) (e : α) : (β ++ [e])[β.length]? = some e := by
  induction β with
  | nil => rfl
  | cons _ β ih => simpa using ih

theorem getD_snoc {α : Type} (d e : α) :
    ∀ (β : List α) (i : Nat), i ≠ β.length → (β ++ [e])[i]?.getD d = β[i]?.getD d
  | [],       0,     h => absurd rfl h
  | [],       _ + 1, _ => rfl
  | _ :: _,   0,     _ => rfl
  | a :: β,   i + 1, h => by simpa using getD_snoc d e β i (fun hi => h (by simp [hi]))

mutual
theorem evTm_lc (ρ : String → M.D) (β β' : List M.D) :
    ∀ (t : Tm), Tm.lcAt 0 t → M.evTm ρ β t = M.evTm ρ β' t
  | .bvar i,  h => absurd h (Nat.not_lt_zero i)
  | .fvar _,  _ => rfl
  | .fn _ ts, h => by simp [KModel.evTm, evTms_lc ρ β β' ts h]
theorem evTms_lc (ρ : String → M.D) (β β' : List M.D) :
    ∀ (ts : List Tm), Tm.lcAtList 0 ts → M.evTms ρ β ts = M.evTms ρ β' ts
  | [],      _ => rfl
  | t :: ts, h => by
      simp [KModel.evTms, evTm_lc ρ β β' t h.1, evTms_lc ρ β β' ts h.2]
end

mutual
theorem evTm_openAt (ρ : String → M.D) (u : Tm) (hu : Tm.lcAt 0 u) (β : List M.D) :
    ∀ (t : Tm), M.evTm ρ β (Tm.openAt β.length u t)
      = M.evTm ρ (β ++ [M.evTm ρ [] u]) t
  | .bvar i => by
      by_cases h : i = β.length
      · subst h
        simp only [Tm.openAt, KModel.evTm, getElem?_snoc]
        exact M.evTm_lc ρ β [] u hu
      · simp only [Tm.openAt, if_neg h, KModel.evTm]
        exact (getD_snoc M.d₀ _ β i h).symm
  | .fvar _ => rfl
  | .fn _ ts => by simp [Tm.openAt, KModel.evTm, evTms_openAt ρ u hu β ts]
theorem evTms_openAt (ρ : String → M.D) (u : Tm) (hu : Tm.lcAt 0 u) (β : List M.D) :
    ∀ (ts : List Tm), M.evTms ρ β (Tm.openAtList β.length u ts)
      = M.evTms ρ (β ++ [M.evTm ρ [] u]) ts
  | []      => rfl
  | t :: ts => by
      simp [Tm.openAtList, KModel.evTms, evTm_openAt ρ u hu β t, evTms_openAt ρ u hu β ts]
end

theorem force_openAt (ρ : String → M.D) (u : Tm) (hu : Tm.lcAt 0 u) :
    ∀ (A : Form) (s : M.S) (β : List M.D),
      M.force (A.openAt β.length u) s ρ β ↔ M.force A s ρ (β ++ [M.evTm ρ [] u]) := by
  intro A
  induction A with
  | top | bot => intro _ _; exact Iff.rfl
  | pred _ ts =>
      intro s β
      show (M.Fl s ∨ _) ↔ (M.Fl s ∨ _)
      rw [M.evTms_openAt ρ u hu β ts]
  | and _ _ ih₁ ih₂ => intro s β; exact and_congr (ih₁ s β) (ih₂ s β)
  | or _ _ ih₁ ih₂ => intro s β; exact or_congr (ih₁ s β) (ih₂ s β)
  | imp _ _ ih₁ ih₂ =>
      intro s β
      exact forall_congr' fun v => imp_congr Iff.rfl (imp_congr (ih₁ v β) (ih₂ v β))
  | circ q _ ih =>
      intro s β
      cases q <;>
        exact forall_congr' fun v => imp_congr Iff.rfl
          (exists_congr fun w => and_congr Iff.rfl (ih w β))
  | forall_ _ ih =>
      intro s β
      exact forall_congr' fun v => imp_congr Iff.rfl
        (forall_congr' fun d => imp_congr Iff.rfl (ih v (d :: β)))
  | exists_ _ ih =>
      intro s β
      exact exists_congr fun d => and_congr Iff.rfl (ih s (d :: β))

/-- The instance used everywhere: opening the outermost binder of a formula
being forced under the empty index environment. -/
theorem force_openWith (ρ : String → M.D) (a : String) (A : Form) (s : M.S) :
    M.force (A.openWith a) s ρ [] ↔ M.force A s ρ [ρ a] :=
  M.force_openAt ρ (.fvar a) trivial A s []

end KModel

/-! ## Semantic consequence

At every state of every model where the context holds, the conclusion holds. -/

/-- `Γ ⊫ A`. -/
def Consequence (Γ : List Form) (A : Form) : Prop :=
  ∀ (M : KModel) (s : M.S) (ρ : String → M.D) (β : List M.D),
    (∀ B ∈ Γ, M.force B s ρ β) → M.force A s ρ β

@[inherit_doc] infix:55 " ⊫ " => Consequence

end LaxLogic.QLL
