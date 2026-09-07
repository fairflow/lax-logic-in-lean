/-
# `LaxLogic.QLL.Complete1` — first-order completeness

The canonical model, now with the quantifiers.  Three things had to be settled
before it could be built, and each is visible in the definitions below.

**Worlds carry a reserve.**  A state is a saturated theory together with the
infinite set of names it has never mentioned (`LaxLogic.QLL.Saturate`).  The
universal-falsity case needs a genuinely new parameter — ω-completeness fails,
so no term already present will do — and that is what the reserve supplies.
Successors spend one name and inherit the rest, which is why the domains
*increase*: `Dom w` is the terms avoiding `w`'s reserve, and a successor's
reserve is smaller.

**The valuation cannot be the identity.**  `Assign` asks that every name denote
an element of the *initial* world's domain, and reserved names are precisely the
ones excluded from it.  So variables are interpreted by `vnm x = x ++ "z"`,
which is injective and lands outside every reserve — reserved names are runs of
`w`.  Injectivity is what the atomic case needs: two names must not be
identified, or `P(r)` and `P(z)` would have to be validated together.

**The induction is on size, not on structure.**  `A⟨t⟩` is not a subformula of
`∀x. A`, but it has the same size.
-/
import LaxLogic.QLL.Saturate

namespace LaxLogic.QLL

/-! ## Size

Opening does not change it, which is what lets the quantifier cases recurse. -/

/-- The number of connectives and binders. -/
def Form.size : Form → Nat
  | .top | .bot | .pred _ _ => 0
  | .and A B | .or A B | .imp A B => A.size + B.size + 1
  | .circ _ A | .forall_ A | .exists_ A => A.size + 1

theorem Form.size_openAt (t : Tm) : ∀ (A : Form) (k : Nat), (A.openAt k t).size = A.size := by
  intro A
  induction A with
  | top | bot | pred _ _ => intro _; rfl
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
      intro k; simp [Form.openAt, Form.size, ih₁ k, ih₂ k]
  | circ _ _ ih => intro k; simp [Form.openAt, Form.size, ih k]
  | forall_ _ ih | exists_ _ ih => intro k; simp [Form.openAt, Form.size, ih (k + 1)]

theorem Form.size_openWith (a : String) (A : Form) : (A.openWith a).size = A.size :=
  Form.size_openAt (.fvar a) A 0

/-! ## Terms, and the names they use -/

/-- No name of the term is reserved. -/
def TmAvoids (R : Set String) (t : Tm) : Prop := ∀ x ∈ Tm.fv t, x ∉ R

theorem TmAvoids.sub {R R' : Set String} {t : Tm} (h : TmAvoids R t) (hs : R' ⊆ R) :
    TmAvoids R' t := fun x hx hm => h x hx (hs hm)

theorem Avoids.sub {R R' : Set String} {A : Form} (h : Avoids R A) (hs : R' ⊆ R) :
    Avoids R' A := fun x hx hm => h x hx (hs hm)

theorem Tm.lcAtList_of_mem : ∀ (ts : List Tm), (∀ t ∈ ts, Tm.lcAt 0 t) → Tm.lcAtList 0 ts
  | [],      _ => trivial
  | t :: ts, h => ⟨h t (by simp), Tm.lcAtList_of_mem ts (fun u hu => h u (by simp [hu]))⟩

theorem Tm.mem_fvList : ∀ {ts : List Tm} {x : String},
    x ∈ Tm.fvList ts → ∃ t ∈ ts, x ∈ Tm.fv t
  | [],      _, h => by simp [Tm.fvList] at h
  | t :: ts, x, h => by
      rcases List.mem_append.mp h with h | h
      · exact ⟨t, by simp, h⟩
      · obtain ⟨u, hu, hx⟩ := Tm.mem_fvList h
        exact ⟨u, List.mem_cons_of_mem _ hu, hx⟩

/-! ## Reserved names are runs of `w`

So any name containing another character is available in every world — which is
what the initial assignment needs. -/

theorem pnm_toList : ∀ i, (pnm i).toList = List.replicate (i + 1) 'w' := by
  intro i
  induction i with
  | zero => rfl
  | succ n ih => simp [pnm, ih, List.replicate_succ']

theorem ne_pnm_of_mem {x : String} {c : Char} (hc : c ∈ x.toList) (hne : c ≠ 'w') (i : Nat) :
    x ≠ pnm i := by
  intro h
  rw [h, pnm_toList] at hc
  exact hne (List.eq_of_mem_replicate hc)

theorem notMem_allNames_of_mem {f : Nat → Nat} {x : String} {c : Char}
    (hc : c ∈ x.toList) (hne : c ≠ 'w') : x ∉ allNames f := by
  rintro ⟨i, hi⟩
  exact ne_pnm_of_mem hc hne (f i) hi

theorem notMem_oddNames_of_mem {f : Nat → Nat} {x : String} {c : Char}
    (hc : c ∈ x.toList) (hne : c ≠ 'w') : x ∉ oddNames f :=
  fun h => notMem_allNames_of_mem hc hne (unused_sub_allNames (oddNames_sub_unused 0 h))

/-! ## Worlds

A saturated theory together with the reserve it has never mentioned.  The
reserve is what a successor spends to name a new individual, and what the
domain omits — so successors have larger domains, and the model has increasing
domains for exactly the reason the logic requires: the constant-domain axiom is
underivable. -/

/-- A state of the canonical model. -/
structure World where
  /-- The indexing of this world's reserve. -/
  f : Nat → Nat
  /-- Strictly monotone, so a name's index bounds its length. -/
  hf : StrictMono f
  /-- The theory. -/
  T : Theory
  /-- Consistent, total on its language, saturated, and silent about the reserve. -/
  hT : Saturated f T

/-- The names this world has never used. -/
def World.res (w : World) : Set String := oddNames w.f

/-- The canonical model. -/
def canon : KModel where
  S := World
  D := Tm
  Dom w t := Tm.lcAt 0 t ∧ TmAvoids w.res t
  Ri w v := v.res ⊆ w.res ∧ w.T.val ⊆ v.T.val
  RA w v := (v.res ⊆ w.res ∧ w.T.val ⊆ v.T.val) ∧ w.T.mfal .all ⊆ v.T.mfal .all
  RE w v := (v.res ⊆ w.res ∧ w.T.val ⊆ v.T.val) ∧ w.T.mfal .ex ⊆ v.T.mfal .ex
  Fl w := Form.bot ∈ w.T.val
  refl_i _ := ⟨subset_rfl, subset_rfl⟩
  trans_i h h' := ⟨h'.1.trans h.1, h.2.trans h'.2⟩
  refl_A _ := ⟨⟨subset_rfl, subset_rfl⟩, subset_rfl⟩
  trans_A h h' := ⟨⟨h'.1.1.trans h.1.1, h.1.2.trans h'.1.2⟩, h.2.trans h'.2⟩
  sub_A h := h.1
  refl_E _ := ⟨⟨subset_rfl, subset_rfl⟩, subset_rfl⟩
  trans_E h h' := ⟨⟨h'.1.1.trans h.1.1, h.1.2.trans h'.1.2⟩, h.2.trans h'.2⟩
  sub_E h := h.1
  dom_mono h hd := ⟨hd.1, fun x hx hm => hd.2 x hx (h.1 hm)⟩
  d₀ := .fvar "e"
  dom_d₀ w := ⟨trivial, by
    intro x hx
    rw [show x = "e" by simpa [Tm.fv] using hx]
    exact notMem_oddNames_of_mem (c := 'e') (by decide) (by decide)⟩
  hered_Fl h hb := h.2 hb
  fn f ds := .fn f ds
  I w P ds := Form.pred P ds ∈ w.T.val
  hered_I h hp := h.2 hp
  fn_dom h := ⟨Tm.lcAtList_of_mem _ (fun t ht => (h t ht).1), by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Tm.mem_fvList (by simpa [Tm.fv] using hx)
    exact (h t ht).2 x hxt⟩

/-- The identity valuation: a locally closed term denotes itself. -/
def canonρ : String → canon.D := fun x => .fvar x

mutual
theorem canon_ev_id : ∀ (t : Tm), Tm.lcAt 0 t → canon.evTm canonρ [] t = t
  | .bvar i,  h => absurd h (Nat.not_lt_zero i)
  | .fvar _,  _ => rfl
  | .fn f ts, h => by
      show Tm.fn f (canon.evTms canonρ [] ts) = Tm.fn f ts
      rw [canon_evs_id ts h]
theorem canon_evs_id : ∀ (ts : List Tm), Tm.lcAtList 0 ts → canon.evTms canonρ [] ts = ts
  | [],      _ => rfl
  | t :: ts, h => by
      show canon.evTm canonρ [] t :: canon.evTms canonρ [] ts = _
      rw [canon_ev_id t h.1, canon_evs_id ts h.2]
      rfl
end


/-! ## Founding a successor

Two forms.  `child` keeps the whole reserve, for the cases that only need a
larger theory; `childPar` spends its first name, for the case that needs a new
individual — the universal-falsity case, where no term already present can
serve, since ω-completeness fails. -/

/-- The reserve a successor inherits when no name is spent. -/
def World.childF (w : World) : Nat → Nat := fun k => w.f (2 * k + 1)

theorem World.childF_mono (w : World) : StrictMono w.childF :=
  fun _ _ h => w.hf (by omega)

theorem World.allNames_childF (w : World) : allNames w.childF = w.res := rfl

theorem World.child (w : World) {T₀ : Theory} (h₀ : Consistent T₀)
    (hI₀ : ∀ A, (A ∈ T₀.val ∨ A ∈ T₀.fal ∨ ∃ q, A ∈ T₀.mfal q) → Avoids w.res A) :
    ∃ v : World, v.res ⊆ w.res ∧ T₀ ≤ v.T := by
  obtain ⟨T, hle, hS⟩ := exists_saturated w.childF_mono h₀
    (by rw [World.allNames_childF]; exact hI₀)
  exact ⟨⟨w.childF, w.childF_mono, T, hS⟩, fun _ hx => oddNames_sub_allNames hx, hle⟩

/-- The reserve a successor inherits when the first name is spent. -/
def World.parF (w : World) : Nat → Nat := fun k => w.f (2 * k + 3)

/-- The name spent to found a successor. -/
def World.par (w : World) : String := resName w.f 1

theorem World.parF_mono (w : World) : StrictMono w.parF :=
  fun _ _ h => w.hf (by omega)

theorem World.allNames_parF_sub (w : World) : allNames w.parF ⊆ w.res :=
  fun _ ⟨i, hi⟩ => ⟨i + 1, by rw [hi]; rfl⟩

theorem World.par_notMem_parF (w : World) : w.par ∉ allNames w.parF := by
  rintro ⟨i, hi⟩
  have := resName_inj w.hf hi
  omega

theorem World.childPar (w : World) {T₀ : Theory} (h₀ : Consistent T₀)
    (hI₀ : ∀ A, (A ∈ T₀.val ∨ A ∈ T₀.fal ∨ ∃ q, A ∈ T₀.mfal q) →
      Avoids (allNames w.parF) A) :
    ∃ v : World, v.res ⊆ w.res ∧ T₀ ≤ v.T ∧ w.par ∉ v.res := by
  obtain ⟨T, hle, hS⟩ := exists_saturated w.parF_mono h₀ hI₀
  exact ⟨⟨w.parF, w.parF_mono, T, hS⟩,
    fun _ hx => w.allNames_parF_sub (oddNames_sub_allNames hx), hle,
    fun hx => w.par_notMem_parF (oddNames_sub_allNames hx)⟩

/-! ## The truth lemma

By induction on *size*: `A⟨t⟩` is not a subformula of `∀x. A`, but it is no
larger, and that is all the recursion needs. -/

theorem truth_lemma1 : ∀ (n : Nat) (A : Form), A.size = n → Form.lc A →
    ∀ w : World, Avoids w.res A →
      (A ∈ w.T.val → canon.force A w canonρ []) ∧
      (A ∈ w.T.fal → ¬ canon.force A w canonρ []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hsz hlc w hav
    cases A with
    | top =>
        exact ⟨fun _ => trivial,
               fun h _ => w.hT.good.not_fal_deriv h ⟨[], by simp, .topI⟩⟩
    | bot =>
        exact ⟨fun h => h, fun h hf => w.hT.good.not_fal_deriv h (SetPrv.of_mem hf)⟩
    | pred P ts =>
        have hev : canon.evTms canonρ [] ts = ts := canon_evs_id ts hlc
        constructor
        · intro h
          show canon.Fl w ∨ canon.I w P _
          rw [hev]; exact Or.inr h
        · intro h hf
          rcases hf with hb | hp
          · exact w.hT.good.not_fal_deriv h
              ((SetPrv.of_mem hb).map (fun _ p => .botE p))
          · rw [hev] at hp
            exact w.hT.good.not_fal_deriv h (SetPrv.of_mem hp)
    | and A B =>
        have hA : A.size < n := by subst hsz; simp [Form.size]; omega
        have hB : B.size < n := by subst hsz; simp [Form.size]; omega
        have ihA := ih A.size hA A rfl hlc.1 w (Avoids.left (Or.inl hav))
        have ihB := ih B.size hB B rfl hlc.2 w (Avoids.right (Or.inl hav))
        constructor
        · intro h
          exact ⟨ihA.1 (w.hT.good.ded_closed (Avoids.left (Or.inl hav))
                   ((SetPrv.of_mem h).map (fun _ p => .andE₁ p))),
                 ihB.1 (w.hT.good.ded_closed (Avoids.right (Or.inl hav))
                   ((SetPrv.of_mem h).map (fun _ p => .andE₂ p)))⟩
        · intro h hf
          rcases w.hT.good.fal_and hav h with h' | h'
          · exact ihA.2 h' hf.1
          · exact ihB.2 h' hf.2
    | or A B =>
        have hA : A.size < n := by subst hsz; simp [Form.size]; omega
        have hB : B.size < n := by subst hsz; simp [Form.size]; omega
        have ihA := ih A.size hA A rfl hlc.1 w (Avoids.left (Or.inr (Or.inl hav)))
        have ihB := ih B.size hB B rfl hlc.2 w (Avoids.right (Or.inr (Or.inl hav)))
        constructor
        · intro h
          rcases w.hT.good.or_mem hav h with h' | h'
          · exact Or.inl (ihA.1 h')
          · exact Or.inr (ihB.1 h')
        · intro h hf
          obtain ⟨h₁, h₂⟩ := w.hT.good.fal_or hav h
          rcases hf with hf | hf
          · exact ihA.2 h₁ hf
          · exact ihB.2 h₂ hf
    | imp A B =>
        have hA : A.size < n := by subst hsz; simp [Form.size]; omega
        have hB : B.size < n := by subst hsz; simp [Form.size]; omega
        constructor
        · intro h v hv hfA
          have havv : Avoids v.res (Form.imp A B) := hav.sub hv.1
          rcases v.hT.good.imp_mem havv (hv.2 h) with h' | h'
          · exact absurd hfA
              ((ih A.size hA A rfl hlc.1 v (Avoids.left (Or.inr (Or.inr havv)))).2 h')
          · exact (ih B.size hB B rfl hlc.2 v (Avoids.right (Or.inr (Or.inr havv)))).1 h'
        · intro h hf
          have hcons : Consistent ⟨insert A w.T.val, {B}, fun _ => ∅⟩ := by
            intro Ds TA TE hD hA' hE hne hder
            have hTA : TA = [] := by
              cases TA with
              | nil => rfl
              | cons X _ => exact absurd (hA' X (by simp)) (by simp)
            have hTE : TE = [] := by
              cases TE with
              | nil => rfl
              | cons X _ => exact absurd (hE X (by simp)) (by simp)
            subst hTA; subst hTE
            rw [disjOf_fal] at hder
            exact w.hT.good.not_fal_deriv h (SetPrv.deduct
              (SetPrv.bigOr_collapse Ds _ (fun X hX => hD X hX) hder))
          obtain ⟨v, hres, hle⟩ := w.child hcons (by
            rintro X (hX | hX | ⟨q, hX⟩)
            · rcases hX with rfl | hX
              · exact Avoids.left (Or.inr (Or.inr hav))
              · exact w.hT.inv X (Or.inl hX)
            · rcases hX with rfl
              exact Avoids.right (Or.inr (Or.inr hav))
            · exact absurd hX (by simp))
          have havv : Avoids v.res (Form.imp A B) := hav.sub hres
          exact (ih B.size hB B rfl hlc.2 v (Avoids.right (Or.inr (Or.inr havv)))).2
            (hle.2.1 rfl)
            (hf v ⟨hres, (Set.subset_insert ..).trans hle.1⟩
              ((ih A.size hA A rfl hlc.1 v (Avoids.left (Or.inr (Or.inr havv)))).1
                (hle.1 (Set.mem_insert ..))))
    | circ q A =>
        have hA : A.size < n := by subst hsz; simp [Form.size]
        have havA : Avoids w.res A := Avoids.under (Or.inl hav)
        cases q
        · constructor
          · intro h v hv
            have hcons : Consistent
                ⟨insert A v.T.val, ∅, fun r => match r with
                  | .all => v.T.mfal .all | .ex => ∅⟩ := by
              intro Ds TA TE hD hA' hE hne hder
              have hDs : Ds = [] := by
                cases Ds with
                | nil => rfl
                | cons X _ => exact absurd (hD X (by simp)) (by simp)
              have hTE : TE = [] := by
                cases TE with
                | nil => rfl
                | cons X _ => exact absurd (hE X (by simp)) (by simp)
              subst hDs; subst hTE
              have hTA : TA ≠ [] := by intro hnil; exact hne (by simp [hnil])
              rw [disjOf_all hTA] at hder
              refine v.hT.good.1 [] TA [] (by simp) hA' (by simp) (by simp [hTA]) ?_
              rw [disjOf_all hTA]
              exact SetPrv.lax_bind (SetPrv.of_mem (hv.2 h)) (SetPrv.deduct hder)
            obtain ⟨u, hres, hle⟩ := v.child hcons (by
              rintro X (hX | hX | ⟨r, hX⟩)
              · rcases hX with rfl | hX
                · exact havA.sub hv.1
                · exact v.hT.inv X (Or.inl hX)
              · exact absurd hX (by simp)
              · cases r
                · exact v.hT.inv X (Or.inr (Or.inr ⟨.all, hX⟩))
                · exact absurd hX (by simp))
            exact ⟨u, ⟨⟨hres, (Set.subset_insert ..).trans hle.1⟩, hle.2.2 .all⟩,
              (ih A.size hA A rfl hlc u ((havA.sub hv.1).sub hres)).1
                (hle.1 (Set.mem_insert ..))⟩
          · intro h hf
            have hcons : Consistent
                ⟨w.T.val, ∅, fun r => match r with | .all => {A} | .ex => ∅⟩ := by
              intro Ds TA TE hD hA' hE hne hder
              have hDs : Ds = [] := by
                cases Ds with
                | nil => rfl
                | cons X _ => exact absurd (hD X (by simp)) (by simp)
              have hTE : TE = [] := by
                cases TE with
                | nil => rfl
                | cons X _ => exact absurd (hE X (by simp)) (by simp)
              subst hDs; subst hTE
              have hTA : TA ≠ [] := by intro hnil; exact hne (by simp [hnil])
              rw [disjOf_all hTA] at hder
              exact w.hT.good.not_fal_deriv h
                (SetPrv.lax_collapse TA (fun X hX => hA' X hX) hder)
            obtain ⟨v, hres, hle⟩ := w.child hcons (by
              rintro X (hX | hX | ⟨r, hX⟩)
              · exact w.hT.inv X (Or.inl hX)
              · exact absurd hX (by simp)
              · cases r
                · rcases hX with rfl; exact havA
                · exact absurd hX (by simp))
            obtain ⟨u, hRm, hfA⟩ := hf v ⟨hres, hle.1⟩
            exact (ih A.size hA A rfl hlc u
              (((havA.sub hres).sub hRm.1.1))).2
              (u.hT.good.mfal_sub_fal ((havA.sub hres).sub hRm.1.1)
                (hRm.2 (hle.2.2 .all rfl))) hfA
        · constructor
          · intro h v hv
            have hcons : Consistent
                ⟨insert A v.T.val, ∅, fun r => match r with
                  | .all => ∅ | .ex => v.T.mfal .ex⟩ := by
              intro Ds TA TE hD hA' hE hne hder
              have hDs : Ds = [] := by
                cases Ds with
                | nil => rfl
                | cons X _ => exact absurd (hD X (by simp)) (by simp)
              have hTA : TA = [] := by
                cases TA with
                | nil => rfl
                | cons X _ => exact absurd (hA' X (by simp)) (by simp)
              subst hDs; subst hTA
              have hTE : TE ≠ [] := by intro hnil; exact hne (by simp [hnil])
              rw [disjOf_ex hTE] at hder
              refine v.hT.good.1 [] [] TE (by simp) (by simp) hE (by simp [hTE]) ?_
              rw [disjOf_ex hTE]
              exact SetPrv.lax_bind (SetPrv.of_mem (hv.2 h)) (SetPrv.deduct hder)
            obtain ⟨u, hres, hle⟩ := v.child hcons (by
              rintro X (hX | hX | ⟨r, hX⟩)
              · rcases hX with rfl | hX
                · exact havA.sub hv.1
                · exact v.hT.inv X (Or.inl hX)
              · exact absurd hX (by simp)
              · cases r
                · exact absurd hX (by simp)
                · exact v.hT.inv X (Or.inr (Or.inr ⟨.ex, hX⟩)))
            exact ⟨u, ⟨⟨hres, (Set.subset_insert ..).trans hle.1⟩, hle.2.2 .ex⟩,
              (ih A.size hA A rfl hlc u ((havA.sub hv.1).sub hres)).1
                (hle.1 (Set.mem_insert ..))⟩
          · intro h hf
            have hcons : Consistent
                ⟨w.T.val, ∅, fun r => match r with | .all => ∅ | .ex => {A}⟩ := by
              intro Ds TA TE hD hA' hE hne hder
              have hDs : Ds = [] := by
                cases Ds with
                | nil => rfl
                | cons X _ => exact absurd (hD X (by simp)) (by simp)
              have hTA : TA = [] := by
                cases TA with
                | nil => rfl
                | cons X _ => exact absurd (hA' X (by simp)) (by simp)
              subst hDs; subst hTA
              have hTE : TE ≠ [] := by intro hnil; exact hne (by simp [hnil])
              rw [disjOf_ex hTE] at hder
              exact w.hT.good.not_fal_deriv h
                (SetPrv.lax_collapse TE (fun X hX => hE X hX) hder)
            obtain ⟨v, hres, hle⟩ := w.child hcons (by
              rintro X (hX | hX | ⟨r, hX⟩)
              · exact w.hT.inv X (Or.inl hX)
              · exact absurd hX (by simp)
              · cases r
                · exact absurd hX (by simp)
                · rcases hX with rfl; exact havA)
            obtain ⟨u, hRm, hfA⟩ := hf v ⟨hres, hle.1⟩
            exact (ih A.size hA A rfl hlc u ((havA.sub hres).sub hRm.1.1)).2
              (u.hT.good.mfal_sub_fal ((havA.sub hres).sub hRm.1.1)
                (hRm.2 (hle.2.2 .ex rfl))) hfA
    | forall_ A =>
        have hA : A.size < n := by subst hsz; simp [Form.size]
        have havA : Avoids w.res A := Avoids.under (q := Q.all) (Or.inr (Or.inl hav))
        constructor
        · intro h v hv d hd
          have hopen : Avoids v.res (A.openAt 0 d) :=
            ((havA.sub hv.1).openAt (fun x hx => hd.2 x hx))
          have hmem : A.openAt 0 d ∈ v.T.val :=
            v.hT.good.all_mem hd.1 hopen (hv.2 h)
          have key := (ih (A.openAt 0 d).size (by rw [Form.size_openAt]; exact hA)
            (A.openAt 0 d) rfl (Form.lcAt_openAt A 0 d hd.1 hlc) v hopen).1 hmem
          rw [show (0 : Nat) = ([] : List canon.D).length from rfl] at key
          rw [canon.force_openAt canonρ d hd.1 A v []] at key
          rwa [canon_ev_id d hd.1] at key
        · intro h hf
          have hcpar : Avoids (allNames w.parF) (A.openWith w.par) :=
            (havA.sub w.allNames_parF_sub).openAt (by
              intro x hx
              rw [show x = w.par by simpa [Tm.fv] using hx]
              exact w.par_notMem_parF)
          have hlcA : Form.lc (A.openWith w.par) :=
            Form.lcAt_openAt A 0 (.fvar w.par) trivial hlc
          have hcons : Consistent ⟨w.T.val, {A.openWith w.par}, fun _ => ∅⟩ := by
            intro Ds TA TE hD hA' hE hne hder
            have hTA : TA = [] := by
              cases TA with
              | nil => rfl
              | cons X _ => exact absurd (hA' X (by simp)) (by simp)
            have hTE : TE = [] := by
              cases TE with
              | nil => rfl
              | cons X _ => exact absurd (hE X (by simp)) (by simp)
            subst hTA; subst hTE
            rw [disjOf_fal] at hder
            obtain ⟨L, hL, hp⟩ := SetPrv.bigOr_collapse Ds _ (fun X hX => hD X hX) hder
            refine w.hT.good.not_fal_deriv h ⟨L, hL, ?_⟩
            refine Prv.allI_of_fresh ?_ ?_ hp
            · intro hc
              obtain ⟨X, hX, hx⟩ := mem_ctxFv' hc
              exact w.hT.inv X (Or.inl (hL X hX)) _ hx ⟨0, rfl⟩
            · exact fun hc => havA _ hc ⟨0, rfl⟩
          obtain ⟨v, hres, hle, hpar⟩ := w.childPar hcons (by
            rintro X (hX | hX | ⟨q, hX⟩)
            · exact (w.hT.inv X (Or.inl hX)).sub w.allNames_parF_sub
            · rcases hX with rfl; exact hcpar
            · exact absurd hX (by simp))
          have hd : canon.Dom v (.fvar w.par) := ⟨trivial, by
            intro x hx
            rw [show x = w.par by simpa [Tm.fv] using hx]
            exact hpar⟩
          have key := hf v ⟨hres, hle.1⟩ (.fvar w.par) hd
          refine (ih (A.openWith w.par).size (by rw [Form.size_openWith]; exact hA)
            (A.openWith w.par) rfl hlcA v ((havA.sub hres).openAt (by
              intro x hx
              rw [show x = w.par by simpa [Tm.fv] using hx]
              exact hpar))).2 (hle.2.1 rfl) ?_
          rwa [canon.force_openWith canonρ w.par A v]
    | exists_ A =>
        have hA : A.size < n := by subst hsz; simp [Form.size]
        have havA : Avoids w.res A := Avoids.under (q := Q.all) (Or.inr (Or.inr hav))
        constructor
        · intro h
          obtain ⟨c, hc, hmem⟩ := w.hT.sat A h
          have hd : canon.Dom w (.fvar c) := ⟨trivial, by
            intro x hx
            rw [show x = c by simpa [Tm.fv] using hx]
            exact hc⟩
          refine ⟨.fvar c, hd, ?_⟩
          have key := (ih (A.openWith c).size (by rw [Form.size_openWith]; exact hA)
            (A.openWith c) rfl (Form.lcAt_openAt A 0 (.fvar c) trivial hlc) w
            (havA.openAt (by
              intro x hx
              rw [show x = c by simpa [Tm.fv] using hx]
              exact hc))).1 hmem
          rwa [canon.force_openWith canonρ c A w] at key
        · rintro h ⟨d, hd, hforce⟩
          have hopen : Avoids w.res (A.openAt 0 d) :=
            havA.openAt (fun x hx => hd.2 x hx)
          have key := (ih (A.openAt 0 d).size (by rw [Form.size_openAt]; exact hA)
            (A.openAt 0 d) rfl (Form.lcAt_openAt A 0 d hd.1 hlc) w hopen).2
            (w.hT.good.fal_exists hd.1 hopen h)
          refine key ?_
          rw [show (0 : Nat) = ([] : List canon.D).length from rfl,
            canon.force_openAt canonρ d hd.1 A w [], canon_ev_id d hd.1]
          exact hforce


/-! ## Completeness

The reserve of the initial world is chosen above every name in `Γ` and `A`, so
the identity valuation is an assignment there — which is exactly what the
weakened `Assign` asks for, and what the total one could never have given. -/

/-- **Completeness**: a locally closed consequence is derivable. -/
theorem completeness1 {Γ : List Form} {A : Form}
    (hΓ : ∀ B ∈ Γ, Form.lc B) (hA : Form.lc A) (h : Γ ⊫ A) : Γ ⊢q A := by
  by_contra hn
  obtain ⟨f₀, hfdef⟩ : ∃ g : Nat → Nat, g = fun k => maxLen (ctxFv Γ ++ A.fv) + k :=
    ⟨_, rfl⟩
  have hf₀ : StrictMono f₀ := by
    intro a b hab; rw [hfdef]; simp; omega
  have havoid : ∀ x ∈ ctxFv Γ ++ A.fv, x ∉ allNames f₀ := by
    rintro x hx ⟨i, rfl⟩
    exact pnm_notMem_of_ge (by rw [hfdef]; simp) hx
  have hcons : Consistent ⟨{B | B ∈ Γ}, {A}, fun _ => ∅⟩ := by
    intro Ds TA TE hD hA' hE hne hder
    have hTA : TA = [] := by
      cases TA with
      | nil => rfl
      | cons X _ => exact absurd (hA' X (by simp)) (by simp)
    have hTE : TE = [] := by
      cases TE with
      | nil => rfl
      | cons X _ => exact absurd (hE X (by simp)) (by simp)
    subst hTA; subst hTE
    rw [disjOf_fal] at hder
    obtain ⟨L, hL, hp⟩ := SetPrv.bigOr_collapse Ds _ (fun X hX => hD X hX) hder
    exact hn (hp.weaken (fun X hX => hL X hX))
  obtain ⟨T, hle, hS⟩ := exists_saturated hf₀ hcons (by
    rintro X (hX | hX | ⟨q, hX⟩)
    · exact fun x hx => havoid x (List.mem_append_left _ (mem_ctxFv hX hx))
    · rcases hX with rfl
      exact fun x hx => havoid x (List.mem_append_right _ hx)
    · exact absurd hX (by simp))
  obtain ⟨w, hwdef⟩ : ∃ v : World, v = ⟨f₀, hf₀, T, hS⟩ := ⟨_, rfl⟩
  have hres : w.res = oddNames f₀ := by rw [hwdef]; rfl
  have havw : ∀ X : Form, (∀ x ∈ X.fv, x ∈ ctxFv Γ ++ A.fv) → Avoids w.res X := by
    intro X hsub x hx hm
    exact havoid x (hsub x hx) (oddNames_sub_allNames (hres ▸ hm))
  have hTw : w.T = T := by rw [hwdef]
  refine truth_lemma1 A.size A rfl hA w
    (havw A (fun x hx => List.mem_append_right _ hx)) |>.2 ?_ ?_
  · rw [hTw]; exact hle.2.1 rfl
  · refine h canon w canonρ (fun x hx => ⟨trivial, ?_⟩) (fun B hB => ?_)
    · intro y hy hm
      rw [show y = x by simpa [canonρ, Tm.fv] using hy] at hm
      exact havoid x hx (oddNames_sub_allNames (hres ▸ hm))
    · refine (truth_lemma1 B.size B rfl (hΓ B hB) w
        (havw B (fun x hx => List.mem_append_left _ (mem_ctxFv hB hx)))).1 ?_
      rw [hTw]; exact hle.1 hB

/-- **Adequacy**: for locally closed data, derivability and consequence coincide. -/
theorem prv_iff_consequence {Γ : List Form} {A : Form}
    (hΓ : ∀ B ∈ Γ, Form.lc B) (hA : Form.lc A) : Γ ⊢q A ↔ Γ ⊫ A :=
  ⟨Prv.sound, completeness1 hΓ hA⟩

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.truth_lemma1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms truth_lemma1

/-- info: 'LaxLogic.QLL.completeness1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms completeness1

/-- info: 'LaxLogic.QLL.prv_iff_consequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prv_iff_consequence

end LaxLogic.QLL
