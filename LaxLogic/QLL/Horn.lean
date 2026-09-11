/-
# `LaxLogic.QLL.Horn` — Horn clauses, made explicit

Stage H1 of `docs/qll-herbrand-horn-plan.md`.

A clause of Definition 5.1 is `∀x̃. S ⊃ H` with `S` a Σ-formula, which is a
*positive existential* formula: `⊤`, atoms, `∧`, `∨`, `∃`.  A Horn clause here
has a *primitive positive* body: `⊤`, atoms, `∧`, `∃`, no `∨`.  The draft's
indices `ind(S)` (§6.2) choose one side of every `∨`, and `sel S g` is `S` with
the choices `g` made: the draft's `S♯g` before its existential quantifiers are
pulled to the front.  Splitting a clause at its disjunctions is the positive
part of the Lloyd–Topor transformation, and it is an equivalence:

    [S] ⊢q ⋁_{g ∈ ind S} sel S g            [sel S g] ⊢q S      (g ∈ ind S)
    [c.form] ⊢q h.form   (h ∈ c.toHorn)      c.toHorn.forms ⊢q c.form

The forcing counterpart of the first line, `force_iff_sel`, is what the Herbrand
models use.

The body is left primitive positive rather than prenexed (decision D1 of the
plan): splitting `∨` leaves every de Bruijn index where it was, while
`A ∧ ∃y.B ⊣⊢ ∃y.(A↑ ∧ B)` shifts the indices of `A`, and the syntax has no lift.
Lloyd's own form, a conjunction of atoms with the body-only variables
quantified in front, is the prenex form of a primitive positive body; it comes
in stage 4, whose Table 1 needs the lift anyway.
-/
import LaxLogic.QLL.LLP
import LaxLogic.QLL.Prov
import LaxLogic.QLL.Size

namespace LaxLogic.QLL

/-! ## Primitive positive formulas -/

/-- Built from `⊤`, atoms, `∧` and `∃`. -/
inductive IsPP : Form → Prop
  | top : IsPP .top
  | pred (P : String) (ts : List Tm) : IsPP (.pred P ts)
  | and {A B : Form} : IsPP A → IsPP B → IsPP (.and A B)
  | ex {A : Form} : IsPP A → IsPP (.exists_ A)

theorem IsPP.isSigma {A : Form} : IsPP A → IsSigma A
  | .top => .top
  | .pred P ts => .pred P ts
  | .and h₁ h₂ => .and h₁.isSigma h₂.isSigma
  | .ex h => .ex h.isSigma

theorem IsSigma.openAt {A : Form} (h : IsSigma A) :
    ∀ (k : Nat) (t : Tm), IsSigma (A.openAt k t) := by
  induction h with
  | top => intro _ _; exact .top
  | pred P _ => intro _ _; exact .pred P _
  | and _ _ ih₁ ih₂ => intro k t; exact .and (ih₁ k t) (ih₂ k t)
  | or _ _ ih₁ ih₂ => intro k t; exact .or (ih₁ k t) (ih₂ k t)
  | ex _ ih => intro k t; exact .ex (ih (k + 1) t)

theorem IsSigma.instAll : ∀ (ts : List Tm) {A : Form}, IsSigma A → IsSigma (Form.instAll ts A)
  | [],      _, h => h
  | t :: ts, _, h => IsSigma.instAll ts (h.openAt _ t)

/-! ## Horn clauses -/

/-- `∀x₁…xₘ. φ ⊃ P(t̃)`, or `∀x₁…xₘ. φ ⊃ ◯_q P(t̃)`, with `φ` primitive positive.
The head's arguments are arbitrary terms, as in Lloyd; Definition 5.1's
`P(x₁,…,xₘ)` is the case `args = headVars arity`. -/
structure Horn where
  arity : Nat
  body : Form
  body_pp : IsPP body
  head : String
  args : List Tm
  modal : Bool
  q : Q

/-- `P(t̃)`. -/
def Horn.headAtom (h : Horn) : Form := .pred h.head h.args

/-- `P(t̃)` or `◯_q P(t̃)`. -/
def Horn.headForm (h : Horn) : Form :=
  if h.modal then .circ h.q h.headAtom else h.headAtom

/-- The formula the clause stands for. -/
def Horn.form (h : Horn) : Form := Form.foralls h.arity (.imp h.body h.headForm)

/-! ## The draft's indices, and selection -/

/-- An element of `ind(S)`: which side of each `∨` is taken. -/
inductive Idx
  | leaf
  | pair (g₁ g₂ : Idx)
  | inl (g : Idx)
  | inr (g : Idx)
  | ex (g : Idx)
  deriving DecidableEq, Repr

/-- `ind(S)`, §6.2: `ind(true) = ind(A) = {⋆}`, pairs at `∧`, tagged choices at
`∨`, and `∃` passes through. -/
def ind : Form → List Idx
  | .and A B   => (ind A).flatMap fun g₁ => (ind B).map fun g₂ => .pair g₁ g₂
  | .or A B    => (ind A).map .inl ++ (ind B).map .inr
  | .exists_ A => (ind A).map .ex
  | _          => [.leaf]

/-- `S` at index `g`: every `∨` replaced by the side `g` chooses. -/
def sel : Form → Idx → Form
  | .and A B,   .pair g₁ g₂ => .and (sel A g₁) (sel B g₂)
  | .or A _,    .inl g      => sel A g
  | .or _ B,    .inr g      => sel B g
  | .exists_ A, .ex g       => .exists_ (sel A g)
  | A,          _           => A

theorem sel_top (g : Idx) : sel .top g = .top := by cases g <;> rfl

theorem sel_pred (P : String) (ts : List Tm) (g : Idx) : sel (.pred P ts) g = .pred P ts := by
  cases g <;> rfl

/-- (N1) A Σ-formula at an index is primitive positive. -/
theorem IsSigma.pp_sel {S : Form} (hS : IsSigma S) : ∀ {g : Idx}, g ∈ ind S → IsPP (sel S g) := by
  induction hS with
  | top => intro g _; rw [sel_top]; exact .top
  | pred P ts => intro g _; rw [sel_pred]; exact .pred P ts
  | and _ _ ih₁ ih₂ =>
      intro g hg
      obtain ⟨g₁, hg₁, hg⟩ := List.mem_flatMap.1 hg
      obtain ⟨g₂, hg₂, rfl⟩ := List.mem_map.1 hg
      exact .and (ih₁ hg₁) (ih₂ hg₂)
  | or _ _ ih₁ ih₂ =>
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
        exact ih₁ hg'
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
        exact ih₂ hg'
  | ex _ ih =>
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      exact .ex (ih hg')

/-! ## Selection commutes with instantiation -/

theorem ind_openAt : ∀ (A : Form) (k : Nat) (t : Tm), ind (A.openAt k t) = ind A
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .pred _ _, _, _ => rfl
  | .and A B, k, t => by
      show ind (.and (A.openAt k t) (B.openAt k t)) = ind (.and A B)
      simp only [ind, ind_openAt A k t, ind_openAt B k t]
  | .or A B, k, t => by
      show ind (.or (A.openAt k t) (B.openAt k t)) = ind (.or A B)
      simp only [ind, ind_openAt A k t, ind_openAt B k t]
  | .imp _ _, _, _ => rfl
  | .circ _ _, _, _ => rfl
  | .forall_ _, _, _ => rfl
  | .exists_ A, k, t => by
      show ind (.exists_ (A.openAt (k + 1) t)) = ind (.exists_ A)
      simp only [ind, ind_openAt A (k + 1) t]

theorem sel_openAt : ∀ (A : Form) (g : Idx) (k : Nat) (t : Tm),
    sel (A.openAt k t) g = (sel A g).openAt k t
  | .top, g, k, t => by
      show sel .top g = (sel .top g).openAt k t
      rw [sel_top]; rfl
  | .bot, g, _, _ => by cases g <;> rfl
  | .pred P ts, g, k, t => by
      show sel (.pred P (Tm.openAtList k t ts)) g = (sel (.pred P ts) g).openAt k t
      rw [sel_pred, sel_pred]; rfl
  | .and A B, g, k, t => by
      cases g with
      | pair g₁ g₂ =>
          show Form.and (sel (A.openAt k t) g₁) (sel (B.openAt k t) g₂)
            = Form.and ((sel A g₁).openAt k t) ((sel B g₂).openAt k t)
          rw [sel_openAt A g₁ k t, sel_openAt B g₂ k t]
      | _ => rfl
  | .or A B, g, k, t => by
      cases g with
      | inl g => exact sel_openAt A g k t
      | inr g => exact sel_openAt B g k t
      | _ => rfl
  | .imp _ _, g, _, _ => by cases g <;> rfl
  | .circ _ _, g, _, _ => by cases g <;> rfl
  | .forall_ _, g, _, _ => by cases g <;> rfl
  | .exists_ A, g, k, t => by
      cases g with
      | ex g =>
          show Form.exists_ (sel (A.openAt (k + 1) t) g) = Form.exists_ ((sel A g).openAt (k + 1) t)
          rw [sel_openAt A g (k + 1) t]
      | _ => rfl

theorem ind_instAll : ∀ (ts : List Tm) (A : Form), ind (Form.instAll ts A) = ind A
  | [],      _ => rfl
  | t :: ts, A => (ind_instAll ts _).trans (ind_openAt A _ t)

theorem sel_instAll : ∀ (ts : List Tm) (A : Form) (g : Idx),
    sel (Form.instAll ts A) g = Form.instAll ts (sel A g)
  | [],      _, _ => rfl
  | t :: ts, A, g => by
      show sel (Form.instAll ts (A.openAt ts.length t)) g
        = Form.instAll ts ((sel A g).openAt ts.length t)
      rw [sel_instAll ts, sel_openAt]

/-! ## Size, for induction through `∃`

`Form.size` is `Size.lean`'s, and opening does not change it. -/

theorem Form.size_lt_left {A B : Form} {n : Nat} (h : A.size + B.size + 1 < n + 1) : A.size < n :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_of_succ_lt_succ h)

theorem Form.size_lt_right {A B : Form} {n : Nat} (h : A.size + B.size + 1 < n + 1) : B.size < n :=
  Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_of_succ_lt_succ h)

/-! ## Disjunctions of a list, in `Prv` -/

/-- `A₁ ∨ (A₂ ∨ ( … ∨ ⊥))`. -/
def Form.disj : List Form → Form
  | []      => .bot
  | A :: As => .or A (Form.disj As)

theorem Prv.disj_intro : ∀ {As : List Form} {A : Form} {Γ : List Form},
    A ∈ As → Prv Γ A → Prv Γ (Form.disj As)
  | [],      _, _, h, _  => nomatch h
  | _ :: _, _, _, h, hA => by
      rcases List.mem_cons.1 h with rfl | h
      · exact .orI₁ hA
      · exact .orI₂ (Prv.disj_intro h hA)

theorem Prv.disj_elim : ∀ {As : List Form} {Γ : List Form} {K : Form},
    Prv Γ (Form.disj As) → (∀ A ∈ As, Prv (A :: Γ) K) → Prv Γ K
  | [],      _, _, h, _  => .botE h
  | B :: As, Γ, K, h, hK =>
      .orE h (hK B (List.mem_cons.2 (Or.inl rfl)))
        (Prv.disj_elim (.var (List.mem_cons.2 (Or.inl rfl))) fun A hA =>
          (hK A (List.mem_cons.2 (Or.inr hA))).weaken fun C hC => by
            rcases List.mem_cons.1 hC with rfl | hC
            · exact List.mem_cons.2 (Or.inl rfl)
            · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr hC))))

/-- Discharging a whole context of derivable assumptions. -/
theorem Prv.cutAll : ∀ {Γ' Δ : List Form} {B : Form},
    (∀ A ∈ Γ', Prv Δ A) → Prv Γ' B → Prv Δ B
  | [],      _, _, _,  h => h.weaken fun _ h => nomatch h
  | A :: _, _, _, hA, h =>
      .impE (Prv.cutAll (fun C hC => hA C (List.mem_cons.2 (Or.inr hC))) (.impI h))
        (hA A (List.mem_cons.2 (Or.inl rfl)))

/-! ## (N2) A Σ-formula is the disjunction of its selections -/

theorem Prv.of_sel_aux : ∀ (n : Nat) {S : Form}, S.size < n → IsSigma S →
    ∀ {g : Idx}, g ∈ ind S → ∀ {Γ : List Form}, Prv Γ (sel S g) → Prv Γ S
  | 0, _, hn, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, hn, hS, g, hg, Γ, h => by
      cases hS with
      | top => rwa [sel_top] at h
      | pred P ts => rwa [sel_pred] at h
      | @and A B h₁ h₂ =>
          obtain ⟨g₁, hg₁, hg⟩ := List.mem_flatMap.1 hg
          obtain ⟨g₂, hg₂, rfl⟩ := List.mem_map.1 hg
          exact .andI (Prv.of_sel_aux n (Form.size_lt_left hn) h₁ hg₁ (.andE₁ h))
            (Prv.of_sel_aux n (Form.size_lt_right hn) h₂ hg₂ (.andE₂ h))
      | @or A B h₁ h₂ =>
          rcases List.mem_append.1 hg with hg | hg
          · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
            exact .orI₁ (Prv.of_sel_aux n (Form.size_lt_left hn) h₁ hg' h)
          · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
            exact .orI₂ (Prv.of_sel_aux n (Form.size_lt_right hn) h₂ hg' h)
      | @ex A hA =>
          obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
          refine .exE [] h fun a _ => .exI (.fvar a) trivial ?_
          refine Prv.of_sel_aux n (by rw [Form.size_openAt]; exact Nat.lt_of_succ_lt_succ hn) (hA.openAt 0 _)
            (g := g') (by rw [ind_openAt]; exact hg') ?_
          rw [sel_openAt]
          exact .var (List.mem_cons.2 (Or.inl rfl))

/-- `[sel S g] ⊢q S`. -/
theorem Prv.of_sel {S : Form} (hS : IsSigma S) {g : Idx} (hg : g ∈ ind S) {Γ : List Form}
    (h : Prv Γ (sel S g)) : Prv Γ S :=
  Prv.of_sel_aux _ (Nat.lt_succ_self _) hS hg h

theorem Prv.disj_sel_aux : ∀ (n : Nat) {S : Form}, S.size < n → IsSigma S →
    ∀ {Γ : List Form}, Prv Γ S → Prv Γ (Form.disj ((ind S).map (sel S)))
  | 0, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, hn, hS, Γ, h => by
      cases hS with
      | top => exact Prv.disj_intro (List.mem_map.2 ⟨.leaf, List.mem_cons.2 (Or.inl rfl), rfl⟩) h
      | pred P ts =>
          exact Prv.disj_intro (List.mem_map.2 ⟨.leaf, List.mem_cons.2 (Or.inl rfl), rfl⟩) h
      | @and A B h₁ h₂ =>
          refine Prv.disj_elim (Prv.disj_sel_aux n (Form.size_lt_left hn) h₁ (.andE₁ h)) fun C hC => ?_
          obtain ⟨g₁, hg₁, rfl⟩ := List.mem_map.1 hC
          have hB : Prv (sel A g₁ :: Γ) B :=
            (Prv.andE₂ h).weaken fun D hD => List.mem_cons.2 (Or.inr hD)
          refine Prv.disj_elim (Prv.disj_sel_aux n (Form.size_lt_right hn) h₂ hB) fun D hD => ?_
          obtain ⟨g₂, hg₂, rfl⟩ := List.mem_map.1 hD
          refine Prv.disj_intro (A := sel (.and A B) (.pair g₁ g₂))
            (List.mem_map.2 ⟨.pair g₁ g₂, List.mem_flatMap.2 ⟨g₁, hg₁, List.mem_map.2 ⟨g₂, hg₂, rfl⟩⟩,
              rfl⟩) ?_
          exact .andI (.var (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
            (.var (List.mem_cons.2 (Or.inl rfl)))
      | @or A B h₁ h₂ =>
          refine .orE h ?_ ?_
          · refine Prv.disj_elim (Prv.disj_sel_aux n (Form.size_lt_left hn) h₁
              (.var (List.mem_cons.2 (Or.inl rfl)))) fun C hC => ?_
            obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hC
            exact Prv.disj_intro (A := sel (.or A B) (.inl g))
              (List.mem_map.2 ⟨.inl g, List.mem_append.2 (Or.inl (List.mem_map.2 ⟨g, hg, rfl⟩)), rfl⟩)
              (.var (List.mem_cons.2 (Or.inl rfl)))
          · refine Prv.disj_elim (Prv.disj_sel_aux n (Form.size_lt_right hn) h₂
              (.var (List.mem_cons.2 (Or.inl rfl)))) fun C hC => ?_
            obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hC
            exact Prv.disj_intro (A := sel (.or A B) (.inr g))
              (List.mem_map.2 ⟨.inr g, List.mem_append.2 (Or.inr (List.mem_map.2 ⟨g, hg, rfl⟩)), rfl⟩)
              (.var (List.mem_cons.2 (Or.inl rfl)))
      | @ex A hA =>
          refine .exE [] h fun a _ => ?_
          refine Prv.disj_elim (Prv.disj_sel_aux n (by rw [Form.size_openAt]; exact Nat.lt_of_succ_lt_succ hn)
            (hA.openAt 0 (.fvar a)) (.var (List.mem_cons.2 (Or.inl rfl)))) fun C hC => ?_
          obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hC
          rw [ind_openAt] at hg
          refine Prv.disj_intro (A := sel (.exists_ A) (.ex g))
            (List.mem_map.2 ⟨.ex g, List.mem_map.2 ⟨g, hg, rfl⟩, rfl⟩) ?_
          refine .exI (.fvar a) trivial ?_
          rw [← sel_openAt]
          exact .var (List.mem_cons.2 (Or.inl rfl))

/-- `[S] ⊢q ⋁_{g ∈ ind S} sel S g`. -/
theorem Prv.disj_sel {S : Form} (hS : IsSigma S) {Γ : List Form} (h : Prv Γ S) :
    Prv Γ (Form.disj ((ind S).map (sel S))) :=
  Prv.disj_sel_aux _ (Nat.lt_succ_self _) hS h

/-- The same, in every Kripke model: a Σ-formula is forced exactly when one of
its selections is. -/
theorem KModel.force_iff_sel (M : KModel) {S : Form} (hS : IsSigma S) :
    ∀ (s : M.S) (ρ : String → M.D) (β : List M.D),
      M.force S s ρ β ↔ ∃ g ∈ ind S, M.force (sel S g) s ρ β := by
  induction hS with
  | top =>
      intro s ρ β
      exact ⟨fun h => ⟨.leaf, List.mem_cons.2 (Or.inl rfl), h⟩,
        fun ⟨g, _, h⟩ => by rwa [sel_top] at h⟩
  | pred P ts =>
      intro s ρ β
      exact ⟨fun h => ⟨.leaf, List.mem_cons.2 (Or.inl rfl), h⟩,
        fun ⟨g, _, h⟩ => by rwa [sel_pred] at h⟩
  | and _ _ ih₁ ih₂ =>
      intro s ρ β
      constructor
      · rintro ⟨h₁, h₂⟩
        obtain ⟨g₁, hg₁, h₁⟩ := (ih₁ s ρ β).1 h₁
        obtain ⟨g₂, hg₂, h₂⟩ := (ih₂ s ρ β).1 h₂
        exact ⟨.pair g₁ g₂, List.mem_flatMap.2 ⟨g₁, hg₁, List.mem_map.2 ⟨g₂, hg₂, rfl⟩⟩, h₁, h₂⟩
      · rintro ⟨g, hg, h⟩
        obtain ⟨g₁, hg₁, hg⟩ := List.mem_flatMap.1 hg
        obtain ⟨g₂, hg₂, rfl⟩ := List.mem_map.1 hg
        exact ⟨(ih₁ s ρ β).2 ⟨g₁, hg₁, h.1⟩, (ih₂ s ρ β).2 ⟨g₂, hg₂, h.2⟩⟩
  | or _ _ ih₁ ih₂ =>
      intro s ρ β
      constructor
      · rintro (h | h)
        · obtain ⟨g, hg, h⟩ := (ih₁ s ρ β).1 h
          exact ⟨.inl g, List.mem_append.2 (Or.inl (List.mem_map.2 ⟨g, hg, rfl⟩)), h⟩
        · obtain ⟨g, hg, h⟩ := (ih₂ s ρ β).1 h
          exact ⟨.inr g, List.mem_append.2 (Or.inr (List.mem_map.2 ⟨g, hg, rfl⟩)), h⟩
      · rintro ⟨g, hg, h⟩
        rcases List.mem_append.1 hg with hg | hg
        · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
          exact Or.inl ((ih₁ s ρ β).2 ⟨g', hg', h⟩)
        · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
          exact Or.inr ((ih₂ s ρ β).2 ⟨g', hg', h⟩)
  | ex _ ih =>
      intro s ρ β
      constructor
      · rintro ⟨d, hd, h⟩
        obtain ⟨g, hg, h⟩ := (ih s ρ (d :: β)).1 h
        exact ⟨.ex g, List.mem_map.2 ⟨g, hg, rfl⟩, d, hd, h⟩
      · rintro ⟨g, hg, h⟩
        obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
        obtain ⟨d, hd, h⟩ := h
        exact ⟨d, hd, (ih s ρ (d :: β)).2 ⟨g', hg', h⟩⟩

/-! ## (N3) A clause of Definition 5.1 is its Horn clauses -/

/-- Congruence of `∀x₁…xₘ`: to get from a context of `∀x̃`-formulas to a
`∀x̃`-formula it is enough to do so at every instance. -/
theorem Prv.foralls_congr : ∀ (m : Nat) (Γ : List Form) (B : Form),
    (∀ ts : List Tm, ts.length = m → (∀ t ∈ ts, Tm.lcAt 0 t) →
      Prv (Γ.map (Form.instAll ts)) (Form.instAll ts B)) →
    Prv (Γ.map (Form.foralls m)) (Form.foralls m B)
  | 0, _, _, h => h [] rfl fun _ h => nomatch h
  | m + 1, Γ, B, h => by
      refine .allI [] fun a _ => ?_
      show Prv _ ((Form.foralls m B).openAt 0 (.fvar a))
      rw [Form.openAt_foralls, Nat.zero_add]
      refine Prv.cutAll (Γ' := (Γ.map fun A => A.openAt m (.fvar a)).map (Form.foralls m)) ?_ ?_
      · intro C hC
        obtain ⟨A', hA', rfl⟩ := List.mem_map.1 hC
        obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA'
        have := Prv.allE (.fvar a) trivial
          (Prv.var (Γ := Γ.map (Form.foralls (m + 1))) (List.mem_map.2 ⟨A, hA, rfl⟩))
        rwa [Form.openAt_foralls, Nat.zero_add] at this
      · refine Prv.foralls_congr m _ _ fun ts hts hlc => ?_
        have := h (.fvar a :: ts) (by rw [List.length_cons, hts]) fun t ht => by
          rcases List.mem_cons.1 ht with rfl | ht
          · trivial
          · exact hlc t ht
        have e : ∀ A : Form, Form.instAll (.fvar a :: ts) A = Form.instAll ts (A.openAt m (.fvar a)) :=
          fun A => by rw [← hts]; rfl
        rw [List.map_map]
        rw [e B] at this
        have e' : Γ.map (Form.instAll (.fvar a :: ts))
            = Γ.map (Form.instAll ts ∘ fun A => A.openAt m (.fvar a)) :=
          List.map_congr_left fun A _ => e A
        rw [e'] at this
        exact this

/-- The Horn clauses of a Definition 5.1 clause: one for each index of its body. -/
def Clause.toHorn (c : Clause) : List Horn :=
  (ind c.body).attach.map fun g =>
    { arity := c.arity, body := sel c.body g.1, body_pp := c.body_sigma.pp_sel g.2,
      head := c.head, args := headVars c.arity, modal := c.modal, q := c.q }

theorem Clause.map_form_toHorn (c : Clause) :
    c.toHorn.map Horn.form
      = ((ind c.body).map fun g => Form.imp (sel c.body g) c.headForm).map (Form.foralls c.arity) := by
  rw [Clause.toHorn, List.map_map, List.map_map]
  exact List.attach_map_val (l := ind c.body)
    (f := fun g => Form.foralls c.arity (.imp (sel c.body g) c.headForm))

/-- `[c.form] ⊢q h.form` for each of its Horn clauses. -/
theorem Clause.prv_toHorn (c : Clause) {h : Horn} (hh : h ∈ c.toHorn) : Prv [c.form] h.form := by
  obtain ⟨⟨g, hg⟩, _, rfl⟩ := List.mem_map.1 hh
  show Prv ([Form.imp c.body c.headForm].map (Form.foralls c.arity))
    (Form.foralls c.arity (.imp (sel c.body g) c.headForm))
  refine Prv.foralls_congr c.arity _ _ fun ts _ _ => ?_
  show Prv [Form.instAll ts (.imp c.body c.headForm)] (Form.instAll ts (.imp (sel c.body g) c.headForm))
  rw [Form.instAll_imp, Form.instAll_imp, ← sel_instAll]
  refine .impI (.impE (.var (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))) ?_)
  exact Prv.of_sel (c.body_sigma.instAll ts) (by rw [ind_instAll]; exact hg)
    (.var (List.mem_cons.2 (Or.inl rfl)))

/-- `c.toHorn.forms ⊢q c.form`. -/
theorem Clause.prv_of_toHorn (c : Clause) : Prv (c.toHorn.map Horn.form) c.form := by
  rw [Clause.map_form_toHorn]
  refine Prv.foralls_congr c.arity _ (.imp c.body c.headForm) fun ts _ _ => ?_
  rw [List.map_map, Form.instAll_imp]
  refine .impI ?_
  refine Prv.disj_elim (Prv.disj_sel (c.body_sigma.instAll ts)
    (.var (List.mem_cons.2 (Or.inl rfl)))) fun C hC => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hC
  rw [ind_instAll] at hg
  refine .impE (.var ?_) (.var (List.mem_cons.2 (Or.inl rfl)))
  refine List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_map.2 ⟨g, hg, ?_⟩))))
  show Form.instAll ts (.imp (sel c.body g) c.headForm) = _
  rw [Form.instAll_imp, sel_instAll]

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.IsSigma.pp_sel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IsSigma.pp_sel

/-- info: 'LaxLogic.QLL.sel_openAt' depends on axioms: [propext] -/
#guard_msgs in #print axioms sel_openAt

/-- info: 'LaxLogic.QLL.Prv.of_sel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Prv.of_sel

/-- info: 'LaxLogic.QLL.Prv.disj_sel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Prv.disj_sel

/-- info: 'LaxLogic.QLL.KModel.force_iff_sel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms KModel.force_iff_sel

/-- info: 'LaxLogic.QLL.Prv.foralls_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Prv.foralls_congr

/-- info: 'LaxLogic.QLL.Clause.prv_toHorn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Clause.prv_toHorn

/-- info: 'LaxLogic.QLL.Clause.prv_of_toHorn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Clause.prv_of_toHorn

end LaxLogic.QLL
