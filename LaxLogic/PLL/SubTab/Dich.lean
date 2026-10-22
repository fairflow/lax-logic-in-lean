import LaxLogic.PLL.SubTab.Steps

/-!
# The subframe tableau: the dichotomy (closed tableau or open tree)

2026-10-15.  Every signed sequent over a closed universe has a
closed tableau, or an open saturated tree (`Good`) whose root covers it.
By strong induction on `meas` (`SubTab/Steps.lean`).

Fragment first (CLAUDE.md rule 8): `dich_boxFree` is the ◯-free instance;
`dich` is PLL.
-/

open PLLFormula

namespace PLLND
namespace SubTab

/-! ## Open trees -/

inductive OTree where
  | node (isS : Bool) (Γ Δ : List PLLFormula) (kids : List OTree)

namespace OTree
def isS : OTree → Bool | node b _ _ _ => b
def ant : OTree → List PLLFormula | node _ Γ _ _ => Γ
def suc : OTree → List PLLFormula | node _ _ Δ _ => Δ
def kids : OTree → List OTree | node _ _ _ ks => ks
end OTree

/-- Every demand of the world has a child serving it. -/
structure Demanded (isS : Bool) (Γ Δ : List PLLFormula) (kids : List OTree) : Prop where
  impR : ∀ A B, PLLFormula.ifThen A B ∈ Δ → A ∉ Γ →
    ∃ k ∈ kids, k.isS = false ∧ A ∈ k.ant ∧ B ∈ k.suc
  boxR : ∀ A, isS = false → PLLFormula.somehow A ∈ Δ → ∃ k ∈ kids, k.isS = true ∧ A ∈ k.suc

/-- An open tree: every world consistent, saturated, its demands served, its
true formulas carried to its children. -/
inductive Good : OTree → Prop
  | mk {isS : Bool} {Γ Δ : List PLLFormula} {kids : List OTree}
      (noBot : PLLFormula.falsePLL ∉ Γ) (disj : ∀ A ∈ Γ, A ∉ Δ)
      (sat : Saturated isS Γ Δ) (dem : Demanded isS Γ Δ kids)
      (sub : ∀ k ∈ kids, Γ ⊆ k.ant) (good : ∀ k ∈ kids, Good k) :
      Good (.node isS Γ Δ kids)

/-- The tree's root extends the sequent. -/
def Covers (t : OTree) (s : SSeq) : Prop := t.isS = s.isS ∧ s.ant ⊆ t.ant ∧ s.suc ⊆ t.suc

/-- The two outcomes. -/
def Outcome (s : SSeq) : Prop := (∃ c, check s c = true) ∨ (∃ t, Good t ∧ Covers t s)

theorem collect (L : List Dem) (P : Dem → Prop) (Q : Dem → OTree → Prop)
    (h : ∀ d ∈ L, P d ∨ ∃ t, Q d t) :
    (∃ d ∈ L, P d) ∨
      ∃ ts : List OTree, (∀ d ∈ L, ∃ t ∈ ts, Q d t) ∧ (∀ t ∈ ts, ∃ d ∈ L, Q d t) := by
  induction L with
  | nil => exact .inr ⟨[], fun _ hd => absurd hd List.not_mem_nil,
      fun _ ht => absurd ht List.not_mem_nil⟩
  | cons d L ih =>
    rcases h d List.mem_cons_self with hp | ⟨t, ht⟩
    · exact .inl ⟨d, List.mem_cons_self, hp⟩
    · rcases ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) with
        ⟨d', hd', hp⟩ | ⟨ts, h1, h2⟩
      · exact .inl ⟨d', List.mem_cons_of_mem _ hd', hp⟩
      · refine .inr ⟨t :: ts, fun d' hd' => ?_, fun t' ht' => ?_⟩
        · rcases List.mem_cons.mp hd' with e | hd'
          · subst e; exact ⟨t, List.mem_cons_self, ht⟩
          · obtain ⟨t'', ht'', hq⟩ := h1 d' hd'
            exact ⟨t'', List.mem_cons_of_mem _ ht'', hq⟩
        · rcases List.mem_cons.mp ht' with e | ht'
          · subst e; exact ⟨d, List.mem_cons_self, ht⟩
          · obtain ⟨d'', hd'', hq⟩ := h2 t' ht'
            exact ⟨d'', List.mem_cons_of_mem _ hd'', hq⟩

/-- A one-premise rule: a closed premise closes the conclusion; an open tree
for the premise covers the conclusion. -/
theorem step1 {s s' : SSeq} {r : TCert → TCert}
    (hcert : ∀ c, check s' c = true → check s (r c) = true)
    (hb : s'.isS = s.isS) (ha : s.ant ⊆ s'.ant) (hs : s.suc ⊆ s'.suc)
    (h : Outcome s') : Outcome s := by
  rcases h with ⟨c, hc⟩ | ⟨t, hg, hb', ha', hs'⟩
  · exact .inl ⟨r c, hcert c hc⟩
  · exact .inr ⟨t, hg, hb'.trans hb, fun _ hx => ha' (ha hx), fun _ hx => hs' (hs hx)⟩

/-- A two-premise rule: both closed close the conclusion; either open covers it. -/
theorem step2 {s s₁ s₂ : SSeq} {r : TCert → TCert → TCert}
    (hcert : ∀ c₁ c₂, check s₁ c₁ = true → check s₂ c₂ = true → check s (r c₁ c₂) = true)
    (hb₁ : s₁.isS = s.isS) (ha₁ : s.ant ⊆ s₁.ant) (hs₁ : s.suc ⊆ s₁.suc)
    (hb₂ : s₂.isS = s.isS) (ha₂ : s.ant ⊆ s₂.ant) (hs₂ : s.suc ⊆ s₂.suc)
    (h₁ : Outcome s₁) (h₂ : Outcome s₂) : Outcome s := by
  rcases h₁ with ⟨c₁, hc₁⟩ | ⟨t, hg, hb', ha', hs'⟩
  · rcases h₂ with ⟨c₂, hc₂⟩ | ⟨t, hg, hb', ha', hs'⟩
    · exact .inl ⟨r c₁ c₂, hcert c₁ c₂ hc₁ hc₂⟩
    · exact .inr ⟨t, hg, hb'.trans hb₂, fun _ hx => ha' (ha₂ hx), fun _ hx => hs' (hs₂ hx)⟩
  · exact .inr ⟨t, hg, hb'.trans hb₁, fun _ hx => ha' (ha₁ hx), fun _ hx => hs' (hs₁ hx)⟩

theorem sub_app {l : List PLLFormula} (as : List PLLFormula) : l ⊆ l ++ as :=
  List.subset_append_left l as

theorem app_sub {l as U : List PLLFormula} (h : l ⊆ U) (h' : ∀ a ∈ as, a ∈ U) :
    l ++ as ⊆ U := List.append_subset.mpr ⟨h, fun a ha => h' a ha⟩

theorem mem_app_last {l : List PLLFormula} {A : PLLFormula} : A ∈ l ++ [A] :=
  List.mem_append_right l List.mem_cons_self

theorem mem_app_two₁ {l : List PLLFormula} {A B : PLLFormula} : A ∈ l ++ [A, B] :=
  List.mem_append_right l List.mem_cons_self

theorem mem_app_two₂ {l : List PLLFormula} {A B : PLLFormula} : B ∈ l ++ [A, B] :=
  List.mem_append_right l (List.mem_cons_of_mem _ List.mem_cons_self)

/-- No `◯` in the universe. -/
def NoBox (U : List PLLFormula) : Prop := ∀ A, PLLFormula.somehow A ∉ U

/-- **The dichotomy, ◯-free instance.** -/
theorem dich_boxFree (U : List PLLFormula) (hU : Closed U) (hBF : NoBox U) :
    ∀ (n : Nat) (s : SSeq), meas U s.isS s.ant s.suc = n → s.ant ⊆ U → s.suc ⊆ U →
      Outcome s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn hΓ hΔ
  obtain ⟨isS, Γ, Δ⟩ := s
  have IH : ∀ s' : SSeq, meas U s'.isS s'.ant s'.suc < n → s'.ant ⊆ U → s'.suc ⊆ U →
      Outcome s' := fun s' hlt h1 h2 => ih _ hlt s' rfl h1 h2
  subst hn
  simp only at hΓ hΔ IH
  cases hc : closeCert Γ Δ with
  | some c => exact .inl ⟨c, closeCert_some hc⟩
  | none =>
  obtain ⟨noBot, disj⟩ := closeCert_none hc
  cases hs : findStep isS Γ Δ with
  | some st =>
    have pre := findStep_some hs
    cases st with
    | andL A B =>
      obtain ⟨hm, hn⟩ := pre
      obtain ⟨hA, hB⟩ := hU.and A B (hΓ hm)
      have hlt : meas U isS (Γ ++ [A, B]) Δ < meas U isS Γ Δ := by
        rcases Decidable.em (A ∈ Γ) with ha | ha
        · exact meas_ant isS hB (fun hb => hn ⟨ha, hb⟩) (sub_app _) mem_app_two₂
        · exact meas_ant isS hA ha (sub_app _) mem_app_two₁
      refine step1 (s' := ⟨isS, Γ ++ [A, B], Δ⟩) (r := .andL A B) (fun c hc => ?_) rfl
        (sub_app _) (fun _ h => h)
        (IH _ hlt (app_sub hΓ (all_two hA hB)) hΔ)
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hm, hc⟩
    | orL A B =>
      obtain ⟨hm, ha, hb⟩ := pre
      obtain ⟨hA, hB⟩ := hU.or A B (hΓ hm)
      refine step2 (s₁ := ⟨isS, Γ ++ [A], Δ⟩) (s₂ := ⟨isS, Γ ++ [B], Δ⟩) (r := .orL A B)
        (fun c₁ c₂ h₁ h₂ => ?_) rfl (sub_app _) (fun _ h => h) rfl (sub_app _) (fun _ h => h)
        (IH _ (meas_ant isS hA ha (sub_app _) mem_app_last) (app_sub hΓ (all_one hA)) hΔ)
        (IH _ (meas_ant isS hB hb (sub_app _) mem_app_last) (app_sub hΓ (all_one hB)) hΔ)
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hm, h₁⟩, h₂⟩
    | impL A B =>
      obtain ⟨hm, ha, hb⟩ := pre
      obtain ⟨hA, hB⟩ := hU.imp A B (hΓ hm)
      refine step2 (s₁ := ⟨isS, Γ, Δ ++ [A]⟩) (s₂ := ⟨isS, Γ ++ [B], Δ⟩) (r := .impL A B)
        (fun c₁ c₂ h₁ h₂ => ?_) rfl (fun _ h => h) (sub_app _) rfl (sub_app _) (fun _ h => h)
        (IH _ (meas_suc isS hA ha (sub_app _) mem_app_last) hΓ (app_sub hΔ (all_one hA)))
        (IH _ (meas_ant isS hB hb (sub_app _) mem_app_last) (app_sub hΓ (all_one hB)) hΔ)
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hm, h₁⟩, h₂⟩
    | boxL A => exact absurd (hΓ pre.2.1) (hBF A)
    | andR A B =>
      obtain ⟨hm, ha, hb⟩ := pre
      obtain ⟨hA, hB⟩ := hU.and A B (hΔ hm)
      refine step2 (s₁ := ⟨isS, Γ, Δ ++ [A]⟩) (s₂ := ⟨isS, Γ, Δ ++ [B]⟩) (r := .andR A B)
        (fun c₁ c₂ h₁ h₂ => ?_) rfl (fun _ h => h) (sub_app _) rfl (fun _ h => h) (sub_app _)
        (IH _ (meas_suc isS hA ha (sub_app _) mem_app_last) hΓ (app_sub hΔ (all_one hA)))
        (IH _ (meas_suc isS hB hb (sub_app _) mem_app_last) hΓ (app_sub hΔ (all_one hB)))
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hm, h₁⟩, h₂⟩
    | orR A B =>
      obtain ⟨hm, hn⟩ := pre
      obtain ⟨hA, hB⟩ := hU.or A B (hΔ hm)
      have hlt : meas U isS Γ (Δ ++ [A, B]) < meas U isS Γ Δ := by
        rcases Decidable.em (A ∈ Δ) with ha | ha
        · exact meas_suc isS hB (fun hb => hn ⟨ha, hb⟩) (sub_app _) mem_app_two₂
        · exact meas_suc isS hA ha (sub_app _) mem_app_two₁
      refine step1 (s' := ⟨isS, Γ, Δ ++ [A, B]⟩) (r := .orR A B) (fun c hc => ?_) rfl
        (fun _ h => h) (sub_app _) (IH _ hlt hΓ (app_sub hΔ (all_two hA hB)))
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hm, hc⟩
    | impLoc A B =>
      obtain ⟨hm, ha, hb⟩ := pre
      obtain ⟨hA, hB⟩ := hU.imp A B (hΔ hm)
      refine step1 (s' := ⟨isS, Γ, Δ ++ [B]⟩) (r := .impLoc A B) (fun c hc => ?_) rfl
        (fun _ h => h) (sub_app _)
        (IH _ (meas_suc isS hB hb (sub_app _) mem_app_last) hΓ (app_sub hΔ (all_one hB)))
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hm, ha⟩, hc⟩
    | boxLoc A => exact absurd (hΔ pre.2.1) (hBF A)
  | none =>
    have sat := findStep_none hs
    have hD : ∀ d ∈ demands isS Γ Δ,
        (∃ c, check (d.child Γ) c = true) ∨ ∃ t, Good t ∧ Covers t (d.child Γ) := by
      intro d hd
      have hdm := mem_demands hd
      cases d with
      | imp A B =>
        obtain ⟨hm, ha⟩ := hdm
        obtain ⟨hA, hB⟩ := hU.imp A B (hΔ hm)
        exact IH ⟨false, Γ ++ [A], [B]⟩ (meas_impR isS hA ha) (app_sub hΓ (all_one hA))
          (all_one hB)
      | box A => exact absurd (hΔ hdm.2) (hBF A)
    rcases collect _ _ _ hD with ⟨d, hd, c, hc⟩ | ⟨ts, h1, h2⟩
    · exact .inl ⟨d.cert c, demand_check hd hc⟩
    · refine .inr ⟨.node isS Γ Δ ts, .mk noBot disj sat ⟨?_, ?_⟩ ?_ ?_,
        rfl, fun _ h => h, fun _ h => h⟩
      · intro A B hm ha
        obtain ⟨t, ht, _, hb, hat, hst⟩ := h1 _ (imp_mem_demands hm ha)
        exact ⟨t, ht, hb, hat mem_app_last, hst List.mem_cons_self⟩
      · intro A hS hm
        subst hS
        obtain ⟨t, ht, _, hb, _, hst⟩ := h1 _ (box_mem_demands (Γ := Γ) hm)
        exact ⟨t, ht, hb, hst List.mem_cons_self⟩
      · intro t ht
        obtain ⟨d, _, _, _, hat, _⟩ := h2 t ht
        cases d with
        | imp A B => exact fun _ hx => hat (sub_app _ hx)
        | box A => exact hat
      · intro t ht
        obtain ⟨d, _, hg, _⟩ := h2 t ht
        exact hg

/-- **The dichotomy** (PLL): the ◯-free proof, with its three ◯ cases filled in. -/
theorem dich (U : List PLLFormula) (hU : Closed U) :
    ∀ (n : Nat) (s : SSeq), meas U s.isS s.ant s.suc = n → s.ant ⊆ U → s.suc ⊆ U →
      Outcome s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn hΓ hΔ
  obtain ⟨isS, Γ, Δ⟩ := s
  have IH : ∀ s' : SSeq, meas U s'.isS s'.ant s'.suc < n → s'.ant ⊆ U → s'.suc ⊆ U →
      Outcome s' := fun s' hlt h1 h2 => ih _ hlt s' rfl h1 h2
  subst hn
  simp only at hΓ hΔ IH
  cases hc : closeCert Γ Δ with
  | some c => exact .inl ⟨c, closeCert_some hc⟩
  | none =>
  obtain ⟨noBot, disj⟩ := closeCert_none hc
  cases hs : findStep isS Γ Δ with
  | some st =>
    have pre := findStep_some hs
    cases st with
    | andL A B =>
      obtain ⟨hm, hn⟩ := pre
      obtain ⟨hA, hB⟩ := hU.and A B (hΓ hm)
      have hlt : meas U isS (Γ ++ [A, B]) Δ < meas U isS Γ Δ := by
        rcases Decidable.em (A ∈ Γ) with ha | ha
        · exact meas_ant isS hB (fun hb => hn ⟨ha, hb⟩) (sub_app _) mem_app_two₂
        · exact meas_ant isS hA ha (sub_app _) mem_app_two₁
      refine step1 (s' := ⟨isS, Γ ++ [A, B], Δ⟩) (r := .andL A B) (fun c hc => ?_) rfl
        (sub_app _) (fun _ h => h)
        (IH _ hlt (app_sub hΓ (all_two hA hB)) hΔ)
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hm, hc⟩
    | orL A B =>
      obtain ⟨hm, ha, hb⟩ := pre
      obtain ⟨hA, hB⟩ := hU.or A B (hΓ hm)
      refine step2 (s₁ := ⟨isS, Γ ++ [A], Δ⟩) (s₂ := ⟨isS, Γ ++ [B], Δ⟩) (r := .orL A B)
        (fun c₁ c₂ h₁ h₂ => ?_) rfl (sub_app _) (fun _ h => h) rfl (sub_app _) (fun _ h => h)
        (IH _ (meas_ant isS hA ha (sub_app _) mem_app_last) (app_sub hΓ (all_one hA)) hΔ)
        (IH _ (meas_ant isS hB hb (sub_app _) mem_app_last) (app_sub hΓ (all_one hB)) hΔ)
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hm, h₁⟩, h₂⟩
    | impL A B =>
      obtain ⟨hm, ha, hb⟩ := pre
      obtain ⟨hA, hB⟩ := hU.imp A B (hΓ hm)
      refine step2 (s₁ := ⟨isS, Γ, Δ ++ [A]⟩) (s₂ := ⟨isS, Γ ++ [B], Δ⟩) (r := .impL A B)
        (fun c₁ c₂ h₁ h₂ => ?_) rfl (fun _ h => h) (sub_app _) rfl (sub_app _) (fun _ h => h)
        (IH _ (meas_suc isS hA ha (sub_app _) mem_app_last) hΓ (app_sub hΔ (all_one hA)))
        (IH _ (meas_ant isS hB hb (sub_app _) mem_app_last) (app_sub hΓ (all_one hB)) hΔ)
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hm, h₁⟩, h₂⟩
    | boxL A =>
      obtain ⟨hS, hm, ha⟩ := pre
      have hA := hU.box A (hΓ hm)
      refine step1 (s' := ⟨isS, Γ ++ [A], Δ⟩) (r := .boxL A) (fun c hc => ?_) rfl
        (sub_app _) (fun _ h => h)
        (IH _ (meas_ant isS hA ha (sub_app _) mem_app_last) (app_sub hΓ (all_one hA)) hΔ)
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hS, hm⟩, hc⟩
    | andR A B =>
      obtain ⟨hm, ha, hb⟩ := pre
      obtain ⟨hA, hB⟩ := hU.and A B (hΔ hm)
      refine step2 (s₁ := ⟨isS, Γ, Δ ++ [A]⟩) (s₂ := ⟨isS, Γ, Δ ++ [B]⟩) (r := .andR A B)
        (fun c₁ c₂ h₁ h₂ => ?_) rfl (fun _ h => h) (sub_app _) rfl (fun _ h => h) (sub_app _)
        (IH _ (meas_suc isS hA ha (sub_app _) mem_app_last) hΓ (app_sub hΔ (all_one hA)))
        (IH _ (meas_suc isS hB hb (sub_app _) mem_app_last) hΓ (app_sub hΔ (all_one hB)))
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hm, h₁⟩, h₂⟩
    | orR A B =>
      obtain ⟨hm, hn⟩ := pre
      obtain ⟨hA, hB⟩ := hU.or A B (hΔ hm)
      have hlt : meas U isS Γ (Δ ++ [A, B]) < meas U isS Γ Δ := by
        rcases Decidable.em (A ∈ Δ) with ha | ha
        · exact meas_suc isS hB (fun hb => hn ⟨ha, hb⟩) (sub_app _) mem_app_two₂
        · exact meas_suc isS hA ha (sub_app _) mem_app_two₁
      refine step1 (s' := ⟨isS, Γ, Δ ++ [A, B]⟩) (r := .orR A B) (fun c hc => ?_) rfl
        (fun _ h => h) (sub_app _) (IH _ hlt hΓ (app_sub hΔ (all_two hA hB)))
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hm, hc⟩
    | impLoc A B =>
      obtain ⟨hm, ha, hb⟩ := pre
      obtain ⟨hA, hB⟩ := hU.imp A B (hΔ hm)
      refine step1 (s' := ⟨isS, Γ, Δ ++ [B]⟩) (r := .impLoc A B) (fun c hc => ?_) rfl
        (fun _ h => h) (sub_app _)
        (IH _ (meas_suc isS hB hb (sub_app _) mem_app_last) hΓ (app_sub hΔ (all_one hB)))
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hm, ha⟩, hc⟩
    | boxLoc A =>
      obtain ⟨hS, hm, ha⟩ := pre
      have hA := hU.box A (hΔ hm)
      refine step1 (s' := ⟨isS, Γ, Δ ++ [A]⟩) (r := .boxLoc A) (fun c hc => ?_) rfl
        (fun _ h => h) (sub_app _)
        (IH _ (meas_suc isS hA ha (sub_app _) mem_app_last) hΓ (app_sub hΔ (all_one hA)))
      simp only [check, mem, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hS, hm⟩, hc⟩
  | none =>
    have sat := findStep_none hs
    have hD : ∀ d ∈ demands isS Γ Δ,
        (∃ c, check (d.child Γ) c = true) ∨ ∃ t, Good t ∧ Covers t (d.child Γ) := by
      intro d hd
      have hdm := mem_demands hd
      cases d with
      | imp A B =>
        obtain ⟨hm, ha⟩ := hdm
        obtain ⟨hA, hB⟩ := hU.imp A B (hΔ hm)
        exact IH ⟨false, Γ ++ [A], [B]⟩ (meas_impR isS hA ha) (app_sub hΓ (all_one hA))
          (all_one hB)
      | box A =>
        obtain ⟨hS, hm⟩ := hdm
        subst hS
        have hA := hU.box A (hΔ hm)
        exact IH ⟨true, Γ, [A]⟩ meas_boxR hΓ (all_one hA)
    rcases collect _ _ _ hD with ⟨d, hd, c, hc⟩ | ⟨ts, h1, h2⟩
    · exact .inl ⟨d.cert c, demand_check hd hc⟩
    · refine .inr ⟨.node isS Γ Δ ts, .mk noBot disj sat ⟨?_, ?_⟩ ?_ ?_,
        rfl, fun _ h => h, fun _ h => h⟩
      · intro A B hm ha
        obtain ⟨t, ht, _, hb, hat, hst⟩ := h1 _ (imp_mem_demands hm ha)
        exact ⟨t, ht, hb, hat mem_app_last, hst List.mem_cons_self⟩
      · intro A hS hm
        subst hS
        obtain ⟨t, ht, _, hb, _, hst⟩ := h1 _ (box_mem_demands (Γ := Γ) hm)
        exact ⟨t, ht, hb, hst List.mem_cons_self⟩
      · intro t ht
        obtain ⟨d, _, _, _, hat, _⟩ := h2 t ht
        cases d with
        | imp A B => exact fun _ hx => hat (sub_app _ hx)
        | box A => exact hat
      · intro t ht
        obtain ⟨d, _, hg, _⟩ := h2 t ht
        exact hg

end SubTab
end PLLND

#axioms_within PLLND.SubTab.dich_boxFree [propext, Quot.sound]
#axioms_within PLLND.SubTab.dich [propext, Quot.sound]
