/-
# `LaxLogic.QLL.Bridge` — the proof-term calculus and the erased one

`Derives` is Fig. 5 with its proof terms; `Prv` is the same rules with the
terms erased and the two binding rules quantified cofinitely.  Everything
proof-theoretic is proved of the first and everything model-theoretic of the
second, so the two have to be connected or the completeness theorem says
nothing about the calculus the report actually presents.

**Erasure.**  `Derives.erase` below.  The hypothesis is the same one the
soundness theorem of `Sound.lean` carries — the proof term is locally closed in
its individual indices — and it is not decoration: `Derives.allE` places no
condition on the instantiated term, so a derivation may instantiate at a loose
de Bruijn index, which `Prv.allE` rightly refuses.  Local closedness of the
proof term supplies exactly the missing side condition, since `Pf.lcI` on
`inst t p` demands `Tm.lcAt` of `t`.

The two binding rules are where the exists-fresh and cofinite presentations
meet: `Derives` supplies a derivation at *one* fresh name, and
`Prv.allI_of_fresh` and `Prv.exE_of_fresh` (`ProvFresh.lean`) are what turn
that into the cofinite premise.

**The converse is not proved here**, and the reason is recorded in
`docs/qll-model-theory.md`: it needs an abstraction operation `closeP` on proof
terms together with its round trip against `openP`, which the development does
not have.  What holds without it is stated below as `Prv.derivable_iff`'s
missing half; it is a gap in the encoding, not in the mathematics.
-/
import LaxLogic.QLL.Deriv
import LaxLogic.QLL.ProvFresh
import LaxLogic.QLL.Abstract

namespace LaxLogic.QLL

/-! ## Forgetting the proof terms -/

/-- The formulas of a context. -/
def Ctx.forms (Γ : Ctx) : List Form := Γ.map Prod.snd

@[simp] theorem Ctx.forms_cons (e : Pf × Form) (Γ : Ctx) :
    Ctx.forms (e :: Γ) = e.2 :: Ctx.forms Γ := rfl

theorem Ctx.mem_forms {Γ : Ctx} {p : Pf} {A : Form} (h : (p, A) ∈ Γ) :
    A ∈ Ctx.forms Γ := List.mem_map_of_mem h

/-- A name free in the erased context was free in the context. -/
theorem Ctx.ctxFv_sub_fvI : ∀ (Γ : Ctx) (x : String),
    x ∈ ctxFv (Ctx.forms Γ) → x ∈ Ctx.fvI Γ
  | [],          _, h => by simp [Ctx.forms, ctxFv] at h
  | (p, A) :: Γ, x, h => by
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (List.mem_append_right _ h)
      · exact List.mem_append_right _ (Ctx.ctxFv_sub_fvI Γ x h)

/-! ## Erasure -/

/-- **Erasure**: a derivation with a locally closed proof term erases to a
derivation of the same formula from the same context, in the calculus the
model theory is about. -/
theorem Derives.erase : ∀ {p : Pf} {Γ : Ctx} {A : Form},
    Derives p Γ A → Pf.lcI 0 p → Prv (Ctx.forms Γ) A := by
  intro p Γ A d
  induction d with
  | var h => intro _; exact .var (Ctx.mem_forms h)
  | topI => intro _; exact .topI
  | botE _ ih => intro h; exact .botE (ih h.2)
  | andI _ _ ih₁ ih₂ => intro h; exact .andI (ih₁ h.1) (ih₂ h.2)
  | andE₁ _ ih => intro h; exact .andE₁ (ih h)
  | andE₂ _ ih => intro h; exact .andE₂ (ih h)
  | orI₁ _ ih => intro h; exact .orI₁ (ih h)
  | orI₂ _ ih => intro h; exact .orI₂ (ih h)
  | @orE _ _ p q _ _ _ y z _ _ _ _ _ ih₀ ih₁ ih₂ =>
      intro h
      exact .orE (ih₀ h.1) (ih₁ (Pf.lcI_openP y p 0 0 h.2.1))
        (ih₂ (Pf.lcI_openP z q 0 0 h.2.2))
  | @impI _ p _ _ z _ _ ih => intro h; exact .impI (ih (Pf.lcI_openP z p 0 0 h))
  | impE _ _ ih₁ ih₂ => intro h; exact .impE (ih₁ h.1) (ih₂ h.2)
  | circI _ ih => intro h; exact .circI (ih h)
  | @circE _ _ _ b _ _ z _ _ _ ih₀ ih₁ =>
      intro h; exact .circE (ih₀ h.1) (ih₁ (Pf.lcI_openP z b 0 0 h.2))
  | @allI _ p A a ha _ ih =>
      intro h
      refine Prv.allI_of_fresh ?_ ha.2.2 (ih (Pf.lcI_openI p 0 (.fvar a) trivial h))
      exact fun hc => ha.1 (Ctx.ctxFv_sub_fvI _ a hc)
  | @allE _ _ _ B t _ hB ih =>
      intro h; subst hB; exact .allE t h.1 (ih h.2)
  | exI t _ ih => intro h; exact .exI t h.1 (ih h.2)
  | @exE _ _ p A K a z ha hK _ _ _ ih₀ ih₁ =>
      intro h
      refine Prv.exE_of_fresh ?_ ha.2.2 hK (ih₀ h.1)
        (ih₁ (Pf.lcI_openP z _ 0 0 (Pf.lcI_openI p 0 (.fvar a) trivial h.2)))
      exact fun hc => ha.1 (Ctx.ctxFv_sub_fvI _ a hc)

/-- The `Prop`-valued form. -/
theorem Derivable.erase {p : Pf} {Γ : Ctx} {A : Form}
    (h : Derivable p Γ A) (hp : Pf.lcI 0 p) : Prv (Ctx.forms Γ) A :=
  h.elim (fun d => d.erase hp)


/-! ## The converse

One rule stands in the way, and it is a defect in that rule rather than in the
bridge.  `botE` derives an *arbitrary* formula from `⊥`, and `Derives` records
that formula in the proof term as `exf A p`; so if the conclusion carries a
loose de Bruijn index — which `Prv.botE` permits, since it constrains its
conclusion not at all — the term it forces is not locally closed, and the
abstraction steps of `∀I` and `∃E` cannot proceed.  A formula with a loose index
is not a formula (`Lc.lean`), so the right reading is that `Prv.botE` is too
permissive.

Adding the condition to `Prv` itself is not available: `bigOr_elim` derives an
arbitrary `K` from the empty disjunction, and its callers in the completeness
proof supply formulas drawn from a theory, which are not locally closed in
general.  So the condition is isolated in `PrvC`, which is `Prv` with ex falso
restricted to genuine formulas.  `PrvC.toPrv` forgets it; the converse
`Prv → PrvC` is the one thing this file leaves open, and it is a question about
loose indices in cut formulas, not about the logic. -/

/-- `Prv` with ex falso restricted to locally closed conclusions. -/
inductive PrvC : List Form → Form → Prop where
  | var   {Γ A} : A ∈ Γ → PrvC Γ A
  | topI  {Γ} : PrvC Γ .top
  | botE  {Γ A} : Form.lc A → PrvC Γ .bot → PrvC Γ A
  | andI  {Γ A B} : PrvC Γ A → PrvC Γ B → PrvC Γ (.and A B)
  | andE₁ {Γ A B} : PrvC Γ (.and A B) → PrvC Γ A
  | andE₂ {Γ A B} : PrvC Γ (.and A B) → PrvC Γ B
  | orI₁  {Γ A B} : PrvC Γ A → PrvC Γ (.or A B)
  | orI₂  {Γ A B} : PrvC Γ B → PrvC Γ (.or A B)
  | orE   {Γ A B K} : PrvC Γ (.or A B) → PrvC (A :: Γ) K → PrvC (B :: Γ) K → PrvC Γ K
  | impI  {Γ A B} : PrvC (A :: Γ) B → PrvC Γ (.imp A B)
  | impE  {Γ A B} : PrvC Γ (.imp A B) → PrvC Γ A → PrvC Γ B
  | circI {Γ q A} : PrvC Γ A → PrvC Γ (.circ q A)
  | circE {Γ q A B} : PrvC Γ (.circ q A) → PrvC (A :: Γ) (.circ q B) → PrvC Γ (.circ q B)
  | allI  {Γ A} (L : List String) :
      (∀ a, a ∉ L → PrvC Γ (A.openWith a)) → PrvC Γ (.forall_ A)
  | allE  {Γ A} (t : Tm) : Tm.lcAt 0 t → PrvC Γ (.forall_ A) → PrvC Γ (A.openAt 0 t)
  | exI   {Γ A} (t : Tm) : Tm.lcAt 0 t → PrvC Γ (A.openAt 0 t) → PrvC Γ (.exists_ A)
  | exE   {Γ A K} (L : List String) :
      PrvC Γ (.exists_ A) → (∀ a, a ∉ L → PrvC (A.openWith a :: Γ) K) → PrvC Γ K

/-- Forgetting the side condition. -/
theorem PrvC.toPrv {Γ : List Form} {A : Form} (h : PrvC Γ A) : Prv Γ A := by
  induction h with
  | var h => exact .var h
  | topI => exact .topI
  | botE _ _ ih => exact .botE ih
  | andI _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | andE₁ _ ih => exact .andE₁ ih
  | andE₂ _ ih => exact .andE₂ ih
  | orI₁ _ ih => exact .orI₁ ih
  | orI₂ _ ih => exact .orI₂ ih
  | orE _ _ _ ih₀ ih₁ ih₂ => exact .orE ih₀ ih₁ ih₂
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | circI _ ih => exact .circI ih
  | circE _ _ ih₁ ih₂ => exact .circE ih₁ ih₂
  | allI L _ ih => exact .allI L ih
  | allE t ht _ ih => exact .allE t ht ih
  | exI t ht _ ih => exact .exI t ht ih
  | exE L _ _ ih₀ ih₁ => exact .exE L ih₀ ih₁


/-- A context supplying a *variable* for each formula of `Γ`.  `Derives.var`
looks entries up by name, so a context whose entry for `B` is a non-variable
(an outstanding refinement obligation, in the reading of `Ctx.obligations`)
cannot discharge it. -/
def Ctx.Covers (Δ : Ctx) (Γ : List Form) : Prop :=
  ∀ B ∈ Γ, ∃ x : String, (Pf.fvar x, B) ∈ Δ

theorem Ctx.Covers.cons {Δ : Ctx} {Γ : List Form} (h : Ctx.Covers Δ Γ)
    (x : String) (A : Form) : Ctx.Covers ((Pf.fvar x, A) :: Δ) (A :: Γ) := by
  intro B hB
  rcases List.mem_cons.mp hB with rfl | hB
  · exact ⟨x, List.mem_cons_self ..⟩
  · obtain ⟨y, hy⟩ := h B hB
    exact ⟨y, List.mem_cons_of_mem _ hy⟩

theorem PrvC.toDerives {Γ : List Form} {A : Form} (h : PrvC Γ A) :
    ∀ Δ : Ctx, Ctx.Covers Δ Γ →
      ∃ p, Pf.lcP 0 p ∧ Pf.lcI 0 p ∧ Nonempty (Derives p Δ A) := by
  induction h with
  | @var Γ A hmem =>
      intro Δ hΔ
      obtain ⟨x, hx⟩ := hΔ A hmem
      exact ⟨.fvar x, trivial, trivial, ⟨.var hx⟩⟩
  | topI => intro Δ _; exact ⟨.star, trivial, trivial, ⟨.topI⟩⟩
  | @botE Γ A hA _ ih =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih Δ hΔ
      exact ⟨.exf A p, hp, ⟨hA, hi⟩, ⟨.botE d⟩⟩
  | andI _ _ ih₁ ih₂ =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih₁ Δ hΔ
      obtain ⟨q, hq, hj, ⟨e⟩⟩ := ih₂ Δ hΔ
      exact ⟨.pair p q, ⟨hp, hq⟩, ⟨hi, hj⟩, ⟨.andI d e⟩⟩
  | andE₁ _ ih =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih Δ hΔ
      exact ⟨.fst p, hp, hi, ⟨.andE₁ d⟩⟩
  | andE₂ _ ih =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih Δ hΔ
      exact ⟨.snd p, hp, hi, ⟨.andE₂ d⟩⟩
  | orI₁ _ ih =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih Δ hΔ
      exact ⟨.inl p, hp, hi, ⟨.orI₁ d⟩⟩
  | orI₂ _ ih =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih Δ hΔ
      exact ⟨.inr p, hp, hi, ⟨.orI₂ d⟩⟩
  | @orE Γ A B K _ _ _ ih₀ ih₁ ih₂ =>
      intro Δ hΔ
      obtain ⟨r, hr, hri, ⟨d₀⟩⟩ := ih₀ Δ hΔ
      obtain ⟨y, hy⟩ : ∃ y : String, y = freshFor (Ctx.fvP Δ) := ⟨_, rfl⟩
      obtain ⟨p, hp, hpi, ⟨d₁⟩⟩ := ih₁ ((Pf.fvar y, A) :: Δ) (Ctx.Covers.cons hΔ y A)
      obtain ⟨z, hz⟩ : ∃ z : String, z = freshFor (Ctx.fvP Δ) := ⟨_, rfl⟩
      obtain ⟨q, hq, hqi, ⟨d₂⟩⟩ := ih₂ ((Pf.fvar z, B) :: Δ) (Ctx.Covers.cons hΔ z B)
      refine ⟨.caseOr r (Pf.closeP 0 y p) (Pf.closeP 0 z q),
        ⟨hr, Pf.lcP_closeP y p 0 hp, Pf.lcP_closeP z q 0 hq⟩,
        ⟨hri, Pf.lcI_closeP y p 0 0 hpi, Pf.lcI_closeP z q 0 0 hqi⟩, ⟨?_⟩⟩
      refine Derives.orE y z ⟨by rw [hy]; exact freshFor_notMem _, Pf.notMem_fvP_closeP y p 0⟩
        ⟨by rw [hz]; exact freshFor_notMem _, Pf.notMem_fvP_closeP z q 0⟩ d₀ ?_ ?_
      · rw [Pf.openPWith, Pf.openP_closeP y p 0 hp]; exact d₁
      · rw [Pf.openPWith, Pf.openP_closeP z q 0 hq]; exact d₂
  | @impI Γ A B _ ih =>
      intro Δ hΔ
      obtain ⟨z, hz⟩ : ∃ z : String, z = freshFor (Ctx.fvP Δ) := ⟨_, rfl⟩
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih ((Pf.fvar z, A) :: Δ) (Ctx.Covers.cons hΔ z A)
      refine ⟨.lam (Pf.closeP 0 z p), Pf.lcP_closeP z p 0 hp,
        Pf.lcI_closeP z p 0 0 hi, ⟨?_⟩⟩
      refine Derives.impI z ⟨by rw [hz]; exact freshFor_notMem _,
        Pf.notMem_fvP_closeP z p 0⟩ ?_
      rw [Pf.openPWith, Pf.openP_closeP z p 0 hp]; exact d
  | impE _ _ ih₁ ih₂ =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih₁ Δ hΔ
      obtain ⟨q, hq, hj, ⟨e⟩⟩ := ih₂ Δ hΔ
      exact ⟨.app p q, ⟨hp, hq⟩, ⟨hi, hj⟩, ⟨.impE d e⟩⟩
  | @circI Γ q A _ ih =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih Δ hΔ
      exact ⟨.val q p, hp, hi, ⟨.circI d⟩⟩
  | @circE Γ q A B _ _ ih₀ ih₁ =>
      intro Δ hΔ
      obtain ⟨r, hr, hri, ⟨d₀⟩⟩ := ih₀ Δ hΔ
      obtain ⟨z, hz⟩ : ∃ z : String, z = freshFor (Ctx.fvP Δ) := ⟨_, rfl⟩
      obtain ⟨b, hb, hbi, ⟨d₁⟩⟩ := ih₁ ((Pf.fvar z, A) :: Δ) (Ctx.Covers.cons hΔ z A)
      refine ⟨.letQ q r (Pf.closeP 0 z b), ⟨hr, Pf.lcP_closeP z b 0 hb⟩,
        ⟨hri, Pf.lcI_closeP z b 0 0 hbi⟩, ⟨?_⟩⟩
      refine Derives.circE z ⟨by rw [hz]; exact freshFor_notMem _,
        Pf.notMem_fvP_closeP z b 0⟩ d₀ ?_
      rw [Pf.openPWith, Pf.openP_closeP z b 0 hb]; exact d₁
  | @allI Γ A L _ ih =>
      intro Δ hΔ
      obtain ⟨a, ha⟩ : ∃ a : String, a = freshFor (L ++ Ctx.fvI Δ ++ A.fv) := ⟨_, rfl⟩
      have hnot : a ∉ (L ++ Ctx.fvI Δ ++ A.fv) := by rw [ha]; exact freshFor_notMem _
      simp only [List.mem_append, not_or] at hnot
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih a hnot.1.1 Δ hΔ
      refine ⟨.gen (Pf.closeI 0 a p), Pf.lcP_closeI a p 0 0 hp,
        Pf.lcI_closeI a p 0 hi, ⟨?_⟩⟩
      refine Derives.allI a ⟨hnot.1.2, Pf.notMem_fvI_closeI a p 0, hnot.2⟩ ?_
      rw [Pf.openIWith, Pf.openI_closeI a p 0 hi]; exact d
  | @allE Γ A t ht _ ih =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih Δ hΔ
      exact ⟨.inst t p, hp, ⟨ht, hi⟩, ⟨.allE t d rfl⟩⟩
  | @exI Γ A t ht _ ih =>
      intro Δ hΔ
      obtain ⟨p, hp, hi, ⟨d⟩⟩ := ih Δ hΔ
      exact ⟨.pack t p, hp, ⟨ht, hi⟩, ⟨.exI t d⟩⟩
  | @exE Γ A K L _ _ ih₀ ih₁ =>
      intro Δ hΔ
      obtain ⟨r, hr, hri, ⟨d₀⟩⟩ := ih₀ Δ hΔ
      obtain ⟨a, ha⟩ : ∃ a : String,
        a = freshFor (L ++ Ctx.fvI Δ ++ A.fv ++ K.fv) := ⟨_, rfl⟩
      have hnot : a ∉ (L ++ Ctx.fvI Δ ++ A.fv ++ K.fv) := by
        rw [ha]; exact freshFor_notMem _
      simp only [List.mem_append, not_or] at hnot
      obtain ⟨z, hz⟩ : ∃ z : String, z = freshFor (Ctx.fvP Δ) := ⟨_, rfl⟩
      obtain ⟨p, hp, hi, ⟨d₁⟩⟩ := ih₁ a hnot.1.1.1 ((Pf.fvar z, A.openWith a) :: Δ)
        (Ctx.Covers.cons hΔ z (A.openWith a))
      refine ⟨.caseEx r (Pf.closeI 0 a (Pf.closeP 0 z p)),
        ⟨hr, Pf.lcP_closeI a _ 0 1 (Pf.lcP_closeP z p 0 hp)⟩,
        ⟨hri, Pf.lcI_closeI a _ 0 (Pf.lcI_closeP z p 0 0 hi)⟩, ⟨?_⟩⟩
      refine Derives.exE a z
        ⟨hnot.1.1.2, Pf.notMem_fvI_closeI a _ 0, hnot.1.2⟩ hnot.2
        ⟨by rw [hz]; exact freshFor_notMem _, ?_⟩ d₀ ?_
      · rw [Pf.fvP_closeI a _ 0]; exact Pf.notMem_fvP_closeP z p 0
      · rw [Pf.openIWith, Pf.openI_closeI a _ 0 (Pf.lcI_closeP z p 0 0 hi),
          Pf.openPWith, Pf.openP_closeP z p 0 hp]
        exact d₁


/-! ## A context of variables, and what the bridge buys

`Ctx.ofForms` names every entry alike; nothing needs the names distinct, since
`Derives.var` only has to find *some* variable entry, and the binding rules
choose their own fresh names. -/

/-- A context of variable entries for `Γ`. -/
def Ctx.ofForms (Γ : List Form) : Ctx := Γ.map (fun B => (Pf.fvar "u", B))

theorem Ctx.covers_ofForms (Γ : List Form) : Ctx.Covers (Ctx.ofForms Γ) Γ :=
  fun _ hB => ⟨"u", List.mem_map_of_mem hB⟩

theorem Ctx.forms_ofForms (Γ : List Form) : Ctx.forms (Ctx.ofForms Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | cons B Γ ih => simp [Ctx.ofForms, Ctx.forms] at ih ⊢; exact ih

/-- The construction, at the canonical context. -/
theorem PrvC.derivable {Γ : List Form} {A : Form} (h : PrvC Γ A) :
    ∃ p, Pf.lcP 0 p ∧ Pf.lcI 0 p ∧ Nonempty (Derives p (Ctx.ofForms Γ) A) :=
  h.toDerives _ (Ctx.covers_ofForms Γ)

/-- **Soundness transfers to the term calculus.**  This is what erasure is
for: everything the model theory proves of `Prv` now says something about the
calculus of Fig. 5. -/
theorem Derives.consequence {p : Pf} {Γ : Ctx} {A : Form}
    (d : Derives p Γ A) (hp : Pf.lcI 0 p) : Ctx.forms Γ ⊨ A :=
  Prv.sound (d.erase hp)

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.Derives.erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Derives.erase

/-- info: 'LaxLogic.QLL.PrvC.toDerives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms PrvC.toDerives

/-- info: 'LaxLogic.QLL.Derives.consequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Derives.consequence

end LaxLogic.QLL
