/-
# `LaxLogic.QLL.HerbrandCLP` — the canonical constraint model, world 2 (Theorem 7.5)

§7 of the CLP draft builds, for an instrumented program `Θ♯ : θ`, a Kripke model
on the frame

    0 → 1,   0 → 2 → 3,     3 fallible, every arrow modal (`Rm`),

whose worlds `0, 1, 2` carry the least Herbrand models of `Π⁰` (modal clauses
dropped), `Π¹` (`◯` erased) and `Π² = (Θ♯ : θ)♭` (the refined, concrete
program, with the constraint predicates interpreted by given relations `R_B`).
Here `Θ♯` is the abstraction of a concrete non-modal program `Θ` and `θ` its own
constraint table, so `Π²` is `Θ` itself (Proposition 6.6).  The relations `R`
are an arbitrary interpretation of the constraint predicates over the Herbrand
universe.

**The `◯`-free half** (first pass).  World 2 is the least model of `Θ` over `R`,
and for a closed Σ-formula `S`:

    S true in M_Θ(R)  ⟺  some proof tree p of S has total(p) true in R        (world2_free)

**Theorem 7.5.**  For a closed pure Σ-formula `S`, in the canonical model:

    i = 0:  Θ♯ ⊢ S          ⟺  0 ⊨ S
    i = 1:  Θ♯ ⊢ ◯S         ⟺  1 ⊨ S
    i = 2:  some abstract proof a of ◯S against Θ♯ has π₁|a| true in R  ⟺  2 ⊨ S

The draft's "2-consequence" asks for a *solvable* extracted constraint, i.e.
one whose existential closure is true; the statement here asks for a true one,
which is the same thing once the proof's witness terms are chosen to be the
solution.  Lemma 7.2 (the canonical model satisfies `Θ♯` at world 0) is
`canon_sat`.  At world 2, `◯P` is always forced, through the fallible world 3:
the constraint information of world 2 sits in its atoms, as the draft says.
-/
import LaxLogic.QLL.CLPAbstract
import LaxLogic.QLL.HerbrandFix

namespace LaxLogic.QLL

/-! ## The `◯`-free half -/

section
variable {isC : String → Bool} {Θ : Program} {R : String → List Tm → Prop}

/-- A proof tree for a Σ-formula at an index gives one for the formula, with the
same total constraint. -/
theorem CTyped.of_sel_aux : ∀ (n : Nat) {S : Form}, S.size < n → IsSigma S →
    ∀ {g : Idx}, g ∈ ind S → ∀ {p : CProof}, CTyped isC Θ (sel S g) p →
      ∃ p' : CProof, CTyped isC Θ S p' ∧ p'.total = p.total
  | 0, _, hn, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, hn, hS, g, hg, p, h => by
      cases hS with
      | top => exact ⟨p, by rw [sel_top] at h; exact h, rfl⟩
      | pred P ts => exact ⟨p, by rw [sel_pred] at h; exact h, rfl⟩
      | @and A B hA hB =>
          have hg' : g ∈ (ind A).flatMap fun g₁ => (ind B).map fun g₂ => Idx.pair g₁ g₂ := hg
          obtain ⟨g₁, hg₁, hg₂'⟩ := List.mem_flatMap.1 hg'
          obtain ⟨g₂, hg₂, rfl⟩ := List.mem_map.1 hg₂'
          have h' : CTyped isC Θ (.and (sel A g₁) (sel B g₂)) p := h
          cases h' with
          | andI h₁ h₂ =>
            obtain ⟨p₁, hp₁, e₁⟩ := CTyped.of_sel_aux n (Form.size_lt_left hn) hA hg₁ h₁
            obtain ⟨p₂, hp₂, e₂⟩ := CTyped.of_sel_aux n (Form.size_lt_right hn) hB hg₂ h₂
            exact ⟨.andI p₁ p₂, .andI hp₁ hp₂, by show Form.and _ _ = Form.and _ _; rw [e₁, e₂]⟩
      | @or A B hA hB =>
          have hg' : g ∈ (ind A).map Idx.inl ++ (ind B).map Idx.inr := hg
          rcases List.mem_append.1 hg' with hg' | hg'
          · obtain ⟨g₁, hg₁, rfl⟩ := List.mem_map.1 hg'
            obtain ⟨p₁, hp₁, e₁⟩ := CTyped.of_sel_aux n (Form.size_lt_left hn) hA hg₁ h
            exact ⟨.orL p₁, .orL hp₁, e₁⟩
          · obtain ⟨g₂, hg₂, rfl⟩ := List.mem_map.1 hg'
            obtain ⟨p₂, hp₂, e₂⟩ := CTyped.of_sel_aux n (Form.size_lt_right hn) hB hg₂ h
            exact ⟨.orR p₂, .orR hp₂, e₂⟩
      | @ex A hA =>
          have hg' : g ∈ (ind A).map Idx.ex := hg
          obtain ⟨g₁, hg₁, rfl⟩ := List.mem_map.1 hg'
          have h' : CTyped isC Θ (.exists_ (sel A g₁)) p := h
          cases h' with
          | exI t ht h₁ =>
            rw [← sel_openAt] at h₁
            have hn' : (A.openAt 0 t).size < n := by
              rw [Form.size_openAt]; exact Nat.lt_of_succ_lt_succ hn
            obtain ⟨p₁, hp₁, e₁⟩ := CTyped.of_sel_aux n hn' (hA.openAt' 0 t)
              (by rw [ind_openAt]; exact hg₁) h₁
            exact ⟨.exI t p₁, .exI t ht hp₁, e₁⟩

/-- A proof tree for the disjunct at an index gives one for the formula, with the same total. -/
theorem CTyped.of_sel {S : Form} (hS : IsSigma S) {g : Idx} (hg : g ∈ ind S) {p : CProof}
    (h : CTyped isC Θ (sel S g) p) : ∃ p' : CProof, CTyped isC Θ S p' ∧ p'.total = p.total :=
  CTyped.of_sel_aux _ (Nat.lt_succ_self _) hS hg h

/-- What holds in the least model of `Θ` over `R` has a proof tree whose total
constraint is true in `R`. -/
theorem Holds.cproof (hRC : ∀ p us, R p us → isC p = true)
    (hRlc : ∀ p us, R p us → Tm.lcAtList 0 us) (hm : ∀ c ∈ Θ, c.modal = false)
    {φ : Form} (d : Holds R Θ.horn φ) : ∃ p : CProof, CTyped isC Θ φ p ∧ HTrue R p.total := by
  induction d with
  | base hr => exact ⟨.cstr _ _, .cstr (hRC _ _ hr), (HTrue_pred (hRlc _ _ hr)).2 hr⟩
  | top => exact ⟨.top, .top, trivial⟩
  | and _ _ ih₁ ih₂ =>
      obtain ⟨p₁, h₁, t₁⟩ := ih₁
      obtain ⟨p₂, h₂, t₂⟩ := ih₂
      exact ⟨.andI p₁ p₂, .andI h₁ h₂, ⟨t₁, t₂⟩⟩
  | ex t ht _ ih =>
      obtain ⟨p, h, tp⟩ := ih
      exact ⟨.exI t p, .exI t ht h, tp⟩
  | @fire h ts hh hlen hts _ ih =>
      obtain ⟨p, hp, tp⟩ := ih
      obtain ⟨c, hc, hh'⟩ := Program.mem_horn.1 hh
      obtain ⟨⟨g, hg⟩, _, rfl⟩ := List.mem_map.1 hh'
      have hp' : CTyped isC Θ (sel (Form.instAll ts c.body) g) p := by rw [sel_instAll]; exact hp
      obtain ⟨p', hp'', e⟩ := CTyped.of_sel (c.body_sigma.instAll ts)
        (by rw [ind_instAll]; exact hg) hp'
      obtain ⟨w, hw⟩ := List.mem_iff_getElem?.1 hc
      exact ⟨.clause w ts p', .clause w ts hw (hm c hc) hlen hts hp'',
        by show HTrue R p'.total; rw [e]; exact tp⟩

/-- The least Herbrand model of a program's Horn clauses is a model of its clauses. -/
theorem LHM_models_clause (hWF : ∀ c ∈ Θ, c.WF) {c : Clause} (hc : c ∈ Θ) :
    HTrue (LHM R Θ.horn) c.form := by
  have hP : ∀ h ∈ Θ.horn, h.WF := fun h hh => by
    obtain ⟨c', hc', hh'⟩ := Program.mem_horn.1 hh
    exact Clause.toHorn_WF (hWF c' hc') hh'
  exact Prv.sound (Clause.prv_of_toHorn c) (herbrand1 _) () Tm.fvar (fun _ _ => trivial)
    (fun B hB => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hB
      exact HTrue_LHM_form hP (Program.mem_horn.2 ⟨c, hc, hh⟩))

/-- A proof tree whose total constraint is true in `R` gives truth in the least
model of `Θ` over `R`. -/
theorem CTyped.HTrue_of_total (hWF : ∀ c ∈ Θ, c.WF)
    {S : Form} {p : CProof} (h : CTyped isC Θ S p) :
    Form.lcAt 0 S → HTrue R p.total → HTrue (LHM R Θ.horn) S := by
  induction h with
  | top => intro _ _; trivial
  | cstr _ =>
      intro hc ht
      exact (HTrue_pred hc).2 (.base ((HTrue_pred hc).1 ht))
  | andI _ _ ih₁ ih₂ => intro hc ht; exact ⟨ih₁ hc.1 ht.1, ih₂ hc.2 ht.2⟩
  | orL _ ih => intro hc ht; exact Or.inl (ih hc.1 ht)
  | orR _ ih => intro hc ht; exact Or.inr (ih hc.2 ht)
  | exI t ht' _ ih =>
      intro hc ht
      exact HTrue_exists.2 ⟨t, ht', ih (Form.lcAt_openAt _ 0 t ht' hc) ht⟩
  | @clause c p w ts hc' hm' hlen hts _ ih =>
      intro _ ht
      have hmem : c ∈ Θ := List.mem_of_getElem? hc'
      have hbody := ih (Form.lcAt_instAll ts _ hts (by rw [hlen]; exact hWF c hmem)) ht
      have hi := (HTrue_foralls c.arity _).1 (LHM_models_clause (R := R) hWF hmem) ts hlen hts
      rw [Form.instAll_imp] at hi
      have e : Form.instAll ts c.headForm = .pred c.head (Tm.instAllList ts (headVars c.arity)) := by
        unfold Clause.headForm; rw [hm']; exact Form.instAll_pred ts _ _
      rw [e] at hi
      exact HTrue_imp.1 hi hbody

/-- Completeness at world 2: truth in the least model over `R` gives a proof tree whose
total constraint is true in `R`. -/
theorem CTyped.of_HTrue (hRC : ∀ p us, R p us → isC p = true)
    (hRlc : ∀ p us, R p us → Tm.lcAtList 0 us) (hm : ∀ c ∈ Θ, c.modal = false)
    {S : Form} (hS : IsSigma S) (hc : Form.lcAt 0 S) (h : HTrue (LHM R Θ.horn) S) :
    ∃ p : CProof, CTyped isC Θ S p ∧ HTrue R p.total := by
  obtain ⟨g, hg, hsel⟩ := ((herbrand1 _).force_iff_sel hS () Tm.fvar []).1 h
  have d : Holds R Θ.horn (sel S g) := Holds.of_HTrue (hS.pp_sel hg) (Form.lcAt_sel S g 0 hc) hsel
  obtain ⟨p, hp, tp⟩ := d.cproof hRC hRlc hm
  obtain ⟨p', hp', e⟩ := CTyped.of_sel hS hg hp
  exact ⟨p', hp', by rw [e]; exact tp⟩

/-- **World 2, `◯`-free**: truth in the least model of the concrete program over
`R` is the existence of a proof tree whose total constraint is true in `R`. -/
theorem world2_free (hRC : ∀ p us, R p us → isC p = true)
    (hRlc : ∀ p us, R p us → Tm.lcAtList 0 us) (hWF : ∀ c ∈ Θ, c.WF)
    (hm : ∀ c ∈ Θ, c.modal = false) {S : Form} (hS : IsSigma S) (hc : Form.lcAt 0 S) :
    HTrue (LHM R Θ.horn) S ↔ ∃ p : CProof, CTyped isC Θ S p ∧ HTrue R p.total :=
  ⟨CTyped.of_HTrue hRC hRlc hm hS hc, fun ⟨_, hp, tp⟩ => hp.HTrue_of_total hWF hc tp⟩

end

/-! ## Extraction at world 2 -/

/-- Truth in an interpretation is invariant under `⊣⊢`. -/
theorem HTrue_of_PEq {I : String → List Tm → Prop} {A B : Form} (h : PEq A B) (ha : HTrue I A) :
    HTrue I B :=
  Prv.sound h.1 (herbrand1 I) () Tm.fvar (fun _ _ => trivial) (fun C hC => by
    rw [List.mem_singleton] at hC; subst hC; exact ha)

/-- The constraint table of a body is a Σ-formula at every witness. -/
theorem ctable_sigma (isC : String → Bool) : ∀ (z : Wit) (S : Form), IsSigma (ctable isC S z) := by
  intro z
  induction z with
  | unit => intro S; cases S <;> first | exact .top | (show IsSigma (if _ then _ else _); split <;> first | exact .top | exact .pred _ _)
  | pair a b iha ihb => intro S; cases S <;> first | exact .top | exact .and (iha _) (ihb _) | (show IsSigma (if _ then _ else _); split <;> first | exact .top | exact .pred _ _)
  | inl a ih => intro S; cases S <;> first | exact .top | exact ih _ | (show IsSigma (if _ then _ else _); split <;> first | exact .top | exact .pred _ _)
  | inr a ih => intro S; cases S <;> first | exact .top | exact ih _ | (show IsSigma (if _ then _ else _); split <;> first | exact .top | exact .pred _ _)
  | pack t a ih => intro S; cases S <;> first | exact .top | exact ih _ | (show IsSigma (if _ then _ else _); split <;> first | exact .top | exact .pred _ _)

/-- The table of a program is a Σ-formula everywhere. -/
theorem Program.table_sigma (isC : String → Bool) (Θ : Program) :
    ∀ w ts z, IsSigma (Θ.table isC w ts z) := by
  intro w ts z
  unfold Program.table
  split
  · exact ctable_sigma isC z _
  · exact .top

/-- The constraint extracted from an abstract proof is a Σ-formula. -/
theorem AProof.ext_sigma {T : Nat → List Tm → Wit → Form} (hT : ∀ w ts z, IsSigma (T w ts z)) :
    ∀ a : AProof, IsSigma (a.ext T).1
  | .val => .top
  | .andC p r => .and (AProof.ext_sigma hT p) (.and (AProof.ext_sigma hT r) .top)
  | .orL p | .orR p | .exC _ p => .and (AProof.ext_sigma hT p) .top
  | .impC w ts p => .and (AProof.ext_sigma hT p) (hT w ts _)

section
variable {isC : String → Bool} {Θ : Program} {R : String → List Tm → Prop}

/-- **Theorem 7.5, `i = 2`, on the atoms of world 2**: a closed pure query is
true in the least model of `Θ` over `R` iff some abstract proof of `◯S` against
`Θ♯` has an extracted constraint true in `R`. -/
theorem world2_abs (q : Q) (hH : Θ.HeadsOK isC) (hRC : ∀ p us, R p us → isC p = true)
    (hRlc : ∀ p us, R p us → Tm.lcAtList 0 us) (hWF : ∀ c ∈ Θ, c.WF)
    (hm : ∀ c ∈ Θ, c.modal = false) {S : Form} (hS : IsSigma S) (hc : Form.lcAt 0 S)
    (hpure : S.pureB isC = true) :
    (∃ a : AProof, ATyped (Θ.abs isC q) q S a ∧ HTrue R (a.ext (Θ.table isC)).1) ↔
      HTrue (LHM R Θ.horn) S := by
  constructor
  · rintro ⟨a, ha, ht⟩
    have himp : HTrue (LHM R Θ.horn) (.imp (a.ext (Θ.table isC)).1 S) :=
      Prv.sound (cor_9_8_abs hm ha) (herbrand1 _) () Tm.fvar (fun _ _ => trivial) (fun B hB => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hB
        exact LHM_models_clause hWF hc)
    exact HTrue_imp.1 himp
      (HTrue_mono (fun _ _ r => Holds.base r) (AProof.ext_sigma (Program.table_sigma isC Θ) a) ht)
  · intro h
    obtain ⟨p, hp, tp⟩ := CTyped.of_HTrue hRC hRlc hm hS hc h
    refine ⟨p.toA, ?_, ?_⟩
    · have := hp.toA q hH
      rwa [Form.strip_pure isC hS hpure] at this
    · have e : PEq p.total (p.toA.ext (Θ.table isC)).1 :=
        (hp.ext_total hH).symm.trans ((PEq.and (PEq.refl _) (hp.active_pure hpure)).trans
          (PEq.and_top _))
      exact HTrue_of_PEq e tp

end

/-! ## The canonical frame -/

/-- The worlds of the canonical frame. -/
inductive W4 where
  | w0 | w1 | w2 | w3
  deriving DecidableEq

/-- `0 → 1`, `0 → 2 → 3`, reflexive and transitive. -/
def W4.leB : W4 → W4 → Bool
  | .w0, _ => true
  | .w1, .w1 => true
  | .w2, .w2 => true
  | .w2, .w3 => true
  | .w3, .w3 => true
  | _, _ => false

/-- A false accessibility cannot hold. -/
theorem W4.le_false {u v : W4} (h : W4.leB u v = true) (h' : W4.leB u v = false) : False := by
  rw [h] at h'; cases h'

/-- The order is transitive. -/
theorem W4.leB_trans {u v w : W4} (h₁ : W4.leB u v = true) (h₂ : W4.leB v w = true) :
    W4.leB u w = true := by
  cases u <;> cases v <;> cases w <;>
    first | rfl | exact absurd h₁ (by decide) | exact absurd h₂ (by decide)

/-- The draft's frame `F`: every arrow is an `Rm` accessibility, world 3 is fallible. -/
def HFrame.four : HFrame where
  W := W4
  le u v := W4.leB u v = true
  refl u := by cases u <;> rfl
  trans := W4.leB_trans
  Fl w := w = .w3
  hered_Fl := fun {w v} h hw => by
    subst hw; cases v <;> first | rfl | exact absurd h (by decide)
  m u v := W4.leB u v = true
  m_refl u := by cases u <;> rfl
  m_trans := W4.leB_trans
  m_sub h := h

/-- The interpretation of each world; the fallible world 3 makes everything true. -/
def I4 (I₀ I₁ I₂ : String → List Tm → Prop) : W4 → String → List Tm → Prop
  | .w0 => I₀
  | .w1 => I₁
  | .w2 => I₂
  | .w3 => fun _ _ => True

/-- The four-world interpretation is monotone when `I₀ ⊆ I₁` and `I₀ ⊆ I₂`. -/
theorem I4_hered {I₀ I₁ I₂ : String → List Tm → Prop} (h01 : ∀ p us, I₀ p us → I₁ p us)
    (h02 : ∀ p us, I₀ p us → I₂ p us) :
    ∀ {w v : HFrame.four.W} {p : String} {ts : List Tm},
      HFrame.four.le w v → I4 I₀ I₁ I₂ w p ts → I4 I₀ I₁ I₂ v p ts := by
  intro w v p ts h hI
  cases w <;> cases v <;>
    first | exact hI | exact h01 _ _ hI | exact h02 _ _ hI | trivial

/-! ## The canonical model of an abstracted program -/

section
variable (isC : String → Bool) (q : Q) (Θ : Program) (R : String → List Tm → Prop)

/-- `Π⁰` of an abstracted program is empty: every clause of `Θ♯` is modal. -/
theorem Program.horn0_abs : (Θ.abs isC q).horn0 = [] := by
  induction Θ with
  | nil => rfl
  | cons c Θ ih =>
      show (bif true then [] else (c.abs isC q).toHorn) ++ (Program.abs isC q Θ).horn0 = []
      rw [ih]; rfl

/-- World 0 of the canonical model: the least model of `Π⁰`, which is empty
since every clause of `Θ♯` is modal. -/
abbrev canonI0 : String → List Tm → Prop := LHM RNone (Θ.abs isC q).horn0
/-- World 1: the least model of `Π¹`, `◯` erased. -/
abbrev canonI1 : String → List Tm → Prop := LHM RNone (Θ.abs isC q).horn
/-- World 2: the least model of `Π² = Θ` over the constraint relations. -/
abbrev canonI2 : String → List Tm → Prop := LHM R Θ.horn

/-- World 0 of the canonical model has no atoms. -/
theorem canonI0_empty (p : String) (us : List Tm) : ¬ canonI0 isC q Θ p us := by
  intro h
  have h' : Holds RNone [] (.pred p us) := by
    have := h; unfold canonI0 at this; rw [Program.horn0_abs] at this; exact this
  cases h' with
  | base hr => exact hr
  | fire hh _ _ _ => exact absurd hh (List.not_mem_nil)

/-- **Lemma 7.3**: the canonical interpretation is monotone along the frame. -/
theorem canon_hered : ∀ {w v : HFrame.four.W} {p : String} {ts : List Tm},
    HFrame.four.le w v → I4 (canonI0 isC q Θ) (canonI1 isC q Θ) (canonI2 Θ R) w p ts →
      I4 (canonI0 isC q Θ) (canonI1 isC q Θ) (canonI2 Θ R) v p ts :=
  I4_hered (llpI0_le (Program.abs isC q Θ)) (fun p us h => absurd h (canonI0_empty isC q Θ p us))

/-- The canonical Herbrand constraint model `M(Θ♯ : θ)` (Lemma 7.3: the
interpretations are monotone along the frame). -/
abbrev canonModel : KModel :=
  HFrame.four.model (I4 (canonI0 isC q Θ) (canonI1 isC q Θ) (canonI2 Θ R)) (canon_hered isC q Θ R)

end

section
variable {isC : String → Bool} {q : Q} {Θ : Program} {R : String → List Tm → Prop}

/-- At a non-fallible world, a Σ-formula is forced exactly when true in the world's interpretation. -/
theorem canon_sigma {S : Form} (hS : IsSigma S) (w : W4) (hw : w ≠ .w3) :
    (canonModel isC q Θ R).force S w Tm.fvar [] ↔
      HTrue (I4 (canonI0 isC q Θ) (canonI1 isC q Θ) (canonI2 Θ R) w) S :=
  HFrame.force_sigma HFrame.four (I4 (canonI0 isC q Θ) (canonI1 isC q Θ) (canonI2 Θ R)) (canon_hered isC q Θ R) hS w [] hw

/-- Abstraction preserves local closedness. -/
theorem Form.lcAt_strip (isC : String → Bool) : ∀ (A : Form) (k : Nat),
    Form.lcAt k A → Form.lcAt k (A.strip isC)
  | .top, _, h => h
  | .bot, _, h => h
  | .pred B ts, k, h => by
      show Form.lcAt k (if isC B = true then .top else .pred B ts)
      split
      · trivial
      · exact h
  | .and A B, k, h => ⟨Form.lcAt_strip isC A k h.1, Form.lcAt_strip isC B k h.2⟩
  | .or A B, k, h => ⟨Form.lcAt_strip isC A k h.1, Form.lcAt_strip isC B k h.2⟩
  | .imp A B, k, h => ⟨Form.lcAt_strip isC A k h.1, Form.lcAt_strip isC B k h.2⟩
  | .circ _ A, k, h => Form.lcAt_strip isC A k h
  | .forall_ A, k, h => Form.lcAt_strip isC A (k + 1) h
  | .exists_ A, k, h => Form.lcAt_strip isC A (k + 1) h

/-- The abstraction of a well-formed program is well formed. -/
theorem Program.abs_WF (hWF : ∀ c ∈ Θ, c.WF) : ∀ c ∈ Θ.abs isC q, c.WF := by
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  exact Form.lcAt_strip isC c₀.body c₀.arity (hWF c₀ hc₀)

/-- Every modal clause of `Θ♯` uses `q`. -/
theorem Program.abs_OnlyQ : (Θ.abs isC q).OnlyQ q := by
  intro c hc _
  obtain ⟨c₀, _, rfl⟩ := List.mem_map.1 hc
  rfl

/-- **Lemma 7.2**: world 0 of the canonical model forces every clause of `Θ♯`. -/
theorem canon_clause (hWF : ∀ c ∈ Θ, c.WF) {c : Clause} (hc : c ∈ Θ.abs isC q) :
    (canonModel isC q Θ R).force c.form W4.w0 Tm.fvar [] := by
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  have hWFa := Program.abs_WF (isC := isC) (q := q) hWF
  show (canonModel isC q Θ R).force
    (Form.foralls c₀.arity (.imp (c₀.body.strip isC) (.circ q (.pred c₀.head (headVars c₀.arity)))))
    W4.w0 Tm.fvar []
  refine (HFrame.force_foralls HFrame.four (I4 (canonI0 isC q Θ) (canonI1 isC q Θ) (canonI2 Θ R)) (canon_hered isC q Θ R) c₀.arity _ W4.w0).2
    fun v _ ts hlen hts => ?_
  rw [Form.instAll_imp, Form.instAll_circ, Form.instAll_pred]
  intro v' _ hb
  have hS : IsSigma (Form.instAll ts (c₀.body.strip isC)) := (c₀.body_sigma.strip isC).instAll ts
  have hargs : Tm.lcAtList 0 (Tm.instAllList ts (headVars c₀.arity)) :=
    Tm.lcAtList_instAllList ts _ hts (by rw [hlen]; exact headVars_lc _)
  -- the head holds at world 1 whenever the body is true in world 1's interpretation
  have head1 : HTrue (canonI1 isC q Θ) (Form.instAll ts (c₀.body.strip isC)) →
      (canonModel isC q Θ R).force (.pred c₀.head (Tm.instAllList ts (headVars c₀.arity)))
        W4.w1 Tm.fvar [] := by
    intro hb1
    have hcf := LHM_models_clause (R := RNone) hWFa hc
    have hi := (HTrue_foralls c₀.arity _).1 hcf ts hlen hts
    rw [Form.instAll_imp] at hi
    have e : Form.instAll ts (c₀.abs isC q).headForm
        = .circ q (.pred c₀.head (Tm.instAllList ts (headVars c₀.arity))) := by
      show Form.instAll ts (.circ q (.pred c₀.head (headVars c₀.arity))) = _
      rw [Form.instAll_circ, Form.instAll_pred]
    have hh := HTrue_imp.1 hi hb1
    rw [e] at hh
    exact (canon_sigma (.pred _ _) .w1 (by decide)).2 (HTrue_circ.1 hh)
  cases v' with
  | w0 =>
      have hP1 := head1 (HTrue_mono (llpI0_le (Program.abs isC q Θ)) hS
        ((canon_sigma hS .w0 (by decide)).1 hb))
      cases q <;> intro u hu <;> cases u <;>
        first | exact ⟨.w1, rfl, hP1⟩ | exact ⟨.w3, rfl, Or.inl rfl⟩
  | w1 =>
      have hP1 := head1 ((canon_sigma hS .w1 (by decide)).1 hb)
      cases q <;> intro u hu <;> cases u <;>
        first | exact ⟨.w1, rfl, hP1⟩ | exact (W4.le_false (show W4.leB _ _ = true from hu) rfl).elim
  | w2 =>
      cases q <;> intro u hu <;> cases u <;>
        first | exact ⟨.w3, rfl, Or.inl rfl⟩ | exact (W4.le_false (show W4.leB _ _ = true from hu) rfl).elim
  | w3 =>
      cases q <;> intro u hu <;> cases u <;>
        first | exact ⟨.w3, rfl, Or.inl rfl⟩ | exact (W4.le_false (show W4.leB _ _ = true from hu) rfl).elim

/-- Lemma 7.2, as satisfaction: world 0 forces every formula of `Θ♯`. -/
theorem canon_sat (hWF : ∀ c ∈ Θ, c.WF) :
    ∀ B ∈ (Θ.abs isC q).forms, (canonModel isC q Θ R).force B W4.w0 Tm.fvar [] := fun B hB => by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hB
  exact canon_clause hWF hc

/-- **Theorem 7.5, `i = 0`.** -/
theorem thm_7_5_canon0 (hWF : ∀ c ∈ Θ, c.WF) {S : Form} (hS : IsSigma S) (hc : Form.lcAt 0 S) :
    Prv (Θ.abs isC q).forms S ↔ (canonModel isC q Θ R).force S W4.w0 Tm.fvar [] :=
  ⟨fun h => Prv.sound h (canonModel isC q Θ R) W4.w0 Tm.fvar (fun _ _ => trivial) (canon_sat hWF),
   fun h => llp_prv_of_HTrue0 hS hc ((canon_sigma hS .w0 (by decide)).1 h)⟩

/-- **Theorem 7.5, `i = 1`.** -/
theorem thm_7_5_canon1 (hWF : ∀ c ∈ Θ, c.WF) {S : Form} (hS : IsSigma S) (hc : Form.lcAt 0 S) :
    Prv (Θ.abs isC q).forms (.circ q S) ↔ (canonModel isC q Θ R).force S W4.w1 Tm.fvar [] := by
  constructor
  · intro h
    have h0 := Prv.sound h (canonModel isC q Θ R) W4.w0 Tm.fvar (fun _ _ => trivial) (canon_sat hWF)
    have h1 : ∃ u, HFrame.four.m W4.w1 u ∧ (canonModel isC q Θ R).force S u Tm.fvar [] := by
      cases q <;> exact h0 W4.w1 rfl
    obtain ⟨u, hu, hSu⟩ := h1
    cases u <;> first | exact hSu | exact (W4.le_false (show W4.leB _ _ = true from hu) rfl).elim
  · intro h
    exact llp_prv_circ_of_HTrue1 Program.abs_OnlyQ hS hc ((canon_sigma hS .w1 (by decide)).1 h)

/-- **Theorem 7.5, `i = 2`**: a closed pure query is forced at world 2 iff some
abstract proof of `◯S` against `Θ♯` has an extracted constraint true in `R`. -/
theorem thm_7_5_canon2 (hH : Θ.HeadsOK isC) (hRC : ∀ p us, R p us → isC p = true)
    (hRlc : ∀ p us, R p us → Tm.lcAtList 0 us) (hWF : ∀ c ∈ Θ, c.WF)
    (hm : ∀ c ∈ Θ, c.modal = false) {S : Form} (hS : IsSigma S) (hc : Form.lcAt 0 S)
    (hpure : S.pureB isC = true) :
    (∃ a : AProof, ATyped (Θ.abs isC q) q S a ∧ HTrue R (a.ext (Θ.table isC)).1) ↔
      (canonModel isC q Θ R).force S W4.w2 Tm.fvar [] :=
  (world2_abs q hH hRC hRlc hWF hm hS hc hpure).trans (canon_sigma hS .w2 (by decide)).symm

/-- At world 2 every `◯`-formula is forced, through the fallible world 3. -/
theorem canon_circ_w2 (S : Form) : (canonModel isC q Θ R).force (.circ q S) W4.w2 Tm.fvar [] := by
  have hf : (canonModel isC q Θ R).force S W4.w3 Tm.fvar [] :=
    (canonModel isC q Θ R).force_of_fallible S Tm.fvar [] rfl
  cases q <;> intro u hu <;> cases u <;>
    first
      | exact ⟨W4.w3, rfl, hf⟩
      | exact (W4.le_false (show W4.leB _ _ = true from hu) rfl).elim

end



/-! ## Proposition 6.6, second half: REFUTED as stated

The draft claims that for a modal clause `θ = ∀x̃. S ⊃ ◯P` without constraints and
any table `p`, `(p : θ)♭ ⊢ θ`.  Take `θ = ∀x. A(x) ⊃ ◯P(x)` and the table
`λx.λz.(B(x), ⋆)` with `B` a constraint: Definition 6.5 gives
`(p : θ)♭ = ∀x. (A(x) ∧ B(x)) ⊃ P(x)`.  In the one-world Herbrand model where
`A` holds of everything and `B`, `P` of nothing, the refinement is true and `θ`
is false.  With the constraint assumed lax-true, `∀x. ◯B(x)`, the entailment
holds (`p66_with_lax`): that is the missing hypothesis. -/

/-- The refined clause `∀x. A(x) ∧ B(x) ⊃ P(x)` of the countermodel. -/
def p66Refined : Form :=
  .forall_ (.imp (.and (.pred "A" [.bvar 0]) (.pred "B" [.bvar 0])) (.pred "P" [.bvar 0]))

/-- The abstract clause `∀x. A(x) ⊃ ◯P(x)` it is claimed to entail. -/
def p66Abstract (q : Q) : Form :=
  .forall_ (.imp (.pred "A" [.bvar 0]) (.circ q (.pred "P" [.bvar 0])))

/-- One world: `A` holds of every term, `B` and `P` of none. -/
def p66I : String → List Tm → Prop := fun p _ => p = "A"

/-- The refined clause is true in the one-world countermodel. -/
theorem p66_refined_true : HTrue p66I p66Refined := by
  refine HTrue_forall.2 fun t _ => HTrue_imp.2 fun h => ?_
  have hB : False ∨ ("B" = "A") := h.2
  exact hB.elim False.elim (fun e => absurd e (by decide))

/-- The abstract clause is false there. -/
theorem p66_abstract_false (q : Q) : ¬ HTrue p66I (p66Abstract q) := by
  intro h
  have h1 := HTrue_imp.1 (HTrue_forall.1 h (.fn "c" []) trivial)
    (show False ∨ ("A" = "A") from Or.inr rfl)
  have h3 : False ∨ ("P" = "A") := HTrue_circ.1 h1
  exact h3.elim id (fun e => absurd e (by decide))

/-- **Proposition 6.6, second half, REFUTED**: the refinement does not entail the
abstract clause. -/
theorem p66_refuted (q : Q) : ¬ Prv [p66Refined] (p66Abstract q) := fun h =>
  p66_abstract_false q (Prv.sound h (herbrand1 p66I) () Tm.fvar (fun _ _ => trivial)
    (fun B hB => by rw [List.mem_singleton] at hB; subst hB; exact p66_refined_true))

/-- With the table's constraint lax-true, the entailment holds. -/
theorem p66_with_lax (q : Q) :
    Prv [p66Refined, .forall_ (.circ q (.pred "B" [.bvar 0]))] (p66Abstract q) := by
  refine .allI [] fun a _ => ?_
  show Prv _ (.imp (.pred "A" [.fvar a]) (.circ q (.pred "P" [.fvar a])))
  refine .impI ?_
  have hB : Prv (.pred "A" [.fvar a] :: [p66Refined, .forall_ (.circ q (.pred "B" [.bvar 0]))])
      (.circ q (.pred "B" [.fvar a])) :=
    .allE (.fvar a) trivial
      (.var (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))
  have hR : Prv (.pred "A" [.fvar a] :: [p66Refined, .forall_ (.circ q (.pred "B" [.bvar 0]))])
      (.imp (.and (.pred "A" [.fvar a]) (.pred "B" [.fvar a])) (.pred "P" [.fvar a])) :=
    .allE (.fvar a) trivial (.var (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
  exact .circE hB (.circI (.impE hR.weaken_cons
    (.andI (.var (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))) .hd)))

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.CTyped.of_sel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTyped.of_sel

/-- info: 'LaxLogic.QLL.Holds.cproof' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Holds.cproof

/-- info: 'LaxLogic.QLL.LHM_models_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms LHM_models_clause

/-- info: 'LaxLogic.QLL.CTyped.HTrue_of_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTyped.HTrue_of_total

/-- info: 'LaxLogic.QLL.CTyped.of_HTrue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTyped.of_HTrue

/-- info: 'LaxLogic.QLL.world2_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms world2_free

/-- info: 'LaxLogic.QLL.world2_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms world2_abs

/-- info: 'LaxLogic.QLL.canon_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms canon_clause

/-- info: 'LaxLogic.QLL.canon_sat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms canon_sat

/-- info: 'LaxLogic.QLL.thm_7_5_canon0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms thm_7_5_canon0

/-- info: 'LaxLogic.QLL.thm_7_5_canon1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms thm_7_5_canon1

/-- info: 'LaxLogic.QLL.thm_7_5_canon2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms thm_7_5_canon2

/-- info: 'LaxLogic.QLL.canon_circ_w2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms canon_circ_w2


/-- info: 'LaxLogic.QLL.p66_refined_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms p66_refined_true

/-- info: 'LaxLogic.QLL.p66_abstract_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms p66_abstract_false

/-- info: 'LaxLogic.QLL.p66_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms p66_refuted

/-- info: 'LaxLogic.QLL.p66_with_lax' depends on axioms: [propext] -/
#guard_msgs in #print axioms p66_with_lax

end LaxLogic.QLL
