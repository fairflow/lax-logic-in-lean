/-
# The restricted closedness contract, and why it suffices

`docs/checkclosed-checks.md`.  `DBClosed G db` (`FRJ/Gbu/W/Closure.lean`)
quantifies its eight join clauses over families of every arity.  This
file:

  1. iterates B1 (`wip/b1b2_lemmas.lean`): every join family reduces,
     by dropping premises whose goal another premise shares, to a
     sub-family with PAIRWISE DISTINCT GOALS, satisfying the same side
     conditions, with a larger conclusion context (`Shape.toDistinct`);
  2. states `DBClosedDG G db`, the contract with the join clauses
     restricted to distinct-goal irregular families and to promise
     families of size ≤ |Ĝ^◯| + 1;
  3. proves `dbClosed_of_dg : DBClosedDG G db → DBClosed G db`.

A checker (`checkClosed`) then has only bounded families to enumerate:
irregular families of arity ≤ |Sf^R|, promise families of arity
≤ |Ĝ^◯| + 1.
-/
import FRJ.Gbu.W.Saturate
import wip.b1b2_lemmas
import wip.b1b2_relaxed
import wip.b1b2_hitting

open FRJ Form FRJ.Arity

namespace FRJ.Arity

/-! ## 1. Families and reindexing -/

/-- An irregular join family of arity `n + 1`. -/
structure Fam (n : Nat) where
  Ξs : Fin (n + 1) → List Form
  Θs : Fin (n + 1) → List Form
  rhs : Fin (n + 1) → Form

/-- Reindexing along `e`. -/
def Fam.reindex {n m : Nat} (f : Fam n) (e : Fin (m + 1) → Fin (n + 1)) : Fam m :=
  ⟨fun k => f.Ξs (e k), fun k => f.Θs (e k), fun k => f.rhs (e k)⟩

theorem Fam.reindex_reindex {n m l : Nat} (f : Fam n) (e : Fin (m + 1) → Fin (n + 1))
    (e' : Fin (l + 1) → Fin (m + 1)) :
    (f.reindex e).reindex e' = f.reindex (fun k => e (e' k)) := rfl

/-- Pairwise distinct goals. -/
def Fam.DistinctGoals {n : Nat} (f : Fam n) : Prop :=
  ∀ k l, k ≠ l → f.rhs k ≠ f.rhs l

instance {n : Nat} (f : Fam n) : Decidable (∃ i p, i ≠ p ∧ f.rhs i = f.rhs p) :=
  inferInstance

/-! ## 2. A clause shape: a context function, a hypothesis, and one B1 step -/

/-- What a join clause needs of its irregular family: a conclusion
context, a family hypothesis, and the B1 step -- dropping a premise `p`
whose goal premise `i` shares keeps the hypothesis and grows the
context. -/
structure Shape where
  ctx : ∀ {n : Nat}, Fam n → List Form
  Hyp : ∀ {n : Nat}, Fam n → Prop
  step : ∀ {n : Nat} (f : Fam (n + 1)) (p i : Fin (n + 2)), i ≠ p →
    f.rhs i = f.rhs p → Hyp f →
    Hyp (f.reindex (Fin.succAbove p)) ∧ ctx f ⊆ ctx (f.reindex (Fin.succAbove p))

/-- **Iterated B1.**  Every family with the hypothesis reduces to a
sub-family with pairwise distinct goals, along an injective,
goal-covering reindexing, keeping the hypothesis and growing the
context. -/
theorem Shape.toDistinct (S : Shape) : ∀ (n : Nat) (f : Fam n), S.Hyp f →
    ∃ (m : Nat) (e : Fin (m + 1) → Fin (n + 1)),
      (∀ k l, e k = e l → k = l) ∧
      (f.reindex e).DistinctGoals ∧
      (∀ j, ∃ k, f.rhs (e k) = f.rhs j) ∧
      S.Hyp (f.reindex e) ∧ S.ctx f ⊆ S.ctx (f.reindex e)
  | 0, f, hf =>
      ⟨0, id, fun _ _ h => h,
        fun k l hkl => absurd (Fin.ext (by omega)) hkl,
        fun j => ⟨j, rfl⟩, hf, fun _ h => h⟩
  | n + 1, f, hf =>
      if hdup : ∃ i p, i ≠ p ∧ f.rhs i = f.rhs p then by
        obtain ⟨i, p, hip, hgoal⟩ := hdup
        obtain ⟨hHyp', hctx'⟩ := S.step f p i hip hgoal hf
        obtain ⟨m, e', hinj', hdist', hcov', hHyp'', hctx''⟩ :=
          S.toDistinct n (f.reindex (Fin.succAbove p)) hHyp'
        refine ⟨m, fun k => p.succAbove (e' k), ?_, ?_, ?_, hHyp'', ?_⟩
        · exact fun k l h => hinj' k l (Fin.succAbove_right_injective h)
        · exact hdist'
        · intro j
          by_cases hjp : j = p
          · obtain ⟨k₀, hk₀⟩ := Fin.exists_succAbove_eq hip
            obtain ⟨k, hk⟩ := hcov' k₀
            exact ⟨k, by
              show f.rhs (p.succAbove (e' k)) = f.rhs j
              have : f.rhs (p.succAbove (e' k)) = f.rhs (p.succAbove k₀) := hk
              rw [this, hk₀, hgoal, hjp]⟩
          · obtain ⟨k₀, hk₀⟩ := Fin.exists_succAbove_eq hjp
            obtain ⟨k, hk⟩ := hcov' k₀
            exact ⟨k, by
              show f.rhs (p.succAbove (e' k)) = f.rhs j
              have : f.rhs (p.succAbove (e' k)) = f.rhs (p.succAbove k₀) := hk
              rw [this, hk₀]⟩
        · exact fun x hx => hctx'' (hctx' hx)
      else
        ⟨n + 1, id, fun _ _ h => h,
          fun k l hkl heq => hdup ⟨k, l, hkl, heq⟩,
          fun j => ⟨j, rfl⟩, hf, fun _ h => h⟩

/-! ## 3. The shapes with the strict (J2)

The side conditions of each clause on its irregular family, as the
`Hyp`; the `step` is the B1 lemma of `wip/b1b2_lemmas.lean`. -/

/-- (J1). -/
def J1 {n : Nat} (f : Fam n) : Prop := ∀ i j, i ≠ j → f.Ξs i ⊆ f.Ξs j ++ f.Θs j
/-- The strict (J2). -/
def J2 {n : Nat} (f : Fam n) : Prop :=
  ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (f.Ξs j)) → A ∈ upsilon f.rhs
/-- (J3). -/
def J3 {n : Nat} (f : Fam n) : Prop := unionAll (fun j => circPart (f.Ξs j)) = []
/-- The target condition of the `⋈^At` rules. -/
def FNot {n : Nat} (f : Fam n) (F : Form) : Prop := F ∉ unionAll (fun j => atPart (f.Ξs j))
/-- (J5′): every stable modal formula has a promise world closing its body. -/
def J5 {n k : Nat} (f : Fam n) (Δs : Fin (k + 1) → List Form) : Prop :=
  ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (f.Ξs j)) → ∃ i, Clo (Δs i) Y
/-- (J6): every stable formula lies in every promise closure. -/
def J6 {n k : Nat} (f : Fam n) (Δs : Fin (k + 1) → List Form) : Prop :=
  ∀ i j, ∀ X ∈ f.Ξs j, Clo (Δs i) X

section Steps

variable {n : Nat} (f : Fam (n + 1)) (p i : Fin (n + 2)) (hip : i ≠ p)
  (hgoal : f.rhs i = f.rhs p)

theorem step_j1 (h : J1 f) : J1 (f.reindex (Fin.succAbove p)) :=
  j1_comp (Fin.succAbove p) (succAbove_inj p) h

include hip hgoal in
theorem step_j2 (h : J2 f) : J2 (f.reindex (Fin.succAbove p)) :=
  j2_comp (Fin.succAbove p) (cov_of_dup (rhs := f.rhs) p i hip hgoal) h

theorem step_j3 (h : J3 f) : J3 (f.reindex (Fin.succAbove p)) :=
  j3_comp (Fin.succAbove p) h

theorem step_fnot {F : Form} (h : FNot f F) : FNot (f.reindex (Fin.succAbove p)) F :=
  fNot_comp (Fin.succAbove p) h

theorem step_j5 {k : Nat} {Δs : Fin (k + 1) → List Form} (h : J5 f Δs) :
    J5 (f.reindex (Fin.succAbove p)) Δs :=
  j5_comp (Fin.succAbove p) h

theorem step_j6 {k : Nat} {Δs : Fin (k + 1) → List Form} (h : J6 f Δs) :
    J6 (f.reindex (Fin.succAbove p)) Δs :=
  j6_comp (Fin.succAbove p) h

end Steps

/-- The barren `⋈^At` shape (target `F`). -/
def shapeAt (F : Form) : Shape where
  ctx f := ctxAt f.Ξs f.Θs f.rhs F
  Hyp f := J1 f ∧ J2 f ∧ J3 f ∧ FNot f F
  step f p i hip hgoal h :=
    ⟨⟨step_j1 f p h.1, step_j2 f p i hip hgoal h.2.1, step_j3 f p h.2.2.1,
      step_fnot f p h.2.2.2⟩,
     ctxAt_sub (Fin.succAbove p) p (succAbove_ne' p) (succAbove_surj p)
       (cov_of_dup (rhs := f.rhs) p i hip hgoal) h.1 h.2.1 h.2.2.2⟩

/-- The barren `⋈^∨` shape. -/
def shapeOr : Shape where
  ctx f := ctxOr f.Ξs f.Θs f.rhs
  Hyp f := J1 f ∧ J2 f ∧ J3 f
  step f p i hip hgoal h :=
    ⟨⟨step_j1 f p h.1, step_j2 f p i hip hgoal h.2.1, step_j3 f p h.2.2⟩,
     ctxOr_sub (Fin.succAbove p) p (succAbove_ne' p) (succAbove_surj p)
       (cov_of_dup (rhs := f.rhs) p i hip hgoal) h.1 h.2.1⟩

/-- The RefAt-relaxed (J2) of the barren `⋈^◯`. -/
def J2r {n : Nat} (f : Fam n) : Prop :=
  ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (f.Ξs j)) →
    RefAt true (upsilon f.rhs) (ctxOr f.Ξs f.Θs f.rhs) A

/-- The barren `⋈^◯` shape, with the relaxed (J2): the step is
`ctxOr_sub_relaxed` (`wip/b1b2_relaxed.lean`, by induction on formula
size). -/
def shapeCirc : Shape where
  ctx f := ctxOr f.Ξs f.Θs f.rhs
  Hyp f := J1 f ∧ J2r f ∧ J3 f
  step f p i hip hgoal h :=
    ⟨⟨step_j1 f p h.1,
      j2r_comp (Fin.succAbove p) p (succAbove_ne' p) (succAbove_surj p)
        (cov_of_dup (rhs := f.rhs) p i hip hgoal) h.1 h.2.1,
      step_j3 f p h.2.2⟩,
     ctxOr_sub_relaxed (Fin.succAbove p) p (succAbove_ne' p) (succAbove_surj p)
       (cov_of_dup (rhs := f.rhs) p i hip hgoal) h.1 h.2.1⟩

/-- The fallible `⋈^At` shape. -/
def shapeAtF (F : Form) : Shape where
  ctx f := joinCtxAtF f.Ξs f.Θs f.rhs F
  Hyp f := J1 f ∧ J2 f ∧ FNot f F
  step f p i hip hgoal h :=
    ⟨⟨step_j1 f p h.1, step_j2 f p i hip hgoal h.2.1, step_fnot f p h.2.2⟩,
     joinCtxAtF_sub (Fin.succAbove p) p (succAbove_ne' p) (succAbove_surj p)
       (cov_of_dup (rhs := f.rhs) p i hip hgoal) h.1 h.2.1 h.2.2⟩

/-- The fallible `⋈^∨` shape. -/
def shapeOrF : Shape where
  ctx f := joinCtxOrF f.Ξs f.Θs f.rhs
  Hyp f := J1 f ∧ J2 f
  step f p i hip hgoal h :=
    ⟨⟨step_j1 f p h.1, step_j2 f p i hip hgoal h.2⟩,
     joinCtxOrF_sub (Fin.succAbove p) p (succAbove_ne' p) (succAbove_surj p)
       (cov_of_dup (rhs := f.rhs) p i hip hgoal) h.1 h.2⟩

/-- The promise `⋈^At` shape, under a fixed promise family `Δs`. -/
def shapeAtP {k : Nat} (F : Form) (Δs : Fin (k + 1) → List Form) : Shape where
  ctx f := joinCtxAtP f.Ξs f.Θs f.rhs F Δs
  Hyp f := J1 f ∧ J2 f ∧ J5 f Δs ∧ J6 f Δs ∧ FNot f F
  step f p i hip hgoal h :=
    ⟨⟨step_j1 f p h.1, step_j2 f p i hip hgoal h.2.1, step_j5 f p h.2.2.1,
      step_j6 f p h.2.2.2.1, step_fnot f p h.2.2.2.2⟩,
     joinCtxAtP_sub (Fin.succAbove p) p (succAbove_ne' p) (succAbove_surj p)
       (cov_of_dup (rhs := f.rhs) p i hip hgoal) h.1 h.2.1 h.2.2.2.2 h.2.2.1⟩

/-- The promise `⋈^∨`/`⋈^◯` shape, under a fixed promise family `Δs`. -/
def shapeOrP {k : Nat} (Δs : Fin (k + 1) → List Form) : Shape where
  ctx f := joinCtxOrP f.Ξs f.Θs f.rhs Δs
  Hyp f := J1 f ∧ J2 f ∧ J5 f Δs ∧ J6 f Δs
  step f p i hip hgoal h :=
    ⟨⟨step_j1 f p h.1, step_j2 f p i hip hgoal h.2.1, step_j5 f p h.2.2.1,
      step_j6 f p h.2.2.2⟩,
     joinCtxOrP_sub (Fin.succAbove p) p (succAbove_ne' p) (succAbove_surj p)
       (cov_of_dup (rhs := f.rhs) p i hip hgoal) h.1 h.2.1 h.2.2.1⟩

/-! ## 4. The restricted contract

`DBClosed` (`FRJ/Gbu/W/Closure.lean:1179`) with two restrictions: the
eight join clauses ask for pairwise distinct goals (`hdist`), and the
three promise clauses bound the promise family by `|Ĝ^◯| + 1` (`hk`).
Everything else is verbatim. -/

open FRJ.Gbu.W in
structure DBClosedDG (G : Form) (db : List (WRow G)) : Prop where
  axR : ∀ F : Form, F.isPrime → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg .barren (rm (gAt G) F) F) r.s
  andR1 : ∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
    (WSeq.reg t Γ A₁) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s
  andR2 : ∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
    (WSeq.reg t Γ A₂) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s
  impIn : ∀ (t : Tag) (Γ : List Form) (A B : Form),
    (WSeq.reg t Γ B) ∈ db.map (·.s) → Clo Γ A → Form.imp A B ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t Γ (.imp A B)) r.s
  circIn : ∀ (t : Tag) (Γ : List Form) (Z : Form),
    (WSeq.reg t Γ Z) ∈ db.map (·.s) →
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z) →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t Γ (.circ Z)) r.s
  joinAt : ∀ {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    unionAll (fun j => circPart (Ξs j)) = [] →
    F.isPrime → F ∉ unionAll (fun j => atPart (Ξs j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxAtVBase Ξs Θs F ++
        keptOf (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs)) F) r.s
  joinOr : ∀ {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    unionAll (fun j => circPart (Ξs j)) = [] →
    (RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) C₁ ∧
      RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) C₂) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs))
        (.or C₁ C₂)) r.s
  joinCirc : ∀ {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (Z : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) A) →
    unionAll (fun j => circPart (Ξs j)) = [] →
    RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
      keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) Z →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs))
        (.circ Z)) r.s
  joinAtP : ∀ {n k : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form) (t' : Tag)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    k ≤ (dedupF (gCirc G)).length →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) →
    (t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))) →
    F.isPrime → F ∉ unionAll (fun j => atPart (Ξs j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t' (joinCtxAtP Ξs Θs rhs F Δs) F) r.s
  joinOrP : ∀ {n k : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form) (t' : Tag)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    k ≤ (dedupF (gCirc G)).length →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) →
    (t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))) →
    (C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t' (joinCtxOrP Ξs Θs rhs Δs) (.or C₁ C₂)) r.s
  joinCircP : ∀ {n k : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (Z : Form)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    k ≤ (dedupF (gCirc G)).length →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) →
    (∀ i, Ds i = Z ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z)) →
    Z ∈ upsilon rhs → Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg (.chain Z) (joinCtxOrP Ξs Θs rhs Δs) (.circ Z)) r.s
  joinAtF : ∀ {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    F.isPrime → F ∉ unionAll (fun j => atPart (Ξs j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg .blocked (joinCtxAtF Ξs Θs rhs F) F) r.s
  joinOrF : ∀ {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .blocked (joinCtxOrF Ξs Θs rhs) (.or C₁ C₂)) r.s
  axI : ∀ F : Form, F.isPrime → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F) r.s
  andI1 : ∀ (Ξ Θ : List Form) (A₁ A₂ : Form),
    (WSeq.irr Ξ Θ A₁) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr Ξ Θ (.and A₁ A₂)) r.s
  andI2 : ∀ (Ξ Θ : List Form) (A₁ A₂ : Form),
    (WSeq.irr Ξ Θ A₂) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr Ξ Θ (.and A₁ A₂)) r.s
  orI : ∀ (Ξ₁ Θ₁ Ξ₂ Θ₂ : List Form) (C₁ C₂ : Form),
    (WSeq.irr Ξ₁ Θ₁ C₁) ∈ db.map (·.s) →
    (WSeq.irr Ξ₂ Θ₂ C₂) ∈ db.map (·.s) →
    Ξ₁ ⊆ Ξ₂ ++ Θ₂ → Ξ₂ ⊆ Ξ₁ ++ Θ₁ →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr (Ξ₁ ++ Ξ₂) (cap Θ₁ Θ₂) (.or C₁ C₂)) r.s
  impInI : ∀ (Ξ₂ ΘΛ₂ Λ : List Form) (A B : Form),
    (WSeq.irr Ξ₂ ΘΛ₂ B) ∈ db.map (·.s) →
    Clo (Ξ₂ ++ ΘΛ₂.filter (fun x => decide (x ∈ Λ))) A →
    Form.imp A B ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.irr (Ξ₂ ++ ΘΛ₂.filter (fun x => decide (x ∈ Λ)))
        (ΘΛ₂.filter (fun x => !decide (x ∈ Λ))) (.imp A B)) r.s
  lift : ∀ (t₂ : Tag) (Γ₂ : List Form) (C : Form),
    (WSeq.reg t₂ Γ₂ C) ∈ db.map (·.s) →
    ∃ r ∈ db, WSubsumes (.irr [] (maxTh G Γ₂) C) r.s
  circNotIn : ∀ (t₂ : Tag) (Γ₂ : List Form) (Z : Form),
    (WSeq.reg t₂ Γ₂ Z) ∈ db.map (·.s) →
    (t₂ = .barren ∨ ∃ W, t₂ = .chain W ∧ Covers Γ₂ W Z) →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr [] (maxTh G Γ₂) (.circ Z)) r.s
  axIC : ∀ (F : Form) (ats : List Form), ats ⊆ gAt G →
    classForce ats F = false → Form.circ F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.irr [] (vacZoneA G ats) (.circ F)) r.s

/-! ## 5. The strict join clauses of `DBClosed` from the restricted ones -/

section Corollary

open FRJ.Gbu.W

variable {G : Form} {db : List (WRow G)}

/-- A subsumption between two barren rows with the same goal is a context inclusion. -/
theorem wsub_reg_of_sub {t : Tag} {Γ Γ' : List Form} {C : Form} (h : Γ ⊆ Γ') :
    WSubsumes (.reg t Γ C) (.reg t Γ' C) :=
  ⟨rfl, tagLeB_refl' t, h⟩

theorem dg_joinAt (hdg : DBClosedDG G db) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (F : Form),
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    unionAll (fun j => circPart (Ξs j)) = [] →
    F.isPrime → F ∉ unionAll (fun j => atPart (Ξs j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxAtVBase Ξs Θs F ++
        keptOf (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs)) F) r.s := by
  intro n Ξs Θs rhs F hmem hJ1 hJ2 hJ3 hF hFnot hg
  obtain ⟨m, e, -, hdist, -, hHyp, hctx⟩ :=
    (shapeAt F).toDistinct n ⟨Ξs, Θs, rhs⟩ ⟨hJ1, hJ2, hJ3, hFnot⟩
  obtain ⟨r, hr, hsub⟩ := hdg.joinAt (fun k => Ξs (e k)) (fun k => Θs (e k))
    (fun k => rhs (e k)) F hdist (fun k => hmem (e k)) hHyp.1 hHyp.2.1 hHyp.2.2.1
    hF hHyp.2.2.2 hg
  exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx) hsub⟩

theorem dg_joinOr (hdg : DBClosedDG G db) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form),
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    unionAll (fun j => circPart (Ξs j)) = [] →
    (RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) C₁ ∧
      RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) C₂) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs))
        (.or C₁ C₂)) r.s := by
  intro n Ξs Θs rhs C₁ C₂ hmem hJ1 hJ2 hJ3 hC hg
  obtain ⟨m, e, -, hdist, hcov, hHyp, hctx⟩ :=
    shapeOr.toDistinct n ⟨Ξs, Θs, rhs⟩ ⟨hJ1, hJ2, hJ3⟩
  have hΥ := upsilon_sub_comp e rhs hcov
  obtain ⟨r, hr, hsub⟩ := hdg.joinOr (fun k => Ξs (e k)) (fun k => Θs (e k))
    (fun k => rhs (e k)) C₁ C₂ hdist (fun k => hmem (e k)) hHyp.1 hHyp.2.1 hHyp.2.2
    ⟨refAt_mono hΥ hctx hC.1, refAt_mono hΥ hctx hC.2⟩ hg
  exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx) hsub⟩

theorem dg_joinCirc (hdg : DBClosedDG G db) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (Z : Form),
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) A) →
    unionAll (fun j => circPart (Ξs j)) = [] →
    RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
      keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) Z →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs))
        (.circ Z)) r.s := by
  intro n Ξs Θs rhs Z hmem hJ1 hJ2r hJ3 hZ hg
  obtain ⟨m, e, -, hdist, hcov, hHyp, hctx⟩ :=
    shapeCirc.toDistinct n ⟨Ξs, Θs, rhs⟩ ⟨hJ1, hJ2r, hJ3⟩
  have hΥ := upsilon_sub_comp e rhs hcov
  obtain ⟨r, hr, hsub⟩ := hdg.joinCirc (fun k => Ξs (e k)) (fun k => Θs (e k))
    (fun k => rhs (e k)) Z hdist (fun k => hmem (e k)) hHyp.1 hHyp.2.1 hHyp.2.2
    (refAt_mono hΥ hctx hZ) hg
  exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx) hsub⟩

theorem dg_joinAtF (hdg : DBClosedDG G db) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (F : Form),
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    F.isPrime → F ∉ unionAll (fun j => atPart (Ξs j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg .blocked (joinCtxAtF Ξs Θs rhs F) F) r.s := by
  intro n Ξs Θs rhs F hmem hJ1 hJ2 hF hFnot hg
  obtain ⟨m, e, -, hdist, -, hHyp, hctx⟩ :=
    (shapeAtF F).toDistinct n ⟨Ξs, Θs, rhs⟩ ⟨hJ1, hJ2, hFnot⟩
  obtain ⟨r, hr, hsub⟩ := hdg.joinAtF (fun k => Ξs (e k)) (fun k => Θs (e k))
    (fun k => rhs (e k)) F hdist (fun k => hmem (e k)) hHyp.1 hHyp.2.1 hF hHyp.2.2 hg
  exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx) hsub⟩

theorem dg_joinOrF (hdg : DBClosedDG G db) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form),
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .blocked (joinCtxOrF Ξs Θs rhs) (.or C₁ C₂)) r.s := by
  intro n Ξs Θs rhs C₁ C₂ hmem hJ1 hJ2 hC hg
  obtain ⟨m, e, -, hdist, hcov, hHyp, hctx⟩ :=
    shapeOrF.toDistinct n ⟨Ξs, Θs, rhs⟩ ⟨hJ1, hJ2⟩
  have hΥ := upsilon_sub_comp e rhs hcov
  obtain ⟨r, hr, hsub⟩ := hdg.joinOrF (fun k => Ξs (e k)) (fun k => Θs (e k))
    (fun k => rhs (e k)) C₁ C₂ hdist (fun k => hmem (e k)) hHyp.1 hHyp.2
    ⟨hΥ hC.1, hΥ hC.2⟩ hg
  exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx) hsub⟩

/-! ### The promise clauses: B1 on the irregular family, then B2′ on the promise family -/

/-- Stored irregular rows have `Ĝ`-bounded zones. -/
theorem wf_of_mem {Ξ Θ : List Form} {C : Form}
    (h : (WSeq.irr Ξ Θ C) ∈ db.map (·.s)) : Ξ ⊆ gHat G ∧ Θ ⊆ gHat G := by
  obtain ⟨r, -, hrs⟩ := List.mem_map.mp h
  have hw : WfSeq G r.s := wfSeq_of_wDer r.d
  rw [hrs] at hw
  have hw' : Ξ ⊆ gHat G ∧ Θ ⊆ gHat G ∧ C ∈ sfR G := hw
  exact ⟨hw'.1, hw'.2.1⟩

theorem dg_joinAtP (hdg : DBClosedDG G db) : ∀ {n k : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (F : Form) (t' : Tag)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form) (Ds : Fin (k + 1) → Form),
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) →
    (t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))) →
    F.isPrime → F ∉ unionAll (fun j => atPart (Ξs j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t' (joinCtxAtP Ξs Θs rhs F Δs) F) r.s := by
  intro n k Ξs Θs rhs F t' tps Δs Ds hmemI hmemR hJ1 hJ2 hJ5 hJ6 htag hF hFnot hg
  obtain ⟨m, e, -, hdist, -, hHyp, hctx⟩ :=
    (shapeAtP F Δs).toDistinct n ⟨Ξs, Θs, rhs⟩ ⟨hJ1, hJ2, hJ5, hJ6, hFnot⟩
  have hwf : ∀ j, Ξs (e j) ⊆ gHat G ∧ Θs (e j) ⊆ gHat G :=
    fun j => wf_of_mem (hmemI (e j))
  obtain ⟨m', e', hm', hhit⟩ := hittingCut G (Ξs := fun j => Ξs (e j))
    (Θs := fun j => Θs (e j)) (Δs := Δs) hwf
  have hctx' : joinCtxAtP Ξs Θs rhs F Δs ⊆
      joinCtxAtP (fun j => Ξs (e j)) (fun j => Θs (e j)) (fun j => rhs (e j)) F
        (fun i' => Δs (e' i')) :=
    fun x hx => joinCtxAtP_cut e' hhit (hctx hx)
  have hJ5' := j5_cut e' hhit hHyp.2.2.1
  have hJ6' := j6_cut e' hHyp.2.2.2.1
  rcases htag with h0 | ⟨ht', hJ7⟩
  · obtain ⟨r, hr, hsub⟩ := hdg.joinAtP (fun j => Ξs (e j)) (fun j => Θs (e j))
      (fun j => rhs (e j)) F t' (fun i' => tps (e' i')) (fun i' => Δs (e' i'))
      (fun i' => Ds (e' i')) hdist hm' (fun j => hmemI (e j)) (fun i' => hmemR (e' i'))
      hHyp.1 hHyp.2.1 hJ5' hJ6' (Or.inl h0) hF hHyp.2.2.2.2 hg
    exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx') hsub⟩
  · obtain ⟨hJ7', h0'⟩ := j7_cut e' hJ7
    obtain ⟨r, hr, hsub⟩ := hdg.joinAtP (fun j => Ξs (e j)) (fun j => Θs (e j))
      (fun j => rhs (e j)) F t' (fun i' => tps (e' i')) (fun i' => Δs (e' i'))
      (fun i' => Ds (e' i')) hdist hm' (fun j => hmemI (e j)) (fun i' => hmemR (e' i'))
      hHyp.1 hHyp.2.1 hJ5' hJ6' (Or.inr ⟨by rw [ht', h0'], hJ7'⟩) hF hHyp.2.2.2.2 hg
    exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx') hsub⟩

theorem dg_joinOrP (hdg : DBClosedDG G db) : ∀ {n k : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form) (t' : Tag)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form) (Ds : Fin (k + 1) → Form),
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) →
    (t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))) →
    (C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t' (joinCtxOrP Ξs Θs rhs Δs) (.or C₁ C₂)) r.s := by
  intro n k Ξs Θs rhs C₁ C₂ t' tps Δs Ds hmemI hmemR hJ1 hJ2 hJ5 hJ6 htag hC hg
  obtain ⟨m, e, -, hdist, hcov, hHyp, hctx⟩ :=
    (shapeOrP Δs).toDistinct n ⟨Ξs, Θs, rhs⟩ ⟨hJ1, hJ2, hJ5, hJ6⟩
  have hΥ := upsilon_sub_comp e rhs hcov
  have hwf : ∀ j, Ξs (e j) ⊆ gHat G ∧ Θs (e j) ⊆ gHat G :=
    fun j => wf_of_mem (hmemI (e j))
  obtain ⟨m', e', hm', hhit⟩ := hittingCut G (Ξs := fun j => Ξs (e j))
    (Θs := fun j => Θs (e j)) (Δs := Δs) hwf
  have hctx' : joinCtxOrP Ξs Θs rhs Δs ⊆
      joinCtxOrP (fun j => Ξs (e j)) (fun j => Θs (e j)) (fun j => rhs (e j))
        (fun i' => Δs (e' i')) :=
    fun x hx => joinCtxOrP_cut e' hhit (hctx hx)
  have hJ5' := j5_cut e' hhit hHyp.2.2.1
  have hJ6' := j6_cut e' hHyp.2.2.2
  rcases htag with h0 | ⟨ht', hJ7⟩
  · obtain ⟨r, hr, hsub⟩ := hdg.joinOrP (fun j => Ξs (e j)) (fun j => Θs (e j))
      (fun j => rhs (e j)) C₁ C₂ t' (fun i' => tps (e' i')) (fun i' => Δs (e' i'))
      (fun i' => Ds (e' i')) hdist hm' (fun j => hmemI (e j)) (fun i' => hmemR (e' i'))
      hHyp.1 hHyp.2.1 hJ5' hJ6' (Or.inl h0) ⟨hΥ hC.1, hΥ hC.2⟩ hg
    exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx') hsub⟩
  · obtain ⟨hJ7', h0'⟩ := j7_cut e' hJ7
    obtain ⟨r, hr, hsub⟩ := hdg.joinOrP (fun j => Ξs (e j)) (fun j => Θs (e j))
      (fun j => rhs (e j)) C₁ C₂ t' (fun i' => tps (e' i')) (fun i' => Δs (e' i'))
      (fun i' => Ds (e' i')) hdist hm' (fun j => hmemI (e j)) (fun i' => hmemR (e' i'))
      hHyp.1 hHyp.2.1 hJ5' hJ6' (Or.inr ⟨by rw [ht', h0'], hJ7'⟩) ⟨hΥ hC.1, hΥ hC.2⟩ hg
    exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx') hsub⟩

theorem dg_joinCircP (hdg : DBClosedDG G db) : ∀ {n k : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (Z : Form)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form) (Ds : Fin (k + 1) → Form),
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) →
    (∀ i, Ds i = Z ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z)) →
    Z ∈ upsilon rhs → Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg (.chain Z) (joinCtxOrP Ξs Θs rhs Δs) (.circ Z)) r.s := by
  intro n k Ξs Θs rhs Z tps Δs Ds hmemI hmemR hJ1 hJ2 hJ5 hJ6 hDs hZ hg
  obtain ⟨m, e, -, hdist, hcov, hHyp, hctx⟩ :=
    (shapeOrP Δs).toDistinct n ⟨Ξs, Θs, rhs⟩ ⟨hJ1, hJ2, hJ5, hJ6⟩
  have hΥ := upsilon_sub_comp e rhs hcov
  have hwf : ∀ j, Ξs (e j) ⊆ gHat G ∧ Θs (e j) ⊆ gHat G :=
    fun j => wf_of_mem (hmemI (e j))
  obtain ⟨m', e', hm', hhit⟩ := hittingCut G (Ξs := fun j => Ξs (e j))
    (Θs := fun j => Θs (e j)) (Δs := Δs) hwf
  have hctx' : joinCtxOrP Ξs Θs rhs Δs ⊆
      joinCtxOrP (fun j => Ξs (e j)) (fun j => Θs (e j)) (fun j => rhs (e j))
        (fun i' => Δs (e' i')) :=
    fun x hx => joinCtxOrP_cut e' hhit (hctx hx)
  have hJ5' := j5_cut e' hhit hHyp.2.2.1
  have hJ6' := j6_cut e' hHyp.2.2.2
  obtain ⟨r, hr, hsub⟩ := hdg.joinCircP (fun j => Ξs (e j)) (fun j => Θs (e j))
    (fun j => rhs (e j)) Z (fun i' => tps (e' i')) (fun i' => Δs (e' i'))
    (fun i' => Ds (e' i')) hdist hm' (fun j => hmemI (e j)) (fun i' => hmemR (e' i'))
    hHyp.1 hHyp.2.1 hJ5' hJ6' (fun i' => hDs (e' i')) (hΥ hZ) hg
  exact ⟨r, hr, wSubsumes_trans (wsub_reg_of_sub hctx') hsub⟩

/-- **The corollary**: the restricted contract implies the full one. -/
theorem dbClosed_of_dg (h : DBClosedDG G db) : DBClosed G db where
  axR := h.axR
  andR1 := h.andR1
  andR2 := h.andR2
  impIn := h.impIn
  circIn := h.circIn
  joinAt := dg_joinAt h
  joinOr := dg_joinOr h
  joinCirc := dg_joinCirc h
  joinAtP := dg_joinAtP h
  joinOrP := dg_joinOrP h
  joinCircP := dg_joinCircP h
  joinAtF := dg_joinAtF h
  joinOrF := dg_joinOrF h
  axI := h.axI
  andI1 := h.andI1
  andI2 := h.andI2
  orI := h.orI
  impInI := h.impInI
  lift := h.lift
  circNotIn := h.circNotIn
  axIC := h.axIC

end Corollary

/-! ## Pins -/

/-- info: 'FRJ.Arity.dbClosed_of_dg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dbClosed_of_dg

/-- info: 'FRJ.Arity.dg_joinAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dg_joinAt

/-- info: 'FRJ.Arity.dg_joinOr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dg_joinOr

/-- info: 'FRJ.Arity.Shape.toDistinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shape.toDistinct

/-- info: 'FRJ.Arity.shapeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shapeAt

/-- info: 'FRJ.Arity.shapeAtP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shapeAtP

end FRJ.Arity
