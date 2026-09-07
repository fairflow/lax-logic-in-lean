/-
# `LaxLogic.QLL.Saturate` — the ω-construction

Zorn produces a maximal consistent theory but not a saturated one: an
inconsistency names only finitely many falsified formulas, and `∃x A` entails no
finite disjunction of its instances, so nothing forces a witness into `val`.
Witnesses have to be *interleaved* with the decisions, one per stage, and that
is an ω-recursion — hence the enumeration of `LaxLogic.QLL.Countable`.

Two constraints shape the construction.

**Henkin axioms are not intuitionistically conservative.**  Adding
`∃y φ(y) ⊃ φ(c)` outright yields `∃x (∃y φ(y) ⊃ φ(x))`, which is not valid.
What is conservative is adding the *instance* `φ(c)` at a stage where `∃y φ(y)`
is already in `val` — `consistent_insert_witness` below, whose proof is the
elimination rule at a fresh parameter.

**The reserve must survive.**  Each stage spends one name, so a construction
spending every name would leave the limit with none fresh, and the truth
lemma's universal-falsity case needs a fresh one to build its successor world.
So the names are split: the even ones are spent as witnesses, the odd ones are
reserved, and formulas mentioning a reserved name are never decided.  The limit
is total *for the formulas avoiding the odd names*, and those odd names are the
reserve of the world it becomes.
-/
import LaxLogic.QLL.Complete
import LaxLogic.QLL.Countable
import LaxLogic.QLL.ProvFresh

namespace LaxLogic.QLL

/-! ## Parameters

Names built as runs of `w`, so that a name's *index* is bounded by the length
of any list containing it.  That bound is what makes "all but finitely many
parameters are fresh for this formula" a one-line argument. -/

/-- The `i`-th parameter. -/
def pnm : Nat → String
  | 0     => "w"
  | i + 1 => (pnm i).push 'w'

theorem pnm_length : ∀ i, (pnm i).length = i + 1 := by
  intro i; induction i with
  | zero => rfl
  | succ n ih => simp [pnm, ih]

theorem pnm_inj : Function.Injective pnm := by
  intro i j h
  have := pnm_length i
  rw [h, pnm_length j] at this
  omega

/-- The greatest length in a list of names. -/
def maxLen : List String → Nat
  | []     => 0
  | s :: L => max s.length (maxLen L)

theorem le_maxLen : ∀ {L : List String} {s : String}, s ∈ L → s.length ≤ maxLen L
  | _ :: L, s, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact le_trans (le_maxLen h) (Nat.le_max_right _ _)

/-- Every parameter of large enough index is fresh for a given list. -/
theorem pnm_notMem_of_ge {L : List String} {i : Nat} (h : maxLen L ≤ i) : pnm i ∉ L := by
  intro hmem
  have := le_maxLen hmem
  rw [pnm_length] at this
  omega

/-! ## Free variables of a falsified disjunction

`Consistent` is stated with a disjunction assembled from the falsified parts.
The Henkin step needs a parameter fresh for that disjunction, and this is where
that reduces to freshness for the parts. -/

theorem fv_bigOr {x : String} : ∀ (As : List Form), x ∈ (bigOr As).fv → ∃ A ∈ As, x ∈ A.fv
  | []          => by simp [bigOr, Form.fv]
  | [A]         => fun h => ⟨A, by simp, h⟩
  | A :: B :: As => by
      intro h
      simp only [bigOr, Form.fv, List.mem_append] at h
      rcases h with h | h
      · exact ⟨A, by simp, h⟩
      · obtain ⟨C, hC, hx⟩ := fv_bigOr (B :: As) h
        exact ⟨C, List.mem_cons_of_mem _ hC, hx⟩

theorem fv_modalPart {x : String} {q : Q} {Ts : List Form}
    (h : ∃ A ∈ modalPart q Ts, x ∈ A.fv) : ∃ A ∈ Ts, x ∈ A.fv := by
  cases Ts with
  | nil => simp [modalPart] at h
  | cons B Bs =>
      obtain ⟨A, hA, hx⟩ := h
      simp only [modalPart, List.mem_singleton] at hA
      subst hA
      exact fv_bigOr _ (by simpa [Form.fv] using hx)

theorem fv_disjOf {x : String} {Ds TA TE : List Form}
    (h : x ∈ (disjOf Ds TA TE).fv) : ∃ A ∈ Ds ++ TA ++ TE, x ∈ A.fv := by
  obtain ⟨A, hA, hx⟩ := fv_bigOr _ h
  rcases List.mem_append.mp hA with hA | hA
  · rcases List.mem_append.mp hA with hA | hA
    · exact ⟨A, by simp [hA], hx⟩
    · obtain ⟨C, hC, hxC⟩ := fv_modalPart ⟨A, hA, hx⟩
      exact ⟨C, by simp [hC], hxC⟩
  · obtain ⟨C, hC, hxC⟩ := fv_modalPart ⟨A, hA, hx⟩
    exact ⟨C, by simp [hC], hxC⟩

/-! ## Context freeness -/

theorem mem_ctxFv' : ∀ {Γ : List Form} {x : String}, x ∈ ctxFv Γ → ∃ A ∈ Γ, x ∈ A.fv
  | [],     _, h => by simp [ctxFv] at h
  | A :: Γ, x, h => by
      rcases List.mem_append.mp h with h | h
      · exact ⟨A, by simp, h⟩
      · obtain ⟨B, hB, hx⟩ := mem_ctxFv' h
        exact ⟨B, List.mem_cons_of_mem _ hB, hx⟩

/-! ## The conservative Henkin step

The one place the renaming lemma is spent. -/

/-- Adding a witness for an existential already in `val`, at a parameter fresh
for the whole theory, preserves consistency. -/
theorem consistent_insert_witness {T : Theory} (hT : Consistent T) {B : Form} {c : String}
    (hex : Form.exists_ B ∈ T.val)
    (hfresh : ∀ A, (A ∈ T.val ∨ A ∈ T.fal ∨ ∃ q, A ∈ T.mfal q) → c ∉ A.fv) :
    Consistent ⟨insert (B.openWith c) T.val, T.fal, T.mfal⟩ := by
  intro Ds TA TE hD hA hE hne hder
  have hDfv : c ∉ (disjOf Ds TA TE).fv := by
    intro hc
    obtain ⟨X, hX, hx⟩ := fv_disjOf hc
    rcases List.mem_append.mp hX with hX | hX
    · rcases List.mem_append.mp hX with hX | hX
      · exact hfresh X (Or.inr (Or.inl (hD X hX))) hx
      · exact hfresh X (Or.inr (Or.inr ⟨.all, hA X hX⟩)) hx
    · exact hfresh X (Or.inr (Or.inr ⟨.ex, hE X hX⟩)) hx
  have hBfv : c ∉ B.fv := fun hc => hfresh _ (Or.inl hex) (by simpa [Form.fv] using hc)
  obtain ⟨L₁, hL₁, hp₁⟩ := SetPrv.deduct hder
  obtain ⟨L₂, hL₂, hp₂⟩ := SetPrv.of_mem hex
  refine hT Ds TA TE hD hA hE hne ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro X hX
    rcases List.mem_append.mp hX with h | h
    · exact hL₁ X h
    · exact hL₂ X h
  · have hctx : c ∉ ctxFv (L₁ ++ L₂) := by
      intro hc
      obtain ⟨X, hX, hx⟩ := mem_ctxFv' hc
      rcases List.mem_append.mp hX with h | h
      · exact hfresh X (Or.inl (hL₁ X h)) hx
      · exact hfresh X (Or.inl (hL₂ X h)) hx
    refine Prv.exE_of_fresh hctx hBfv hDfv
      (hp₂.weaken (fun X h => List.mem_append_right _ h)) ?_
    exact .impE (Prv.weaken hp₁ (fun X h => List.mem_cons_of_mem _ (List.mem_append_left _ h)))
      (.var (List.mem_cons_self ..))


/-! ## The schedule

`enum` is a surjection; `sched` is a surjection that hits every formula
*infinitely often*, which is what lets a formula wait until the parameters it
mentions have all been spent. -/

/-- The formula scheduled at stage `n`. -/
noncomputable def sched (n : Nat) : Form := enum (Nat.unpair n).1

theorem sched_hits (A : Form) (N : Nat) : ∃ k, N ≤ k ∧ sched k = A := by
  obtain ⟨m, hm⟩ := enum_surj A
  refine ⟨Nat.pair m N, Nat.right_le_pair m N, ?_⟩
  simp [sched, Nat.unpair_pair, hm]

/-! ## The reserve, and what is still unspent

Even slots are spent as witnesses, one per stage; odd slots are never spent and
become the reserve of the theory that results. -/

/-- The `i`-th reserved name. -/
def resName (f : Nat → Nat) (i : Nat) : String := pnm (f i)

/-- The names that survive the construction. -/
def oddNames (f : Nat → Nat) : Set String := {x | ∃ j, x = resName f (2 * j + 1)}

/-- Every reserved name. -/
def allNames (f : Nat → Nat) : Set String := {x | ∃ i, x = resName f i}

/-- The names not yet spent at stage `k`: the unspent witnesses and the whole
reserve. -/
def unused (f : Nat → Nat) (k : Nat) : Set String :=
  {x | (∃ j, k ≤ j ∧ x = resName f (2 * j)) ∨ ∃ j, x = resName f (2 * j + 1)}

theorem resName_inj {f : Nat → Nat} (hf : StrictMono f) : Function.Injective (resName f) :=
  fun _ _ h => hf.injective (pnm_inj h)

theorem oddNames_sub_unused {f : Nat → Nat} (k : Nat) : oddNames f ⊆ unused f k :=
  fun _ ⟨j, hj⟩ => Or.inr ⟨j, hj⟩

theorem unused_sub_allNames {f : Nat → Nat} {k : Nat} : unused f k ⊆ allNames f := by
  rintro x (⟨j, _, rfl⟩ | ⟨j, rfl⟩)
  · exact ⟨2 * j, rfl⟩
  · exact ⟨2 * j + 1, rfl⟩

theorem unused_succ_sub {f : Nat → Nat} {k : Nat} : unused f (k + 1) ⊆ unused f k := by
  rintro x (⟨j, hj, rfl⟩ | ⟨j, rfl⟩)
  · exact Or.inl ⟨j, by omega, rfl⟩
  · exact Or.inr ⟨j, rfl⟩

theorem unused_mono {f : Nat → Nat} {m n : Nat} (h : m ≤ n) : unused f n ⊆ unused f m := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ p ih =>
      rcases Nat.lt_or_ge m (p + 1) with hlt | hge
      · exact unused_succ_sub.trans (ih (by omega))
      · rw [Nat.le_antisymm h hge]

theorem mem_unused_self {f : Nat → Nat} (k : Nat) : resName f (2 * k) ∈ unused f k :=
  Or.inl ⟨k, le_rfl, rfl⟩

theorem notMem_unused_succ {f : Nat → Nat} (hf : StrictMono f) (k : Nat) :
    resName f (2 * k) ∉ unused f (k + 1) := by
  rintro (⟨j, hj, he⟩ | ⟨j, he⟩) <;>
    · have := resName_inj hf he; omega

/-! ## One stage

`decide1` places the scheduled formula on one side or the other — always
possible, by `consistent_split`.  `witness1` then supplies a witness when what
was placed is an existential now in `val`; that is the conservative Henkin step,
and it is the only consumer of a parameter. -/

open Classical in
/-- Decide a formula. -/
noncomputable def decide1 (T : Theory) (A : Form) : Theory :=
  if Consistent ⟨insert A T.val, T.fal, T.mfal⟩
  then ⟨insert A T.val, T.fal, T.mfal⟩
  else ⟨T.val, insert A T.fal, T.mfal⟩

open Classical in
/-- Witness an existential that is in `val`. -/
noncomputable def witness1 (T : Theory) (A : Form) (c : String) : Theory :=
  match A with
  | .exists_ B => if Form.exists_ B ∈ T.val
                  then ⟨insert (B.openWith c) T.val, T.fal, T.mfal⟩ else T
  | _ => T

open Classical in
/-- One stage of the construction. -/
noncomputable def step (f : Nat → Nat) (k : Nat) (T : Theory) : Theory :=
  if Avoids (unused f k) (sched k)
  then witness1 (decide1 T (sched k)) (sched k) (resName f (2 * k))
  else T

/-- The chain. -/
noncomputable def stages (f : Nat → Nat) (T₀ : Theory) : Nat → Theory
  | 0     => T₀
  | k + 1 => step f k (stages f T₀ k)

theorem decide1_le (T : Theory) (A : Form) : T ≤ decide1 T A := by
  unfold decide1; split
  · exact ⟨Set.subset_insert .., subset_rfl, fun _ => subset_rfl⟩
  · exact ⟨subset_rfl, Set.subset_insert .., fun _ => subset_rfl⟩

theorem witness1_le (T : Theory) (A : Form) (c : String) : T ≤ witness1 T A c := by
  unfold witness1; split
  · split
    · exact ⟨Set.subset_insert .., subset_rfl, fun _ => subset_rfl⟩
    · exact le_rfl
  · exact le_rfl

open Classical in
/-- `witness1` at an existential, with the match reduced. -/
theorem witness1_exists (T : Theory) (B : Form) (c : String) :
    witness1 T (Form.exists_ B) c =
      if Form.exists_ B ∈ T.val then ⟨insert (B.openWith c) T.val, T.fal, T.mfal⟩ else T := rfl

theorem step_le (f : Nat → Nat) (k : Nat) (T : Theory) : T ≤ step f k T := by
  unfold step; split
  · exact (decide1_le T _).trans (witness1_le _ _ _)
  · exact le_rfl

theorem stages_mono {f : Nat → Nat} {T₀ : Theory} {m n : Nat} (h : m ≤ n) :
    stages f T₀ m ≤ stages f T₀ n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ p ih =>
      rcases Nat.lt_or_ge m (p + 1) with hlt | hge
      · exact (ih (by omega)).trans (step_le f p _)
      · rw [Nat.le_antisymm h hge]

/-! ## Consistency and the freshness invariant, stage by stage -/

/-- Every formula the theory mentions avoids the names not yet spent. -/
def Inv (f : Nat → Nat) (k : Nat) (T : Theory) : Prop :=
  ∀ A, (A ∈ T.val ∨ A ∈ T.fal ∨ ∃ q, A ∈ T.mfal q) → Avoids (unused f k) A

theorem decide1_consistent {T : Theory} (hT : Consistent T) (A : Form) :
    Consistent (decide1 T A) := by
  unfold decide1; split
  · assumption
  · rcases consistent_split hT A with h | h
    · exact absurd h ‹_›
    · exact h

theorem decide1_inv {f : Nat → Nat} {k : Nat} {T : Theory} (hI : Inv f k T)
    {A : Form} (hA : Avoids (unused f k) A) : Inv f k (decide1 T A) := by
  unfold decide1; split <;> rintro X (hX | hX | ⟨q, hX⟩)
  · rcases hX with rfl | hX
    · exact hA
    · exact hI X (Or.inl hX)
  · exact hI X (Or.inr (Or.inl hX))
  · exact hI X (Or.inr (Or.inr ⟨q, hX⟩))
  · exact hI X (Or.inl hX)
  · rcases hX with rfl | hX
    · exact hA
    · exact hI X (Or.inr (Or.inl hX))
  · exact hI X (Or.inr (Or.inr ⟨q, hX⟩))

theorem witness1_consistent {f : Nat → Nat} {k : Nat} {T : Theory}
    (hT : Consistent T) (hI : Inv f k T) (A : Form) :
    Consistent (witness1 T A (resName f (2 * k))) := by
  unfold witness1; split
  · split
    · refine consistent_insert_witness hT ‹_› (fun X hX hc => ?_)
      exact hI X hX _ hc (mem_unused_self k)
    · exact hT
  · exact hT

theorem witness1_inv {f : Nat → Nat} (hf : StrictMono f) {k : Nat} {T : Theory}
    (hI : Inv f k T) (A : Form) :
    Inv f (k + 1) (witness1 T A (resName f (2 * k))) := by
  have hold : ∀ X, (X ∈ T.val ∨ X ∈ T.fal ∨ ∃ q, X ∈ T.mfal q) →
      Avoids (unused f (k + 1)) X :=
    fun X hX x hx hmem => hI X hX x hx (unused_succ_sub hmem)
  unfold witness1; split
  · next B =>
    split
    · rintro X (hX | hX | ⟨q, hX⟩)
      · rcases hX with rfl | hX
        · intro x hx hmem
          rcases Form.fv_openAt x (.fvar (resName f (2 * k))) B 0 hx with h | h
          · rw [show x = resName f (2 * k) by simpa [Tm.fv] using h] at hmem
            exact notMem_unused_succ hf k hmem
          · exact hold _ (Or.inl ‹Form.exists_ B ∈ T.val›) x (by simpa [Form.fv] using h) hmem
        · exact hold X (Or.inl hX)
      · exact hold X (Or.inr (Or.inl hX))
      · exact hold X (Or.inr (Or.inr ⟨q, hX⟩))
    · exact hold
  · exact hold

theorem stages_consistent {f : Nat → Nat} (hf : StrictMono f) {T₀ : Theory}
    (h₀ : Consistent T₀) (hI₀ : Inv f 0 T₀) :
    ∀ k, Consistent (stages f T₀ k) ∧ Inv f k (stages f T₀ k) := by
  intro k
  induction k with
  | zero => exact ⟨h₀, hI₀⟩
  | succ p ih =>
      obtain ⟨hc, hI⟩ := ih
      show Consistent (step f p _) ∧ Inv f (p + 1) (step f p _)
      unfold step; split
      · next hg =>
        exact ⟨witness1_consistent (decide1_consistent hc _) (decide1_inv hI hg) _,
               witness1_inv hf (decide1_inv hI hg) _⟩
      · exact ⟨hc, fun X hX x hx hmem => hI X hX x hx (unused_succ_sub hmem)⟩


/-! ## The limit

A union along the chain.  Consistency passes to the limit because an
inconsistency is a finite object: it names finitely many falsified formulas and
uses a finite context, so it already lives at some stage. -/

/-- The union of the chain. -/
noncomputable def limit (f : Nat → Nat) (T₀ : Theory) : Theory where
  val := {A | ∃ k, A ∈ (stages f T₀ k).val}
  fal := {A | ∃ k, A ∈ (stages f T₀ k).fal}
  mfal q := {A | ∃ k, A ∈ (stages f T₀ k).mfal q}

theorem stage_le_limit {f : Nat → Nat} {T₀ : Theory} (k : Nat) :
    stages f T₀ k ≤ limit f T₀ :=
  ⟨fun _ h => ⟨k, h⟩, fun _ h => ⟨k, h⟩, fun _ _ h => ⟨k, h⟩⟩

theorem le_limit {f : Nat → Nat} {T₀ : Theory} : T₀ ≤ limit f T₀ := stage_le_limit 0

/-- A finite list drawn from a chain of sets lies inside a single link. -/
theorem exists_stage_forall {S : Nat → Set Form} (hmono : ∀ {m n}, m ≤ n → S m ⊆ S n) :
    ∀ (L : List Form), (∀ X ∈ L, ∃ k, X ∈ S k) → ∃ k, ∀ X ∈ L, X ∈ S k
  | [],     _ => ⟨0, by simp⟩
  | X :: L, h => by
      obtain ⟨k₁, hk₁⟩ := h X (by simp)
      obtain ⟨k₂, hk₂⟩ := exists_stage_forall hmono L (fun Y hY => h Y (by simp [hY]))
      refine ⟨max k₁ k₂, fun Y hY => ?_⟩
      rcases List.mem_cons.mp hY with rfl | hY
      · exact hmono (le_max_left _ _) hk₁
      · exact hmono (le_max_right _ _) (hk₂ Y hY)

theorem limit_consistent {f : Nat → Nat} (hf : StrictMono f) {T₀ : Theory}
    (h₀ : Consistent T₀) (hI₀ : Inv f 0 T₀) : Consistent (limit f T₀) := by
  intro Ds TA TE hD hA hE hne hder
  obtain ⟨L, hL, hp⟩ := hder
  obtain ⟨k₁, hk₁⟩ := exists_stage_forall
    (S := fun k => (stages f T₀ k).val) (fun h => (stages_mono h).1) L hL
  obtain ⟨k₂, hk₂⟩ := exists_stage_forall
    (S := fun k => (stages f T₀ k).fal) (fun h => (stages_mono h).2.1) Ds hD
  obtain ⟨k₃, hk₃⟩ := exists_stage_forall
    (S := fun k => (stages f T₀ k).mfal .all) (fun h => (stages_mono h).2.2 .all) TA hA
  obtain ⟨k₄, hk₄⟩ := exists_stage_forall
    (S := fun k => (stages f T₀ k).mfal .ex) (fun h => (stages_mono h).2.2 .ex) TE hE
  refine (stages_consistent hf h₀ hI₀ (max (max k₁ k₂) (max k₃ k₄))).1 Ds TA TE
    (fun X hX => (stages_mono (le_trans (le_max_right k₁ k₂) (le_max_left _ _))).2.1 (hk₂ X hX))
    (fun X hX => (stages_mono (le_trans (le_max_left k₃ k₄) (le_max_right _ _))).2.2 _ (hk₃ X hX))
    (fun X hX => (stages_mono (le_trans (le_max_right k₃ k₄) (le_max_right _ _))).2.2 _ (hk₄ X hX))
    hne ⟨L, fun X hX =>
      (stages_mono (le_trans (le_max_left k₁ k₂) (le_max_left _ _))).1 (hk₁ X hX), hp⟩

theorem strictMono_le_apply {f : Nat → Nat} (hf : StrictMono f) : ∀ n, n ≤ f n := by
  intro n
  induction n with
  | zero => omega
  | succ p ih =>
      have h := hf (show p < p + 1 by omega)
      omega

/-- The scheduled formula is decided, one way or the other. -/
theorem decide1_decides (T : Theory) (A : Form) :
    A ∈ (decide1 T A).val ∨ A ∈ (decide1 T A).fal := by
  unfold decide1; split
  · exact Or.inl (Set.mem_insert ..)
  · exact Or.inr (Set.mem_insert ..)

/-- Stage `k` decides the formula scheduled there, when the guard admits it. -/
theorem step_decides {f : Nat → Nat} {k : Nat} {T : Theory}
    (hg : Avoids (unused f k) (sched k)) :
    sched k ∈ (step f k T).val ∨ sched k ∈ (step f k T).fal := by
  have hle := witness1_le (decide1 T (sched k)) (sched k) (resName f (2 * k))
  rcases decide1_decides T (sched k) with h | h
  · exact Or.inl (by unfold step; rw [if_pos hg]; exact hle.1 h)
  · exact Or.inr (by unfold step; rw [if_pos hg]; exact hle.2.1 h)

theorem limit_total {f : Nat → Nat} (hf : StrictMono f) {T₀ : Theory} :
    Total (oddNames f) (limit f T₀) := by
  intro A hav
  obtain ⟨k, hk, hs⟩ := sched_hits A (maxLen A.fv)
  have hguard : Avoids (unused f k) (sched k) := by
    rw [hs]
    intro x hx hmem
    rcases hmem with ⟨j, hj, he⟩ | ⟨j, he⟩
    · rw [he] at hx
      exact pnm_notMem_of_ge
        (le_trans hk (le_trans hj (le_trans (by omega) (strictMono_le_apply hf (2 * j))))) hx
    · exact hav x hx ⟨j, he⟩
  rcases step_decides (T := stages f T₀ k) hguard with h | h
  · exact Or.inl ⟨k + 1, hs ▸ h⟩
  · exact Or.inr ⟨k + 1, hs ▸ h⟩

theorem limit_inv {f : Nat → Nat} (hf : StrictMono f) {T₀ : Theory}
    (h₀ : Consistent T₀) (hI₀ : Inv f 0 T₀) :
    ∀ A, (A ∈ (limit f T₀).val ∨ A ∈ (limit f T₀).fal ∨ ∃ q, A ∈ (limit f T₀).mfal q) →
      Avoids (oddNames f) A := by
  intro A hA
  have : ∃ k, A ∈ (stages f T₀ k).val ∨ A ∈ (stages f T₀ k).fal ∨
      ∃ q, A ∈ (stages f T₀ k).mfal q := by
    rcases hA with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨q, k, hk⟩
    · exact ⟨k, Or.inl hk⟩
    · exact ⟨k, Or.inr (Or.inl hk)⟩
    · exact ⟨k, Or.inr (Or.inr ⟨q, hk⟩)⟩
  obtain ⟨k, hk⟩ := this
  exact fun x hx hmem =>
    (stages_consistent hf h₀ hI₀ k).2 A hk x hx (oddNames_sub_unused k hmem)

theorem limit_sat {f : Nat → Nat} (hf : StrictMono f) {T₀ : Theory}
    (h₀ : Consistent T₀) (hI₀ : Inv f 0 T₀) (B : Form)
    (hex : Form.exists_ B ∈ (limit f T₀).val) :
    ∃ c : String, c ∉ oddNames f ∧ B.openWith c ∈ (limit f T₀).val := by
  obtain ⟨k₀, hk₀⟩ := hex
  obtain ⟨k, hk, hs⟩ := sched_hits (Form.exists_ B) k₀
  have hmem : Form.exists_ B ∈ (stages f T₀ k).val := (stages_mono hk).1 hk₀
  have hguard : Avoids (unused f k) (sched k) := by
    rw [hs]; exact (stages_consistent hf h₀ hI₀ k).2 _ (Or.inl hmem)
  refine ⟨resName f (2 * k), ?_, ?_⟩
  · rintro ⟨j, hj⟩
    have := resName_inj hf hj
    omega
  · refine ⟨k + 1, ?_⟩
    show _ ∈ (step f k (stages f T₀ k)).val
    unfold step
    rw [if_pos hguard, hs]
    rw [witness1_exists, if_pos ((decide1_le _ _).1 hmem)]
    exact Set.mem_insert ..

/-! ## The result

Everything the canonical model asks of a state, in one package. -/

/-- A theory fit to be a world: consistent, deciding every formula that avoids
its reserve, mentioning no reserved name, and witnessing every existential it
validates. -/
structure Saturated (f : Nat → Nat) (T : Theory) : Prop where
  /-- Consistent, and total for the formulas avoiding the reserve. -/
  good : Good (oddNames f) T
  /-- No reserved name is mentioned. -/
  inv : ∀ A, (A ∈ T.val ∨ A ∈ T.fal ∨ ∃ q, A ∈ T.mfal q) → Avoids (oddNames f) A
  /-- Every validated existential has a witness. -/
  sat : ∀ B, Form.exists_ B ∈ T.val → ∃ c : String, c ∉ oddNames f ∧ B.openWith c ∈ T.val

/-- **Saturated Lindenbaum.**  A consistent theory mentioning no reserved name
extends to a saturated one, whose own reserve is the odd half of the original. -/
theorem exists_saturated {f : Nat → Nat} (hf : StrictMono f) {T₀ : Theory}
    (h₀ : Consistent T₀)
    (hI₀ : ∀ A, (A ∈ T₀.val ∨ A ∈ T₀.fal ∨ ∃ q, A ∈ T₀.mfal q) → Avoids (allNames f) A) :
    ∃ T, T₀ ≤ T ∧ Saturated f T := by
  have hI : Inv f 0 T₀ := fun A hA x hx hmem => hI₀ A hA x hx (unused_sub_allNames hmem)
  exact ⟨limit f T₀, le_limit,
    ⟨⟨limit_consistent hf h₀ hI, limit_total hf⟩, limit_inv hf h₀ hI,
     limit_sat hf h₀ hI⟩⟩

end LaxLogic.QLL
