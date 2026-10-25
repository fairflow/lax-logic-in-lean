import wip.p2llStatements

/-!
# A two-valued semantics for the shared formula type, and four refutations

File 7 of the P2LL definability campaign (`wip/p2ll-STATUS.md` §8).

The statements RTP, RTJ, MP, MJ of `wip/p2llStatements.lean` quantify over the
WHOLE formula type `Fm`, which both calculi share (§2.1 of the status note):
a P2LL formula may contain `allJ`, a guarded formula may contain `circ`, and
each calculus has no rule for the other's connective.  On such formulas the
round trips fail for the trivial reason that the inert connective is
translated into something the other calculus can use:

    RTP  fails at  ∀°q.q          (`allJ (bvar 0)`):   ∀°q.q ⊬_P2LL ∀p.((◯p → p) → p)
         and at    ∀°q.(q → q):   ∀p.((◯p → p) → (p → p)) ⊬_P2LL ∀°q.(q → q)
    MP   fails at  Γ = [], φ = ∀°q.(q → q):   ⊢_J φ,  ⊬_P2LL φ
    RTJ  fails at  ◯⊥:   ◯⊥ ⊬_J ∀°q.((⊥ → q) → q);   and at ◯⊤:  ∀°q.((⊤ → q) → q) ⊬_J ◯⊤
    MJ   fails at  Θ = [], Γ = [], φ = ◯⊤:   ⊢_P2LL ◯⊤,  ⊬_J ◯⊤

The non-derivabilities are kernel-checked through a two-valued semantics
`beval` on `Fm`: atoms by a valuation `ρ : String → Bool`, indices by an
environment `Nat → Bool`, the connectives Boolean, `∀` the meet over `Bool`,
and the two connectives inert in one of the calculi interpreted by parameters
(`BSem`): `circ` by a function `Bool → Bool` (the identity for P2LL, where the
lax rules must hold; a constant for the guarded calculus), `allJ` by a function
of the two instances (the meet for the guarded calculus, where `∀°E` has
full comprehension on this model; a constant for P2LL).  Soundness
(`LaxND2.bsound`, `JND.bsound`) is by recursion on the derivation; the only
non-routine step is the cofinite `∀I`, which needs a name outside a finite
list, `fresh`.

**Pins.**  Core's lemmas about `String` (`String.toList_ofList`,
`String.length_pushn`, `String.ext`, `Nat.repr_inj`) are all
`[propext, Classical.choice, Quot.sound]` (the UTF-8 representation), so
`fresh_not_mem`, both soundness theorems and the refutations carry that
profile, the one `or_not_fixed` (C6) carries from `Frames.lean`.  The
positive theorems of the campaign (`wip/p2llInterp.lean`) choose no names and
stay at `[propext]`.  With `Nat` variables the refutations would be
`[propext]` too.

The four statements were therefore REFUTED as first stated (2026-10-24).  On
2026-10-25 (Matthew's decision, status note §9) the names in
`wip/p2llStatements.lean` took the restricted text (`allJFree` for RTP and
MP, `circFree` for RTJ and MJ); the wording of 2026-10-24 is kept here as
`RoundTripP2LLUnrestricted`, `RoundTripJUnrestricted`,
`MutualP2LLUnrestricted`, `MutualJUnrestricted`, the record of the refutation.
-/

namespace P2LL

open Fm

/-! ## Free variables and a fresh name -/

/-- The free (named) variables of a formula. -/
def fv : Fm → List String
  | .fvar s => [s]
  | .bvar _ => []
  | .bot => []
  | .and φ ψ => fv φ ++ fv ψ
  | .or φ ψ => fv φ ++ fv ψ
  | .imp φ ψ => fv φ ++ fv ψ
  | .circ φ => fv φ
  | .all ψ => fv ψ
  | .allJ ψ => fv ψ

/-- The free variables of a context. -/
def fvL : List Fm → List String
  | [] => []
  | φ :: Γ => fv φ ++ fvL Γ

theorem not_mem_append_left {α : Type} {a : α} {l₁ l₂ : List α} (h : a ∉ l₁ ++ l₂) : a ∉ l₁ :=
  fun h' => h (List.mem_append_left _ h')

theorem not_mem_append_right {α : Type} {a : α} {l₁ l₂ : List α} (h : a ∉ l₁ ++ l₂) : a ∉ l₂ :=
  fun h' => h (List.mem_append_right _ h')

theorem fvL_sub {γ : Fm} {Γ : List Fm} (h : γ ∈ Γ) : ∀ s, s ∈ fv γ → s ∈ fvL Γ := by
  induction h
  · intro s hs
    exact List.mem_append_left _ hs
  · intro s hs
    rename_i ih
    exact List.mem_append_right _ (ih s hs)

/-- The total length of a list of strings. -/
def sumLen : List String → Nat
  | [] => 0
  | s :: L => s.toList.length + sumLen L

theorem len_le_sumLen {s : String} {L : List String} (h : s ∈ L) :
    s.toList.length ≤ sumLen L := by
  induction h
  · exact Nat.le_add_right _ _
  · rename_i ih
    exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- A string longer than every string in `L`. -/
def fresh (L : List String) : String := String.ofList (List.replicate (sumLen L + 1) 'a')

/-- `fresh L ∉ L`.  Classical through core's `String.toList_ofList`. -/
theorem fresh_not_mem (L : List String) : fresh L ∉ L := fun h => by
  have h1 := len_le_sumLen h
  rw [fresh, String.toList_ofList, List.length_replicate] at h1
  exact Nat.lt_irrefl _ h1

/-! ## The semantics -/

/-- The interpretation of the two connectives that are inert in one calculus. -/
structure BSem where
  circ : Bool → Bool
  allJ : Bool → Bool → Bool

/-- Extend an index environment under a binder. -/
def consE (b : Bool) (env : Nat → Bool) : Nat → Bool
  | 0 => b
  | n + 1 => env n

/-- Insert `b` at index `k` of an environment. -/
def insE (k : Nat) (b : Bool) (env : Nat → Bool) (n : Nat) : Bool :=
  if n < k then env n else if n = k then b else env (n - 1)

/-- Update a valuation at one name. -/
def upd (ρ : String → Bool) (s : String) (b : Bool) (t : String) : Bool :=
  if t = s then b else ρ t

/-- Two-valued evaluation: atoms by `ρ`, indices by `env`, `∀` the meet over
`Bool`, `circ` and `allJ` by the parameters. -/
def beval (S : BSem) (ρ : String → Bool) : Fm → (Nat → Bool) → Bool
  | .fvar s, _ => ρ s
  | .bvar n, env => env n
  | .bot, _ => false
  | .and φ ψ, env => beval S ρ φ env && beval S ρ ψ env
  | .or φ ψ, env => beval S ρ φ env || beval S ρ ψ env
  | .imp φ ψ, env => !beval S ρ φ env || beval S ρ ψ env
  | .circ φ, env => S.circ (beval S ρ φ env)
  | .all ψ, env => beval S ρ ψ (consE true env) && beval S ρ ψ (consE false env)
  | .allJ ψ, env => S.allJ (beval S ρ ψ (consE true env)) (beval S ρ ψ (consE false env))

/-! ### Environments -/

theorem consE_congr {env env' : Nat → Bool} (b : Bool) (h : ∀ n, env n = env' n) :
    ∀ n, consE b env n = consE b env' n
  | 0 => rfl
  | n + 1 => h n

theorem consE_lt {env env' : Nat → Bool} (b : Bool) {k : Nat} (h : ∀ n, n < k → env n = env' n) :
    ∀ n, n < k + 1 → consE b env n = consE b env' n
  | 0, _ => rfl
  | n + 1, hn => h n (Nat.lt_of_succ_lt_succ hn)

theorem insE_zero (b : Bool) (env : Nat → Bool) : ∀ n, insE 0 b env n = consE b env n
  | 0 => rfl
  | _ + 1 => rfl

theorem insE_succ (k : Nat) (b c : Bool) (env : Nat → Bool) :
    ∀ n, insE (k + 1) b (consE c env) n = consE c (insE k b env) n
  | 0 => by
    simp only [insE]
    rw [if_pos (Nat.zero_lt_succ k : 0 < k + 1)]
    rfl
  | m + 1 => by
    show (if m + 1 < k + 1 then consE c env (m + 1)
        else if m + 1 = k + 1 then b else consE c env (m + 1 - 1)) =
      (if m < k then env m else if m = k then b else env (m - 1))
    by_cases h₁ : m < k
    · rw [if_pos (Nat.succ_lt_succ h₁), if_pos h₁]
      rfl
    · rw [if_neg (fun h => h₁ (Nat.lt_of_succ_lt_succ h)), if_neg h₁]
      by_cases h₂ : m = k
      · rw [if_pos (congrArg (· + 1) h₂), if_pos h₂]
      · rw [if_neg (fun h => h₂ (Nat.succ.inj h)), if_neg h₂]
        cases m with
        | zero => exact absurd (Nat.pos_of_ne_zero (Ne.symm h₂)) h₁
        | succ j => rfl

/-! ### Evaluation lemmas -/

/-- Evaluation depends on the environment only through the indices below the
closure bound. -/
theorem beval_lcAt (S : BSem) (ρ : String → Bool) :
    ∀ (φ : Fm) (k : Nat) (env env' : Nat → Bool), lcAt k φ →
      (∀ n, n < k → env n = env' n) → beval S ρ φ env = beval S ρ φ env'
  | .fvar _, _, _, _, _, _ => rfl
  | .bvar n, _, _, _, hl, h => h n hl
  | .bot, _, _, _, _, _ => rfl
  | .and φ ψ, k, env, env', hl, h => by
    simp only [beval]
    rw [beval_lcAt S ρ φ k env env' hl.1 h, beval_lcAt S ρ ψ k env env' hl.2 h]
  | .or φ ψ, k, env, env', hl, h => by
    simp only [beval]
    rw [beval_lcAt S ρ φ k env env' hl.1 h, beval_lcAt S ρ ψ k env env' hl.2 h]
  | .imp φ ψ, k, env, env', hl, h => by
    simp only [beval]
    rw [beval_lcAt S ρ φ k env env' hl.1 h, beval_lcAt S ρ ψ k env env' hl.2 h]
  | .circ φ, k, env, env', hl, h => by
    simp only [beval]
    rw [beval_lcAt S ρ φ k env env' hl h]
  | .all ψ, k, env, env', hl, h => by
    simp only [beval]
    rw [beval_lcAt S ρ ψ (k + 1) _ _ hl (consE_lt true h),
      beval_lcAt S ρ ψ (k + 1) _ _ hl (consE_lt false h)]
  | .allJ ψ, k, env, env', hl, h => by
    simp only [beval]
    rw [beval_lcAt S ρ ψ (k + 1) _ _ hl (consE_lt true h),
      beval_lcAt S ρ ψ (k + 1) _ _ hl (consE_lt false h)]

/-- A locally closed formula ignores the environment. -/
theorem beval_lc (S : BSem) (ρ : String → Bool) {u : Fm} (hu : LC u) (env env' : Nat → Bool) :
    beval S ρ u env = beval S ρ u env' :=
  beval_lcAt S ρ u 0 env env' hu fun n hn => absurd hn (Nat.not_lt_zero n)

theorem beval_congr (S : BSem) (ρ : String → Bool) :
    ∀ (φ : Fm) (env env' : Nat → Bool), (∀ n, env n = env' n) →
      beval S ρ φ env = beval S ρ φ env'
  | .fvar _, _, _, _ => rfl
  | .bvar n, _, _, h => h n
  | .bot, _, _, _ => rfl
  | .and φ ψ, env, env', h => by
    simp only [beval]
    rw [beval_congr S ρ φ env env' h, beval_congr S ρ ψ env env' h]
  | .or φ ψ, env, env', h => by
    simp only [beval]
    rw [beval_congr S ρ φ env env' h, beval_congr S ρ ψ env env' h]
  | .imp φ ψ, env, env', h => by
    simp only [beval]
    rw [beval_congr S ρ φ env env' h, beval_congr S ρ ψ env env' h]
  | .circ φ, env, env', h => by
    simp only [beval]
    rw [beval_congr S ρ φ env env' h]
  | .all ψ, env, env', h => by
    simp only [beval]
    rw [beval_congr S ρ ψ _ _ (consE_congr true h), beval_congr S ρ ψ _ _ (consE_congr false h)]
  | .allJ ψ, env, env', h => by
    simp only [beval]
    rw [beval_congr S ρ ψ _ _ (consE_congr true h), beval_congr S ρ ψ _ _ (consE_congr false h)]

/-- Opening is insertion into the environment (the substitution lemma). -/
theorem beval_openRec (S : BSem) (ρ : String → Bool) {u : Fm} (hu : LC u) :
    ∀ (φ : Fm) (k : Nat) (env : Nat → Bool), lcAt (k + 1) φ →
      beval S ρ (openRec k u φ) env = beval S ρ φ (insE k (beval S ρ u env) env)
  | .fvar _, _, _, _ => rfl
  | .bvar n, k, env, h => by
    show beval S ρ (if n = k then u else .bvar n) env =
      (if n < k then env n else if n = k then beval S ρ u env else env (n - 1))
    by_cases hn : n = k
    · subst hn
      rw [if_pos rfl, if_neg (Nat.lt_irrefl n), if_pos rfl]
    · rw [if_neg hn, if_neg hn, if_pos (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hn)]
      rfl
  | .bot, _, _, _ => rfl
  | .and φ ψ, k, env, h => by
    simp only [openRec, beval]
    rw [beval_openRec S ρ hu φ k env h.1, beval_openRec S ρ hu ψ k env h.2]
  | .or φ ψ, k, env, h => by
    simp only [openRec, beval]
    rw [beval_openRec S ρ hu φ k env h.1, beval_openRec S ρ hu ψ k env h.2]
  | .imp φ ψ, k, env, h => by
    simp only [openRec, beval]
    rw [beval_openRec S ρ hu φ k env h.1, beval_openRec S ρ hu ψ k env h.2]
  | .circ φ, k, env, h => by
    simp only [openRec, beval]
    rw [beval_openRec S ρ hu φ k env h]
  | .all ψ, k, env, h => by
    simp only [openRec, beval]
    rw [beval_openRec S ρ hu ψ (k + 1) (consE true env) h,
      beval_openRec S ρ hu ψ (k + 1) (consE false env) h,
      beval_lc S ρ hu (consE true env) env, beval_lc S ρ hu (consE false env) env,
      beval_congr S ρ ψ _ _ (insE_succ k (beval S ρ u env) true env),
      beval_congr S ρ ψ _ _ (insE_succ k (beval S ρ u env) false env)]
  | .allJ ψ, k, env, h => by
    simp only [openRec, beval]
    rw [beval_openRec S ρ hu ψ (k + 1) (consE true env) h,
      beval_openRec S ρ hu ψ (k + 1) (consE false env) h,
      beval_lc S ρ hu (consE true env) env, beval_lc S ρ hu (consE false env) env,
      beval_congr S ρ ψ _ _ (insE_succ k (beval S ρ u env) true env),
      beval_congr S ρ ψ _ _ (insE_succ k (beval S ρ u env) false env)]

/-- Opening the outermost binder is extension of the environment. -/
theorem beval_opn (S : BSem) (ρ : String → Bool) {u : Fm} (hu : LC u) (ψ : Fm) (env : Nat → Bool)
    (h : lcAt 1 ψ) : beval S ρ (ψ.opn u) env = beval S ρ ψ (consE (beval S ρ u env) env) :=
  (beval_openRec S ρ hu ψ 0 env h).trans (beval_congr S ρ ψ _ _ (insE_zero _ env))

/-- Updating the valuation at a name not free in the formula changes nothing. -/
theorem beval_upd (S : BSem) {ρ : String → Bool} {s : String} {b : Bool} :
    ∀ (φ : Fm) (env : Nat → Bool), s ∉ fv φ → beval S (upd ρ s b) φ env = beval S ρ φ env
  | .fvar t, _, h => by
    simp only [beval, upd]
    rw [if_neg (fun e => h (by rw [e]; exact List.mem_cons_self ..))]
  | .bvar _, _, _ => rfl
  | .bot, _, _ => rfl
  | .and φ ψ, env, h => by
    simp only [beval]
    rw [beval_upd S φ env (not_mem_append_left h), beval_upd S ψ env (not_mem_append_right h)]
  | .or φ ψ, env, h => by
    simp only [beval]
    rw [beval_upd S φ env (not_mem_append_left h), beval_upd S ψ env (not_mem_append_right h)]
  | .imp φ ψ, env, h => by
    simp only [beval]
    rw [beval_upd S φ env (not_mem_append_left h), beval_upd S ψ env (not_mem_append_right h)]
  | .circ φ, env, h => by
    simp only [beval]
    rw [beval_upd S φ env h]
  | .all ψ, env, h => by
    simp only [beval]
    rw [beval_upd S ψ _ h, beval_upd S ψ _ h]
  | .allJ ψ, env, h => by
    simp only [beval]
    rw [beval_upd S ψ _ h, beval_upd S ψ _ h]

/-! ### Boolean facts, by cases -/

theorem bimp_intro {a b : Bool} (h : a = true → b = true) : (!a || b) = true := by
  cases a
  · rfl
  · exact h rfl

theorem bimp_elim {a b : Bool} (h₁ : (!a || b) = true) (h₂ : a = true) : b = true := by
  cases a
  · exact absurd h₂ Bool.false_ne_true
  · exact h₁

theorem band_intro {a b : Bool} (h₁ : a = true) (h₂ : b = true) : (a && b) = true := by
  subst h₁; subst h₂; rfl

theorem band_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a
  · exact h
  · rfl

theorem band_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact h

theorem bor_inl {a b : Bool} (h : a = true) : (a || b) = true := by
  subst h; rfl

theorem bor_inr {a b : Bool} (h : b = true) : (a || b) = true := by
  cases a
  · exact h
  · rfl

theorem bor_elim {a b c : Bool} (h : (a || b) = true) (h₁ : a = true → c = true)
    (h₂ : b = true → c = true) : c = true := by
  cases a
  · exact h₂ h
  · exact h₁ rfl

/-! ## Soundness -/

/-- Hypotheses extend under `::`. -/
theorem consH {S : BSem} {ρ : String → Bool} {env : Nat → Bool} {φ : Fm} {Γ : List Fm}
    (h : beval S ρ φ env = true) (H : ∀ γ, γ ∈ Γ → beval S ρ γ env = true) :
    ∀ γ, γ ∈ φ :: Γ → beval S ρ γ env = true := by
  intro γ hγ
  cases hγ
  · exact h
  · exact H _ (by assumption)

/-- The semantic content of the cofinite `∀I`: a fresh name takes either
value without disturbing the hypotheses or the body. -/
theorem allIntro_sem (S : BSem) {Γ : List Fm} {ψ : Fm} {L : List String} (hψ : lcAt 1 ψ)
    (ih : ∀ s, s ∉ L → ∀ (ρ : String → Bool) (env : Nat → Bool),
      (∀ γ, γ ∈ Γ → beval S ρ γ env = true) → beval S ρ (ψ.opn (.fvar s)) env = true)
    (ρ : String → Bool) (env : Nat → Bool) (H : ∀ γ, γ ∈ Γ → beval S ρ γ env = true)
    (b : Bool) : beval S ρ ψ (consE b env) = true := by
  obtain ⟨s, hs⟩ : ∃ s, s ∉ L ++ fvL Γ ++ fv ψ := ⟨_, fresh_not_mem _⟩
  have hsL : s ∉ L := not_mem_append_left (not_mem_append_left hs)
  have hsΓ : s ∉ fvL Γ := not_mem_append_right (not_mem_append_left hs)
  have hsψ : s ∉ fv ψ := not_mem_append_right hs
  have H' : ∀ γ, γ ∈ Γ → beval S (upd ρ s b) γ env = true := by
    intro γ hγ
    rw [beval_upd S γ env (fun h => hsΓ (fvL_sub hγ _ h))]
    exact H γ hγ
  have h := ih s hsL (upd ρ s b) env H'
  rw [beval_opn S (upd ρ s b) (u := .fvar s) trivial ψ env hψ] at h
  have e : beval S (upd ρ s b) (.fvar s) env = b := by
    show (if s = s then b else ρ s) = b
    exact if_pos rfl
  rw [e, beval_upd S ψ _ hsψ] at h
  exact h

/-- **Soundness of P2LL** for every `S` with `circ` the identity. -/
theorem LaxND2.bsound (S : BSem) (hc : ∀ b, S.circ b = b) :
    ∀ {Γ : List Fm} {φ : Fm}, LaxND2 Γ φ → ∀ (ρ : String → Bool) (env : Nat → Bool),
      (∀ γ, γ ∈ Γ → beval S ρ γ env = true) → beval S ρ φ env = true
  | _, _, .iden _ h, _, _, H => H _ h
  | _, _, .falsoElim _ _ p, ρ, env, H =>
    absurd (LaxND2.bsound S hc p ρ env H) Bool.false_ne_true
  | _, _, .impIntro _ p, ρ, env, H =>
    bimp_intro fun hφ => LaxND2.bsound S hc p ρ env (consH hφ H)
  | _, _, .impElim p₁ p₂, ρ, env, H =>
    bimp_elim (LaxND2.bsound S hc p₁ ρ env H) (LaxND2.bsound S hc p₂ ρ env H)
  | _, _, .andIntro p₁ p₂, ρ, env, H =>
    band_intro (LaxND2.bsound S hc p₁ ρ env H) (LaxND2.bsound S hc p₂ ρ env H)
  | _, _, .andElim1 p, ρ, env, H => band_left (LaxND2.bsound S hc p ρ env H)
  | _, _, .andElim2 p, ρ, env, H => band_right (LaxND2.bsound S hc p ρ env H)
  | _, _, .orIntro1 _ p, ρ, env, H => bor_inl (LaxND2.bsound S hc p ρ env H)
  | _, _, .orIntro2 _ p, ρ, env, H => bor_inr (LaxND2.bsound S hc p ρ env H)
  | _, _, .orElim p₀ p₁ p₂, ρ, env, H =>
    bor_elim (LaxND2.bsound S hc p₀ ρ env H)
      (fun h => LaxND2.bsound S hc p₁ ρ env (consH h H))
      (fun h => LaxND2.bsound S hc p₂ ρ env (consH h H))
  | _, _, .laxIntro p, ρ, env, H => by
    simp only [beval]
    rw [hc]
    exact LaxND2.bsound S hc p ρ env H
  | _, _, .laxElim p₁ p₂, ρ, env, H => by
    have h₁ := LaxND2.bsound S hc p₁ ρ env H
    simp only [beval] at h₁
    rw [hc] at h₁
    have h₂ := LaxND2.bsound S hc p₂ ρ env (consH h₁ H)
    simp only [beval] at h₂ ⊢
    rw [hc] at h₂ ⊢
    exact h₂
  | _, _, @LaxND2.allIntro _ ψ L hψ p, ρ, env, H =>
    band_intro
      (allIntro_sem S hψ (fun s hs ρ env H => LaxND2.bsound S hc (p s hs) ρ env H) ρ env H true)
      (allIntro_sem S hψ (fun s hs ρ env H => LaxND2.bsound S hc (p s hs) ρ env H) ρ env H false)
  | _, _, @LaxND2.allElim _ ψ χ _ hχ p e, ρ, env, H => by
    subst e
    have h := LaxND2.bsound S hc p ρ env H
    simp only [beval] at h
    rw [beval_opn S ρ hχ ψ env p.lc]
    cases hb : beval S ρ χ env
    · exact band_right h
    · exact band_left h

variable {J : List String → Fm → Type}

/-- **Soundness of the guarded calculus** for every `S` with `allJ` the meet
(full comprehension on this model), whatever the class `J` of instances. -/
theorem JND.bsound (S : BSem) (ha : ∀ a b, S.allJ a b = (a && b)) :
    ∀ {Θ : List String} {Γ : List Fm} {φ : Fm}, JND J Θ Γ φ →
      ∀ (ρ : String → Bool) (env : Nat → Bool),
        (∀ γ, γ ∈ Γ → beval S ρ γ env = true) → beval S ρ φ env = true
  | _, _, _, .iden _ h, _, _, H => H _ h
  | _, _, _, .falsoElim _ _ p, ρ, env, H =>
    absurd (JND.bsound S ha p ρ env H) Bool.false_ne_true
  | _, _, _, .impIntro _ p, ρ, env, H =>
    bimp_intro fun hφ => JND.bsound S ha p ρ env (consH hφ H)
  | _, _, _, .impElim p₁ p₂, ρ, env, H =>
    bimp_elim (JND.bsound S ha p₁ ρ env H) (JND.bsound S ha p₂ ρ env H)
  | _, _, _, .andIntro p₁ p₂, ρ, env, H =>
    band_intro (JND.bsound S ha p₁ ρ env H) (JND.bsound S ha p₂ ρ env H)
  | _, _, _, .andElim1 p, ρ, env, H => band_left (JND.bsound S ha p ρ env H)
  | _, _, _, .andElim2 p, ρ, env, H => band_right (JND.bsound S ha p ρ env H)
  | _, _, _, .orIntro1 _ p, ρ, env, H => bor_inl (JND.bsound S ha p ρ env H)
  | _, _, _, .orIntro2 _ p, ρ, env, H => bor_inr (JND.bsound S ha p ρ env H)
  | _, _, _, .orElim p₀ p₁ p₂, ρ, env, H =>
    bor_elim (JND.bsound S ha p₀ ρ env H)
      (fun h => JND.bsound S ha p₁ ρ env (consH h H))
      (fun h => JND.bsound S ha p₂ ρ env (consH h H))
  | _, _, _, @JND.allIntro _ _ _ ψ L hψ p, ρ, env, H =>
    band_intro
      (allIntro_sem S hψ (fun s hs ρ env H => JND.bsound S ha (p s hs) ρ env H) ρ env H true)
      (allIntro_sem S hψ (fun s hs ρ env H => JND.bsound S ha (p s hs) ρ env H) ρ env H false)
  | _, _, _, @JND.allElim _ _ _ ψ χ _ hχ p e, ρ, env, H => by
    subst e
    have h := JND.bsound S ha p ρ env H
    simp only [beval] at h
    rw [beval_opn S ρ hχ ψ env p.lc]
    cases hb : beval S ρ χ env
    · exact band_right h
    · exact band_left h
  | _, _, _, @JND.allJIntro _ _ _ ψ L hψ p, ρ, env, H => by
    simp only [beval]
    rw [ha]
    exact band_intro
      (allIntro_sem S hψ (fun s hs ρ env H => JND.bsound S ha (p s hs) ρ env H) ρ env H true)
      (allIntro_sem S hψ (fun s hs ρ env H => JND.bsound S ha (p s hs) ρ env H) ρ env H false)
  | _, _, _, @JND.allJElim _ _ _ ψ χ _ hχ _ p e, ρ, env, H => by
    subst e
    have h := JND.bsound S ha p ρ env H
    simp only [beval] at h
    rw [ha] at h
    rw [beval_opn S ρ hχ ψ env p.lc]
    cases hb : beval S ρ χ env
    · exact band_right h
    · exact band_left h

/-! ## The wording of 2026-10-24, REFUTED

The four statements as first reported, quantifying over the whole shared
formula type; replaced in `wip/p2llStatements.lean` on 2026-10-25 by the
fragment-restricted wording.  Kept as the record. -/

/-- RTP, wording of 2026-10-24, REFUTED (`roundTripP2LL_false`): no `allJFree φ`. -/
def RoundTripP2LLUnrestricted : Prop :=
  ∀ φ : Fm, LC φ →
    Nonempty (LaxND2 [φ] (rel (toJ φ))) ∧ Nonempty (LaxND2 [rel (toJ φ)] φ)

/-- RTJ, wording of 2026-10-24, REFUTED (`roundTripJ_false`): no `circFree φ`. -/
def RoundTripJUnrestricted : Prop :=
  ∀ (Θ : List String) (φ : Fm), LC φ →
    Nonempty (JND IsJ Θ [φ] (toJ (rel φ))) ∧ Nonempty (JND IsJ Θ [toJ (rel φ)] φ)

/-- MP, wording of 2026-10-24, REFUTED (`mutualP2LL_false`): no `allJFree` on `Γ`, `φ`. -/
def MutualP2LLUnrestricted : Prop :=
  ∀ (Γ : List Fm) (φ : Fm), (∀ ψ ∈ Γ, LC ψ) → LC φ →
    (Nonempty (LaxND2 Γ φ) ↔ Nonempty (JND IsJ [] (Γ.map toJ) (toJ φ)))

/-- MJ, wording of 2026-10-24, REFUTED (`mutualJ_false`): no `circFree` on `Γ`, `φ`. -/
def MutualJUnrestricted : Prop :=
  ∀ (Θ : List String) (Γ : List Fm) (φ : Fm), (∀ ψ ∈ Γ, LC ψ) → LC φ →
    (Nonempty (JND IsJ Θ Γ φ) ↔ Nonempty (LaxND2 (guards Θ ++ Γ.map rel) (rel φ)))

/-! ## The models and the cells -/

/-- The P2LL models: `circ` the identity, `allJ` the constant `c`. -/
def SP (c : Bool) : BSem := ⟨fun b => b, fun _ _ => c⟩

/-- The guarded-calculus models: `allJ` the meet, `circ` the constant `c`. -/
def SJ (c : Bool) : BSem := ⟨fun _ => c, fun a b => a && b⟩

theorem emptyH {S : BSem} {ρ : String → Bool} {env : Nat → Bool} :
    ∀ γ, γ ∈ ([] : List Fm) → beval S ρ γ env = true := fun _ h => nomatch h

theorem singleH {S : BSem} {ρ : String → Bool} {env : Nat → Bool} {γ₀ : Fm}
    (h : beval S ρ γ₀ env = true) : ∀ γ, γ ∈ [γ₀] → beval S ρ γ env = true :=
  consH h emptyH

/-- RTP, first direction, fails at `∀°q.q`:  `∀°q.q ⊬_P2LL ∀p.((◯p → p) → p)`. -/
theorem rtp_fails₁ : ¬ Nonempty (LaxND2 [Fm.allJ (.bvar 0)] (rel (toJ (Fm.allJ (.bvar 0))))) := by
  intro ⟨d⟩
  have h := LaxND2.bsound (SP true) (fun _ => rfl) d (fun _ => true) (fun _ => true)
    (singleH (by decide))
  exact absurd h (by decide)

/-- RTP, second direction, fails at `∀°q.(q → q)`:
`∀p.((◯p → p) → (p → p)) ⊬_P2LL ∀°q.(q → q)`. -/
theorem rtp_fails₂ :
    ¬ Nonempty (LaxND2 [rel (toJ (Fm.allJ (.imp (.bvar 0) (.bvar 0))))]
      (Fm.allJ (.imp (.bvar 0) (.bvar 0)))) := by
  intro ⟨d⟩
  have h := LaxND2.bsound (SP false) (fun _ => rfl) d (fun _ => true) (fun _ => true)
    (singleH (by decide))
  exact absurd h (by decide)

/-- **RTP, wording of 2026-10-24, is REFUTED** (it fails outside the P2LL fragment). -/
theorem roundTripP2LL_false : ¬ RoundTripP2LLUnrestricted := fun h =>
  rtp_fails₁ (h (Fm.allJ (.bvar 0)) (by decide)).1

/-- `⊢_J ∀°q.(q → q)`, under any declarations and hypotheses. -/
def jd_allJ_refl (Θ : List String) (Γ : List Fm) :
    JND IsJ Θ Γ (Fm.allJ (.imp (.bvar 0) (.bvar 0))) :=
  .allJIntro [] (by decide) fun s _ =>
    show JND IsJ (s :: Θ) Γ (.imp (.fvar s) (.fvar s)) from
    .impIntro trivial (.iden trivial (List.mem_cons_self ..))

/-- `⊬_P2LL ∀°q.(q → q)`. -/
theorem mp_fails : ¬ Nonempty (LaxND2 [] (Fm.allJ (.imp (.bvar 0) (.bvar 0)))) := by
  intro ⟨d⟩
  have h := LaxND2.bsound (SP false) (fun _ => rfl) d (fun _ => true) (fun _ => true) emptyH
  exact absurd h (by decide)

/-- **MP, wording of 2026-10-24, is REFUTED** (at `Γ = []`, `φ = ∀°q.(q → q)`). -/
theorem mutualP2LL_false : ¬ MutualP2LLUnrestricted := fun h =>
  mp_fails ((h [] (Fm.allJ (.imp (.bvar 0) (.bvar 0))) (fun _ h => nomatch h) (by decide)).mpr
    ⟨jd_allJ_refl [] []⟩)

/-- RTJ, first direction, fails at `◯⊥`:  `◯⊥ ⊬_J ∀°q.((⊥ → q) → q)`. -/
theorem rtj_fails₁ : ¬ Nonempty (JND IsJ [] [Fm.circ .bot] (toJ (rel (Fm.circ .bot)))) := by
  intro ⟨d⟩
  have h := JND.bsound (SJ true) (fun _ _ => rfl) d (fun _ => true) (fun _ => true)
    (singleH (by decide))
  exact absurd h (by decide)

/-- RTJ, second direction, fails at `◯⊤`:  `∀°q.((⊤ → q) → q) ⊬_J ◯⊤`. -/
theorem rtj_fails₂ : ¬ Nonempty (JND IsJ [] [toJ (rel (Fm.circ Fm.top))] (Fm.circ Fm.top)) := by
  intro ⟨d⟩
  have h := JND.bsound (SJ false) (fun _ _ => rfl) d (fun _ => true) (fun _ => true)
    (singleH (by decide))
  exact absurd h (by decide)

/-- **RTJ, wording of 2026-10-24, is REFUTED** (it fails outside the guarded fragment). -/
theorem roundTripJ_false : ¬ RoundTripJUnrestricted := fun h =>
  rtj_fails₁ (h [] (Fm.circ .bot) trivial).1

/-- `⊢_P2LL ◯⊤`. -/
def pd_circ_top : LaxND2 [] (Fm.circ Fm.top) :=
  .laxIntro (.impIntro trivial (.iden trivial (List.mem_cons_self ..)))

/-- `⊬_J ◯⊤`. -/
theorem mj_fails : ¬ Nonempty (JND IsJ [] [] (Fm.circ Fm.top)) := by
  intro ⟨d⟩
  have h := JND.bsound (SJ false) (fun _ _ => rfl) d (fun _ => true) (fun _ => true) emptyH
  exact absurd h (by decide)

/-- **MJ, wording of 2026-10-24, is REFUTED** (at `Θ = []`, `Γ = []`, `φ = ◯⊤`). -/
theorem mutualJ_false : ¬ MutualJUnrestricted := fun h =>
  mj_fails ((h [] [] (Fm.circ Fm.top) (fun _ h => nomatch h) ⟨trivial, trivial⟩).mpr ⟨pd_circ_top⟩)

end P2LL

/-! ## Pins (upper bounds).  First run at `[]` (2026-10-24): the environment
and evaluation lemmas and the two derivations held; `len_le_sumLen` and
`fresh_not_mem` failed with `propext, Classical.choice, Quot.sound`, carried
by core's `String.toList`/`String.ofList` (which `sumLen` and `fresh` mention)
and `String.toList_ofList`; everything through `fresh` inherits that profile.
See `wip/p2ll-STATUS.md` §8. -/

#axioms_within P2LL.fvL_sub []
#axioms_within P2LL.len_le_sumLen [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.fresh_not_mem [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.insE_zero []
#axioms_within P2LL.insE_succ []
#axioms_within P2LL.beval_lcAt []
#axioms_within P2LL.beval_congr []
#axioms_within P2LL.beval_openRec []
#axioms_within P2LL.beval_opn []
#axioms_within P2LL.beval_upd []
#axioms_within P2LL.allIntro_sem [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.LaxND2.bsound [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.JND.bsound [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.RoundTripP2LLUnrestricted []
#axioms_within P2LL.RoundTripJUnrestricted []
#axioms_within P2LL.MutualP2LLUnrestricted []
#axioms_within P2LL.MutualJUnrestricted []
#axioms_within P2LL.jd_allJ_refl []
#axioms_within P2LL.pd_circ_top []
#axioms_within P2LL.rtp_fails₁ [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.rtp_fails₂ [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.roundTripP2LL_false [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.mp_fails [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.mutualP2LL_false [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.rtj_fails₁ [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.rtj_fails₂ [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.roundTripJ_false [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.mj_fails [propext, Classical.choice, Quot.sound]
#axioms_within P2LL.mutualJ_false [propext, Classical.choice, Quot.sound]
