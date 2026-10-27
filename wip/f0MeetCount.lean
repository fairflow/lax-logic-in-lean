import wip.f0FreeHAn
import Meta.Audit

/-!
# The meet-only counting criterion

Matthew's statement (2026-10-27), on top of `wip/f0FreeHAn.lean`.  Let `Hₙ` be
the free Heyting algebra on `p0 … p(n-1)`, and let `f` act on the ◯-free
formulas in those variables with variable-free values such that

    (faithful)  A ⊣⊢ B  ⟺  f A ⊣⊢ f B
    (meet)      f (A ∧ B) ⊣⊢ f A ∧ f B.

Nothing is assumed about `∨`, `↠` or `⊥`.  With `a := f ⊥`,

    TypeBound a K  ⟹  2ⁿ ≤ K.

Proof: the `2ⁿ` signed conjunctions `d_ε = ⋀ᵢ pᵢ^εᵢ` (`¬p = p ↠ ⊥`) are pairwise
`⊥`-disjoint and none is `⊣⊢ ⊥`; `f` is monotone by (meet) + (faithful), so
`f d_ε ≥ a`, `f d_ε ∧ f d_ε' ⊣⊢ a` for `ε ≠ ε'`, and `f d_ε ≢ a`; hence
`⊬ f d_ε ↠ a`, completeness (`SubTab.complete`, choice-free) gives a finite model
with a world forcing `f d_ε` and refuting `a`, above it an `a`-maximal world
(descent, as `exists_rmax`); no `a`-maximal world forces two of the `f d_ε`
(it would force `a`), so the `2ⁿ` worlds are pairwise separated, and a
relational pigeonhole against `TypeBound` gives `2ⁿ ≤ K`.

## Statements (committed before any proof, METHOD.md §1)

* `MeetEmb n f`: `f` has variable-free values on the ◯-free formulas in
  `p0 … p(n-1)`, is faithful and preserves `∧` (both as `Interd`).
* `MeetCounting := ∀ n K f, MeetEmb n f → TypeBound (f ⊥) K → 2 ^ n ≤ K`.
* `NoMeetCopyH2 b := ¬ ∃ f, MeetEmb 2 f ∧ f ⊥ ⊣⊢ b` (for `b = ⊥`, `t3`).
* `NoFreeHA2AnyNeg`: for variable-free `x₀ x₁` and ANY `y₀ y₁` with
  `[x₀ ∧ y₀] ⊢ t3`, `[x₁ ∧ y₁] ⊢ t3`, some sign pattern `ε` has
  `⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3` where `x^false` is read as `y`.
* `MeetEmbH1 := MeetEmb 1 h₁`, the non-vacuity check (`freeIPL1`'s embedding).
* `typeBound_bot : TypeBound ⊥ 2`, `typeBound_t3 : TypeBound t3 3` restated from
  `f0FreeIPL`; `countingCriterion : CountingCriterion` as a corollary.

## Results

All PROVED, `[propext, Quot.sound]`: `meet_counting` (`meetCounting :
MeetCounting`), `typeBound_bot`, `typeBound_t3`, `typeBound_interd` (the bound
transfers along `⊣⊢` of the base), `noMeetCopyH2_bot`, `noMeetCopyH2_t3`,
`countingCriterion`, `noFreeHA2_anyNeg`, `meetEmb_h1` (`meetEmbH1`).  The
pigeonhole is relational (`rel_pigeon`: `N` indices each related to a value
below `K`, injectively, give `N ≤ K`), so no cell has to be CHOSEN: the cells
exist in `Prop` only; the sign patterns are indexed by the bits of `i < 2ⁿ`
(`Nat.testBit`, `Nat.eq_of_testBit_eq`, `Nat.testBit_lt_two_pow`, choice-free).
The one-world IPC models carry the valuation `valB`, a lookup over
`pvar 0 … pvar (n-1)`; its correctness needs `pvar` injective, which is read
off the UTF-8 byte size (`String.toByteArray_ofList`, `ByteArray.size_append`),
because `String.length_ofList` and `String.toList_ofList` are choice-tainted.
`omega` is kept off negated conjunctions and `iff` hypotheses, as in
`f0FreeHAn`.

Status note: `wip/f0MeetCount-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace MeetCount

open SemUI RNEmbed Sig FreeIPL FreeHAn
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF

/-! ## The signed conjunctions -/

/-- `ε` read on every index, `false` beyond `n`. -/
def padB (n : Nat) (ε : Fin n → Bool) (l : Nat) : Bool :=
  if h : l < n then ε ⟨l, h⟩ else false

/-- `⋀_{l < k} g l`, with `⊤ = ⊥ ↠ ⊥` as the empty conjunction. -/
def conjUpTo (g : Nat → PLLFormula) : Nat → PLLFormula
  | 0 => FreeIPL.topF
  | k + 1 => (conjUpTo g k).and (g k)

/-- **The signed conjunction** `d_ε = ⋀_{i < n} pᵢ^εᵢ`, `p^true = p`, `p^false = p ↠ ⊥`. -/
def signedConj (n : Nat) (ε : Fin n → Bool) : PLLFormula :=
  conjUpTo (fun l => sgnP (padB n ε l) (.prop (pvar l))) n

/-! ## The statements -/

/-- **A meet-embedding of `Hₙ`**: `f` acts on the ◯-free formulas in
`p0 … p(n-1)` with variable-free values,

    (faithful)  A ⊣⊢ B  ⟺  f A ⊣⊢ f B,
    (meet)      f (A ∧ B) ⊣⊢ f A ∧ f B.

Nothing about `∨`, `↠` or `⊥`. -/
structure MeetEmb (n : Nat) (f : PLLFormula → PLLFormula) : Prop where
  vf : ∀ A, boxFree A = true → varsBelow n A = true → atomFree (f A) = true
  faithful : ∀ A B, boxFree A = true → boxFree B = true →
    varsBelow n A = true → varsBelow n B = true → (Interd A B ↔ Interd (f A) (f B))
  meet : ∀ A B, boxFree A = true → boxFree B = true →
    varsBelow n A = true → varsBelow n B = true → Interd (f (A.and B)) ((f A).and (f B))

/-- **The meet counting criterion**: `MeetEmb n f → TypeBound (f ⊥) K → 2ⁿ ≤ K`. -/
def MeetCounting : Prop :=
  ∀ (n K : Nat) (f : PLLFormula → PLLFormula), MeetEmb n f → TypeBound (f .falsePLL) K → 2 ^ n ≤ K

/-- **No ∧-copy of `H₂` with bottom `b`**: `¬ ∃ f, MeetEmb 2 f ∧ f ⊥ ⊣⊢ b`. -/
def NoMeetCopyH2 (b : PLLFormula) : Prop :=
  ¬ ∃ f : PLLFormula → PLLFormula, MeetEmb 2 f ∧ Interd (f .falsePLL) b

/-- `x` for the sign `true`, the given `y` for the sign `false`. -/
def sgnY : Bool → PLLFormula → PLLFormula → PLLFormula
  | true, x, _ => x
  | false, _, y => y

/-- **`noFreeHA2` with any negation**: for variable-free `x₀ x₁` and any `y₀ y₁`
with `[x₀ ∧ y₀] ⊢ t3` and `[x₁ ∧ y₁] ⊢ t3`,

    ∃ ε,  ⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3,     x^true = x,  x^false = y. -/
def NoFreeHA2AnyNeg : Prop :=
  ∀ x₀ x₁ y₀ y₁ : PLLFormula, atomFree x₀ = true → atomFree x₁ = true →
    Deriv [x₀.and y₀] t3 → Deriv [x₁.and y₁] t3 →
    ∃ ε : Bool × Bool, Deriv [] (Rneg ((sgnY ε.1 x₀ y₀).and (sgnY ε.2 x₁ y₁)))

/-- Non-vacuity: `h₁ A = σ(A[p := ◯⊥])` of `freeIPL1` is a meet-embedding of `H₁`. -/
def MeetEmbH1 : Prop := MeetEmb 1 h1

/-! ## Facts about the signed conjunctions -/

/-- Projection out of the conjunction. -/
theorem conjUpTo_proj (g : Nat → PLLFormula) : ∀ (k l : Nat), l < k → Deriv [conjUpTo g k] (g l)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, l, h => by
      show Deriv [(conjUpTo g k).and (g k)] (g l)
      rcases Nat.lt_or_ge l k with hlt | hge
      · exact Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) (conjUpTo_proj g k l hlt)
      · have hl : l = k := by omega
        subst hl
        exact Deriv.andElim2 (Deriv.iden (.head _))

/-! ### The variable names are distinct

`pvar l` is the string of `l + 1` copies of `p`. Its injectivity is read off the byte
size of the UTF-8 encoding: the core lemmas about `String.length` and `String.toList`
of `String.ofList` are choice-tainted (they go through UTF-8 decoding), the size
lemmas are not. -/

theorem utf8Encode_size_replicate_p : ∀ k, (List.replicate k 'p').utf8Encode.size = k
  | 0 => rfl
  | k + 1 => by
    have h1 : (['p'] : List Char).utf8Encode.size = 1 := by decide
    rw [List.replicate_succ, List.utf8Encode_cons, ByteArray.size_append, h1,
      utf8Encode_size_replicate_p k]
    exact Nat.add_comm 1 k

theorem pvar_size (l : Nat) : (pvar l).toByteArray.size = l + 1 := by
  unfold pvar
  rw [String.toByteArray_ofList, utf8Encode_size_replicate_p]

theorem pvar_injective {i j : Nat} (h : pvar i = pvar j) : i = j := by
  have e := congrArg (fun s : String => s.toByteArray.size) h
  simp only [pvar_size] at e
  exact Nat.add_right_cancel e

theorem pvar_ne {i j : Nat} (h : i ≠ j) : pvar i ≠ pvar j := fun e => h (pvar_injective e)

/-- `lookup ε a m = ε l` when `a = pvar l` for some `l < m`, else `false`. -/
def lookup (ε : Nat → Bool) (a : String) : Nat → Bool
  | 0 => false
  | m + 1 => lookup ε a m || (decide (a = pvar m) && ε m)

theorem lookup_pvar (ε : Nat → Bool) (l : Nat) :
    ∀ m, lookup ε (pvar l) m = (decide (l < m) && ε l)
  | 0 => by
    simp only [lookup]
    rw [decide_eq_false (Nat.not_lt_zero l)]
    rfl
  | m + 1 => by
    simp only [lookup]
    rw [lookup_pvar ε l m]
    rcases Nat.lt_trichotomy l m with hlt | heq | hgt
    · rw [decide_eq_true hlt, decide_eq_true (Nat.lt_succ_of_lt hlt),
        decide_eq_false (pvar_ne (Nat.ne_of_lt hlt)), Bool.false_and, Bool.or_false]
    · subst heq
      rw [decide_eq_false (Nat.lt_irrefl l), decide_eq_true (Nat.lt_succ_self l),
        decide_eq_true rfl]
      rfl
    · rw [decide_eq_false (Nat.not_lt.mpr (Nat.le_of_lt hgt)), decide_eq_false (Nat.not_lt.mpr hgt),
        decide_eq_false (pvar_ne (Nat.ne_of_gt hgt))]
      rfl

/-- The valuation of the sign pattern `ε` on the one-world model: `pvar l ↦ ε l`
for `l < n`, every other name `↦ false`. -/
def valB (n : Nat) (ε : Fin n → Bool) (a : String) : Bool := lookup (padB n ε) a n

theorem valB_pvar (n : Nat) (ε : Fin n → Bool) (l : Nat) : valB n ε (pvar l) = padB n ε l := by
  unfold valB
  rw [lookup_pvar]
  cases Nat.lt_or_ge l n with
  | inl h => rw [decide_eq_true h, Bool.true_and]
  | inr h =>
    rw [decide_eq_false (Nat.not_lt.mpr h), Bool.false_and]
    unfold padB
    rw [dif_neg (Nat.not_lt.mpr h)]

theorem pt_conjUpTo (v : String → Bool) (g : Nat → PLLFormula)
    (hg : ∀ l, (pt v).force () (g l)) : ∀ k, (pt v).force () (conjUpTo g k)
  | 0 => fun _ _ h => h
  | k + 1 => ⟨pt_conjUpTo v g hg k, hg k⟩

theorem pt_signedConj (n : Nat) (ε : Fin n → Bool) :
    (pt (valB n ε)).force () (signedConj n ε) :=
  pt_conjUpTo (valB n ε) _ (fun l => pt_sgnP (valB n ε) (pvar l) (padB n ε l) (valB_pvar n ε l)) n

/-- **No signed conjunction is `⊣⊢ ⊥`** (the one-world model with valuation `ε`). -/
theorem signedConj_not_bot (n : Nat) (ε : Fin n → Bool) : ¬ Deriv [signedConj n ε] .falsePLL :=
  fun ⟨d⟩ => SubframeModel.CF.soundness₁ d (pt (valB n ε)) () (pt_signedConj n ε)

/-- **Two signed conjunctions differing at a bit are disjoint.** -/
theorem signedConj_disj {n : Nat} {ε ε' : Fin n → Bool} {l : Nat} (hl : l < n)
    (hne : padB n ε l ≠ padB n ε' l) :
    Deriv [(signedConj n ε).and (signedConj n ε')] .falsePLL := by
  have h1 : Deriv [(signedConj n ε).and (signedConj n ε')] (sgnP (padB n ε l) (.prop (pvar l))) :=
    Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) (conjUpTo_proj _ n l hl)
  have h2 : Deriv [(signedConj n ε).and (signedConj n ε')] (sgnP (padB n ε' l) (.prop (pvar l))) :=
    Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) (conjUpTo_proj _ n l hl)
  revert hne h1 h2
  cases padB n ε l <;> cases padB n ε' l
  · intro hne; exact absurd rfl hne
  · intro _ h1 h2; exact Deriv.impElim h1 h2
  · intro _ h1 h2; exact Deriv.impElim h2 h1
  · intro hne; exact absurd rfl hne

theorem boxFree_conjUpTo (g : Nat → PLLFormula) (hg : ∀ l, boxFree (g l) = true) :
    ∀ k, boxFree (conjUpTo g k) = true
  | 0 => rfl
  | k + 1 => by
      show (boxFree (conjUpTo g k) && boxFree (g k)) = true
      rw [boxFree_conjUpTo g hg k, hg k]; rfl

theorem boxFree_signedConj (n : Nat) (ε : Fin n → Bool) : boxFree (signedConj n ε) = true :=
  boxFree_conjUpTo _ (fun _ => boxFree_sgnP _ rfl) n

theorem varsBelow_pvar {n l : Nat} (hl : l < n) : varsBelow n (.prop (pvar l)) = true := by
  show ((List.range n).any fun i => decide (pvar l = pvar i)) = true
  exact List.any_eq_true.mpr ⟨l, List.mem_range.mpr hl, decide_eq_true rfl⟩

theorem varsBelow_sgnP {n l : Nat} (hl : l < n) (b : Bool) :
    varsBelow n (sgnP b (.prop (pvar l))) = true := by
  cases b
  · show (varsBelow n (.prop (pvar l)) && varsBelow n .falsePLL) = true
    rw [varsBelow_pvar hl]; rfl
  · exact varsBelow_pvar hl

theorem varsBelow_conjUpTo {n : Nat} (g : Nat → PLLFormula)
    (hg : ∀ l, l < n → varsBelow n (g l) = true) :
    ∀ k, k ≤ n → varsBelow n (conjUpTo g k) = true
  | 0, _ => rfl
  | k + 1, hk => by
      show (varsBelow n (conjUpTo g k) && varsBelow n (g k)) = true
      rw [varsBelow_conjUpTo g hg k (by omega), hg k (by omega)]; rfl

theorem varsBelow_signedConj (n : Nat) (ε : Fin n → Bool) : varsBelow n (signedConj n ε) = true :=
  varsBelow_conjUpTo _ (fun _ hl => varsBelow_sgnP hl _) n (Nat.le_refl n)

/-! ## Monotonicity of a meet-embedding -/

/-- **(meet) + (faithful) give monotonicity**: `[A] ⊢ B → [f A] ⊢ f B`. -/
theorem MeetEmb.mono {n : Nat} {f : PLLFormula → PLLFormula} (hf : MeetEmb n f) {A B : PLLFormula}
    (hA : boxFree A = true) (hB : boxFree B = true)
    (vA : varsBelow n A = true) (vB : varsBelow n B = true)
    (h : Deriv [A] B) : Deriv [f A] (f B) := by
  have hAB : boxFree (A.and B) = true := by
    show (boxFree A && boxFree B) = true
    rw [hA, hB]; rfl
  have vAB : varsBelow n (A.and B) = true := by
    show (varsBelow n A && varsBelow n B) = true
    rw [vA, vB]; rfl
  have h1 : Interd A (A.and B) :=
    ⟨Deriv.andIntro (Deriv.iden (.head _)) h, Deriv.andElim1 (Deriv.iden (.head _))⟩
  have h2 : Interd (f A) ((f A).and (f B)) :=
    ((hf.faithful A (A.and B) hA hAB vA vAB).mp h1).trans (hf.meet A B hA hB vA vB)
  exact Deriv.andElim2 h2.1

/-! ## `b`-maximal worlds: transfer along `⊣⊢`, and existence by descent -/

theorem bmax_of_interd {b b' : PLLFormula} (hi : Interd b b') {M : SubframeModel} {w : M.W}
    (hw : BMax b M w) : BMax b' M w :=
  ⟨fun h => hw.1 (hi.2.elim fun d => SubframeModel.CF.soundness₁ d M w h),
   fun v hv hv' => hw.2 v hv (fun h => hv' (hi.1.elim fun d => SubframeModel.CF.soundness₁ d M v h))⟩

/-- **The type bound transfers along `⊣⊢` of the base.** -/
theorem typeBound_interd {b b' : PLLFormula} (hi : Interd b b') {K : Nat} (h : TypeBound b K) :
    TypeBound b' K := by
  obtain ⟨Ts, ty, hty⟩ := h
  exact ⟨Ts, ty, fun M inst w hw => @hty M inst w (bmax_of_interd hi.symm hw)⟩

theorem exists_bmax_aux (b : PLLFormula) (M : SubframeModel) [FinDec M] :
    ∀ (k : Nat) (w : M.W), Normal.nProper M w ≤ k → ¬ M.force w b →
      ∃ m, M.le w m ∧ BMax b M m := by
  intro k
  induction k with
  | zero =>
      intro w hk hw
      refine ⟨w, M.refl w, hw, fun v hv _ => ?_⟩
      exact Decidable.byContradiction fun hvw =>
        absurd (Nat.lt_of_lt_of_le (Normal.nProper_lt M hv hvw) hk) (Nat.not_lt_zero _)
  | succ k ih =>
      intro w hk hw
      rcases Decidable.em (∃ v ∈ FinDec.elems (M := M), M.le w v ∧ ¬ M.force v b ∧ ¬ M.le v w)
        with hex | hno
      · obtain ⟨v, _, hv, hvb, hvw⟩ := hex
        obtain ⟨m, hvm, hm⟩ :=
          ih v (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Normal.nProper_lt M hv hvw) hk)) hvb
        exact ⟨m, M.trans hv hvm, hm⟩
      · exact ⟨w, M.refl w, hw, fun v hv hvb => Decidable.byContradiction fun hvw =>
          hno ⟨v, FinDec.complete v, hv, hvb, hvw⟩⟩

/-- Above every world refuting `b` there is a `b`-maximal one. -/
theorem exists_bmax (b : PLLFormula) (M : SubframeModel) [FinDec M] {w : M.W}
    (hw : ¬ M.force w b) : ∃ m, M.le w m ∧ BMax b M m :=
  exists_bmax_aux b M _ w (Nat.le_refl _) hw

/-! ## The cells of a meet-embedding -/

/-- **For every sign pattern an `f ⊥`-maximal world forcing `f d_ε`**, by
completeness and descent. -/
theorem exists_cell {n : Nat} {f : PLLFormula → PLLFormula} (hf : MeetEmb n f) (ε : Fin n → Bool) :
    ∃ (M : SubframeModel) (_ : FinDec M) (w : M.W),
      BMax (f .falsePLL) M w ∧ M.force w (f (signedConj n ε)) := by
  have hbd : boxFree (signedConj n ε) = true := boxFree_signedConj n ε
  have hvd : varsBelow n (signedConj n ε) = true := varsBelow_signedConj n ε
  have hnd : ¬ Deriv [] ((f (signedConj n ε)).ifThen (f .falsePLL)) := by
    intro h
    have h1 : Deriv [f (signedConj n ε)] (f .falsePLL) :=
      Deriv.impElim (Deriv.rename (fun _ hx => absurd hx List.not_mem_nil) h) (Deriv.iden (.head _))
    have h2 : Deriv [f .falsePLL] (f (signedConj n ε)) :=
      hf.mono rfl hbd rfl hvd (Deriv.falsoElim _ (Deriv.iden (.head _)))
    have h3 : Interd (signedConj n ε) .falsePLL :=
      (hf.faithful (signedConj n ε) .falsePLL hbd rfl hvd rfl).mpr ⟨h1, h2⟩
    exact signedConj_not_bot n ε h3.1
  rcases SubTab.complete ((f (signedConj n ε)).ifThen (f .falsePLL)) with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact absurd (SubTab.holds_of_check hc) hnd
  · have hm0 : m.refutes ((f (signedConj n ε)).ifThen (f .falsePLL)) = true := hm
    simp only [SubTab.SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm0
    have hr := (SubTab.SubCM.ok_parts hm0.1).1
    have hnf : ¬ (m.toModel hm0.1).force ⟨m.root, hr⟩ ((f (signedConj n ε)).ifThen (f .falsePLL)) :=
      fun hfo => by
        have hb := (SubTab.SubCM.forceB_iff hm0.1 _ ⟨m.root, hr⟩).mpr hfo
        rw [hm0.2] at hb
        exact Bool.false_ne_true hb
    obtain ⟨v, _, hvψ, hvt⟩ := SubframeModel.CF.exists_of_not_force_imp hnf
    obtain ⟨w, hvw, hw⟩ := exists_bmax (f .falsePLL) (m.toModel hm0.1) hvt
    exact ⟨m.toModel hm0.1, inferInstance, w, hw, SubframeModel.force_mono _ _ hvw hvψ⟩

/-! ## The relational pigeonhole, choice-free -/

/-- `N` indices, each related to some value below `K`, no two to the same value:
`N ≤ K`.  Nothing is chosen. -/
theorem rel_pigeon : ∀ (N K : Nat) (R : Nat → Nat → Prop),
    (∀ i, i < N → ∃ k, k < K ∧ R i k) →
    (∀ i j k, i < N → j < N → R i k → R j k → i = j) → N ≤ K := by
  intro N
  induction N with
  | zero => intro K _ _ _; exact Nat.zero_le K
  | succ N ih =>
      intro K R hex hinj
      obtain ⟨k₀, hk₀, hR₀⟩ := hex N (Nat.lt_succ_self N)
      let R' : Nat → Nat → Prop := fun i k => (k < k₀ ∧ R i k) ∨ (k₀ ≤ k ∧ R i (k + 1))
      have hex' : ∀ i, i < N → ∃ k, k < K - 1 ∧ R' i k := by
        intro i hi
        obtain ⟨k, hk, hR⟩ := hex i (by omega)
        have hne : k ≠ k₀ := fun h => by
          subst h
          exact absurd (hinj i N k (by omega) (Nat.lt_succ_self N) hR hR₀) (by omega)
        rcases Nat.lt_or_ge k k₀ with hlt | hge
        · exact ⟨k, by omega, Or.inl ⟨hlt, hR⟩⟩
        · refine ⟨k - 1, by omega, Or.inr ⟨by omega, ?_⟩⟩
          have e : k - 1 + 1 = k := by omega
          rw [e]
          exact hR
      have hinj' : ∀ i j k, i < N → j < N → R' i k → R' j k → i = j := by
        intro i j k hi hj h1 h2
        rcases h1 with ⟨hk1, hR1⟩ | ⟨hk1, hR1⟩ <;> rcases h2 with ⟨hk2, hR2⟩ | ⟨hk2, hR2⟩
        · exact hinj i j k (by omega) (by omega) hR1 hR2
        · exact absurd hk2 (by omega)
        · exact absurd hk1 (by omega)
        · exact hinj i j (k + 1) (by omega) (by omega) hR1 hR2
      have := ih (K - 1) R' hex' hinj'
      omega

/-! ## The criterion -/

/-- **The meet counting criterion**: `MeetEmb n f → TypeBound (f ⊥) K → 2ⁿ ≤ K`. -/
theorem meet_counting {n K : Nat} {f : PLLFormula → PLLFormula} (hf : MeetEmb n f)
    (hK : TypeBound (f .falsePLL) K) : 2 ^ n ≤ K := by
  obtain ⟨Ts, ty, hty⟩ := hK
  refine rel_pigeon (2 ^ n) K
    (fun i k => ∃ (M : SubframeModel) (inst : FinDec M) (w : M.W),
      BMax (f .falsePLL) M w ∧ M.force w (f (signedConj n (fun j => i.testBit j.1))) ∧
      (@ty M inst w).1 = k) ?_ ?_
  · intro i _
    obtain ⟨M, inst, w, hmax, hforce⟩ := exists_cell hf (fun j => i.testBit j.1)
    exact ⟨(@ty M inst w).1, (@ty M inst w).2, M, inst, w, hmax, hforce, rfl⟩
  · intro i j k hi hj h1 h2
    obtain ⟨M, inst, w, hmax, hfw, hk⟩ := h1
    obtain ⟨M', inst', w', hmax', hfw', hk'⟩ := h2
    have heq : @ty M inst w = @ty M' inst' w' := Fin.ext (hk.trans hk'.symm)
    have hth : ∀ φ, atomFree φ = true → (M.force w φ ↔ M'.force w' φ) := by
      intro φ hφ
      rw [@hty M inst w hmax φ hφ, @hty M' inst' w' hmax' φ hφ, heq]
    have hfw'i : M'.force w' (f (signedConj n (fun j => i.testBit j.1))) :=
      (hth _ (hf.vf _ (boxFree_signedConj _ _) (varsBelow_signedConj _ _))).mp hfw
    have hbits : ∀ l, l < n → i.testBit l = j.testBit l := by
      intro l hl
      refine Decidable.byContradiction fun hne => ?_
      have hne' : padB n (fun j => i.testBit j.1) l ≠ padB n (fun j' => j.testBit j'.1) l := by
        unfold padB
        rw [dif_pos hl, dif_pos hl]
        exact hne
      have hd := signedConj_disj hl hne'
      have hbb : boxFree ((signedConj n (fun j => i.testBit j.1)).and
          (signedConj n (fun j' => j.testBit j'.1))) = true := by
        show (boxFree _ && boxFree _) = true
        rw [boxFree_signedConj, boxFree_signedConj]; rfl
      have hvv : varsBelow n ((signedConj n (fun j => i.testBit j.1)).and
          (signedConj n (fun j' => j.testBit j'.1))) = true := by
        show (varsBelow n _ && varsBelow n _) = true
        rw [varsBelow_signedConj, varsBelow_signedConj]; rfl
      have hd' : Deriv [(f (signedConj n (fun j => i.testBit j.1))).and
          (f (signedConj n (fun j' => j.testBit j'.1)))] (f .falsePLL) :=
        Deriv.cutHead
          (hf.meet _ _ (boxFree_signedConj _ _) (boxFree_signedConj _ _)
            (varsBelow_signedConj _ _) (varsBelow_signedConj _ _)).2
          (hf.mono hbb rfl hvv rfl hd)
      exact hmax'.1 (hd'.elim fun d => SubframeModel.CF.soundness₁ d M' w' ⟨hfw'i, hfw'⟩)
    exact Nat.eq_of_testBit_eq fun l => by
      rcases Nat.lt_or_ge l n with hl | hl
      · exact hbits l hl
      · have h2 : 2 ^ n ≤ 2 ^ l := Nat.pow_le_pow_right (by decide) hl
        rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem meetCounting : MeetCounting := fun _ _ _ hf hK => meet_counting hf hK

/-! ## The known type bounds, restated: `k(⊥) ≤ 2`, `k(t3) ≤ 3` -/

/-- Some `S`-world lies above `w`. -/
def hasS (M : SubframeModel) [FinDec M] (w : M.W) : Prop :=
  ∃ v ∈ FinDec.elems (M := M), M.le w v ∧ v ∈ M.S

instance (M : SubframeModel) [FinDec M] (w : M.W) : Decidable (hasS M w) := by
  unfold hasS; exact inferInstance

/-- The two types at `⊥`: `Te` (no `S`-world above) and `Tn`. -/
def botTs (k : Fin 2) : PLLFormula → Bool := if k.1 = 0 then Te else Tn

def botTy (M : SubframeModel) [FinDec M] (w : M.W) : Fin 2 :=
  if hasS M w then ⟨1, by decide⟩ else ⟨0, by decide⟩

theorem force_ne_of_hasS {M : SubframeModel} [FinDec M] {w : M.W} (hw : BMax .falsePLL M w)
    (h : hasS M w) : M.force w ne := by
  obtain ⟨v, _, hwv, hvS⟩ := h
  intro u hwu hue
  have huw : M.le u w := hw.2 u hwu (fun h => h)
  exact hue v (M.trans huw hwv) hvS

theorem force_e_of_not_hasS {M : SubframeModel} [FinDec M] {w : M.W} (h : ¬ hasS M w) :
    M.force w e :=
  fun v hv hvS => h ⟨v, FinDec.complete v, hv, hvS⟩

/-- **`k(⊥) ≤ 2`**: a top world forces `◯⊥` or `¬◯⊥`, and is then of type `Te` or `Tn`. -/
theorem typeBound_bot : TypeBound .falsePLL 2 := by
  refine ⟨botTs, botTy, fun M inst w hw φ hφ => ?_⟩
  rcases Decidable.em (hasS M w) with hS | hS
  · have e1 : botTs (botTy M w) = Tn := by
      unfold botTs botTy
      rw [if_pos hS]
      exact if_neg Nat.one_ne_zero
    rw [e1]
    exact force_ne_iff_Tn M φ w hφ (force_ne_of_hasS hw hS)
  · have e1 : botTs (botTy M w) = Te := by
      unfold botTs botTy
      rw [if_neg hS]
      exact if_pos rfl
    rw [e1]
    exact force_e_iff_Te M φ w hφ (force_e_of_not_hasS hS)

/-- The three types at `t3`: `(S, ¬N)`, `(S, N)`, `(¬S, N)`. -/
def t3Ts (k : Fin 3) : PLLFormula → Bool :=
  if k.1 = 0 then Tmax true false else if k.1 = 1 then Tmax true true else Tmax false true

def t3Ty (M : SubframeModel) [FinDec M] (w : M.W) : Fin 3 :=
  if InS M w then (if HasN M w then ⟨1, by decide⟩ else ⟨0, by decide⟩) else ⟨2, by decide⟩

/-- **`k(t3) ≤ 3`** (`rmax_force`, `rmax_inS_or_hasN` of `f0FreeIPL`). -/
theorem typeBound_t3 : TypeBound t3 3 := by
  refine ⟨t3Ts, t3Ty, fun M inst w hw φ hφ => ?_⟩
  have hw' : RMax M w := hw
  rcases Decidable.em (InS M w) with hs | hs
  · rcases Decidable.em (HasN M w) with hn | hn
    · have e1 : t3Ts (t3Ty M w) = Tmax true true := by
        unfold t3Ts t3Ty
        rw [if_pos hs, if_pos hn]
        exact (if_neg Nat.one_ne_zero).trans (if_pos rfl)
      rw [e1]
      exact rmax_force M hw' (iff_of_true rfl hs) (iff_of_true rfl hn) φ hφ
    · have e1 : t3Ts (t3Ty M w) = Tmax true false := by
        unfold t3Ts t3Ty
        rw [if_pos hs, if_neg hn]
        exact if_pos rfl
      rw [e1]
      exact rmax_force M hw' (iff_of_true rfl hs) (iff_of_false Bool.false_ne_true hn) φ hφ
  · have hn : HasN M w := (rmax_inS_or_hasN M hw').resolve_left hs
    have e1 : t3Ts (t3Ty M w) = Tmax false true := by
      unfold t3Ts t3Ty
      rw [if_neg hs]
      exact (if_neg (by decide)).trans (if_neg (by decide))
    rw [e1]
    exact rmax_force M hw' (iff_of_false Bool.false_ne_true hs) (iff_of_true rfl hn) φ hφ

/-! ## Corollaries -/

/-- **No ∧-copy of `H₂` with bottom `t3`.** -/
theorem noMeetCopyH2_t3 : NoMeetCopyH2 t3 := by
  rintro ⟨f, hf, hi⟩
  have h := meet_counting hf (typeBound_interd hi.symm typeBound_t3)
  exact absurd h (by decide)

/-- **No ∧-copy of `H₂` with bottom `⊥`.** -/
theorem noMeetCopyH2_bot : NoMeetCopyH2 .falsePLL := by
  rintro ⟨f, hf, hi⟩
  have h := meet_counting hf (typeBound_interd hi.symm typeBound_bot)
  exact absurd h (by decide)

theorem relB_vf {b : PLLFormula} (hb : atomFree b = true) {x : String → PLLFormula}
    (hx : ∀ a, atomFree (x a) = true) : ∀ A, atomFree (relB b x A) = true
  | .prop a => hx a
  | .falsePLL => hb
  | .and A B => by
      show (atomFree (relB b x A) && atomFree (relB b x B)) = true
      rw [relB_vf hb hx A, relB_vf hb hx B]; rfl
  | .or A B => by
      show (atomFree (relB b x A) && atomFree (relB b x B)) = true
      rw [relB_vf hb hx A, relB_vf hb hx B]; rfl
  | .ifThen A B => by
      show (atomFree (relB b x A) && atomFree (relB b x B)) = true
      rw [relB_vf hb hx A, relB_vf hb hx B]; rfl
  | .somehow A => relB_vf hb hx A

/-- A relativisation that is faithful is a meet-embedding (`relB` of `∧` is `∧`). -/
theorem meetEmb_relB {n : Nat} {b : PLLFormula} (hb : atomFree b = true) {x : String → PLLFormula}
    (hx : ∀ a, atomFree (x a) = true)
    (hfaith : ∀ A B, boxFree A = true → boxFree B = true →
      varsBelow n A = true → varsBelow n B = true →
      (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))) : MeetEmb n (relB b x) where
  vf A _ _ := relB_vf hb hx A
  faithful A B hA hB vA vB :=
    ⟨fun h => ⟨(hfaith A B hA hB vA vB).mp h.1, (hfaith B A hB hA vB vA).mp h.2⟩,
     fun h => ⟨(hfaith A B hA hB vA vB).mpr h.1, (hfaith B A hB hA vB vA).mpr h.2⟩⟩
  meet _ _ _ _ _ _ := Interd.refl _

/-- **The counting criterion of `f0FreeHAn`**, as a corollary. -/
theorem countingCriterion : CountingCriterion := by
  intro b n K hb hfree hK
  obtain ⟨x, hx, _, hfaith⟩ := hfree
  exact meet_counting (meetEmb_relB hb hx hfaith) hK

theorem sgnY_le_sgn {x y : PLLFormula} (hy : Deriv [x.and y] t3) :
    ∀ b, Deriv [sgnY b x y] (sgn b x)
  | true => Deriv.iden (.head _)
  | false => Deriv.impIntro (Deriv.cutHead
      (Deriv.andIntro (Deriv.iden (.head _)) (Deriv.iden (.tail _ (.head _)))) hy)

/-- **`noFreeHA2` with any negation**: the relative negation `x ↠ t3` is the
largest `y` with `x ∧ y ≤ t3`, so a signed conjunction with `y`'s lies below the
one with `↠`'s. -/
theorem noFreeHA2_anyNeg : NoFreeHA2AnyNeg := by
  intro x₀ x₁ y₀ y₁ h₀ h₁ hy₀ hy₁
  obtain ⟨ε, hε⟩ := noFreeHA2 x₀ x₁ h₀ h₁
  refine ⟨ε, Deriv.impIntro ?_⟩
  have hd : Deriv [(sgnY ε.1 x₀ y₀).and (sgnY ε.2 x₁ y₁)] ((sgn ε.1 x₀).and (sgn ε.2 x₁)) :=
    Deriv.andIntro (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) (sgnY_le_sgn hy₀ ε.1))
      (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) (sgnY_le_sgn hy₁ ε.2))
  exact Deriv.cutHead hd
    (Deriv.impElim (Deriv.rename (fun _ hx => absurd hx List.not_mem_nil) hε) (Deriv.iden (.head _)))

/-! ## Non-vacuity: `h₁` is a meet-embedding of `H₁` -/

theorem onlyP_of_varsBelow1 : ∀ A : PLLFormula, varsBelow 1 A = true → FreeIPL.onlyP A = true
  | .prop a, h => by
      obtain ⟨i, hi, hd⟩ := List.any_eq_true.mp h
      have hi0 : i = 0 := by
        have := List.mem_range.mp hi
        omega
      subst hi0
      have ha : a = pvar 0 := of_decide_eq_true hd
      show decide (a = pv) = true
      rw [ha]
      rfl
  | .falsePLL, _ => rfl
  | .and A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (varsBelow 1 A && varsBelow 1 B) = true)
      show (FreeIPL.onlyP A && FreeIPL.onlyP B) = true
      rw [onlyP_of_varsBelow1 A h'.1, onlyP_of_varsBelow1 B h'.2]; rfl
  | .or A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (varsBelow 1 A && varsBelow 1 B) = true)
      show (FreeIPL.onlyP A && FreeIPL.onlyP B) = true
      rw [onlyP_of_varsBelow1 A h'.1, onlyP_of_varsBelow1 B h'.2]; rfl
  | .ifThen A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (varsBelow 1 A && varsBelow 1 B) = true)
      show (FreeIPL.onlyP A && FreeIPL.onlyP B) = true
      rw [onlyP_of_varsBelow1 A h'.1, onlyP_of_varsBelow1 B h'.2]; rfl
  | .somehow A, h => onlyP_of_varsBelow1 A h

/-- **`h₁` is a meet-embedding of `H₁`** (`freeIPL1`), consistent with `k(t3) = 3 ≥ 2`. -/
theorem meetEmb_h1 : MeetEmb 1 h1 where
  vf A _ hv := sig_vf (onlyP_embed_vf A (onlyP_of_varsBelow1 A hv))
  faithful A B hA hB vA vB :=
    have pA := onlyP_of_varsBelow1 A vA
    have pB := onlyP_of_varsBelow1 B vB
    ⟨fun h => ⟨(freeIPL1.2 A B hA hB pA pB).mp h.1, (freeIPL1.2 B A hB hA pB pA).mp h.2⟩,
     fun h => ⟨(freeIPL1.2 A B hA hB pA pB).mpr h.1, (freeIPL1.2 B A hB hA pB pA).mpr h.2⟩⟩
  meet _ _ _ _ _ _ := Interd.refl _

theorem meetEmbH1 : MeetEmbH1 := meetEmb_h1

end MeetCount
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.MeetCount.pvar_injective [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.valB_pvar [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.signedConj_not_bot [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.signedConj_disj [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.MeetEmb.mono [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.typeBound_interd [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.exists_bmax [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.exists_cell [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.rel_pigeon [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.meet_counting [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.meetCounting [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.typeBound_bot [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.typeBound_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.noMeetCopyH2_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.noMeetCopyH2_bot [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.countingCriterion [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.noFreeHA2_anyNeg [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.meetEmb_h1 [propext, Quot.sound]
#axioms_within PLLND.F0.MeetCount.meetEmbH1 [propext, Quot.sound]
