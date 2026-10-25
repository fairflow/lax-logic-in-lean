import wip.esakiaNuclearFinBase

/-!
# Nuclear Esakia duality, finite case: the proofs (Phase A)

Proofs of the statements F1–F10 of `wip/esakiaNuclearFin.lean`, each a
`theorem` for the unchanged `def … : Prop`, over the kit
`wip/esakiaNuclearFinBase.lean`.  Choice-free.
-/

namespace EsakiaNuclear

namespace FinHA

variable {H : FinHA}

/-! ## F1: `α : A ≅ Up(X_A)` -/

theorem Ax.mem_dual_pts {i : Nat} (h : i < H.mprimes.length) : i < H.dual.n := h

/-- `α a ⊆ α b` iff every meet-prime above `b` is above `a`. -/
theorem subset_alpha_iff {a b : Nat} : H.dual.subsetOf (H.alpha a) (H.alpha b) = true ↔
    ∀ i, i < H.mprimes.length → H.le b (H.mp i) = true → H.le a (H.mp i) = true := by
  rw [FinOrd.subsetOf_iff]
  constructor
  · intro h i hi hb
    cases ha : H.le a (H.mp i)
    · have := h i hi ((mem_alpha_true hi).mpr ha)
      rw [mem_alpha_true hi, hb] at this
      exact this.symm
    · rfl
  · intro h i hi hai
    rw [mem_alpha_true hi] at hai ⊢
    cases hb : H.le b (H.mp i)
    · rfl
    · rw [h i hi hb] at hai
      exact hai

theorem Ax.alpha_isUp (hA : H.Ax) {a : Nat} (ha : a < H.ord.n) :
    H.dual.isUp (H.alpha a) = true := by
  rw [FinOrd.isUp_iff]
  intro i k hi hk hai hik
  rw [mem_alpha_true hi] at hai
  rw [mem_alpha_true hk]
  cases e : H.le a (H.mp k)
  · rfl
  · rw [hA.trans ha (mp_spec hk).1 (mp_spec hi).1 e hik] at hai
    exact hai

theorem Ax.le_eq_subset (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n) :
    H.le a b = H.dual.subsetOf (H.alpha a) (H.alpha b) := by
  rw [Bool.eq_iff_iff, subset_alpha_iff]
  constructor
  · intro hab i hi hbi
    exact hA.trans ha hb (mp_spec hi).1 hab hbi
  · intro h
    refine hA.le_of_primes ha hb fun m hm hp hbm => ?_
    obtain ⟨i, hi, rfl⟩ := exists_mp hm hp
    exact h i hi hbm

/-- The element `⋀{x ∈ X_A | x ∉ U}`. -/
def gen (H : FinHA) (U : Bits) : Nat :=
  H.meetL (((List.range H.mprimes.length).filter fun i => !(mem U i)).map H.mp)

theorem gen_mem {U : Bits} {x : Nat} :
    x ∈ ((List.range H.mprimes.length).filter fun i => !(mem U i)).map H.mp ↔
      ∃ i, i < H.mprimes.length ∧ mem U i = false ∧ H.mp i = x := by
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hi1, hi2⟩ := List.mem_filter.mp hi
    exact ⟨i, List.mem_range.mp hi1, by simpa using hi2, rfl⟩
  · rintro ⟨i, hi, hU, rfl⟩
    exact ⟨i, List.mem_filter.mpr ⟨mem_range_of_lt hi, by rw [hU]; rfl⟩, rfl⟩

theorem gen_lt_aux {U : Bits} :
    ∀ x ∈ ((List.range H.mprimes.length).filter fun i => !(mem U i)).map H.mp,
      x < H.ord.n := by
  intro x hx
  obtain ⟨i, hi, -, rfl⟩ := gen_mem.mp hx
  exact (mp_spec hi).1

theorem Ax.gen_lt (hA : H.Ax) {U : Bits} : H.gen U < H.ord.n := hA.meetL_lt gen_lt_aux

theorem Ax.alpha_gen (hA : H.Ax) {U : Bits} (hU : U ∈ H.dual.ups) : H.alpha (H.gen U) = U := by
  have hUl : U.length = H.mprimes.length := FinOrd.length_of_mem_ups hU
  have hUu := FinOrd.isUp_iff.mp (FinOrd.isUp_of_mem_ups hU)
  refine bits_ext length_alpha hUl fun i hi => ?_
  rw [mem_alpha hi]
  cases hUi : mem U i
  · have : H.le (H.gen U) (H.mp i) = true :=
      hA.meetL_le gen_lt_aux (gen_mem.mpr ⟨i, hi, hUi, rfl⟩)
    rw [this]; rfl
  · cases e : H.le (H.gen U) (H.mp i)
    · rfl
    · exfalso
      obtain ⟨y, hy, hyi⟩ := hA.prime_meetL (mp_spec hi).1 (mp_spec hi).2 gen_lt_aux e
      obtain ⟨k, hk, hUk, rfl⟩ := gen_mem.mp hy
      have := hUu i k hi hk hUi hyi
      rw [hUk] at this
      exact Bool.noConfusion this

theorem Ax.alpha_surj (hA : H.Ax) {U : Bits} (hU : U ∈ H.dual.ups) :
    ∃ a ∈ H.pts, H.alpha a = U :=
  ⟨H.gen U, mem_range_of_lt hA.gen_lt, hA.alpha_gen hU⟩

theorem Ax.alpha_himp (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n) :
    H.alpha (H.himp a b) = H.dual.impUp (H.alpha a) (H.alpha b) := by
  have hdp := hA.dual_po
  refine bits_ext length_alpha FinOrd.length_impUp fun i hi => ?_
  rw [Bool.eq_iff_iff, mem_alpha_true hi, FinOrd.mem_impUp_true hi]
  constructor
  · intro hi' k hk hik hak
    rw [mem_alpha_true hk] at hak ⊢
    cases hbk : H.le b (H.mp k)
    · rfl
    · exfalso
      have hm := mp_spec hk
      rcases hA.prime_meet hm.2 (hA.himp_lt ha hb) ha
          (hA.trans (hA.meet_lt (hA.himp_lt ha hb) ha) hb hm.1 (hA.meet_himp_le ha hb) hbk)
        with h | h
      · rw [hA.trans (hA.himp_lt ha hb) hm.1 (mp_spec hi).1 h hik] at hi'
        exact Bool.noConfusion hi'
      · rw [hak] at h
        exact Bool.noConfusion h
  · intro hI
    -- `impUp (α a) (α b)` is `α c` for some `c ≤ a → b`
    obtain ⟨c, hc, hcI⟩ := hA.alpha_surj (FinOrd.impUp_mem_ups hdp
      (U := H.alpha a) (V := H.alpha b))
    have hc' := List.mem_range.mp hc
    have hca : H.le c (H.himp a b) = true := by
      rw [← hA.himp_adj ha hb hc']
      refine hA.le_of_primes (hA.meet_lt hc' ha) hb fun m hm hp hbm => ?_
      obtain ⟨k, hk, rfl⟩ := exists_mp hm hp
      cases hak : H.le a (H.mp k)
      · cases hck : H.le c (H.mp k)
        · exfalso
          have hIk : mem (H.dual.impUp (H.alpha a) (H.alpha b)) k = true := by
            rw [← hcI, mem_alpha_true hk]; exact hck
          have := (FinOrd.mem_impUp_true hk).mp hIk k hk (hdp.refl hk)
            ((mem_alpha_true hk).mpr hak)
          rw [mem_alpha_true hk, hbm] at this
          exact Bool.noConfusion this
        · exact hA.trans (hA.meet_lt hc' ha) hc' hm (hA.meet_le_left hc' ha) hck
      · exact hA.trans (hA.meet_lt hc' ha) ha hm (hA.meet_le_right hc' ha) hak
    have hci : mem (H.alpha c) i = true := by
      rw [hcI]
      exact (FinOrd.mem_impUp_true hi).mpr hI
    rw [mem_alpha_true hi] at hci
    cases e : H.le (H.himp a b) (H.mp i)
    · rfl
    · rw [hA.trans hc' (hA.himp_lt ha hb) (mp_spec hi).1 hca e] at hci
      exact hci

end FinHA

open FinHA

/-- **F1** (PROVED). -/
theorem f1 : F1 := by
  intro H hH
  have hA := ax_of_isHA hH
  refine ⟨fun a ha => hA.alpha_isUp (List.mem_range.mp ha),
    fun a ha b hb => hA.le_eq_subset (List.mem_range.mp ha) (List.mem_range.mp hb),
    fun U hU => hA.alpha_surj hU,
    fun a ha b hb => hA.alpha_himp (List.mem_range.mp ha) (List.mem_range.mp hb)⟩

/-! ## From the axioms back to `isHA`, and nuclei -/

theorem bool_imp1 {p r : Bool} (h : p = true → r = true) : (!p || r) = true := by
  cases p
  · rfl
  · rw [h rfl]; rfl

theorem bool_imp2 {p q r : Bool} (h : p = true → q = true → r = true) :
    (!(p && q) || r) = true := by
  cases p
  · rfl
  · cases q
    · rfl
    · rw [h rfl rfl]; rfl

theorem FinOrd.isPoset_of_po {P : FinOrd} (h : P.PO) : P.isPoset = true := by
  unfold FinOrd.isPoset
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨List.all_eq_true.mpr fun x hx => h.refl (List.mem_range.mp hx),
    List.all_eq_true.mpr fun x hx => List.all_eq_true.mpr fun y hy => ?_⟩,
    List.all_eq_true.mpr fun x hx => List.all_eq_true.mpr fun y hy =>
      List.all_eq_true.mpr fun z hz => ?_⟩
  · exact bool_imp2 fun h1 h2 =>
      beq_iff_eq.mpr (h.antisymm (List.mem_range.mp hx) (List.mem_range.mp hy) h1 h2)
  · exact bool_imp2 fun h1 h2 =>
      h.trans (List.mem_range.mp hx) (List.mem_range.mp hy) (List.mem_range.mp hz) h1 h2

theorem FinHA.isHA_of_ax {H : FinHA} (hA : H.Ax) : H.isHA = true := by
  unfold FinHA.isHA
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨FinOrd.isPoset_of_po hA.po, hA.top_lt⟩, hA.bot_lt⟩, ?_⟩, ?_⟩
  · refine List.all_eq_true.mpr fun x hx => ?_
    rw [hA.le_top (List.mem_range.mp hx), hA.bot_le (List.mem_range.mp hx)]; rfl
  · refine List.all_eq_true.mpr fun a ha => List.all_eq_true.mpr fun b hb => ?_
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨hA.meet_lt ha' hb', hA.join_lt ha' hb'⟩, hA.himp_lt ha' hb'⟩,
      hA.meet_le_left ha' hb'⟩, hA.meet_le_right ha' hb'⟩, hA.le_join_left ha' hb'⟩,
      hA.le_join_right ha' hb'⟩, List.all_eq_true.mpr fun x hx => ?_⟩
    have hx' := List.mem_range.mp hx
    simp only [Bool.and_eq_true]
    exact ⟨⟨bool_imp2 (hA.le_meet ha' hb' hx'), bool_imp2 (hA.join_le ha' hb' hx')⟩,
      beq_iff_eq.mpr (hA.himp_adj ha' hb' hx')⟩

/-- What `isNucleus` asserts, unpacked. -/
structure FinHA.Nuc (H : FinHA) (j : Nat → Nat) : Prop where
  lt : ∀ {a}, a < H.ord.n → j a < H.ord.n
  infl : ∀ {a}, a < H.ord.n → H.le a (j a) = true
  idem : ∀ {a}, a < H.ord.n → H.le (j (j a)) (j a) = true
  meet : ∀ {a b}, a < H.ord.n → b < H.ord.n → j (H.meet a b) = H.meet (j a) (j b)

theorem FinHA.nuc_of_isNucleus {H : FinHA} {j : Nat → Nat} (h : H.isNucleus j = true) :
    H.Nuc j := by
  unfold FinHA.isNucleus at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : ∀ a, a < H.ord.n → (j a < H.ord.n ∧ H.le a (j a) = true) ∧
      H.le (j (j a)) (j a) = true := fun a ha => by
    have := List.all_eq_true.mp h1 a (mem_range_of_lt ha)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  exact ⟨fun ha => (e1 _ ha).1.1, fun ha => (e1 _ ha).1.2, fun ha => (e1 _ ha).2,
    fun ha hb => beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp h2 _
      (mem_range_of_lt ha)) _ (mem_range_of_lt hb))⟩

theorem FinHA.isNucleus_of_nuc {H : FinHA} {j : Nat → Nat} (h : H.Nuc j) :
    H.isNucleus j = true := by
  unfold FinHA.isNucleus
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr fun a ha => ?_, List.all_eq_true.mpr fun a ha =>
    List.all_eq_true.mpr fun b hb => beq_iff_eq.mpr (h.meet (List.mem_range.mp ha)
      (List.mem_range.mp hb))⟩
  have ha' := List.mem_range.mp ha
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h.lt ha', h.infl ha'⟩, h.idem ha'⟩

/-! ## F2: `ε : X ≅ X_{Up(X)}` -/

namespace FinOrd

variable {X : FinOrd}

/-- The `i`-th up-set. -/
abbrev up (X : FinOrd) (i : Nat) : Bits := X.ups.getD i []

theorem up_mem {i : Nat} (hi : i < X.ups.length) : X.up i ∈ X.ups := getD_ups_mem hi

theorem up_length {i : Nat} (hi : i < X.ups.length) : (X.up i).length = X.n :=
  length_of_mem_ups (up_mem hi)

theorem up_isUp {i : Nat} (hi : i < X.ups.length) :
    ∀ x y, x < X.n → y < X.n → mem (X.up i) x = true → X.le x y = true →
      mem (X.up i) y = true :=
  isUp_iff.mp (isUp_of_mem_ups (up_mem hi))

theorem up_upIdx {W : Bits} (h : W ∈ X.ups) : X.up (X.upIdx W) = W := (upIdx_spec h).2

theorem upIdx_lt {W : Bits} (h : W ∈ X.ups) : X.upIdx W < X.ups.length := (upIdx_spec h).1

theorem upHA_n : X.upHA.ord.n = X.ups.length := rfl

theorem upHA_le {i k : Nat} : X.upHA.le i k = X.subsetOf (X.up i) (X.up k) := rfl

theorem upHA_meet {i k : Nat} (hi : i < X.ups.length) (hk : k < X.ups.length) :
    X.upHA.meet i k = X.upIdx (List.zipWith (· && ·) (X.up i) (X.up k)) := by
  show (((List.range X.ups.length).map fun i => (List.range X.ups.length).map fun k =>
    X.upIdx (List.zipWith (· && ·) (X.up i) (X.up k))).getD i []).getD k 0 = _
  rw [getD_map_range' hi, getD_map_range hk]

theorem upHA_join {i k : Nat} (hi : i < X.ups.length) (hk : k < X.ups.length) :
    X.upHA.join i k = X.upIdx (List.zipWith (· || ·) (X.up i) (X.up k)) := by
  show (((List.range X.ups.length).map fun i => (List.range X.ups.length).map fun k =>
    X.upIdx (List.zipWith (· || ·) (X.up i) (X.up k))).getD i []).getD k 0 = _
  rw [getD_map_range' hi, getD_map_range hk]

theorem upHA_himp {i k : Nat} (hi : i < X.ups.length) (hk : k < X.ups.length) :
    X.upHA.himp i k = X.upIdx (X.impUp (X.up i) (X.up k)) := by
  show (((List.range X.ups.length).map fun i => (List.range X.ups.length).map fun k =>
    X.upIdx (X.impUp (X.up i) (X.up k))).getD i []).getD k 0 = _
  rw [getD_map_range' hi, getD_map_range hk]

theorem upHA_top : X.upHA.top = X.upIdx (X.pts.map fun _ => true) := rfl
theorem upHA_bot : X.upHA.bot = X.upIdx (X.pts.map fun _ => false) := rfl

theorem all_mem_ups : (X.pts.map fun _ => true) ∈ X.ups :=
  mem_ups_of length_map_range (isUp_iff.mpr fun _ y _ hy _ _ => by
    show mem ((List.range X.n).map fun _ => true) y = true
    rw [mem_map_range hy])

theorem none_mem_ups : (X.pts.map fun _ => false) ∈ X.ups :=
  mem_ups_of length_map_range (isUp_iff.mpr fun x _ hx _ h _ => by
    have : mem ((List.range X.n).map fun _ => false) x = true := h
    rw [mem_map_range hx] at this
    exact Bool.noConfusion this)

theorem up_top : X.up X.upHA.top = X.pts.map fun _ => true := up_upIdx all_mem_ups

theorem up_bot : X.up X.upHA.bot = X.pts.map fun _ => false := up_upIdx none_mem_ups

theorem inter_mem_ups {U V : Bits} (hU : U ∈ X.ups) (hV : V ∈ X.ups) :
    List.zipWith (· && ·) U V ∈ X.ups := by
  have hUl := length_of_mem_ups hU
  have hVl := length_of_mem_ups hV
  refine mem_ups_of (length_zipWith_eq hUl hVl) (isUp_iff.mpr fun x y hx hy h hxy => ?_)
  rw [mem_zipWith hUl hVl hx, Bool.and_eq_true] at h
  rw [mem_zipWith hUl hVl hy, Bool.and_eq_true]
  exact ⟨isUp_iff.mp (isUp_of_mem_ups hU) x y hx hy h.1 hxy,
    isUp_iff.mp (isUp_of_mem_ups hV) x y hx hy h.2 hxy⟩

theorem union_mem_ups {U V : Bits} (hU : U ∈ X.ups) (hV : V ∈ X.ups) :
    List.zipWith (· || ·) U V ∈ X.ups := by
  have hUl := length_of_mem_ups hU
  have hVl := length_of_mem_ups hV
  refine mem_ups_of (length_zipWith_eq hUl hVl) (isUp_iff.mpr fun x y hx hy h hxy => ?_)
  rw [mem_zipWith hUl hVl hx, Bool.or_eq_true] at h
  rw [mem_zipWith hUl hVl hy, Bool.or_eq_true]
  rcases h with h | h
  · exact Or.inl (isUp_iff.mp (isUp_of_mem_ups hU) x y hx hy h hxy)
  · exact Or.inr (isUp_iff.mp (isUp_of_mem_ups hV) x y hx hy h hxy)

/-- Up-sets with the same members have the same index. -/
theorem idx_eq_of_mem {i k : Nat} (hi : i < X.ups.length) (hk : k < X.ups.length)
    (h : ∀ x, x < X.n → mem (X.up i) x = mem (X.up k) x) : i = k := by
  have e : X.up i = X.up k := bits_ext (up_length hi) (up_length hk) h
  rw [← upIdx_getD hi, ← upIdx_getD hk]
  exact congrArg X.upIdx e

theorem upAlg_antisymm {i k : Nat} (hi : i < X.ups.length) (hk : k < X.ups.length)
    (h1 : X.subsetOf (X.up i) (X.up k) = true) (h2 : X.subsetOf (X.up k) (X.up i) = true) :
    i = k :=
  idx_eq_of_mem hi hk fun x hx => by
    have a1 := subsetOf_iff.mp h1 x hx
    have a2 := subsetOf_iff.mp h2 x hx
    cases e : mem (X.up i) x
    · cases e' : mem (X.up k) x
      · rfl
      · have h := a2 e'
        rw [e] at h
        exact h
    · exact (a1 e).symm

theorem upHA_ax (hX : X.PO) : X.upHA.Ax := by
  have hmeet : ∀ {i k}, i < X.ups.length → k < X.ups.length →
      X.upHA.meet i k < X.ups.length ∧ ∀ x, x < X.n →
        mem (X.up (X.upHA.meet i k)) x = (mem (X.up i) x && mem (X.up k) x) := by
    intro i k hi hk
    have hm := inter_mem_ups (up_mem hi) (up_mem hk)
    rw [upHA_meet hi hk]
    exact ⟨upIdx_lt hm, fun x hx => by
      rw [up_upIdx hm, mem_zipWith (up_length hi) (up_length hk) hx]⟩
  have hjoin : ∀ {i k}, i < X.ups.length → k < X.ups.length →
      X.upHA.join i k < X.ups.length ∧ ∀ x, x < X.n →
        mem (X.up (X.upHA.join i k)) x = (mem (X.up i) x || mem (X.up k) x) := by
    intro i k hi hk
    have hm := union_mem_ups (up_mem hi) (up_mem hk)
    rw [upHA_join hi hk]
    exact ⟨upIdx_lt hm, fun x hx => by
      rw [up_upIdx hm, mem_zipWith (up_length hi) (up_length hk) hx]⟩
  have hhimp : ∀ {i k}, i < X.ups.length → k < X.ups.length →
      X.upHA.himp i k < X.ups.length ∧ X.up (X.upHA.himp i k) = X.impUp (X.up i) (X.up k) := by
    intro i k hi hk
    have hm : X.impUp (X.up i) (X.up k) ∈ X.ups := impUp_mem_ups hX
    rw [upHA_himp hi hk]
    exact ⟨upIdx_lt hm, up_upIdx hm⟩
  have htop : X.up X.upHA.top = X.pts.map fun _ => true := up_upIdx all_mem_ups
  have hbot : X.up X.upHA.bot = X.pts.map fun _ => false := up_upIdx none_mem_ups
  refine {
    po := ⟨fun _ => subsetOf_iff.mpr fun _ _ h => h,
      fun hi hk h1 h2 => upAlg_antisymm hi hk h1 h2,
      fun _ _ _ h1 h2 => subsetOf_iff.mpr fun x hx h =>
        subsetOf_iff.mp h2 x hx (subsetOf_iff.mp h1 x hx h)⟩
    top_lt := upIdx_lt all_mem_ups
    bot_lt := upIdx_lt none_mem_ups
    le_top := fun _ => subsetOf_iff.mpr fun x hx _ => by
      show mem (X.up X.upHA.top) x = true
      rw [htop]; exact mem_map_range hx
    bot_le := fun _ => subsetOf_iff.mpr fun x hx h => by
      have h' : mem (X.up X.upHA.bot) x = true := h
      rw [hbot] at h'
      have : mem ((List.range X.n).map fun _ => false) x = true := h'
      rw [mem_map_range hx] at this
      exact absurd this Bool.false_ne_true
    meet_lt := fun hi hk => (hmeet hi hk).1
    join_lt := fun hi hk => (hjoin hi hk).1
    himp_lt := fun hi hk => (hhimp hi hk).1
    meet_le_left := fun hi hk => subsetOf_iff.mpr fun x hx h => by
      rw [(hmeet hi hk).2 x hx, Bool.and_eq_true] at h; exact h.1
    meet_le_right := fun hi hk => subsetOf_iff.mpr fun x hx h => by
      rw [(hmeet hi hk).2 x hx, Bool.and_eq_true] at h; exact h.2
    le_join_left := fun hi hk => subsetOf_iff.mpr fun x hx h => by
      rw [(hjoin hi hk).2 x hx, h]; rfl
    le_join_right := fun hi hk => subsetOf_iff.mpr fun x hx h => by
      rw [(hjoin hi hk).2 x hx, h, Bool.or_true]
    le_meet := fun hi hk _ h1 h2 => subsetOf_iff.mpr fun x hx h => by
      rw [(hmeet hi hk).2 x hx, subsetOf_iff.mp h1 x hx h, subsetOf_iff.mp h2 x hx h]; rfl
    join_le := fun hi hk _ h1 h2 => subsetOf_iff.mpr fun x hx h => by
      rw [(hjoin hi hk).2 x hx, Bool.or_eq_true] at h
      rcases h with h | h
      · exact subsetOf_iff.mp h1 x hx h
      · exact subsetOf_iff.mp h2 x hx h
    himp_adj := fun hi hk hx => ?_ }
  · rename_i a b x
    rw [Bool.eq_iff_iff]
    show X.subsetOf (X.up (X.upHA.meet x a)) (X.up b) = true ↔
      X.subsetOf (X.up x) (X.up (X.upHA.himp a b)) = true
    rw [subsetOf_iff, subsetOf_iff, (hhimp hi hk).2]
    constructor
    · intro h z hz hzx
      rw [mem_impUp_true hz]
      intro y hy hzy hya
      refine h y hy ?_
      rw [(hmeet hx hi).2 y hy, up_isUp hx z y hz hy hzx hzy, hya]; rfl
    · intro h z hz hzm
      rw [(hmeet hx hi).2 z hz, Bool.and_eq_true] at hzm
      exact (mem_impUp_true hz).mp (h z hz hzm.1) z hz (hX.refl hz) hzm.2

/-- `X ∖ ↓x` as bits. -/
def notBelow (X : FinOrd) (x : Nat) : Bits := X.pts.map fun y => !(X.le y x)

theorem mem_notBelow {x y : Nat} (hy : y < X.n) : mem (X.notBelow x) y = !(X.le y x) :=
  mem_map_range hy

theorem notBelow_mem_ups (hX : X.PO) {x : Nat} (hx : x < X.n) : X.notBelow x ∈ X.ups := by
  refine mem_ups_of length_map_range (isUp_iff.mpr fun y z hy hz h hyz => ?_)
  rw [mem_notBelow hy] at h
  rw [mem_notBelow hz]
  cases e : X.le z x
  · rfl
  · rw [hX.trans hy hz hx hyz e] at h; exact h

theorem up_eps (hX : X.PO) {x : Nat} (hx : x < X.n) : X.up (X.eps x) = X.notBelow x :=
  up_upIdx (notBelow_mem_ups hX hx)

theorem eps_lt (hX : X.PO) {x : Nat} (hx : x < X.n) : X.eps x < X.ups.length :=
  upIdx_lt (notBelow_mem_ups hX hx)

theorem eps_prime (hX : X.PO) {x : Nat} (hx : x < X.n) :
    X.upHA.isMeetPrime (X.eps x) = true := by
  have hA := upHA_ax hX
  have hW := up_eps hX hx
  refine FinHA.isMeetPrime_iff.mpr ⟨fun ht => ?_, fun i k hi hk h => ?_⟩
  · have e : X.up (X.eps x) = X.up X.upHA.top := by rw [ht]
    rw [hW, up_top] at e
    have h1 : mem (X.notBelow x) x = mem (X.pts.map fun _ => true) x := by rw [e]
    rw [mem_notBelow hx, hX.refl hx] at h1
    have h2 : mem ((List.range X.n).map fun _ => true) x = true := mem_map_range hx
    exact Bool.noConfusion (h1.trans h2)
  · have hsub := subsetOf_iff.mp (show X.subsetOf (X.up (X.upHA.meet i k)) (X.up (X.eps x)) =
      true from h)
    rw [hW] at hsub
    have hfree : ∀ j, j < X.ups.length → mem (X.up j) x = false →
        X.upHA.le j (X.eps x) = true := fun j hj hjx => by
      show X.subsetOf (X.up j) (X.up (X.eps x)) = true
      rw [hW]
      refine subsetOf_iff.mpr fun z hz hzj => ?_
      rw [mem_notBelow hz]
      cases e : X.le z x
      · rfl
      · rw [up_isUp hj z x hz hx hzj e] at hjx; exact Bool.noConfusion hjx
    cases ei : mem (X.up i) x
    · exact Or.inl (hfree i hi ei)
    · cases ek : mem (X.up k) x
      · exact Or.inr (hfree k hk ek)
      · exfalso
        have hm : mem (X.up (X.upHA.meet i k)) x = true := by
          rw [upHA_meet hi hk, up_upIdx (inter_mem_ups (up_mem hi) (up_mem hk)),
            mem_zipWith (up_length hi) (up_length hk) hx, ei, ek]; rfl
        have := hsub x hx hm
        rw [mem_notBelow hx, hX.refl hx] at this
        exact Bool.noConfusion this

/-- Members of an iterated meet in `Up(X)`. -/
theorem mem_up_meetL (hX : X.PO) {z : Nat} (hz : z < X.n) : ∀ {L : List Nat},
    (∀ y ∈ L, y < X.ups.length) →
      (mem (X.up (X.upHA.meetL L)) z = true ↔ ∀ y ∈ L, mem (X.up y) z = true)
  | [], _ => by
      show mem (X.up X.upHA.top) z = true ↔ _
      rw [up_top]
      exact ⟨fun _ y hy => absurd hy List.not_mem_nil, fun _ => mem_map_range hz⟩
  | a :: L, hL => by
      have hA := upHA_ax hX
      have ha := hL a List.mem_cons_self
      have hL' : ∀ y ∈ L, y < X.ups.length := fun y hy => hL y (List.mem_cons_of_mem a hy)
      have hmL : X.upHA.meetL L < X.ups.length := hA.meetL_lt hL'
      show mem (X.up (X.upHA.meet a (X.upHA.meetL L))) z = true ↔ _
      rw [upHA_meet ha hmL, up_upIdx (inter_mem_ups (up_mem ha) (up_mem hmL)),
        mem_zipWith (up_length ha) (up_length hmL) hz, Bool.and_eq_true,
        mem_up_meetL hX hz hL']
      constructor
      · rintro ⟨h1, h2⟩ y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h1
        · exact h2 y hy
      · intro h
        exact ⟨h a List.mem_cons_self, fun y hy => h y (List.mem_cons_of_mem a hy)⟩

theorem eps_surj (hX : X.PO) {m : Nat} (hm : m < X.ups.length)
    (hp : X.upHA.isMeetPrime m = true) : ∃ x ∈ X.pts, X.eps x = m := by
  have hA := upHA_ax hX
  let D := X.pts.filter fun x => !(mem (X.up m) x)
  let L := D.map X.eps
  have hD : ∀ {x}, x ∈ D ↔ x < X.n ∧ mem (X.up m) x = false := by
    intro x
    rw [List.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨List.mem_range.mp h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨mem_range_of_lt h1, by rw [h2]; rfl⟩
  have hLlt : ∀ y ∈ L, y < X.ups.length := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact eps_lt hX (hD.mp hx).1
  have hle : X.upHA.le (X.upHA.meetL L) m = true := by
    show X.subsetOf (X.up (X.upHA.meetL L)) (X.up m) = true
    refine subsetOf_iff.mpr fun z hz h => ?_
    rw [mem_up_meetL hX hz hLlt] at h
    cases e : mem (X.up m) z
    · exfalso
      have := h (X.eps z) (List.mem_map.mpr ⟨z, hD.mpr ⟨hz, e⟩, rfl⟩)
      rw [up_eps hX hz, mem_notBelow hz, hX.refl hz] at this
      exact Bool.noConfusion this
    · rfl
  obtain ⟨y, hy, hym⟩ := hA.prime_meetL hm hp hLlt hle
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  obtain ⟨hx', hxm⟩ := hD.mp hx
  refine ⟨x, mem_range_of_lt hx', idx_eq_of_mem (eps_lt hX hx') hm fun z hz => ?_⟩
  have h1 := subsetOf_iff.mp (show X.subsetOf (X.up (X.eps x)) (X.up m) = true from hym) z hz
  rw [up_eps hX hx'] at h1 ⊢
  cases e : mem (X.up m) z
  · cases e' : mem (X.notBelow x) z
    · rfl
    · rw [h1 e'] at e; exact e
  · rw [mem_notBelow hz]
    cases e' : X.le z x
    · rfl
    · rw [up_isUp hm z x hz hx' e e'] at hxm; exact Bool.noConfusion hxm

theorem le_eq_eps (hX : X.PO) {x y : Nat} (hx : x < X.n) (hy : y < X.n) :
    X.le x y = X.upHA.le (X.eps y) (X.eps x) := by
  rw [upHA_le, up_eps hX hx, up_eps hX hy, Bool.eq_iff_iff, subsetOf_iff]
  constructor
  · intro hxy z hz h
    rw [mem_notBelow hz] at h ⊢
    cases e : X.le z x
    · rfl
    · rw [hX.trans hz hx hy e hxy] at h; exact h
  · intro h
    cases e : X.le x y
    · exfalso
      have := h x hx (by rw [mem_notBelow hx, e]; rfl)
      rw [mem_notBelow hx, hX.refl hx] at this
      exact Bool.noConfusion this
    · rfl

theorem up_meet {i k : Nat} (hi : i < X.ups.length) (hk : k < X.ups.length) :
    X.upHA.meet i k < X.ups.length ∧ ∀ x, x < X.n →
      mem (X.up (X.upHA.meet i k)) x = (mem (X.up i) x && mem (X.up k) x) := by
  have hm := inter_mem_ups (up_mem hi) (up_mem hk)
  rw [upHA_meet hi hk]
  exact ⟨upIdx_lt hm, fun x hx => by
    rw [up_upIdx hm, mem_zipWith (up_length hi) (up_length hk) hx]⟩

theorem up_jSIdx (hX : X.PO) {S : Bits} {i : Nat} : X.up (X.jSIdx S i) = X.jS S (X.up i) :=
  up_upIdx (jS_mem_ups hX)

/-! ## F3, F5: `j_S` on `Up(X)` -/

/-- `j_S` is inflationary on up-sets. -/
theorem jS_infl {S U : Bits}
    (hU : ∀ x y, x < X.n → y < X.n → mem U x = true → X.le x y = true → mem U y = true)
    {x : Nat} (hx : x < X.n) (h : mem U x = true) : mem (X.jS S U) x = true :=
  (mem_jS_true hx).mpr fun y hy hxy _ => hU x y hx hy h hxy

/-- `j_S j_S U ⊆ j_S U`. -/
theorem jS_idem (hX : X.PO) {S U : Bits} {x : Nat} (hx : x < X.n)
    (h : mem (X.jS S (X.jS S U)) x = true) : mem (X.jS S U) x = true :=
  (mem_jS_true hx).mpr fun y hy hxy hS =>
    (mem_jS_true hy).mp ((mem_jS_true hx).mp h y hy hxy hS) y hy (hX.refl hy) hS

/-- `j_S (U ∩ V) = j_S U ∩ j_S V`, pointwise. -/
theorem jS_inter {S U V : Bits} {x : Nat} (hx : x < X.n)
    (hUV : ∀ y, y < X.n → mem (List.zipWith (· && ·) U V) y = (mem U y && mem V y)) :
    mem (X.jS S (List.zipWith (· && ·) U V)) x = (mem (X.jS S U) x && mem (X.jS S V) x) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, mem_jS_true hx, mem_jS_true hx, mem_jS_true hx]
  constructor
  · intro h
    refine ⟨fun y hy hxy hS => ?_, fun y hy hxy hS => ?_⟩
    · have := h y hy hxy hS; rw [hUV y hy, Bool.and_eq_true] at this; exact this.1
    · have := h y hy hxy hS; rw [hUV y hy, Bool.and_eq_true] at this; exact this.2
  · rintro ⟨h1, h2⟩ y hy hxy hS
    rw [hUV y hy, h1 y hy hxy hS, h2 y hy hxy hS]; rfl

theorem jS_nuc (hX : X.PO) (S : Bits) : X.upHA.Nuc (X.jSIdx S) := by
  have hA := upHA_ax hX
  refine ⟨fun _ => upIdx_lt (jS_mem_ups hX), fun {i} hi => ?_, fun {i} hi => ?_,
    fun {i k} hi hk => ?_⟩
  · show X.subsetOf (X.up i) (X.up (X.jSIdx S i)) = true
    rw [up_jSIdx hX]
    exact subsetOf_iff.mpr fun x hx h => jS_infl (up_isUp hi) hx h
  · show X.subsetOf (X.up (X.jSIdx S (X.jSIdx S i))) (X.up (X.jSIdx S i)) = true
    rw [up_jSIdx hX, up_jSIdx hX]
    exact subsetOf_iff.mpr fun x hx h => jS_idem hX hx h
  · have hji : X.jSIdx S i < X.ups.length := upIdx_lt (jS_mem_ups hX)
    have hjk : X.jSIdx S k < X.ups.length := upIdx_lt (jS_mem_ups hX)
    refine idx_eq_of_mem (upIdx_lt (jS_mem_ups hX)) (up_meet hji hjk).1 fun x hx => ?_
    rw [up_jSIdx hX, (up_meet hji hjk).2 x hx, up_jSIdx hX, up_jSIdx hX]
    have hm := inter_mem_ups (up_mem hi) (up_mem hk)
    rw [upHA_meet hi hk, up_upIdx hm]
    exact jS_inter hx fun y hy => mem_zipWith (up_length hi) (up_length hk) hy

theorem jS_notBelow_iff (hX : X.PO) {S : Bits} {x : Nat} (hx : x < X.n) :
    X.jS S (X.notBelow x) = X.notBelow x ↔ mem S x = true := by
  constructor
  · intro h
    cases e : mem S x
    · exfalso
      have hm : mem (X.jS S (X.notBelow x)) x = true := by
        refine (mem_jS_true hx).mpr fun y hy hxy hS => ?_
        rw [mem_notBelow hy]
        cases e' : X.le y x
        · rfl
        · have hxy' : x = y := hX.antisymm hx hy hxy e'
          rw [← hxy', e] at hS
          exact Bool.noConfusion hS
      rw [h, mem_notBelow hx, hX.refl hx] at hm
      exact Bool.noConfusion hm
    · rfl
  · intro hS
    refine bits_ext length_jS length_map_range fun z hz => ?_
    rw [Bool.eq_iff_iff, mem_jS_true hz, mem_notBelow hz]
    constructor
    · intro h
      cases e : X.le z x
      · rfl
      · exfalso
        have := h x hx e hS
        rw [mem_notBelow hx, hX.refl hx] at this
        exact Bool.noConfusion this
    · intro h y hy hzy _
      rw [mem_notBelow hy]
      cases e : X.le y x
      · rfl
      · rw [hX.trans hz hy hx hzy e] at h
        exact Bool.noConfusion h

end FinOrd

/-- **F3** (PROVED). -/
theorem f3 : F3 := by
  intro X hX S _
  have hP := FinOrd.po_of_isPoset hX
  exact ⟨fun _ _ => FinOrd.isUp_jS hP, FinHA.isNucleus_of_nuc (FinOrd.jS_nuc hP S)⟩

/-- **F5** (PROVED). -/
theorem f5 : F5 := by
  intro X hX S _ x hx
  have hP := FinOrd.po_of_isPoset hX
  have hx' := List.mem_range.mp hx
  have hW := FinOrd.notBelow_mem_ups hP hx'
  rw [Bool.eq_iff_iff, beq_iff_eq, ← FinOrd.jS_notBelow_iff hP hx']
  constructor
  · intro h
    show X.upIdx (X.jS S (X.up (X.eps x))) = X.eps x
    rw [FinOrd.up_eps hP hx', h]
    rfl
  · intro h
    have := congrArg X.up h
    rw [FinOrd.up_jSIdx hP, FinOrd.up_eps hP hx'] at this
    exact this

/-- **F2** (PROVED). -/
theorem f2 : F2 := by
  intro X hX
  have hP := FinOrd.po_of_isPoset hX
  exact ⟨FinHA.isHA_of_ax (FinOrd.upHA_ax hP),
    fun x hx => FinOrd.eps_prime hP (List.mem_range.mp hx),
    fun m hm hp => FinOrd.eps_surj hP (List.mem_range.mp hm) hp,
    fun x hx y hy => FinOrd.le_eq_eps hP (List.mem_range.mp hx) (List.mem_range.mp hy)⟩

/-! ## Nuclei on `A`: F4 -/

namespace FinHA

variable {H : FinHA} {j : Nat → Nat}

theorem Nuc.mono (hA : H.Ax) (hj : H.Nuc j) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n)
    (h : H.le a b = true) : H.le (j a) (j b) = true := by
  have e := hj.meet ha hb
  rw [hA.meet_eq_left ha hb h] at e
  rw [e]
  exact hA.meet_le_right (hj.lt ha) (hj.lt hb)

theorem Nuc.fix_of_le (hA : H.Ax) (hj : H.Nuc j) {a : Nat} (ha : a < H.ord.n)
    (h : H.le (j a) a = true) : j a = a :=
  hA.antisymm (hj.lt ha) ha h (hj.infl ha)

theorem Nuc.top (hA : H.Ax) (hj : H.Nuc j) : j H.top = H.top :=
  hA.antisymm (hj.lt hA.top_lt) hA.top_lt (hA.le_top (hj.lt hA.top_lt)) (hj.infl hA.top_lt)

theorem Nuc.meetL (hA : H.Ax) (hj : H.Nuc j) : ∀ {l : List Nat}, (∀ x ∈ l, x < H.ord.n) →
    j (H.meetL l) = H.meetL (l.map j)
  | [], _ => hj.top hA
  | a :: l, hl => by
      have hl' : ∀ x ∈ l, x < H.ord.n := fun x hx => hl x (List.mem_cons_of_mem a hx)
      show j (H.meet a (H.meetL l)) = H.meet (j a) (H.meetL (l.map j))
      rw [hj.meet (hl a List.mem_cons_self) (hA.meetL_lt hl'), hj.meetL hA hl']

/-- **The pointwise form of F4** ([BBCGGJ] Lemma 3.15 with Lemma 3.14): for a
meet-prime `m`, `j a ≤ m` iff some `j`-fixed meet-prime `z ≤ m` lies above
`a`. -/
theorem Ax.nuc_le_prime_iff (hA : H.Ax) (hj : H.Nuc j) {a m : Nat} (ha : a < H.ord.n)
    (hm : m < H.ord.n) (hp : H.isMeetPrime m = true) :
    H.le (j a) m = true ↔ ∃ z, z < H.ord.n ∧ H.isMeetPrime z = true ∧
      H.le z m = true ∧ j z = z ∧ H.le a z = true := by
  have hja := hj.lt ha
  constructor
  · intro hjm
    let Q : Nat → Bool := fun z => H.isMeetPrime z && H.le (j a) z && H.le z m
    have hQm : Q m = true := by
      show (H.isMeetPrime m && H.le (j a) m && H.le m m) = true
      rw [hp, hjm, hA.refl hm]; rfl
    obtain ⟨y, hy, hQy, hym, hmin⟩ := FinOrd.exists_min hA.po Q hm hQm
    have hQy' : (H.isMeetPrime y = true ∧ H.le (j a) y = true) ∧ H.le y m = true := by
      have : (H.isMeetPrime y && H.le (j a) y && H.le y m) = true := hQy
      simpa only [Bool.and_eq_true] using this
    -- the meet-primes above `j a`
    let P := H.mprimes.filter fun z => H.le (j a) z
    have hP : ∀ {z}, z ∈ P ↔ (z < H.ord.n ∧ H.isMeetPrime z = true) ∧ H.le (j a) z = true := by
      intro z
      rw [List.mem_filter, mem_mprimes]
    have hPlt : ∀ z ∈ P, z < H.ord.n := fun z hz => (hP.mp hz).1.1
    have hPjlt : ∀ z ∈ P.map j, z < H.ord.n := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      exact hj.lt (hPlt w hw)
    have he : H.le (H.meetL P) (j a) = true :=
      hA.le_of_primes (hA.meetL_lt hPlt) hja fun m' hm' hp' hjm' =>
        hA.meetL_le hPlt (hP.mpr ⟨⟨hm', hp'⟩, hjm'⟩)
    have hjP : H.le (H.meetL (P.map j)) y = true := by
      rw [← hj.meetL hA hPlt]
      exact hA.trans (hj.lt (hA.meetL_lt hPlt)) (hj.lt hja) hy
        (hj.mono hA (hA.meetL_lt hPlt) hja he)
        (hA.trans (hj.lt hja) hja hy (hj.idem ha) hQy'.1.2)
    obtain ⟨w, hw, hwy⟩ := hA.prime_meetL hy hQy'.1.1 hPjlt hjP
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    have hz' := hP.mp hz
    have hzy : H.le z y = true := hA.trans hz'.1.1 (hj.lt hz'.1.1) hy (hj.infl hz'.1.1) hwy
    have hzm : H.le z m = true := hA.trans hz'.1.1 hy hm hzy hQy'.2
    have hzQ : Q z = true := by
      show (H.isMeetPrime z && H.le (j a) z && H.le z m) = true
      rw [hz'.1.2, hz'.2, hzm]; rfl
    have hzy' : z = y := hmin z hz'.1.1 hzQ hzy
    rw [hzy'] at hwy
    exact ⟨y, hy, hQy'.1.1, hQy'.2, hj.fix_of_le hA hy hwy,
      hA.trans ha hja hy (hj.infl ha) hQy'.1.2⟩
  · rintro ⟨z, hz, -, hzm, hjz, haz⟩
    have := hj.mono hA ha hz haz
    rw [hjz] at this
    exact hA.trans hja hz hm this hzm

theorem mem_Sj {i : Nat} (hi : i < H.mprimes.length) : mem (H.Sj j) i = (j (H.mp i) == H.mp i) :=
  mem_map_range hi

theorem length_Sj : (H.Sj j).length = H.mprimes.length := length_map_range

theorem Ax.rep (hA : H.Ax) (hj : H.Nuc j) {a : Nat} (ha : a < H.ord.n) :
    H.alpha (j a) = H.dual.jS (H.Sj j) (H.alpha a) := by
  refine bits_ext length_alpha FinOrd.length_jS fun i hi => ?_
  rw [Bool.eq_iff_iff, mem_alpha_true hi, FinOrd.mem_jS_true hi]
  have hmi := mp_spec hi
  constructor
  · intro hjm k hk hik hS
    rw [mem_alpha_true hk]
    rw [mem_Sj hk, beq_iff_eq] at hS
    cases e : H.le a (H.mp k)
    · rfl
    · exfalso
      have := (hA.nuc_le_prime_iff hj ha hmi.1 hmi.2).mpr
        ⟨H.mp k, (mp_spec hk).1, (mp_spec hk).2, hik, hS, e⟩
      rw [hjm] at this
      exact Bool.noConfusion this
  · intro h
    cases e : H.le (j a) (H.mp i)
    · rfl
    · exfalso
      obtain ⟨z, hz, hzp, hzm, hjz, haz⟩ := (hA.nuc_le_prime_iff hj ha hmi.1 hmi.2).mp e
      obtain ⟨k, hk, rfl⟩ := exists_mp hz hzp
      have := h k hk hzm (by rw [mem_Sj hk, hjz]; exact beq_iff_eq.mpr rfl)
      rw [mem_alpha_true hk, haz] at this
      exact Bool.noConfusion this

end FinHA

/-- **F4** (PROVED). -/
theorem f4 : F4 := by
  intro H j hH hj a ha
  exact (FinHA.ax_of_isHA hH).rep (FinHA.nuc_of_isNucleus hj) (List.mem_range.mp ha)

end EsakiaNuclear

#axioms_within EsakiaNuclear.f1 [propext, Quot.sound]
#axioms_within EsakiaNuclear.f4 [propext, Quot.sound]
#axioms_within EsakiaNuclear.f2 [propext, Quot.sound]
#axioms_within EsakiaNuclear.f3 [propext, Quot.sound]
#axioms_within EsakiaNuclear.f5 [propext, Quot.sound]
