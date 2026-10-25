import wip.esakiaNuclearFinProofs

/-!
# Nuclear Esakia duality, finite case: proofs of F6–F9 (Phase A)

The bijection between nuclei on `A` and subsets of `X_A` ([BG] Thm 30 in
its finite form), the order reversal, [BG] Cor 31 and [BG] Thm 34.
Choice-free.
-/

namespace EsakiaNuclear

namespace FinHA

variable {H : FinHA}

/-! ## `α` is injective, preserves `∧`, and has an inverse on up-sets -/

theorem Ax.alpha_inj (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n)
    (h : H.alpha a = H.alpha b) : a = b := by
  have refl : ∀ U : Bits, H.dual.subsetOf U U = true :=
    fun _ => FinOrd.subsetOf_iff.mpr fun _ _ h => h
  refine hA.antisymm ha hb ?_ ?_
  · rw [hA.le_eq_subset ha hb, h]; exact refl _
  · rw [hA.le_eq_subset hb ha, h]; exact refl _

theorem Ax.alpha_meet (hA : H.Ax) {x y i : Nat} (hx : x < H.ord.n) (hy : y < H.ord.n)
    (hi : i < H.mprimes.length) :
    mem (H.alpha (H.meet x y)) i = (mem (H.alpha x) i && mem (H.alpha y) i) := by
  have hm := mp_spec hi
  rw [mem_alpha hi, mem_alpha hi, mem_alpha hi]
  cases e1 : H.le x (H.mp i)
  · cases e2 : H.le y (H.mp i)
    · cases e : H.le (H.meet x y) (H.mp i)
      · rfl
      · rcases hA.prime_meet hm.2 hx hy e with h | h
        · rw [e1] at h; exact Bool.noConfusion h
        · rw [e2] at h; exact Bool.noConfusion h
    · rw [hA.trans (hA.meet_lt hx hy) hy hm.1 (hA.meet_le_right hx hy) e2]; rfl
  · rw [hA.trans (hA.meet_lt hx hy) hx hm.1 (hA.meet_le_left hx hy) e1]; rfl

theorem Ax.alphaInv_spec (hA : H.Ax) {U : Bits} (hU : U ∈ H.dual.ups) :
    H.alphaInv U < H.ord.n ∧ H.alpha (H.alphaInv U) = U := by
  unfold FinHA.alphaInv
  obtain ⟨a, ha, haU⟩ := hA.alpha_surj hU
  obtain ⟨c, hc, hcm, hcp⟩ := find?_of_exists (p := fun a => H.alpha a == U)
    ⟨a, ha, beq_iff_eq.mpr haU⟩
  rw [hc, Option.getD_some]
  exact ⟨List.mem_range.mp hcm, beq_iff_eq.mp hcp⟩

theorem Ax.jA_spec (hA : H.Ax) {S : Bits} {a : Nat} :
    H.jA S a < H.ord.n ∧ H.alpha (H.jA S a) = H.dual.jS S (H.alpha a) :=
  hA.alphaInv_spec (FinOrd.jS_mem_ups hA.dual_po)

/-- `α (m_i) = X_A ∖ ↓i`. -/
theorem alpha_mp {i : Nat} : H.alpha (H.mp i) = H.dual.notBelow i := by
  refine bits_ext length_alpha length_map_range fun k hk => ?_
  rw [mem_alpha hk, FinOrd.mem_notBelow hk]
  rfl

theorem Ax.jA_nuc (hA : H.Ax) (S : Bits) : H.Nuc (H.jA S) := by
  have hdp := hA.dual_po
  refine ⟨fun _ => hA.jA_spec.1, fun {a} ha => ?_, fun {a} ha => ?_, fun {a b} ha hb => ?_⟩
  · rw [hA.le_eq_subset ha hA.jA_spec.1, hA.jA_spec.2]
    exact FinOrd.subsetOf_iff.mpr fun x hx h =>
      FinOrd.jS_infl (FinOrd.isUp_iff.mp (hA.alpha_isUp ha)) hx h
  · rw [hA.le_eq_subset hA.jA_spec.1 hA.jA_spec.1, hA.jA_spec.2, hA.jA_spec.2]
    exact FinOrd.subsetOf_iff.mpr fun x hx h => FinOrd.jS_idem hdp hx h
  · have hja : H.jA S a < H.ord.n := hA.jA_spec.1
    have hjb : H.jA S b < H.ord.n := hA.jA_spec.1
    refine hA.alpha_inj hA.jA_spec.1 (hA.meet_lt hja hjb) ?_
    refine bits_ext length_alpha length_alpha fun i hi => ?_
    rw [hA.jA_spec.2, hA.alpha_meet hja hjb hi, hA.jA_spec.2, hA.jA_spec.2]
    have hal : (H.alpha (H.meet a b)) = List.zipWith (· && ·) (H.alpha a) (H.alpha b) :=
      bits_ext length_alpha (length_zipWith_eq length_alpha length_alpha) fun k hk => by
        rw [hA.alpha_meet ha hb hk, mem_zipWith length_alpha length_alpha hk]
    rw [hal]
    exact FinOrd.jS_inter hi fun y hy => mem_zipWith length_alpha length_alpha hy

theorem Ax.Sj_jA (hA : H.Ax) {S : Bits} (hS : S.length = H.mprimes.length) :
    H.Sj (H.jA S) = S := by
  refine bits_ext length_Sj hS fun i hi => ?_
  have hm := mp_spec hi
  rw [mem_Sj hi, Bool.eq_iff_iff, beq_iff_eq, ← FinOrd.jS_notBelow_iff hA.dual_po hi,
    ← alpha_mp]
  constructor
  · intro h
    rw [← hA.jA_spec.2, h]
  · intro h
    exact hA.alpha_inj hA.jA_spec.1 hm.1 (by rw [hA.jA_spec.2]; exact h)

end FinHA

/-- **F6** (PROVED). -/
theorem f6 : F6 := by
  intro H hH S hS
  have hA := FinHA.ax_of_isHA hH
  exact ⟨FinHA.isNucleus_of_nuc (hA.jA_nuc S), hA.Sj_jA (length_of_mem_allSubs hS)⟩

/-! ## F7, F8, F9 -/

namespace FinHA

variable {H : FinHA}

theorem Ax.ordRev (hA : H.Ax) {j k : Nat → Nat} (hj : H.Nuc j) (hk : H.Nuc k) :
    (H.pts.all fun a => H.le (j a) (k a)) = H.dual.subsetOf (H.Sj k) (H.Sj j) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, FinOrd.subsetOf_iff]
  constructor
  · intro h i hi hki
    rw [mem_Sj hi, beq_iff_eq] at hki ⊢
    have hm := (mp_spec hi).1
    have := h (H.mp i) (mem_range_of_lt hm)
    rw [hki] at this
    exact hj.fix_of_le hA hm this
  · intro h a ha
    have ha' := List.mem_range.mp ha
    refine hA.le_of_primes (hj.lt ha') (hk.lt ha') fun m hm hp hkm => ?_
    obtain ⟨z, hz, hzp, hzm, hkz, haz⟩ := (hA.nuc_le_prime_iff hk ha' hm hp).mp hkm
    obtain ⟨i, hi, rfl⟩ := exists_mp hz hzp
    have hjz : j (H.mp i) = H.mp i := by
      have := h i hi (by rw [mem_Sj hi, hkz]; exact beq_iff_eq.mpr rfl)
      rw [mem_Sj hi] at this
      exact beq_iff_eq.mp this
    exact (hA.nuc_le_prime_iff hj ha' hm hp).mpr ⟨H.mp i, hz, hzp, hzm, hjz, haz⟩

theorem Ax.meetUnion (hA : H.Ax) {j k : Nat → Nat} (hj : H.Nuc j) (hk : H.Nuc k) :
    H.Sj (H.jMeet j k) = bunion (H.Sj j) (H.Sj k) := by
  refine bits_ext length_Sj (length_zipWith_eq length_Sj length_Sj) fun i hi => ?_
  have hm := mp_spec hi
  have hjm := hj.lt hm.1
  have hkm := hk.lt hm.1
  show mem (H.Sj (H.jMeet j k)) i = mem (List.zipWith (· || ·) (H.Sj j) (H.Sj k)) i
  rw [mem_zipWith length_Sj length_Sj hi, mem_Sj hi, mem_Sj hi, mem_Sj hi, Bool.eq_iff_iff,
    Bool.or_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq]
  show H.meet (j (H.mp i)) (k (H.mp i)) = H.mp i ↔ _
  constructor
  · intro h
    have hle : H.le (H.meet (j (H.mp i)) (k (H.mp i))) (H.mp i) = true := by
      rw [h]; exact hA.refl hm.1
    rcases hA.prime_meet hm.2 hjm hkm hle with h1 | h1
    · exact Or.inl (hj.fix_of_le hA hm.1 h1)
    · exact Or.inr (hk.fix_of_le hA hm.1 h1)
  · rintro (h | h)
    · rw [h]; exact hA.meet_eq_left hm.1 hkm (hk.infl hm.1)
    · rw [h]
      exact hA.antisymm (hA.meet_lt hjm hm.1) hm.1 (hA.meet_le_right hjm hm.1)
        (hA.le_meet hjm hm.1 hm.1 (hj.infl hm.1) (hA.refl hm.1))

theorem mem_bcompl {s : Bits} {i : Nat} (hi : i < s.length) : mem (bcompl s) i = !(mem s i) := by
  unfold bcompl mem
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    getD_eq_getElem hi]
  rfl

theorem length_bcompl {s : Bits} : (bcompl s).length = s.length := List.length_map _

/-- `a ∨ m = m` iff `a ≤ m`. -/
theorem Ax.join_eq_iff (hA : H.Ax) {a m : Nat} (ha : a < H.ord.n) (hm : m < H.ord.n) :
    H.join a m = m ↔ H.le a m = true := by
  constructor
  · intro h
    have := hA.le_join_left ha hm
    rw [h] at this
    exact this
  · intro h
    exact hA.antisymm (hA.join_lt ha hm) hm (hA.join_le ha hm hm h (hA.refl hm))
      (hA.le_join_right ha hm)

/-- `a → m = m` iff `a ≰ m`, for a meet-prime `m`. -/
theorem Ax.himp_eq_iff (hA : H.Ax) {a m : Nat} (ha : a < H.ord.n) (hm : m < H.ord.n)
    (hp : H.isMeetPrime m = true) : H.himp a m = m ↔ H.le a m = false := by
  constructor
  · intro h
    cases e : H.le a m
    · rfl
    · exfalso
      have htop : H.le H.top (H.himp a m) = true := by
        rw [← hA.himp_adj ha hm hA.top_lt]
        exact hA.trans (hA.meet_lt hA.top_lt ha) ha hm (hA.meet_le_right hA.top_lt ha) e
      rw [h, hA.not_top_le hm hp] at htop
      exact Bool.noConfusion htop
  · intro h
    refine hA.antisymm (hA.himp_lt ha hm) hm ?_ (hA.le_himp ha hm)
    rcases hA.prime_meet hp (hA.himp_lt ha hm) ha (hA.meet_himp_le ha hm) with h1 | h1
    · exact h1
    · rw [h] at h1; exact Bool.noConfusion h1

/-- `(m → a) → a = m` iff `m` is a minimal meet-prime above `a`. -/
theorem Ax.w_eq_iff (hA : H.Ax) {a i : Nat} (ha : a < H.ord.n) (hi : i < H.mprimes.length) :
    H.himp (H.himp (H.mp i) a) a = H.mp i ↔
      H.le a (H.mp i) = true ∧ ∀ s, s < H.mprimes.length → H.le a (H.mp s) = true →
        H.le (H.mp s) (H.mp i) = true → s = i := by
  have hm := mp_spec hi
  let m := H.mp i
  have hma : H.himp m a < H.ord.n := hA.himp_lt hm.1 ha
  have hw : H.himp (H.himp m a) a < H.ord.n := hA.himp_lt hma ha
  -- `m ≤ w` and `a ≤ w`
  have hmw : H.le m (H.himp (H.himp m a) a) = true := by
    rw [← hA.himp_adj hma ha hm.1]
    exact hA.trans (hA.meet_lt hm.1 hma) (hA.meet_lt hma hm.1) ha (hA.meet_comm_le hm.1 hma)
      (hA.meet_himp_le hm.1 ha)
  have haw : H.le a (H.himp (H.himp m a) a) = true := hA.le_himp hma ha
  -- if `m → a ≤ m` then `m → a = a`, so `w = ⊤`
  have top_of : H.le (H.himp m a) m = true → H.himp (H.himp m a) a = H.top := by
    intro h
    have h1 : H.le (H.himp m a) a = true := by
      have := hA.le_meet hma hm.1 hma (hA.refl hma) h
      exact hA.trans hma (hA.meet_lt hma hm.1) ha this (hA.meet_himp_le hm.1 ha)
    have h2 : H.himp m a = a := hA.antisymm hma ha h1 (hA.le_himp hm.1 ha)
    refine (hA.top_eq hw ?_).symm ▸ rfl
    rw [h2, ← hA.himp_adj ha ha hA.top_lt]
    exact hA.meet_le_right hA.top_lt ha
  constructor
  · intro h
    refine ⟨by rw [← h]; exact haw, fun s hs has hsm => ?_⟩
    have hz := mp_spec hs
    cases e : H.le m (H.mp s)
    · -- `m ∧ (m → a) ≤ a ≤ z`, so `m → a ≤ z ≤ m`
      have hle : H.le (H.meet m (H.himp m a)) (H.mp s) = true :=
        hA.trans (hA.meet_lt hm.1 hma) ha hz.1
          (hA.trans (hA.meet_lt hm.1 hma) (hA.meet_lt hma hm.1) ha (hA.meet_comm_le hm.1 hma)
            (hA.meet_himp_le hm.1 ha)) has
      rcases hA.prime_meet hz.2 hm.1 hma hle with h1 | h1
      · rw [e] at h1; exact Bool.noConfusion h1
      · exfalso
        have := top_of (hA.trans hma hz.1 hm.1 h1 hsm)
        rw [h] at this
        exact (isMeetPrime_iff.mp hm.2).1 this
    · exact mp_inj hs hi (hA.antisymm hz.1 hm.1 hsm e)
  · rintro ⟨ham, hmin⟩
    refine hA.antisymm hw hm.1 ?_ hmw
    have hle : H.le (H.meet (H.himp m a) (H.himp (H.himp m a) a)) m = true :=
      hA.trans (hA.meet_lt hma hw) ha hm.1
        (hA.trans (hA.meet_lt hma hw) (hA.meet_lt hw hma) ha (hA.meet_comm_le hma hw)
          (hA.meet_himp_le hma ha)) ham
    rcases hA.prime_meet hm.2 hma hw hle with h1 | h1
    · exfalso
      -- the meet-primes above `a` other than `m`
      let P := ((List.range H.mprimes.length).filter fun s =>
        H.le a (H.mp s) && s != i).map H.mp
      have hPm : ∀ {y}, y ∈ P → ∃ s, s < H.mprimes.length ∧ H.le a (H.mp s) = true ∧
          s ≠ i ∧ H.mp s = y := by
        intro y hy
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
        obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
        simp only [Bool.and_eq_true] at hs2
        exact ⟨s, List.mem_range.mp hs1, hs2.1, by simpa using hs2.2, rfl⟩
      have hPlt : ∀ y ∈ P, y < H.ord.n := by
        intro y hy
        obtain ⟨s, hs, -, -, rfl⟩ := hPm hy
        exact (mp_spec hs).1
      have hb := hA.meetL_lt hPlt
      -- `m ∧ ⋀P ≤ a`
      have hmb : H.le (H.meet (H.meetL P) m) a = true := by
        refine hA.le_of_primes (hA.meet_lt hb hm.1) ha fun m' hm' hp' ham' => ?_
        obtain ⟨s, hs, rfl⟩ := exists_mp hm' hp'
        cases e : (s == i)
        · have hsP : H.mp s ∈ P := List.mem_map.mpr ⟨s, List.mem_filter.mpr
            ⟨mem_range_of_lt hs, by rw [ham']; simp [bne, e]⟩, rfl⟩
          exact hA.trans (hA.meet_lt hb hm.1) hb (mp_spec hs).1 (hA.meet_le_left hb hm.1)
            (hA.meetL_le hPlt hsP)
        · rw [beq_iff_eq.mp e]
          exact hA.meet_le_right hb hm.1
      rw [hA.himp_adj hm.1 ha hb] at hmb
      obtain ⟨y, hy, hym⟩ := hA.prime_meetL hm.1 hm.2 hPlt (hA.trans hb hma hm.1 hmb h1)
      obtain ⟨s, hs, has, hsi, rfl⟩ := hPm hy
      exact hsi (hmin s hs has hym)
    · exact h1

theorem Ax.thm34 (hA : H.Ax) {a : Nat} (ha : a < H.ord.n) :
    H.Sj (H.u a) = bcompl (H.alpha a) ∧ H.Sj (H.v a) = H.alpha a ∧
      H.Sj (H.w a) = H.dual.maxOf (bcompl (H.alpha a)) := by
  refine ⟨bits_ext length_Sj (length_bcompl.trans length_alpha) fun i hi => ?_,
    bits_ext length_Sj length_alpha fun i hi => ?_,
    bits_ext length_Sj length_map_range fun i hi => ?_⟩
  · have hm := mp_spec hi
    rw [mem_Sj hi, mem_bcompl (length_alpha.symm ▸ hi), mem_alpha hi, Bool.eq_iff_iff,
      beq_iff_eq]
    show H.join a (H.mp i) = H.mp i ↔ _
    rw [hA.join_eq_iff ha hm.1]
    cases H.le a (H.mp i) <;> simp
  · have hm := mp_spec hi
    rw [mem_Sj hi, mem_alpha hi, Bool.eq_iff_iff, beq_iff_eq]
    show H.himp a (H.mp i) = H.mp i ↔ _
    rw [hA.himp_eq_iff ha hm.1 hm.2]
    cases H.le a (H.mp i) <;> simp
  · rw [mem_Sj hi, Bool.eq_iff_iff, beq_iff_eq]
    show H.himp (H.himp (H.mp i) a) a = H.mp i ↔ _
    rw [hA.w_eq_iff ha hi]
    have hT : ∀ s, s < H.mprimes.length → mem (bcompl (H.alpha a)) s = H.le a (H.mp s) := by
      intro s hs
      rw [mem_bcompl (length_alpha.symm ▸ hs), mem_alpha hs]
      cases H.le a (H.mp s) <;> rfl
    show _ ↔ mem ((List.range H.mprimes.length).map fun t =>
      mem (bcompl (H.alpha a)) t && !(H.dual.pts.any fun s =>
        mem (bcompl (H.alpha a)) s && H.dual.le t s && s != t)) i = true
    rw [mem_map_range hi, hT i hi, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      cases e : (H.dual.pts.any fun s =>
          mem (bcompl (H.alpha a)) s && H.dual.le i s && s != i)
      · rfl
      · exfalso
        obtain ⟨s, hs, hp⟩ := List.any_eq_true.mp e
        have hs' := List.mem_range.mp hs
        simp only [Bool.and_eq_true] at hp
        rw [hT s hs'] at hp
        exact (by simpa using hp.2 : s ≠ i) (h2 s hs' hp.1.1 hp.1.2)
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun s hs has hsi => ?_⟩
      cases e : (s == i)
      · exfalso
        have : (H.dual.pts.any fun s =>
            mem (bcompl (H.alpha a)) s && H.dual.le i s && s != i) = true :=
          List.any_eq_true.mpr ⟨s, mem_range_of_lt hs, by
            rw [hT s hs, has]
            show (true && H.le (H.mp s) (H.mp i) && s != i) = true
            rw [hsi]; simp [bne, e]⟩
        rw [this] at h2
        exact Bool.noConfusion h2
      · exact beq_iff_eq.mp e

end FinHA

/-- **F7** (PROVED). -/
theorem f7 : F7 := fun _ _ _ hH hj hk =>
  (FinHA.ax_of_isHA hH).ordRev (FinHA.nuc_of_isNucleus hj) (FinHA.nuc_of_isNucleus hk)

/-- **F8** (PROVED). -/
theorem f8 : F8 := fun _ _ _ hH hj hk =>
  (FinHA.ax_of_isHA hH).meetUnion (FinHA.nuc_of_isNucleus hj) (FinHA.nuc_of_isNucleus hk)

/-- **F9** (PROVED). -/
theorem f9 : F9 := fun _ hH _ ha =>
  (FinHA.ax_of_isHA hH).thm34 (List.mem_range.mp ha)

end EsakiaNuclear

#axioms_within EsakiaNuclear.f6 [propext, Quot.sound]
#axioms_within EsakiaNuclear.f7 [propext, Quot.sound]
#axioms_within EsakiaNuclear.f8 [propext, Quot.sound]
#axioms_within EsakiaNuclear.f9 [propext, Quot.sound]
