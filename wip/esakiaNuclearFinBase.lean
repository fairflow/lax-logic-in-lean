import wip.esakiaNuclearFin

/-!
# Nuclear Esakia duality, finite case: the proof kit (Phase A)

Reflection lemmas for the encoding of `wip/esakiaNuclearFin.lean` (lists of
bits, order tables, `find?`), the axioms of a finite Heyting algebra
extracted from `isHA`, the existence of maximal elements in a finite
poset, and the finite prime filter theorem (`exists_prime`): if `a ≰ b`
there is a meet-prime `m ≥ b` with `a ≰ m`.  Choice-free: everything is a
`Bool` computation over `List.range`.
-/

namespace EsakiaNuclear

/-! ## 0. Lists, bits, `find?` -/

theorem getD_eq_getElem {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem mem_map_range {n i : Nat} {f : Nat → Bool} (h : i < n) :
    mem ((List.range n).map f) i = f i := by
  unfold mem
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem length_map_range {n : Nat} {β : Type} {f : Nat → β} :
    ((List.range n).map f).length = n := by
  rw [List.length_map, List.length_range]

theorem getD_map_range {n i : Nat} {f : Nat → Nat} (h : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem getD_map_range' {n i : Nat} {β : Type} {f : Nat → β} {d : β} (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-- Two bit lists of length `n` that agree below `n` are equal. -/
theorem bits_ext {s t : Bits} {n : Nat} (hs : s.length = n) (ht : t.length = n)
    (h : ∀ i, i < n → mem s i = mem t i) : s = t := by
  apply List.ext_getElem (hs.trans ht.symm)
  intro i h1 h2
  have e := h i (hs ▸ h1)
  unfold mem at e
  rw [getD_eq_getElem h1, getD_eq_getElem h2] at e
  exact e

theorem mem_zipWith {s t : Bits} {n i : Nat} {f : Bool → Bool → Bool}
    (hs : s.length = n) (ht : t.length = n) (hi : i < n) :
    mem (List.zipWith f s t) i = f (mem s i) (mem t i) := by
  unfold mem
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem (hs ▸ hi), List.getElem?_eq_getElem (ht ▸ hi),
    getD_eq_getElem (hs ▸ hi), getD_eq_getElem (ht ▸ hi)]
  rfl

theorem length_zipWith_eq {s t : Bits} {n : Nat} {f : Bool → Bool → Bool}
    (hs : s.length = n) (ht : t.length = n) : (List.zipWith f s t).length = n := by
  rw [List.length_zipWith, hs, ht, Nat.min_self]

/-- `find?` returns a witness when one exists. -/
theorem find?_of_exists {α : Type} {l : List α} {p : α → Bool}
    (h : ∃ x ∈ l, p x = true) : ∃ y, l.find? p = some y ∧ y ∈ l ∧ p y = true := by
  cases hf : l.find? p with
  | none =>
      rw [List.find?_eq_none] at hf
      obtain ⟨x, hx, hpx⟩ := h
      exact absurd hpx (hf x hx)
  | some y => exact ⟨y, rfl, List.mem_of_find?_eq_some hf, List.find?_some hf⟩

/-- An index enumerating a list's members. -/
theorem forall_mem_iff_getD {l : List Nat} {P : Nat → Prop} :
    (∀ m ∈ l, P m) ↔ ∀ i, i < l.length → P (l.getD i 0) := by
  constructor
  · intro h i hi
    rw [getD_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · intro h m hm
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    have := h i hi
    rwa [getD_eq_getElem hi] at this

theorem getD_mem {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [getD_eq_getElem hi]
  exact List.getElem_mem hi

/-! ## 1. `allSubs` -/

theorem length_of_mem_allSubs : ∀ {n : Nat} {s : Bits}, s ∈ allSubs n → s.length = n
  | 0, s, h => by
      have : s = [] := List.mem_singleton.mp h
      subst this
      rfl
  | n + 1, s, h => by
      obtain ⟨t, ht, hs⟩ := List.mem_flatMap.mp h
      have htl := length_of_mem_allSubs ht
      rcases List.mem_cons.mp hs with rfl | hs
      · rw [List.length_append, htl]; rfl
      · rw [List.mem_singleton.mp hs, List.length_append, htl]; rfl

theorem mem_allSubs_of_length : ∀ {n : Nat} {s : Bits}, s.length = n → s ∈ allSubs n
  | 0, s, h => by
      rw [List.eq_nil_of_length_eq_zero h]
      exact List.mem_singleton.mpr rfl
  | n + 1, s, h => by
      rcases List.eq_nil_or_concat s with rfl | ⟨t, b, rfl⟩
      · exact absurd h (Nat.noConfusion ·)
      · have htl : t.length = n := by
          rw [List.concat_eq_append, List.length_append] at h
          exact Nat.succ.inj h
        refine List.mem_flatMap.mpr ⟨t, mem_allSubs_of_length htl, ?_⟩
        rw [List.concat_eq_append]
        cases b
        · exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))

theorem mem_allSubs {n : Nat} {s : Bits} : s ∈ allSubs n ↔ s.length = n :=
  ⟨length_of_mem_allSubs, mem_allSubs_of_length⟩

theorem nodup_flatMap_snoc : ∀ {l : List Bits}, l.Nodup →
    (l.flatMap fun s => [s ++ [false], s ++ [true]]).Nodup
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
      have h' := List.nodup_cons.mp h
      rw [List.flatMap_cons]
      refine List.nodup_append.mpr ⟨?_, nodup_flatMap_snoc h'.2, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.Pairwise.nil⟩⟩
        intro hm
        have := congrArg List.getLast? (List.mem_singleton.mp hm)
        simp at this
      · intro x hx y hy hxy
        obtain ⟨t, ht, hy⟩ := List.mem_flatMap.mp hy
        have hx' : x.dropLast = a := by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.dropLast_concat
          · rw [List.mem_singleton.mp hx]; exact List.dropLast_concat
        have hy' : y.dropLast = t := by
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.dropLast_concat
          · rw [List.mem_singleton.mp hy]; exact List.dropLast_concat
        rw [hxy, hy'] at hx'
        exact h'.1 (hx' ▸ ht)

theorem allSubs_nodup : ∀ n, (allSubs n).Nodup
  | 0 => List.nodup_cons.mpr ⟨List.not_mem_nil, List.Pairwise.nil⟩
  | n + 1 => nodup_flatMap_snoc (allSubs_nodup n)

theorem nodup_getElem_inj {α : Type} : ∀ {l : List α}, l.Nodup →
    ∀ {i k : Nat} (hi : i < l.length) (hk : k < l.length), l[i] = l[k] → i = k
  | [], _, i, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, h, i, k, hi, hk, e => by
      have h' := List.nodup_cons.mp h
      cases i with
      | zero =>
          cases k with
          | zero => rfl
          | succ k =>
              exfalso
              simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e
              exact h'.1 (e ▸ List.getElem_mem _)
      | succ i =>
          cases k with
          | zero =>
              exfalso
              simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e
              exact h'.1 (e ▸ List.getElem_mem _)
          | succ k =>
              simp only [List.getElem_cons_succ] at e
              exact congrArg Nat.succ (nodup_getElem_inj h'.2 _ _ e)


/-! ## 2. Boolean helpers -/

theorem bor_not_and {a b c : Bool} (h : (!(a && b) || c) = true) (ha : a = true)
    (hb : b = true) : c = true := by
  rw [ha, hb] at h
  simpa using h

theorem bor_not {a c : Bool} (h : (!a || c) = true) (ha : a = true) : c = true := by
  rw [ha] at h
  simpa using h

theorem mem_range_of_lt {x n : Nat} (h : x < n) : x ∈ List.range n := List.mem_range.mpr h

/-! ## 3. Finite posets -/

/-- The partial-order axioms on the carrier. -/
structure FinOrd.PO (P : FinOrd) : Prop where
  refl : ∀ {x}, x < P.n → P.le x x = true
  antisymm : ∀ {x y}, x < P.n → y < P.n → P.le x y = true → P.le y x = true → x = y
  trans : ∀ {x y z}, x < P.n → y < P.n → z < P.n →
    P.le x y = true → P.le y z = true → P.le x z = true

theorem FinOrd.po_of_isPoset {P : FinOrd} (h : P.isPoset = true) : P.PO := by
  unfold FinOrd.isPoset at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [List.all_eq_true] at h1 h2 h3
  refine ⟨fun hx => h1 _ (mem_range_of_lt hx), ?_, ?_⟩
  · intro x y hx hy hxy hyx
    have e := List.all_eq_true.mp (h2 x (mem_range_of_lt hx)) y (mem_range_of_lt hy)
    have := bor_not_and e hxy hyx
    simpa using this
  · intro x y z hx hy hz hxy hyz
    have e := List.all_eq_true.mp (List.all_eq_true.mp (h3 x (mem_range_of_lt hx)) y
      (mem_range_of_lt hy)) z (mem_range_of_lt hz)
    exact bor_not_and e hxy hyz

namespace FinOrd

variable {P : FinOrd}

theorem isUp_iff {U : Bits} : P.isUp U = true ↔
    ∀ x y, x < P.n → y < P.n → mem U x = true → P.le x y = true → mem U y = true := by
  unfold FinOrd.isUp
  constructor
  · intro h x y hx hy hU hxy
    exact bor_not_and (List.all_eq_true.mp (List.all_eq_true.mp h x (mem_range_of_lt hx)) y
      (mem_range_of_lt hy)) hU hxy
  · intro h
    refine List.all_eq_true.mpr fun x hx => List.all_eq_true.mpr fun y hy => ?_
    have hx' := List.mem_range.mp hx
    have hy' := List.mem_range.mp hy
    cases hU : mem U x
    · rfl
    · cases hxy : P.le x y
      · rfl
      · simp [h x y hx' hy' hU hxy]

theorem subsetOf_iff {U V : Bits} : P.subsetOf U V = true ↔
    ∀ x, x < P.n → mem U x = true → mem V x = true := by
  unfold FinOrd.subsetOf
  constructor
  · intro h x hx hU
    exact bor_not (List.all_eq_true.mp h x (mem_range_of_lt hx)) hU
  · intro h
    refine List.all_eq_true.mpr fun x hx => ?_
    cases hU : mem U x
    · rfl
    · simp [h x (List.mem_range.mp hx) hU]

theorem length_of_mem_ups {U : Bits} (h : U ∈ P.ups) : U.length = P.n :=
  length_of_mem_allSubs (List.mem_filter.mp h).1

theorem isUp_of_mem_ups {U : Bits} (h : U ∈ P.ups) : P.isUp U = true :=
  (List.mem_filter.mp h).2

theorem mem_ups_of {U : Bits} (hl : U.length = P.n) (hu : P.isUp U = true) : U ∈ P.ups :=
  List.mem_filter.mpr ⟨mem_allSubs_of_length hl, hu⟩

theorem nodup_filter {α : Type} {p : α → Bool} : ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | _, h => List.Pairwise.filter p h

theorem ups_nodup : P.ups.Nodup := nodup_filter (allSubs_nodup P.n)

/-- `upIdx` finds an up-set. -/
theorem upIdx_spec {U : Bits} (h : U ∈ P.ups) :
    P.upIdx U < P.ups.length ∧ P.ups.getD (P.upIdx U) [] = U := by
  unfold FinOrd.upIdx
  obtain ⟨i, hi, hiU⟩ := List.mem_iff_getElem.mp h
  have hex : ∃ x ∈ List.range P.ups.length, (P.ups.getD x [] == U) = true :=
    ⟨i, mem_range_of_lt hi, by rw [getD_eq_getElem hi, hiU]; exact beq_self_eq_true U⟩
  obtain ⟨y, hy, hym, hyp⟩ := find?_of_exists hex
  rw [hy, Option.getD_some]
  exact ⟨List.mem_range.mp hym, beq_iff_eq.mp hyp⟩

theorem getD_ups_mem {i : Nat} (hi : i < P.ups.length) : P.ups.getD i [] ∈ P.ups := by
  rw [getD_eq_getElem hi]
  exact List.getElem_mem hi

/-- `upIdx` inverts indexing. -/
theorem upIdx_getD {i : Nat} (hi : i < P.ups.length) : P.upIdx (P.ups.getD i []) = i := by
  obtain ⟨h1, h2⟩ := upIdx_spec (getD_ups_mem hi)
  have e : P.ups[P.upIdx (P.ups.getD i [])] = P.ups[i] := by
    rw [← getD_eq_getElem h1 (d := []), h2, getD_eq_getElem hi]
  exact nodup_getElem_inj ups_nodup h1 hi e

/-- Up-sets with the same index are equal, and conversely. -/
theorem upIdx_inj {U V : Bits} (hU : U ∈ P.ups) (hV : V ∈ P.ups) (h : P.upIdx U = P.upIdx V) :
    U = V := by
  rw [← (upIdx_spec hU).2, ← (upIdx_spec hV).2, h]

theorem mem_jS {S U : Bits} {x : Nat} (hx : x < P.n) :
    mem (P.jS S U) x = !(P.pts.any fun y => P.le x y && mem S y && !(mem U y)) :=
  mem_map_range hx

theorem length_jS {S U : Bits} : (P.jS S U).length = P.n := length_map_range

theorem mem_impUp {U V : Bits} {x : Nat} (hx : x < P.n) :
    mem (P.impUp U V) x = !(P.pts.any fun y => P.le x y && mem U y && !(mem V y)) :=
  mem_map_range hx

theorem length_impUp {U V : Bits} : (P.impUp U V).length = P.n := length_map_range

/-- `x ∈ j_S(U)` iff every `S`-point above `x` is in `U`. -/
theorem mem_jS_true {S U : Bits} {x : Nat} (hx : x < P.n) :
    mem (P.jS S U) x = true ↔
      ∀ y, y < P.n → P.le x y = true → mem S y = true → mem U y = true := by
  rw [mem_jS hx]
  constructor
  · intro h y hy hxy hS
    cases hU : mem U y
    · exfalso
      have : (P.pts.any fun y => P.le x y && mem S y && !(mem U y)) = true :=
        List.any_eq_true.mpr ⟨y, mem_range_of_lt hy, by rw [hxy, hS, hU]; rfl⟩
      rw [this] at h
      exact Bool.noConfusion h
    · rfl
  · intro h
    cases ha : (P.pts.any fun y => P.le x y && mem S y && !(mem U y))
    · rfl
    · exfalso
      obtain ⟨y, hy, hp⟩ := List.any_eq_true.mp ha
      have hy' := List.mem_range.mp hy
      cases hxy : P.le x y <;> cases hS : mem S y <;> cases hU : mem U y <;>
        rw [hxy, hS, hU] at hp <;> simp at hp
      exact Bool.noConfusion ((h y hy' hxy hS).symm.trans hU)

theorem mem_impUp_true {U V : Bits} {x : Nat} (hx : x < P.n) :
    mem (P.impUp U V) x = true ↔
      ∀ y, y < P.n → P.le x y = true → mem U y = true → mem V y = true :=
  mem_jS_true (S := U) (U := V) hx

theorem isUp_jS (hP : P.PO) {S U : Bits} : P.isUp (P.jS S U) = true := by
  rw [isUp_iff]
  intro x y hx hy hj hxy
  rw [mem_jS_true hy]
  intro z hz hyz hS
  exact (mem_jS_true hx).mp hj z hz (hP.trans hx hy hz hxy hyz) hS

theorem jS_mem_ups (hP : P.PO) {S U : Bits} : P.jS S U ∈ P.ups :=
  mem_ups_of length_jS (isUp_jS hP)

theorem impUp_mem_ups (hP : P.PO) {U V : Bits} : P.impUp U V ∈ P.ups :=
  jS_mem_ups hP (S := U) (U := V)

end FinOrd

theorem eq_of_not_bne {y x : Nat} (h : ¬ (y != x) = true) : y = x := by
  cases e : (y == x)
  · exfalso; apply h; simp [bne, e]
  · exact beq_iff_eq.mp e

/-! ## 4. Counting, and maximal elements in a finite poset -/

theorem length_filter_le_of {p q : Nat → Bool} : ∀ {l : List Nat},
    (∀ z ∈ l, p z = true → q z = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl 0
  | a :: l, h => by
      have ih := length_filter_le_of (l := l) fun z hz => h z (List.mem_cons_of_mem a hz)
      rw [List.filter_cons, List.filter_cons]
      cases hp : p a
      · cases hq : q a
        · exact ih
        · exact Nat.le_succ_of_le ih
      · have hq : q a = true := h a (List.mem_cons_self) hp
        rw [hq]
        exact Nat.succ_le_succ ih

theorem length_filter_lt_of {p q : Nat → Bool} : ∀ {l : List Nat},
    (∀ z ∈ l, p z = true → q z = true) → ∀ {z0 : Nat}, z0 ∈ l → q z0 = true → p z0 = false →
    (l.filter p).length < (l.filter q).length
  | [], _, _, hz0, _, _ => absurd hz0 List.not_mem_nil
  | a :: l, h, z0, hz0, hq0, hp0 => by
      have h' : ∀ z ∈ l, p z = true → q z = true := fun z hz => h z (List.mem_cons_of_mem a hz)
      rw [List.filter_cons, List.filter_cons]
      rcases List.mem_cons.mp hz0 with rfl | hz0
      · rw [hp0, hq0]
        exact Nat.lt_succ_of_le (length_filter_le_of h')
      · have ih := length_filter_lt_of h' hz0 hq0 hp0
        cases hp : p a
        · cases hq : q a
          · exact ih
          · exact Nat.lt_succ_of_lt ih
        · have hq : q a = true := h a (List.mem_cons_self) hp
          rw [hq]
          exact Nat.succ_lt_succ ih

namespace FinOrd

variable {P : FinOrd}

theorem exists_max_aux (hP : P.PO) (C : Nat → Bool) : ∀ (k x : Nat), x < P.n → C x = true →
    ((List.range P.n).filter fun y => C y && P.le x y).length ≤ k →
    ∃ m, m < P.n ∧ C m = true ∧ P.le x m = true ∧
      ∀ y, y < P.n → C y = true → P.le m y = true → y = m := by
  intro k
  induction k with
  | zero =>
      intro x hx hC hk
      exfalso
      have hmem : x ∈ (List.range P.n).filter fun y => C y && P.le x y :=
        List.mem_filter.mpr ⟨mem_range_of_lt hx, by rw [hC, hP.refl hx]; rfl⟩
      exact Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le (List.length_pos_of_mem hmem) hk)
  | succ k ih =>
      intro x hx hC hk
      cases hb : (List.range P.n).any (fun y => C y && P.le x y && y != x) with
      | false =>
          refine ⟨x, hx, hC, hP.refl hx, ?_⟩
          intro y hy hCy hxy
          have e := (List.any_eq_false.mp hb) y (mem_range_of_lt hy)
          rw [hCy, hxy] at e
          exact eq_of_not_bne (by simpa using e)
      | true =>
          obtain ⟨y, hy, hp⟩ := List.any_eq_true.mp hb
          have hy' := List.mem_range.mp hy
          simp only [Bool.and_eq_true] at hp
          obtain ⟨⟨hCy, hxy⟩, hne⟩ := hp
          have hne' : y ≠ x := by simpa using hne
          have hlt : ((List.range P.n).filter fun z => C z && P.le y z).length <
              ((List.range P.n).filter fun z => C z && P.le x z).length := by
            refine length_filter_lt_of ?_ (mem_range_of_lt hx) (by rw [hC, hP.refl hx]; rfl) ?_
            · intro z hz hzz
              have hz' := List.mem_range.mp hz
              simp only [Bool.and_eq_true] at hzz
              rw [hzz.1, hP.trans hx hy' hz' hxy hzz.2]
              rfl
            · cases e : P.le y x
              · simp
              · exact absurd (hP.antisymm hy' hx e hxy) hne'
          obtain ⟨m, hm, hCm, hym, hmax⟩ :=
            ih y hy' hCy (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hk))
          exact ⟨m, hm, hCm, hP.trans hx hy' hm hxy hym, hmax⟩

/-- **Maximal elements.**  In a finite poset every point of a decidable set
lies below a maximal point of the set. -/
theorem exists_max (hP : P.PO) (C : Nat → Bool) {x : Nat} (hx : x < P.n) (hC : C x = true) :
    ∃ m, m < P.n ∧ C m = true ∧ P.le x m = true ∧
      ∀ y, y < P.n → C y = true → P.le m y = true → y = m :=
  exists_max_aux hP C _ x hx hC (Nat.le_refl _)

/-- The reversed order. -/
def rev (P : FinOrd) : FinOrd := ⟨P.n, fun a b => P.le b a⟩

theorem po_rev (hP : P.PO) : P.rev.PO :=
  ⟨fun hx => hP.refl hx, fun hx hy h1 h2 => hP.antisymm hx hy h2 h1,
    fun hx hy hz h1 h2 => hP.trans hz hy hx h2 h1⟩

/-- **Minimal elements.** -/
theorem exists_min (hP : P.PO) (C : Nat → Bool) {x : Nat} (hx : x < P.n) (hC : C x = true) :
    ∃ m, m < P.n ∧ C m = true ∧ P.le m x = true ∧
      ∀ y, y < P.n → C y = true → P.le y m = true → y = m :=
  exists_max_aux (P := P.rev) (po_rev hP) C _ x hx hC (Nat.le_refl _)

end FinOrd

/-! ## 5. The axioms of a finite Heyting algebra -/

namespace FinHA

/-- What `isHA` asserts, unpacked. -/
structure Ax (H : FinHA) : Prop where
  po : H.ord.PO
  top_lt : H.top < H.ord.n
  bot_lt : H.bot < H.ord.n
  le_top : ∀ {x}, x < H.ord.n → H.le x H.top = true
  bot_le : ∀ {x}, x < H.ord.n → H.le H.bot x = true
  meet_lt : ∀ {a b}, a < H.ord.n → b < H.ord.n → H.meet a b < H.ord.n
  join_lt : ∀ {a b}, a < H.ord.n → b < H.ord.n → H.join a b < H.ord.n
  himp_lt : ∀ {a b}, a < H.ord.n → b < H.ord.n → H.himp a b < H.ord.n
  meet_le_left : ∀ {a b}, a < H.ord.n → b < H.ord.n → H.le (H.meet a b) a = true
  meet_le_right : ∀ {a b}, a < H.ord.n → b < H.ord.n → H.le (H.meet a b) b = true
  le_join_left : ∀ {a b}, a < H.ord.n → b < H.ord.n → H.le a (H.join a b) = true
  le_join_right : ∀ {a b}, a < H.ord.n → b < H.ord.n → H.le b (H.join a b) = true
  le_meet : ∀ {a b x}, a < H.ord.n → b < H.ord.n → x < H.ord.n →
    H.le x a = true → H.le x b = true → H.le x (H.meet a b) = true
  join_le : ∀ {a b x}, a < H.ord.n → b < H.ord.n → x < H.ord.n →
    H.le a x = true → H.le b x = true → H.le (H.join a b) x = true
  himp_adj : ∀ {a b x}, a < H.ord.n → b < H.ord.n → x < H.ord.n →
    H.le (H.meet x a) b = H.le x (H.himp a b)

theorem ax_of_isHA {H : FinHA} (h : H.isHA = true) : H.Ax := by
  unfold FinHA.isHA at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hpo, htop⟩, hbot⟩, hbd⟩, hops⟩ := h
  have po := FinOrd.po_of_isPoset hpo
  have bd : ∀ x, x < H.ord.n → H.le x H.top = true ∧ H.le H.bot x = true := fun x hx => by
    have := List.all_eq_true.mp hbd x (mem_range_of_lt hx)
    simpa only [Bool.and_eq_true] using this
  have ops : ∀ a b, a < H.ord.n → b < H.ord.n →
      ((((((((H.meet a b < H.ord.n ∧ H.join a b < H.ord.n) ∧ H.himp a b < H.ord.n) ∧
        H.le (H.meet a b) a = true) ∧ H.le (H.meet a b) b = true) ∧
        H.le a (H.join a b) = true) ∧ H.le b (H.join a b) = true) ∧
        (H.pts.all fun x =>
          (!(H.le x a && H.le x b) || H.le x (H.meet a b)) &&
          (!(H.le a x && H.le b x) || H.le (H.join a b) x) &&
          (H.le (H.meet x a) b == H.le x (H.himp a b))) = true)) := fun a b ha hb => by
    have := List.all_eq_true.mp (List.all_eq_true.mp hops a (mem_range_of_lt ha)) b
      (mem_range_of_lt hb)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  have inner : ∀ a b x, a < H.ord.n → b < H.ord.n → x < H.ord.n →
      ((!(H.le x a && H.le x b) || H.le x (H.meet a b)) = true ∧
       (!(H.le a x && H.le b x) || H.le (H.join a b) x) = true) ∧
      (H.le (H.meet x a) b == H.le x (H.himp a b)) = true := fun a b x ha hb hx => by
    have := List.all_eq_true.mp (ops a b ha hb).2 x (mem_range_of_lt hx)
    simpa only [Bool.and_eq_true] using this
  exact {
    po := po
    top_lt := htop
    bot_lt := hbot
    le_top := fun hx => (bd _ hx).1
    bot_le := fun hx => (bd _ hx).2
    meet_lt := fun ha hb => (ops _ _ ha hb).1.1.1.1.1.1.1
    join_lt := fun ha hb => (ops _ _ ha hb).1.1.1.1.1.1.2
    himp_lt := fun ha hb => (ops _ _ ha hb).1.1.1.1.1.2
    meet_le_left := fun ha hb => (ops _ _ ha hb).1.1.1.1.2
    meet_le_right := fun ha hb => (ops _ _ ha hb).1.1.1.2
    le_join_left := fun ha hb => (ops _ _ ha hb).1.1.2
    le_join_right := fun ha hb => (ops _ _ ha hb).1.2
    le_meet := fun ha hb hx h1 h2 => bor_not_and (inner _ _ _ ha hb hx).1.1 h1 h2
    join_le := fun ha hb hx h1 h2 => bor_not_and (inner _ _ _ ha hb hx).1.2 h1 h2
    himp_adj := fun ha hb hx => beq_iff_eq.mp (inner _ _ _ ha hb hx).2 }

variable {H : FinHA}

theorem Ax.refl (hA : H.Ax) {a : Nat} (ha : a < H.ord.n) : H.le a a = true := hA.po.refl ha
theorem Ax.antisymm (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n)
    (h1 : H.le a b = true) (h2 : H.le b a = true) : a = b := hA.po.antisymm ha hb h1 h2
theorem Ax.trans (hA : H.Ax) {a b c : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n)
    (hc : c < H.ord.n) (h1 : H.le a b = true) (h2 : H.le b c = true) : H.le a c = true :=
  hA.po.trans ha hb hc h1 h2

theorem Ax.meet_comm_le (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n) :
    H.le (H.meet a b) (H.meet b a) = true :=
  hA.le_meet hb ha (hA.meet_lt ha hb) (hA.meet_le_right ha hb) (hA.meet_le_left ha hb)

theorem Ax.le_meet_self (hA : H.Ax) {a : Nat} (ha : a < H.ord.n) :
    H.le a (H.meet a a) = true := hA.le_meet ha ha ha (hA.refl ha) (hA.refl ha)

/-- `b ≤ a → b`. -/
theorem Ax.le_himp (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n) :
    H.le b (H.himp a b) = true := by
  rw [← hA.himp_adj ha hb hb]
  exact hA.meet_le_left hb ha

/-- `(a → b) ∧ a ≤ b`. -/
theorem Ax.meet_himp_le (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n) :
    H.le (H.meet (H.himp a b) a) b = true := by
  rw [hA.himp_adj ha hb (hA.himp_lt ha hb)]
  exact hA.refl (hA.himp_lt ha hb)

theorem Ax.meet_mono (hA : H.Ax) {a b c d : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n)
    (hc : c < H.ord.n) (hd : d < H.ord.n) (h1 : H.le a c = true) (h2 : H.le b d = true) :
    H.le (H.meet a b) (H.meet c d) = true :=
  hA.le_meet hc hd (hA.meet_lt ha hb)
    (hA.trans (hA.meet_lt ha hb) ha hc (hA.meet_le_left ha hb) h1)
    (hA.trans (hA.meet_lt ha hb) hb hd (hA.meet_le_right ha hb) h2)

theorem Ax.meet_eq_left (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n)
    (h : H.le a b = true) : H.meet a b = a :=
  hA.antisymm (hA.meet_lt ha hb) ha (hA.meet_le_left ha hb)
    (hA.le_meet ha hb ha (hA.refl ha) h)

theorem Ax.top_eq (hA : H.Ax) {x : Nat} (hx : x < H.ord.n) (h : H.le H.top x = true) :
    x = H.top :=
  hA.antisymm hx hA.top_lt (hA.le_top hx) h

/-! ## 6. Meet-primes and the finite prime filter theorem -/

theorem isMeetPrime_iff {m : Nat} : H.isMeetPrime m = true ↔
    m ≠ H.top ∧ ∀ a b, a < H.ord.n → b < H.ord.n →
      H.le (H.meet a b) m = true → H.le a m = true ∨ H.le b m = true := by
  unfold FinHA.isMeetPrime
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, fun a b ha hb hab => ?_⟩
    have e := List.all_eq_true.mp (List.all_eq_true.mp h2 a (mem_range_of_lt ha)) b
      (mem_range_of_lt hb)
    rw [hab] at e
    simpa using e
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, List.all_eq_true.mpr fun a ha =>
      List.all_eq_true.mpr fun b hb => ?_⟩
    cases e : H.le (H.meet a b) m
    · rfl
    · rcases h2 a b (List.mem_range.mp ha) (List.mem_range.mp hb) e with h | h <;> simp [h]

theorem Ax.not_top_le (hA : H.Ax) {m : Nat} (hm : m < H.ord.n) (hp : H.isMeetPrime m = true) :
    H.le H.top m = false := by
  cases e : H.le H.top m
  · rfl
  · exact absurd (hA.top_eq hm e) (isMeetPrime_iff.mp hp).1

theorem Ax.prime_meet (_hA : H.Ax) {m a b : Nat} (hp : H.isMeetPrime m = true)
    (ha : a < H.ord.n) (hb : b < H.ord.n) (h : H.le (H.meet a b) m = true) :
    H.le a m = true ∨ H.le b m = true :=
  (isMeetPrime_iff.mp hp).2 a b ha hb h

/-- **The finite prime filter theorem.**  If `a ≰ b`, some meet-prime `m`
has `b ≤ m` and `a ≰ m`. -/
theorem Ax.exists_prime (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n)
    (hab : H.le a b = false) :
    ∃ m, m < H.ord.n ∧ H.isMeetPrime m = true ∧ H.le b m = true ∧ H.le a m = false := by
  let C : Nat → Bool := fun x => H.le b x && !(H.le a x)
  have hCb : C b = true := by
    show (H.le b b && !(H.le a b)) = true
    rw [hA.refl hb, hab]; rfl
  obtain ⟨m, hm, hCm, -, hmax⟩ := FinOrd.exists_max hA.po C hb hCb
  have hCm' : H.le b m = true ∧ H.le a m = false := by
    have : (H.le b m && !(H.le a m)) = true := hCm
    simpa using this
  -- a candidate above `m` equals `m`
  have cand : ∀ y, y < H.ord.n → H.le m y = true → H.le a y = false → y = m :=
    fun y hy hmy hay => hmax y hy (by
      show (H.le b y && !(H.le a y)) = true
      rw [hA.trans hb hm hy hCm'.1 hmy, hay]; rfl) hmy
  -- `a → m = m`
  have ham : H.himp a m = m := by
    refine cand _ (hA.himp_lt ha hm) (hA.le_himp ha hm) ?_
    cases e : H.le a (H.himp a m)
    · rfl
    · exfalso
      rw [← hA.himp_adj ha hm ha] at e
      have := hA.trans ha (hA.meet_lt ha ha) hm (hA.le_meet_self ha) e
      rw [hCm'.2] at this
      exact Bool.noConfusion this
  refine ⟨m, hm, isMeetPrime_iff.mpr ⟨?_, ?_⟩, hCm'.1, hCm'.2⟩
  · intro hmt
    have := hA.le_top ha
    rw [← hmt, hCm'.2] at this
    exact Bool.noConfusion this
  · intro c d hc hd hcd
    cases hcm : H.le c m
    · right
      cases hach : H.le a (H.himp c m)
      · -- `c → m` is a candidate, so it is `m`
        have hcm' : H.himp c m = m := cand _ (hA.himp_lt hc hm) (hA.le_himp hc hm) hach
        have h1 : H.le (H.meet d c) m = true :=
          hA.trans (hA.meet_lt hd hc) (hA.meet_lt hc hd) hm (hA.meet_comm_le hd hc) hcd
        rw [hA.himp_adj hc hm hd, hcm'] at h1
        exact h1
      · exfalso
        rw [← hA.himp_adj hc hm ha] at hach
        have h1 : H.le (H.meet c a) m = true :=
          hA.trans (hA.meet_lt hc ha) (hA.meet_lt ha hc) hm (hA.meet_comm_le hc ha) hach
        rw [hA.himp_adj ha hm hc, ham, hcm] at h1
        exact Bool.noConfusion h1
    · left; rfl

/-- **Order reflection.**  `a ≤ b` iff every meet-prime above `b` is above `a`. -/
theorem Ax.le_of_primes (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n)
    (h : ∀ m, m < H.ord.n → H.isMeetPrime m = true → H.le b m = true → H.le a m = true) :
    H.le a b = true := by
  cases e : H.le a b
  · obtain ⟨m, hm, hp, hbm, ham⟩ := hA.exists_prime ha hb e
    rw [h m hm hp hbm] at ham
    exact ham.symm
  · rfl

theorem Ax.eq_of_primes (hA : H.Ax) {a b : Nat} (ha : a < H.ord.n) (hb : b < H.ord.n)
    (h : ∀ m, m < H.ord.n → H.isMeetPrime m = true → (H.le a m = true ↔ H.le b m = true)) :
    a = b :=
  hA.antisymm ha hb (hA.le_of_primes ha hb fun m hm hp => (h m hm hp).mpr)
    (hA.le_of_primes hb ha fun m hm hp => (h m hm hp).mp)

/-! ## 7. Iterated meets -/

/-- `⋀ l`. -/
def meetL (H : FinHA) (l : List Nat) : Nat := l.foldr H.meet H.top

theorem Ax.meetL_lt (hA : H.Ax) : ∀ {l : List Nat}, (∀ x ∈ l, x < H.ord.n) →
    H.meetL l < H.ord.n
  | [], _ => hA.top_lt
  | a :: _, h => hA.meet_lt (h a List.mem_cons_self)
      (hA.meetL_lt fun x hx => h x (List.mem_cons_of_mem a hx))

theorem Ax.meetL_le (hA : H.Ax) : ∀ {l : List Nat}, (∀ x ∈ l, x < H.ord.n) →
    ∀ {y}, y ∈ l → H.le (H.meetL l) y = true
  | [], _, _, hy => absurd hy List.not_mem_nil
  | a :: l, h, y, hy => by
      have hl : ∀ x ∈ l, x < H.ord.n := fun x hx => h x (List.mem_cons_of_mem a hx)
      have ha := h a List.mem_cons_self
      show H.le (H.meet a (H.meetL l)) y = true
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hA.meet_le_left ha (hA.meetL_lt hl)
      · exact hA.trans (hA.meet_lt ha (hA.meetL_lt hl)) (hA.meetL_lt hl) (hl y hy)
          (hA.meet_le_right ha (hA.meetL_lt hl)) (hA.meetL_le hl hy)

theorem Ax.le_meetL (hA : H.Ax) {x : Nat} (hx : x < H.ord.n) : ∀ {l : List Nat},
    (∀ y ∈ l, y < H.ord.n) → (∀ y ∈ l, H.le x y = true) → H.le x (H.meetL l) = true
  | [], _, _ => hA.le_top hx
  | a :: l, h, hle => by
      have hl : ∀ y ∈ l, y < H.ord.n := fun y hy => h y (List.mem_cons_of_mem a hy)
      exact hA.le_meet (h a List.mem_cons_self) (hA.meetL_lt hl) hx (hle a List.mem_cons_self)
        (hA.le_meetL hx hl fun y hy => hle y (List.mem_cons_of_mem a hy))

/-- A meet-prime above a finite meet is above one of its terms. -/
theorem Ax.prime_meetL (hA : H.Ax) {m : Nat} (hm : m < H.ord.n)
    (hp : H.isMeetPrime m = true) : ∀ {l : List Nat}, (∀ x ∈ l, x < H.ord.n) →
      H.le (H.meetL l) m = true → ∃ y ∈ l, H.le y m = true
  | [], _, h => by
      have h' : H.le H.top m = true := h
      rw [hA.not_top_le hm hp] at h'
      exact Bool.noConfusion h'
  | a :: l, hl, h => by
      have hl' : ∀ x ∈ l, x < H.ord.n := fun x hx => hl x (List.mem_cons_of_mem a hx)
      rcases hA.prime_meet hp (hl a List.mem_cons_self) (hA.meetL_lt hl') h with h1 | h1
      · exact ⟨a, List.mem_cons_self, h1⟩
      · obtain ⟨y, hy, hym⟩ := hA.prime_meetL hm hp hl' h1
        exact ⟨y, List.mem_cons_of_mem a hy, hym⟩

/-! ## 8. The dual: meet-primes, `α` -/

theorem mem_mprimes {m : Nat} : m ∈ H.mprimes ↔ m < H.ord.n ∧ H.isMeetPrime m = true := by
  unfold FinHA.mprimes
  rw [List.mem_filter]
  exact ⟨fun h => ⟨List.mem_range.mp h.1, h.2⟩, fun h => ⟨mem_range_of_lt h.1, h.2⟩⟩

/-- The `i`-th meet-prime. -/
abbrev mp (H : FinHA) (i : Nat) : Nat := H.mprimes.getD i 0

theorem mp_spec {i : Nat} (hi : i < H.mprimes.length) :
    H.mp i < H.ord.n ∧ H.isMeetPrime (H.mp i) = true :=
  mem_mprimes.mp (getD_mem hi)

theorem dual_n : H.dual.n = H.mprimes.length := rfl

theorem dual_le {i k : Nat} : H.dual.le i k = H.le (H.mp k) (H.mp i) := rfl

theorem mem_alpha {a i : Nat} (hi : i < H.mprimes.length) :
    mem (H.alpha a) i = !(H.le a (H.mp i)) := mem_map_range hi

theorem length_alpha {a : Nat} : (H.alpha a).length = H.mprimes.length := length_map_range

theorem mem_alpha_true {a i : Nat} (hi : i < H.mprimes.length) :
    mem (H.alpha a) i = true ↔ H.le a (H.mp i) = false := by
  rw [mem_alpha hi]
  cases H.le a (H.mp i) <;> simp

/-- `List.range n` has no duplicates (core's `List.nodup_range` reaches
`Classical.choice`). -/
theorem nodup_range' : ∀ n, (List.range n).Nodup
  | 0 => List.Pairwise.nil
  | n + 1 => by
      rw [List.range_succ]
      refine List.nodup_append.mpr ⟨nodup_range' n,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.Pairwise.nil⟩, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton.mp hb] at hab
      rw [hab] at ha
      exact Nat.lt_irrefl n (List.mem_range.mp ha)

theorem mprimes_nodup : H.mprimes.Nodup := FinOrd.nodup_filter (nodup_range' _)

theorem mp_inj {i k : Nat} (hi : i < H.mprimes.length) (hk : k < H.mprimes.length)
    (e : H.mp i = H.mp k) : i = k := by
  have e' : H.mprimes.getD i 0 = H.mprimes.getD k 0 := e
  rw [getD_eq_getElem hi, getD_eq_getElem hk] at e'
  exact nodup_getElem_inj mprimes_nodup hi hk e'

theorem Ax.dual_po (hA : H.Ax) : H.dual.PO :=
  ⟨fun hi => hA.refl (mp_spec hi).1,
    fun hi hk h1 h2 => mp_inj hi hk (hA.antisymm (mp_spec hi).1 (mp_spec hk).1 h2 h1),
    fun hi hj hk h1 h2 => hA.trans (mp_spec hk).1 (mp_spec hj).1 (mp_spec hi).1 h2 h1⟩

/-- Every meet-prime has an index. -/
theorem exists_mp {m : Nat} (hm : m < H.ord.n) (hp : H.isMeetPrime m = true) :
    ∃ i, i < H.mprimes.length ∧ H.mp i = m := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp (mem_mprimes.mpr ⟨hm, hp⟩)
  exact ⟨i, hi, by show H.mprimes.getD i 0 = m; rw [getD_eq_getElem hi]; exact e⟩

end FinHA

end EsakiaNuclear

/-! ## Pins -/

#axioms_within EsakiaNuclear.bits_ext [propext, Quot.sound]
#axioms_within EsakiaNuclear.mem_allSubs [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinOrd.upIdx_getD [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinOrd.exists_max [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinOrd.exists_min [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinHA.ax_of_isHA [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinHA.Ax.exists_prime [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinHA.Ax.eq_of_primes [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinHA.Ax.prime_meetL [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinHA.Ax.dual_po [propext, Quot.sound]
