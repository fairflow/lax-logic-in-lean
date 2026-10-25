import wip.esakiaNuclearFinProofs2

/-!
# Nuclear Esakia duality, finite case: proofs of F10a and F10 (Phase A)

Heyting homomorphisms and their duals: `h_*` is a p-morphism (F10a), and
`h` commutes with nuclei exactly when condition (∗) holds (F10, ours).
Choice-free.
-/

namespace EsakiaNuclear

namespace FinHA

variable {H : FinHA}

/-! ## Iterated joins -/

/-- `⋁ l`. -/
def joinL (H : FinHA) (l : List Nat) : Nat := l.foldr H.join H.bot

theorem Ax.joinL_lt (hA : H.Ax) : ∀ {l : List Nat}, (∀ x ∈ l, x < H.ord.n) →
    H.joinL l < H.ord.n
  | [], _ => hA.bot_lt
  | a :: _, h => hA.join_lt (h a List.mem_cons_self)
      (hA.joinL_lt fun x hx => h x (List.mem_cons_of_mem a hx))

theorem Ax.le_joinL (hA : H.Ax) : ∀ {l : List Nat}, (∀ x ∈ l, x < H.ord.n) →
    ∀ {y}, y ∈ l → H.le y (H.joinL l) = true
  | [], _, _, hy => absurd hy List.not_mem_nil
  | a :: l, h, y, hy => by
      have hl : ∀ x ∈ l, x < H.ord.n := fun x hx => h x (List.mem_cons_of_mem a hx)
      have ha := h a List.mem_cons_self
      show H.le y (H.join a (H.joinL l)) = true
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hA.le_join_left ha (hA.joinL_lt hl)
      · exact hA.trans (hl y hy) (hA.joinL_lt hl) (hA.join_lt ha (hA.joinL_lt hl))
          (hA.le_joinL hl hy) (hA.le_join_right ha (hA.joinL_lt hl))

theorem Ax.joinL_le (hA : H.Ax) {z : Nat} (hz : z < H.ord.n) : ∀ {l : List Nat},
    (∀ y ∈ l, y < H.ord.n) → (∀ y ∈ l, H.le y z = true) → H.le (H.joinL l) z = true
  | [], _, _ => hA.bot_le hz
  | a :: l, h, hle => by
      have hl : ∀ y ∈ l, y < H.ord.n := fun y hy => h y (List.mem_cons_of_mem a hy)
      exact hA.join_le (h a List.mem_cons_self) (hA.joinL_lt hl) hz (hle a List.mem_cons_self)
        (hA.joinL_le hz hl fun y hy => hle y (List.mem_cons_of_mem a hy))

/-! ## Heyting homomorphisms -/

/-- What `isHAHom` asserts, unpacked. -/
structure Hom (A B : FinHA) (h : Nat → Nat) : Prop where
  lt : ∀ {a}, a < A.ord.n → h a < B.ord.n
  top : h A.top = B.top
  bot : h A.bot = B.bot
  meet : ∀ {a b}, a < A.ord.n → b < A.ord.n → h (A.meet a b) = B.meet (h a) (h b)
  join : ∀ {a b}, a < A.ord.n → b < A.ord.n → h (A.join a b) = B.join (h a) (h b)
  himp : ∀ {a b}, a < A.ord.n → b < A.ord.n → h (A.himp a b) = B.himp (h a) (h b)

theorem hom_of_isHAHom {A B : FinHA} {h : Nat → Nat} (hh : isHAHom A B h = true) :
    Hom A B h := by
  unfold isHAHom at hh
  simp only [Bool.and_eq_true, beq_iff_eq] at hh
  obtain ⟨⟨⟨hlt, htop⟩, hbot⟩, hops⟩ := hh
  have ops : ∀ a b, a < A.ord.n → b < A.ord.n →
      (h (A.meet a b) = B.meet (h a) (h b) ∧ h (A.join a b) = B.join (h a) (h b)) ∧
        h (A.himp a b) = B.himp (h a) (h b) := fun a b ha hb => by
    have := List.all_eq_true.mp (List.all_eq_true.mp hops a (mem_range_of_lt ha)) b
      (mem_range_of_lt hb)
    simpa only [Bool.and_eq_true, beq_iff_eq] using this
  exact ⟨fun ha => by simpa using List.all_eq_true.mp hlt _ (mem_range_of_lt ha), htop, hbot,
    fun ha hb => (ops _ _ ha hb).1.1, fun ha hb => (ops _ _ ha hb).1.2,
    fun ha hb => (ops _ _ ha hb).2⟩

variable {A B : FinHA} {h : Nat → Nat}

theorem Hom.mono (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) {a b : Nat} (ha : a < A.ord.n)
    (hb : b < A.ord.n) (hab : A.le a b = true) : B.le (h a) (h b) = true := by
  have e := hh.meet ha hb
  rw [hA.meet_eq_left ha hb hab] at e
  rw [e]
  exact hB.meet_le_right (hh.lt ha) (hh.lt hb)

theorem Hom.joinL (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) : ∀ {l : List Nat},
    (∀ x ∈ l, x < A.ord.n) → h (A.joinL l) = B.joinL (l.map h)
  | [], _ => hh.bot
  | a :: l, hl => by
      have hl' : ∀ x ∈ l, x < A.ord.n := fun x hx => hl x (List.mem_cons_of_mem a hx)
      show h (A.join a (A.joinL l)) = B.join (h a) (B.joinL (l.map h))
      rw [hh.join (hl a List.mem_cons_self) (hA.joinL_lt hl'), hh.joinL hB hA hl']

/-- `h_*(y)` is the greatest `a` with `h a ≤ y`. -/
theorem Hom.hstar_spec (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) {y : Nat} (hy : y < B.ord.n) :
    hstar A B h y < A.ord.n ∧ B.le (h (hstar A B h y)) y = true ∧
      ∀ b, b < A.ord.n → B.le (h b) y = true → A.le b (hstar A B h y) = true := by
  let L := A.pts.filter fun a => B.le (h a) y
  have hL : ∀ {a}, a ∈ L ↔ a < A.ord.n ∧ B.le (h a) y = true := by
    intro a
    rw [List.mem_filter]
    exact ⟨fun h => ⟨List.mem_range.mp h.1, h.2⟩, fun h => ⟨mem_range_of_lt h.1, h.2⟩⟩
  have hLlt : ∀ x ∈ L, x < A.ord.n := fun x hx => (hL.mp hx).1
  have hLh : ∀ x ∈ L.map h, x < B.ord.n := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact hh.lt (hLlt a ha)
  have hstarL : B.le (h (A.joinL L)) y = true := by
    rw [hh.joinL hB hA hLlt]
    refine hB.joinL_le hy hLh fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact (hL.mp ha).2
  have hex : ∃ a ∈ A.pts, (B.le (h a) y && A.pts.all fun b => !(B.le (h b) y) || A.le b a)
      = true := by
    refine ⟨A.joinL L, mem_range_of_lt (hA.joinL_lt hLlt), ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨hstarL, List.all_eq_true.mpr fun b hb => bool_imp1 fun hby =>
      hA.le_joinL hLlt (hL.mpr ⟨List.mem_range.mp hb, hby⟩)⟩
  obtain ⟨c, hc, hcm, hcp⟩ := find?_of_exists hex
  unfold hstar
  rw [hc, Option.getD_some]
  rw [Bool.and_eq_true] at hcp
  exact ⟨List.mem_range.mp hcm, hcp.1, fun b hb hby =>
    bor_not (List.all_eq_true.mp hcp.2 b (mem_range_of_lt hb)) hby⟩

/-- The adjunction `h a ≤ y ↔ a ≤ h_*(y)`. -/
theorem Hom.adj (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) {a y : Nat} (ha : a < A.ord.n)
    (hy : y < B.ord.n) : B.le (h a) y = A.le a (hstar A B h y) := by
  have hs := hh.hstar_spec hB hA hy
  rw [Bool.eq_iff_iff]
  exact ⟨hs.2.2 a ha, fun hle => hB.trans (hh.lt ha) (hh.lt hs.1) hy
    (hh.mono hB hA ha hs.1 hle) hs.2.1⟩

/-- `h_*` maps meet-primes to meet-primes. -/
theorem Hom.hstar_prime (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) {x : Nat} (hx : x < B.ord.n)
    (hp : B.isMeetPrime x = true) : A.isMeetPrime (hstar A B h x) = true := by
  have hs := hh.hstar_spec hB hA hx
  refine isMeetPrime_iff.mpr ⟨fun ht => ?_, fun c d hc hd hcd => ?_⟩
  · have e := hh.adj hB hA hA.top_lt hx
    rw [ht, hA.refl hA.top_lt, hh.top, hB.not_top_le hx hp] at e
    exact Bool.noConfusion e
  · rw [← hh.adj hB hA (hA.meet_lt hc hd) hx, hh.meet hc hd] at hcd
    rcases hB.prime_meet hp (hh.lt hc) (hh.lt hd) hcd with h1 | h1
    · exact Or.inl (by rw [← hh.adj hB hA hc hx]; exact h1)
    · exact Or.inr (by rw [← hh.adj hB hA hd hx]; exact h1)

/-- The least element of `{b | b ≰ x}` for a meet-prime `x`. -/
def low (B : FinHA) (x : Nat) : Nat := B.meetL (B.pts.filter fun b => !(B.le b x))

theorem Ax.low_spec (hB : B.Ax) {x : Nat} (hx : x < B.ord.n) (hp : B.isMeetPrime x = true) :
    B.low x < B.ord.n ∧ B.le (B.low x) x = false ∧
      ∀ b, b < B.ord.n → B.le b x = false → B.le (B.low x) b = true := by
  let L := B.pts.filter fun b => !(B.le b x)
  have hL : ∀ {b}, b ∈ L ↔ b < B.ord.n ∧ B.le b x = false := by
    intro b
    rw [List.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨List.mem_range.mp h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨mem_range_of_lt h1, by rw [h2]; rfl⟩
  have hLlt : ∀ b ∈ L, b < B.ord.n := fun b hb => (hL.mp hb).1
  refine ⟨hB.meetL_lt hLlt, ?_, fun b hb hbx => hB.meetL_le hLlt (hL.mpr ⟨hb, hbx⟩)⟩
  cases e : B.le (B.low x) x
  · rfl
  · exfalso
    obtain ⟨y, hy, hyx⟩ := hB.prime_meetL hx hp hLlt e
    rw [(hL.mp hy).2] at hyx
    exact Bool.noConfusion hyx

/-- **The back condition** of a p-morphism, for `h_*`. -/
theorem Hom.back (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) {x y : Nat} (hx : x < B.ord.n)
    (hxp : B.isMeetPrime x = true) (hy : y < A.ord.n) (hyp : A.isMeetPrime y = true)
    (hyx : A.le y (hstar A B h x) = true) :
    ∃ z, z < B.ord.n ∧ B.isMeetPrime z = true ∧ B.le z x = true ∧ hstar A B h z = y := by
  obtain ⟨hq, hqx, hqmin⟩ := hB.low_spec hx hxp
  obtain ⟨hp, hpy, hpmin⟩ := hA.low_spec hy hyp
  have hhp := hh.lt hp
  have hhy := hh.lt hy
  have hs := hh.hstar_spec hB hA hx
  -- `low x ∧ h(low y) ≰ h y`
  have hdis : B.le (B.meet (B.low x) (h (A.low y))) (h y) = false := by
    cases e : B.le (B.meet (B.low x) (h (A.low y))) (h y)
    · rfl
    · exfalso
      rw [hB.himp_adj hhp hhy hq, ← hh.himp hp hy] at e
      have hpy' := hA.himp_lt hp hy
      -- `h(p → y) ≰ x`, so `p → y ≰ h_* x`, so `p → y ≰ y`
      have h1 : B.le (h (A.himp (A.low y) y)) x = false := by
        cases e' : B.le (h (A.himp (A.low y) y)) x
        · rfl
        · rw [hB.trans hq (hh.lt hpy') hx e e'] at hqx; exact hqx
      rw [hh.adj hB hA hpy' hx] at h1
      have h2 : A.le (A.himp (A.low y) y) y = false := by
        cases e' : A.le (A.himp (A.low y) y) y
        · rfl
        · rw [hA.trans hpy' hy hs.1 e' hyx] at h1; exact h1
      rcases hA.prime_meet hyp hpy' hp (hA.meet_himp_le hp hy) with h3 | h3
      · rw [h2] at h3; exact Bool.noConfusion h3
      · rw [hpy] at h3; exact Bool.noConfusion h3
  obtain ⟨z, hz, hzp, hyz, hqz⟩ := hB.exists_prime (hB.meet_lt hq hhp) hhy hdis
  have hq_z : B.le (B.low x) z = false := by
    cases e : B.le (B.low x) z
    · rfl
    · rw [hB.trans (hB.meet_lt hq hhp) hq hz (hB.meet_le_left hq hhp) e] at hqz
      exact hqz
  have hp_z : B.le (h (A.low y)) z = false := by
    cases e : B.le (h (A.low y)) z
    · rfl
    · rw [hB.trans (hB.meet_lt hq hhp) hhp hz (hB.meet_le_right hq hhp) e] at hqz
      exact hqz
  have hzx : B.le z x = true := by
    cases e : B.le z x
    · rw [hqmin z hz e] at hq_z; exact Bool.noConfusion hq_z
    · rfl
  have hsz := hh.hstar_spec hB hA hz
  refine ⟨z, hz, hzp, hzx, hA.antisymm hsz.1 hy ?_ (by rw [← hh.adj hB hA hy hz]; exact hyz)⟩
  cases e : A.le (hstar A B h z) y
  · have := hpmin _ hsz.1 e
    rw [← hh.adj hB hA hp hz, hp_z] at this
    exact this
  · rfl

/-! ## F10a -/

theorem Hom.pmorph (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) : PMorph A B h := by
  refine ⟨fun x hx => ?_, fun x hx x' hx' hle => ?_, fun x hx y hy hyx => ?_,
    fun a ha x hx => ?_⟩
  · obtain ⟨h1, h2⟩ := mem_mprimes.mp hx
    exact hh.hstar_prime hB hA h1 h2
  · have hx1 := (mem_mprimes.mp hx).1
    have hx1' := (mem_mprimes.mp hx').1
    have hs' := hh.hstar_spec hB hA hx1'
    rw [← hh.adj hB hA hs'.1 hx1]
    exact hB.trans (hh.lt hs'.1) hx1' hx1 hs'.2.1 hle
  · obtain ⟨hx1, hx2⟩ := mem_mprimes.mp hx
    obtain ⟨hy1, hy2⟩ := mem_mprimes.mp hy
    obtain ⟨z, hz, hzp, hzx, hzy⟩ := hh.back hB hA hx1 hx2 hy1 hy2 hyx
    exact ⟨z, mem_mprimes.mpr ⟨hz, hzp⟩, hzx, hzy⟩
  · exact hh.adj hB hA (List.mem_range.mp ha) (mem_mprimes.mp hx).1

end FinHA

/-- **F10a** (PROVED). -/
theorem f10a : F10a := fun _ _ _ hA hB hh =>
  (FinHA.hom_of_isHAHom hh).pmorph (FinHA.ax_of_isHA hB) (FinHA.ax_of_isHA hA)

/-! ## F10 -/

namespace FinHA

variable {A B : FinHA} {h j k : Nat → Nat}

/-- `h (j a) ≤ x` iff a `j`-fixed meet-prime below `h_*(x)` lies above `a`. -/
theorem Hom.left_iff (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) (hj : A.Nuc j) {a x : Nat}
    (ha : a < A.ord.n) (hx : x < B.ord.n) (hxp : B.isMeetPrime x = true) :
    B.le (h (j a)) x = true ↔ ∃ z ∈ A.mprimes, A.le z (hstar A B h x) = true ∧ j z = z ∧
      A.le a z = true := by
  have hs := hh.hstar_spec hB hA hx
  rw [hh.adj hB hA (hj.lt ha) hx,
    hA.nuc_le_prime_iff hj ha hs.1 (hh.hstar_prime hB hA hx hxp)]
  constructor
  · rintro ⟨z, hz, hzp, h1, h2, h3⟩; exact ⟨z, mem_mprimes.mpr ⟨hz, hzp⟩, h1, h2, h3⟩
  · rintro ⟨z, hz, h1, h2, h3⟩
    obtain ⟨hz1, hz2⟩ := mem_mprimes.mp hz
    exact ⟨z, hz1, hz2, h1, h2, h3⟩

/-- `k (h a) ≤ x` iff a `k`-fixed meet-prime `s ≤ x` has `a ≤ h_*(s)`. -/
theorem Hom.right_iff (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) (hk : B.Nuc k) {a x : Nat}
    (ha : a < A.ord.n) (hx : x < B.ord.n) (hxp : B.isMeetPrime x = true) :
    B.le (k (h a)) x = true ↔ ∃ s ∈ B.mprimes, B.le s x = true ∧ k s = s ∧
      A.le a (hstar A B h s) = true := by
  rw [hB.nuc_le_prime_iff hk (hh.lt ha) hx hxp]
  constructor
  · rintro ⟨s, hs, hsp, h1, h2, h3⟩
    exact ⟨s, mem_mprimes.mpr ⟨hs, hsp⟩, h1, h2, by rw [← hh.adj hB hA ha hs]; exact h3⟩
  · rintro ⟨s, hs, h1, h2, h3⟩
    obtain ⟨hs1, hs2⟩ := mem_mprimes.mp hs
    exact ⟨s, hs1, hs2, h1, h2, by rw [hh.adj hB hA ha hs1]; exact h3⟩

theorem Hom.nuclear (hB : B.Ax) (hA : A.Ax) (hh : Hom A B h) (hj : A.Nuc j) (hk : B.Nuc k) :
    NuclearHom A B j k h := by
  -- the two sides of (∗), as propositions
  have hL : ∀ x t, (A.mprimes.any fun z =>
      A.le z (hstar A B h x) && j z == z && A.le t z) = true ↔
      ∃ z ∈ A.mprimes, A.le z (hstar A B h x) = true ∧ j z = z ∧ A.le t z = true := by
    intro x t
    rw [List.any_eq_true]
    constructor
    · rintro ⟨z, hz, hp⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact ⟨z, hz, hp.1.1, hp.1.2, hp.2⟩
    · rintro ⟨z, hz, h1, h2, h3⟩
      exact ⟨z, hz, by rw [h1, h3, beq_iff_eq.mpr h2]; rfl⟩
  have hR : ∀ x t, (B.mprimes.any fun s =>
      B.le s x && k s == s && A.le t (hstar A B h s)) = true ↔
      ∃ s ∈ B.mprimes, B.le s x = true ∧ k s = s ∧ A.le t (hstar A B h s) = true := by
    intro x t
    rw [List.any_eq_true]
    constructor
    · rintro ⟨s, hs, hp⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact ⟨s, hs, hp.1.1, hp.1.2, hp.2⟩
    · rintro ⟨s, hs, h1, h2, h3⟩
      exact ⟨s, hs, by rw [h1, h3, beq_iff_eq.mpr h2]; rfl⟩
  show (A.pts.all fun a => h (j a) == k (h a)) = starCond A B j k h
  unfold starCond
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro hn x hx
    obtain ⟨hx1, hx2⟩ := mem_mprimes.mp hx
    refine List.all_eq_true.mpr fun t ht => ?_
    have ht1 := (mem_mprimes.mp ht).1
    have e := beq_iff_eq.mp (hn t (mem_range_of_lt ht1))
    rw [beq_iff_eq, Bool.eq_iff_iff, hL, hR, ← hh.left_iff hB hA hj ht1 hx1 hx2,
      ← hh.right_iff hB hA hk ht1 hx1 hx2, e]
  · intro hs a ha
    have ha' := List.mem_range.mp ha
    have hst : ∀ x ∈ B.mprimes, ∀ t ∈ A.mprimes,
        ((∃ z ∈ A.mprimes, A.le z (hstar A B h x) = true ∧ j z = z ∧ A.le t z = true) ↔
         (∃ s ∈ B.mprimes, B.le s x = true ∧ k s = s ∧ A.le t (hstar A B h s) = true)) := by
      intro x hx t ht
      rw [← hL, ← hR]
      exact Bool.eq_iff_iff.mp (beq_iff_eq.mp (List.all_eq_true.mp (hs x hx) t ht))
    refine beq_iff_eq.mpr (hB.eq_of_primes (hh.lt (hj.lt ha')) (hk.lt (hh.lt ha'))
      fun x hx hxp => ?_)
    have hxm : x ∈ B.mprimes := mem_mprimes.mpr ⟨hx, hxp⟩
    rw [hh.left_iff hB hA hj ha' hx hxp, hh.right_iff hB hA hk ha' hx hxp]
    constructor
    · rintro ⟨z, hz, h1, h2, h3⟩
      obtain ⟨s, hs', g1, g2, g3⟩ := (hst x hxm z hz).mp
        ⟨z, hz, h1, h2, hA.refl (mem_mprimes.mp hz).1⟩
      exact ⟨s, hs', g1, g2, hA.trans ha' (mem_mprimes.mp hz).1
        (hh.hstar_spec hB hA (mem_mprimes.mp hs').1).1 h3 g3⟩
    · rintro ⟨s, hs', h1, h2, h3⟩
      have hs1 := (mem_mprimes.mp hs').1
      have hgs := hh.hstar_spec hB hA hs1
      have hgm : hstar A B h s ∈ A.mprimes :=
        mem_mprimes.mpr ⟨hgs.1, hh.hstar_prime hB hA hs1 (mem_mprimes.mp hs').2⟩
      obtain ⟨z, hz, g1, g2, g3⟩ := (hst x hxm _ hgm).mpr
        ⟨s, hs', h1, h2, hA.refl hgs.1⟩
      exact ⟨z, hz, g1, g2, hA.trans ha' hgs.1 (mem_mprimes.mp hz).1 h3 g3⟩

end FinHA

/-- **F10** (PROVED). -/
theorem f10 : F10 := fun _ _ _ _ _ hA hB hj hk hh =>
  (FinHA.hom_of_isHAHom hh).nuclear (FinHA.ax_of_isHA hB) (FinHA.ax_of_isHA hA)
    (FinHA.nuc_of_isNucleus hj) (FinHA.nuc_of_isNucleus hk)

end EsakiaNuclear

#axioms_within EsakiaNuclear.f10a [propext, Quot.sound]
#axioms_within EsakiaNuclear.f10 [propext, Quot.sound]
