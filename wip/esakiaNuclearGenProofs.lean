import wip.esakiaNuclearGenBase

/-!
# Nuclear Esakia duality, general case: G1–G4 and R5 PROVED (Phase B)

Statements: `wip/esakiaNuclearGen.lean`, unchanged.  Kit:
`wip/esakiaNuclearGenBase.lean`.  Classical; pins
`[propext, Classical.choice, Quot.sound]`.
-/

namespace EsakiaNuclear.Gen

open Set

/-! ## G1: Esakia duality, objects -/

theorem esakiaObjects (A : Type*) [HeytingAlgebra A] : EsakiaObjects A :=
  ⟨⟨inferInstance, inferInstance, fun _ hU => isClopen_lowerClosure hU⟩,
    phi_injective, fun a => ⟨isClopen_phi a, phi_upper a⟩,
    fun _ hU hup => exists_phi_of_clopen_upper hU hup,
    phi_inf, phi_sup, phi_top, phi_bot, phi_himp⟩

/-- **G1** (Esakia 1974; [ABMZ] Thm 3.5, objects). -/
theorem g1 : G1 := fun A _ => esakiaObjects A

/-! ## Nuclei and nuclear subsets -/

variable {A : Type*} [HeytingAlgebra A]

theorem mem_compl_lower {N : Set (Spec A)} {a : A} {x : Spec A} :
    x ∈ (lowerClosure (N \ phi a) : Set (Spec A))ᶜ ↔ ∀ y ∈ N, x ≤ y → a ∈ y.carrier := by
  rw [mem_compl_iff, mem_lowerClosure_iff]
  constructor
  · intro h y hy hxy
    by_contra ha
    exact h ⟨y, ⟨hy, ha⟩, hxy⟩
  · rintro h ⟨y, ⟨hy, ha⟩, hxy⟩
    exact ha (h y hy hxy)

/-- A nucleus is represented by its nuclear subset:
`φ(j a) = X ∖ ↓(N_j ∖ φ a)` (prime filter theorem in `A_j`). -/
theorem phi_nucleus (j : Nucleus A) (a : A) :
    phi (j a) = (lowerClosure (Nj j \ phi a) : Set (Spec A))ᶜ := by
  ext x
  rw [mem_compl_lower]
  constructor
  · intro hx y hy hxy
    exact mem_Nj.mp hy a (hxy hx)
  · intro h
    by_contra hx
    have hx' : ⊤ ⇨ j a ∉ x.carrier := by rw [top_himp]; exact hx
    obtain ⟨y, hxy, hy, -, hay⟩ := exists_spec_nuclear j x hx'
    exact hay (h y hy hxy)

/-- `↓(φ a ∩ φ(b)ᶜ ∩ N_j) = X ∖ φ(a → j b)`. -/
theorem lower_basic_nuclear (j : Nucleus A) (a b : A) :
    (lowerClosure (phi a ∩ (phi b)ᶜ ∩ Nj j) : Set (Spec A)) = (phi (a ⇨ j b))ᶜ := by
  ext x
  rw [mem_lowerClosure_iff, mem_compl_iff]
  constructor
  · rintro ⟨y, ⟨⟨hay, hby⟩, hy⟩, hxy⟩ hx
    exact hby (mem_Nj.mp hy b (y.mem_of_le' inf_himp_le (y.inf_mem' hay (hxy hx))))
  · intro hx
    obtain ⟨y, hxy, hy, hay, hby⟩ := exists_spec_nuclear j x hx
    exact ⟨y, ⟨⟨hay, hby⟩, hy⟩, hxy⟩

theorem isClosed_Nj (j : Nucleus A) : IsClosed (Nj j) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  have hn : ¬ ∀ c, j c ∈ x.carrier → c ∈ x.carrier := fun h => hx (mem_Nj.mpr h)
  push Not at hn
  obtain ⟨c, hjc, hc⟩ := hn
  exact ⟨phi (j c) ∩ (phi c)ᶜ, fun z hz hzN => hz.2 (mem_Nj.mp hzN c hz.1),
    (isOpen_phi _).inter (isOpen_phi_compl _), hjc, hc⟩

/-- `N_j` is a nuclear subset. -/
theorem isNuclear_Nj (j : Nucleus A) : IsNuclear (Nj j) := by
  refine ⟨isClosed_Nj j, fun U hU => ?_⟩
  obtain ⟨s, hs, rfl⟩ := clopen_eq_union hU
  rw [iUnion₂_inter, lowerClosure_biUnion]
  refine hs.isClopen_biUnion fun p _ => ?_
  rw [lower_basic_nuclear]
  exact (isClopen_phi _).compl

/-! ## G2: [BG] Thm 30 -/

theorem bgThm30 (A : Type*) [HeytingAlgebra A] : BGThm30 A := by
  refine ⟨isNuclear_Nj, fun N hN => ?_, fun j N hN hj => ?_, fun j k => ?_⟩
  · -- (ii) the nucleus of a nuclear subset
    have hD : ∀ a : A, ∃ c : A, phi c = (lowerClosure (N \ phi a) : Set (Spec A))ᶜ := by
      intro a
      refine exists_phi_of_clopen_upper ?_ (lowerClosure (N \ phi a)).lower.compl
      have e : N \ phi a = (phi a)ᶜ ∩ N := by rw [sdiff_eq, inter_comm]
      rw [e]
      exact (hN.2 _ (isClopen_phi a).compl).compl
    choose f hf using hD
    refine ⟨⟨⟨f, fun a b => ?_⟩, fun a => ?_, fun a => ?_⟩, hf⟩
    · show f (a ⊓ b) = f a ⊓ f b
      apply phi_injective
      rw [hf, phi_inf (f a) (f b), hf, hf]
      ext x
      rw [mem_inter_iff, mem_compl_lower, mem_compl_lower, mem_compl_lower]
      constructor
      · intro h
        exact ⟨fun y hy hxy => y.mem_of_le' inf_le_left (h y hy hxy),
          fun y hy hxy => y.mem_of_le' inf_le_right (h y hy hxy)⟩
      · rintro ⟨h1, h2⟩ y hy hxy
        exact y.inf_mem' (h1 y hy hxy) (h2 y hy hxy)
    · show f (f a) ≤ f a
      apply phi_subset_iff.mp
      intro x hx
      rw [hf, mem_compl_lower] at hx ⊢
      intro y hy hxy
      have h1 : y ∈ phi (f a) := hx y hy hxy
      rw [hf, mem_compl_lower] at h1
      exact h1 y hy le_rfl
    · show a ≤ f a
      apply phi_subset_iff.mp
      intro x hx
      rw [hf, mem_compl_lower]
      intro y _ hxy
      exact hxy hx
  · -- (iii) the nuclear subset of `j_N` is `N`
    ext x
    constructor
    · intro hx
      by_contra hxN
      obtain ⟨v, ⟨c, d, rfl⟩, hxv, hvN⟩ :=
        isBasis.exists_subset_of_mem_open hxN hN.1.isOpen_compl
      have hcd : c ⇨ d ∉ x.carrier := fun h =>
        hxv.2 (x.mem_of_le' inf_himp_le (x.inf_mem' hxv.1 h))
      have hj' : x ∈ phi (j (c ⇨ d)) := by
        rw [hj, mem_compl_lower]
        intro y hy hxy
        have hcy : c ∈ y.carrier := hxy hxv.1
        have hdy : d ∈ y.carrier := by
          by_contra hd
          exact hvN ⟨hcy, hd⟩ hy
        exact y.mem_of_le' le_himp hdy
      exact hcd (mem_Nj.mp hx _ hj')
    · intro hx
      refine mem_Nj.mpr fun c hc => ?_
      have h1 : x ∈ phi (j c) := hc
      rw [hj, mem_compl_lower] at h1
      exact h1 x hx le_rfl
  · -- (iv) order reversal
    constructor
    · intro hjk x hx
      exact mem_Nj.mpr fun c hc => mem_Nj.mp hx c (x.mem_of_le' (Nucleus.coe_le_coe.mpr hjk c) hc)
    · intro hN
      refine Nucleus.coe_le_coe.mp fun c => ?_
      apply phi_subset_iff.mp
      rw [phi_nucleus j, phi_nucleus k]
      intro x hx
      rw [mem_compl_lower] at hx ⊢
      exact fun y hy hxy => hx y (hN hy) hxy

/-- **G2** ([BG] Thm 30 = [ABMZ] Thm 4.3). -/
theorem g2 : G2 := fun A _ => bgThm30 A

/-! ## G3: [BG] Cor 31 -/

theorem bgCor31 (A : Type*) [HeytingAlgebra A] : BGCor31 A := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j k m hm => ?_⟩
  · exact eq_univ_of_forall fun x => mem_Nj.mpr fun c hc => by rw [hj] at hc; exact hc
  · refine eq_empty_of_forall_notMem fun x hx => x.isPrime.bot_not_mem (mem_Nj.mp hx ⊥ ?_)
    rw [hj]
    exact x.top_mem'
  · ext x
    rw [mem_union, mem_Nj, mem_Nj, mem_Nj]
    constructor
    · intro h
      by_contra hn
      push Not at hn
      obtain ⟨⟨c, hjc, hc⟩, ⟨d, hkd, hd⟩⟩ := hn
      have hm' : m (c ⊔ d) ∈ x.carrier := by
        rw [hm]
        exact x.inf_mem' (x.mem_of_le' (nmono (j := j) le_sup_left) hjc)
          (x.mem_of_le' (nmono (j := k) le_sup_right) hkd)
      rcases x.isPrime.mem_or_mem (h _ hm') with h' | h'
      · exact hc h'
      · exact hd h'
    · rintro (h | h) c hc
      · have hle : m c ≤ j c := by rw [hm]; exact inf_le_left
        exact h c (x.mem_of_le' hle hc)
      · have hle : m c ≤ k c := by rw [hm]; exact inf_le_right
        exact h c (x.mem_of_le' hle hc)

/-- **G3** ([BG] Cor 31). -/
theorem g3 : G3 := fun A _ => bgCor31 A

/-! ## G4: [BG] Thm 34 -/

theorem bgThm34 (A : Type*) [HeytingAlgebra A] : BGThm34 A := by
  intro a j
  refine ⟨fun hj => ?_, fun hj => ?_, fun hj => ?_⟩
  · -- closed nucleus `a ∨ –`
    ext x
    rw [mem_Nj, mem_compl_iff, mem_phi]
    constructor
    · intro h ha
      have h1 : j ⊥ ∈ x.carrier := by rw [hj, sup_bot_eq]; exact ha
      exact x.isPrime.bot_not_mem (h ⊥ h1)
    · intro ha c hc
      rw [hj] at hc
      rcases x.isPrime.mem_or_mem hc with h | h
      · exact absurd h ha
      · exact h
  · -- open nucleus `a → –`
    ext x
    rw [mem_Nj, mem_phi]
    constructor
    · intro h
      apply h a
      rw [hj, himp_self]
      exact x.top_mem'
    · intro ha c hc
      rw [hj] at hc
      exact x.mem_of_le' inf_himp_le (x.inf_mem' ha hc)
  · -- the nucleus `(– → a) → a`
    ext x
    rw [mem_Nj]
    constructor
    · intro h
      have hax : a ∉ x.carrier := by
        intro ha
        apply x.isPrime.bot_not_mem
        apply h ⊥
        rw [hj, bot_himp, top_himp]
        exact ha
      refine ⟨hax, fun y hy hxy => le_antisymm (Spec.le_def.mpr fun c hcy => ?_) hxy⟩
      by_contra hcx
      have hdy : c ⇨ a ∉ y.carrier := fun hd =>
        hy (y.mem_of_le' inf_himp_le (y.inf_mem' hcy hd))
      have e : (c ⊔ (c ⇨ a)) ⇨ a = a := by
        rw [sup_himp_distrib]
        exact le_antisymm inf_himp_le (le_inf le_himp le_himp)
      have hjcd : j (c ⊔ (c ⇨ a)) ∈ x.carrier := by
        rw [hj, e, himp_self]
        exact x.top_mem'
      rcases x.isPrime.mem_or_mem (h _ hjcd) with h' | h'
      · exact hcx h'
      · exact hdy (hxy h')
    · rintro ⟨hax, hmax⟩ c hc
      by_contra hcx
      rw [hj] at hc
      have hca : c ⇨ a ∉ x.carrier := fun h' =>
        hax (x.mem_of_le' inf_himp_le (x.inf_mem' h' hc))
      obtain ⟨y, hxy, hcy, hay⟩ := exists_spec_himp x hca
      have hyx : y = x := hmax y hay hxy
      rw [hyx] at hcy
      exact hcx hcy

/-- **G4** ([BG] Thm 34 = [ABMZ] Thm 4.4). -/
theorem g4 : G4 := fun A _ => bgThm34 A

end EsakiaNuclear.Gen

/-! ## R5: the designed infinite cell -/

namespace EsakiaNuclear.Bridge

open Set PLLND

theorem omega_HC_gt (w : Nat) : ConstraintModel.HC omegaChain {n | w < n} :=
  ⟨fun hxy hx => Nat.lt_of_lt_of_le hx hxy, fun _ h => False.elim h⟩

theorem r5 : R5 := by
  refine ⟨fun w h => ?_, fun S => ?_, ⟨fun U hU => hU.1, ?_, ?_, ?_, ?_, ?_⟩,
    fun U hU => ?_, fun w e => ?_⟩
  · -- (a) no world is Rₘ-final
    exact Nat.not_succ_le_self w (h (Nat.succ w) (Nat.le_succ w))
  · -- (b) no `S` represents `j_C`
    rcases S.eq_empty_or_nonempty with rfl | ⟨m, hm⟩
    · refine ⟨∅, ⟨fun _ h => False.elim h, fun _ h => False.elim h⟩, fun e => ?_⟩
      have h0 : (0 : Nat) ∈ {x : Nat | ∀ y, x ≤ y → y ∈ (∅ : Set Nat) → y ∈ (∅ : Set Nat)} :=
        fun _ _ h => h
      have h1 : (0 : Nat) ∈ ConstraintModel.jC omegaChain ∅ := e ▸ h0
      obtain ⟨u, _, hu⟩ := h1 (0 : Nat) (Nat.le_refl 0)
      exact hu
    · refine ⟨{n | m < n}, omega_HC_gt m, fun e => ?_⟩
      have hm' : m ∈ ConstraintModel.jC omegaChain {n | m < n} :=
        fun v hv => ⟨Nat.succ v, Nat.le_succ v, Nat.lt_succ_of_le hv⟩
      have h2 : m ∈ {x : Nat | ∀ y, x ≤ y → y ∈ S → y ∈ {n | m < n}} := e ▸ hm'
      exact Nat.lt_irrefl m (h2 m (Nat.le_refl m) hm)
  · -- (c) `x_∞` is a prime filter of `H_C`
    exact ⟨⟨fun _ _ => trivial, fun _ _ => trivial⟩, ⟨0, trivial⟩⟩
  · rintro ⟨_, n, hn⟩
    exact hn
  · intro U V hV hU hUV
    exact ⟨hV, hU.2.mono hUV⟩
  · rintro U ⟨hU, m, hm⟩ V ⟨hV, n, hn⟩
    exact ⟨⟨fun hxy hx => ⟨hU.1 hxy hx.1, hV.1 hxy hx.2⟩, fun _ h => False.elim h⟩,
      max m n, hU.1 (Nat.le_max_left m n) hm, hV.1 (Nat.le_max_right m n) hn⟩
  · rintro U V hU hV ⟨_, n, hn⟩
    rcases hn with hn | hn
    · exact Or.inl ⟨hU, n, hn⟩
    · exact Or.inr ⟨hV, n, hn⟩
  · -- `x_∞` is fixed by `j_C`
    constructor
    · rintro ⟨_, w, hw⟩
      obtain ⟨u, _, hu⟩ := hw w (Nat.le_refl w)
      exact ⟨hU, u, hu⟩
    · rintro ⟨_, m, hm⟩
      refine ⟨⟨fun hxy hx v hyv => hx v (Nat.le_trans hxy hyv), fun _ h => False.elim h⟩,
        0, fun v _ => ⟨Nat.max v m, Nat.le_max_left v m, hU.1 (Nat.le_max_right v m) hm⟩⟩
  · -- `x_∞` is not principal
    have hw : {n : Nat | w < n} ∈ xInf := ⟨omega_HC_gt w, w + 1, Nat.lt_succ_self w⟩
    rw [e] at hw
    exact Nat.lt_irrefl w hw.2

end EsakiaNuclear.Bridge

#axioms_within EsakiaNuclear.Gen.g1 [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.g2 [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.g3 [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.g4 [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Bridge.r5 [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.phi_nucleus [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.lower_basic_nuclear [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.isClosed_Nj [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.isNuclear_Nj [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Bridge.omega_HC_gt []

-- The pin gate, watched failing: G1 needs `Classical.choice`.
/-- error: 'EsakiaNuclear.Gen.g1' depends on Classical.choice, which the bound does not allow.
  declared: [propext, Quot.sound]
Locate the entry with:  #axiom_path Classical.choice EsakiaNuclear.Gen.g1 -/
#guard_msgs in
#axioms_within EsakiaNuclear.Gen.g1 [propext, Quot.sound]
