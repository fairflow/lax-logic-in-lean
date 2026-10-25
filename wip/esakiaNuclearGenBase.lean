import wip.esakiaNuclearGen

/-!
# Nuclear Esakia duality, general case: proof kit (Phase B)

Classical.  The prime filter theorem enters ONLY through
`DistribLattice.prime_ideal_of_disjoint_filter_ideal` (Zorn), wrapped once
as `exists_prime_set`; compactness of the spectrum enters ONLY through
Alexander's subbasis theorem `isCompact_generateFrom`.

Contents.
* §1 the prime filter theorem in set form, for any bounded distributive
  lattice; two instances: `A` itself (`exists_spec`) and the lattice
  `Fix j` of fixed points of a nucleus (`exists_spec_nuclear`);
* §2 `φ` preserves the lattice operations and `→` (`phi_himp`), and is an
  order embedding;
* §3 the topology: the basis `φ(a) ∩ φ(b)ᶜ`, compactness, clopens as finite
  unions of basic sets, clopen up-sets as `φ(a)`, the Esakia condition.
-/

namespace EsakiaNuclear.Gen

open Set

/-! ## §1 The prime filter theorem -/

section PFT

variable {α : Type*} [DistribLattice α] [BoundedOrder α]

/-- **Prime filter theorem**, set form: a filter `G` disjoint from an ideal
`I` extends to a prime filter disjoint from `I`.  The only use of Zorn's
lemma in the development. -/
theorem exists_prime_set (G I : Set α) (hG : G.Nonempty)
    (hGu : ∀ {a b : α}, a ≤ b → a ∈ G → b ∈ G)
    (hGi : ∀ {a b : α}, a ∈ G → b ∈ G → a ⊓ b ∈ G)
    (hI : I.Nonempty) (hId : ∀ {a b : α}, a ≤ b → b ∈ I → a ∈ I)
    (hIs : ∀ {a b : α}, a ∈ I → b ∈ I → a ⊔ b ∈ I) (hdisj : ∀ a ∈ G, a ∉ I) :
    ∃ P : Set α, G ⊆ P ∧ (∀ a ∈ P, a ∉ I) ∧ ⊤ ∈ P ∧ ⊥ ∉ P ∧
      (∀ {a b : α}, a ≤ b → a ∈ P → b ∈ P) ∧ (∀ {a b : α}, a ∈ P → b ∈ P → a ⊓ b ∈ P) ∧
      (∀ {a b : α}, a ⊔ b ∈ P → a ∈ P ∨ b ∈ P) := by
  classical
  have hGF : Order.IsPFilter G := Order.IsPFilter.of_def hG
    (fun a ha b hb => ⟨a ⊓ b, hGi ha hb, inf_le_left, inf_le_right⟩) hGu
  have hII : Order.IsIdeal I :=
    ⟨fun _ _ hba ha => hId hba ha, hI, fun a ha b hb => ⟨a ⊔ b, hIs ha hb, le_sup_left, le_sup_right⟩⟩
  obtain ⟨J, hJ, hIJ, hdis⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal
    (F := hGF.toPFilter) (I := hII.toIdeal)
    (Set.disjoint_left.mpr fun a ha hb => hdisj a ha hb)
  refine ⟨(J : Set α)ᶜ, fun a ha haJ => Set.disjoint_left.mp hdis ha haJ,
    fun a ha haI => ha (hIJ ((Order.Ideal.mem_toIdeal hII).mpr haI)), ?_, ?_, ?_, ?_, ?_⟩
  · exact Order.Ideal.IsProper.top_notMem hJ.toIsProper
  · exact fun h => h J.bot_mem
  · intro a b hab ha hb
    exact ha (J.lower hab hb)
  · intro a b ha hb hab
    rcases hJ.mem_or_mem hab with h | h
    · exact ha h
    · exact hb h
  · intro a b hab
    by_cases ha : a ∈ (J : Set α)
    · by_cases hb : b ∈ (J : Set α)
      · exact absurd (Order.Ideal.sup_mem ha hb) hab
      · exact Or.inr hb
    · exact Or.inl ha

end PFT

variable {A : Type*} [HeytingAlgebra A]

/-- A prime filter, packaged, from its set and properties. -/
def Spec.ofSet (P : Set A) (htop : ⊤ ∈ P) (hbot : ⊥ ∉ P)
    (hle : ∀ {a b : A}, a ≤ b → a ∈ P → b ∈ P) (hinf : ∀ {a b : A}, a ∈ P → b ∈ P → a ⊓ b ∈ P)
    (hor : ∀ {a b : A}, a ⊔ b ∈ P → a ∈ P ∨ b ∈ P) : Spec A :=
  ⟨P, ⟨htop, hbot, hle, hinf, hor⟩⟩

/-- The prime filter theorem in `A`. -/
theorem exists_spec (G I : Set A) (hG : G.Nonempty)
    (hGu : ∀ {a b : A}, a ≤ b → a ∈ G → b ∈ G)
    (hGi : ∀ {a b : A}, a ∈ G → b ∈ G → a ⊓ b ∈ G)
    (hI : I.Nonempty) (hId : ∀ {a b : A}, a ≤ b → b ∈ I → a ∈ I)
    (hIs : ∀ {a b : A}, a ∈ I → b ∈ I → a ⊔ b ∈ I) (hdisj : ∀ a ∈ G, a ∉ I) :
    ∃ y : Spec A, G ⊆ y.carrier ∧ ∀ a ∈ I, a ∉ y.carrier := by
  obtain ⟨P, hGP, hPI, htop, hbot, hle, hinf, hor⟩ :=
    exists_prime_set G I hG hGu hGi hI hId hIs hdisj
  exact ⟨Spec.ofSet P htop hbot hle hinf hor, hGP, fun a ha hP => hPI a hP ha⟩

theorem exists_spec_not_le {a b : A} (h : ¬ a ≤ b) :
    ∃ y : Spec A, a ∈ y.carrier ∧ b ∉ y.carrier := by
  obtain ⟨y, h1, h2⟩ := exists_spec (Ici a) (Iic b) ⟨a, le_refl a⟩
    (fun hab ha => le_trans ha hab) (fun ha hb => le_inf ha hb) ⟨b, le_refl b⟩
    (fun hab hb => le_trans hab hb) (fun ha hb => sup_le ha hb)
    (fun c hac hcb => h (le_trans hac hcb))
  exact ⟨y, h1 (le_refl a), h2 b (le_refl b)⟩

theorem Spec.mem_of_le' (x : Spec A) {a b : A} (h : a ≤ b) (ha : a ∈ x.carrier) :
    b ∈ x.carrier := x.isPrime.mem_of_le h ha

theorem Spec.top_mem' (x : Spec A) : (⊤ : A) ∈ x.carrier := x.isPrime.top_mem

theorem Spec.inf_mem' (x : Spec A) {a b : A} (ha : a ∈ x.carrier) (hb : b ∈ x.carrier) :
    a ⊓ b ∈ x.carrier := x.isPrime.inf_mem ha hb

theorem Spec.le_def {x y : Spec A} : x ≤ y ↔ x.carrier ⊆ y.carrier := Iff.rfl

/-- The prime filter theorem relative to `x`: if `a → b ∉ x` there is a prime
`y ⊇ x` with `a ∈ y`, `b ∉ y`. -/
theorem exists_spec_himp (x : Spec A) {a b : A} (h : a ⇨ b ∉ x.carrier) :
    ∃ y : Spec A, x ≤ y ∧ a ∈ y.carrier ∧ b ∉ y.carrier := by
  obtain ⟨y, h1, h2⟩ := exists_spec {c | ∃ e ∈ x.carrier, e ⊓ a ≤ c} (Iic b)
    ⟨⊤, ⊤, x.top_mem', le_top⟩
    (fun hcd ⟨e, he, hc⟩ => ⟨e, he, le_trans hc hcd⟩)
    (fun ⟨e₁, he₁, h₁⟩ ⟨e₂, he₂, h₂⟩ => ⟨e₁ ⊓ e₂, x.inf_mem' he₁ he₂,
      le_inf (le_trans (inf_le_inf_right a inf_le_left) h₁)
        (le_trans (inf_le_inf_right a inf_le_right) h₂)⟩)
    ⟨b, le_refl b⟩ (fun hab hb => le_trans hab hb) (fun ha hb => sup_le ha hb)
    (fun c ⟨e, he, hc⟩ hcb => h (x.mem_of_le' (le_himp_iff.mpr (le_trans hc hcb)) he))
  exact ⟨y, fun c hc => h1 ⟨c, hc, inf_le_left⟩, h1 ⟨⊤, x.top_mem', inf_le_right⟩, h2 b (le_refl b)⟩

/-! ### Three nucleus facts, choice-free

Mathlib's `Nucleus.le_apply`, `Nucleus.idempotent` and `Nucleus.monotone`
reach `Classical.choice` (through `Nucleus.toClosureOperator` and
`OrderHomClass`, measured with `#axiom_path`); these replacements read the
structure's own fields and `map_inf`. -/

theorem nle {j : Nucleus A} {x : A} : x ≤ j x := NucleusClass.le_apply x j

theorem nidem {j : Nucleus A} (x : A) : j (j x) = j x :=
  le_antisymm (NucleusClass.idempotent x j) nle

theorem nmono {j : Nucleus A} {x y : A} (h : x ≤ y) : j x ≤ j y := by
  have e : j (x ⊓ y) = j x ⊓ j y := Nucleus.map_inf
  rw [inf_eq_left.mpr h] at e
  rw [e]
  exact inf_le_right

/-! ### The fixed points of a nucleus form a bounded distributive lattice -/

/-- `A_j`, the fixed points of `j`. -/
def Fix (j : Nucleus A) : Type _ := {c : A // j c = c}

instance (j : Nucleus A) : Lattice (Fix j) where
  le c d := c.1 ≤ d.1
  le_refl c := le_refl c.1
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  le_antisymm c d h₁ h₂ := Subtype.ext (le_antisymm h₁ h₂)
  inf c d := ⟨c.1 ⊓ d.1, by rw [Nucleus.map_inf, c.2, d.2]⟩
  inf_le_left c d := (inf_le_left : c.1 ⊓ d.1 ≤ c.1)
  inf_le_right c d := (inf_le_right : c.1 ⊓ d.1 ≤ d.1)
  le_inf _ _ _ h₁ h₂ := le_inf h₁ h₂
  sup c d := ⟨j (c.1 ⊔ d.1), nidem _⟩
  le_sup_left c d := le_trans (le_sup_left : c.1 ≤ c.1 ⊔ d.1) nle
  le_sup_right c d := le_trans (le_sup_right : d.1 ≤ c.1 ⊔ d.1) nle
  sup_le c d e h₁ h₂ := by
    show j (c.1 ⊔ d.1) ≤ e.1
    calc j (c.1 ⊔ d.1) ≤ j e.1 := nmono (sup_le h₁ h₂)
      _ = e.1 := e.2

theorem Fix.le_iff {j : Nucleus A} {c d : Fix j} : c ≤ d ↔ c.1 ≤ d.1 := Iff.rfl

theorem Fix.inf_val {j : Nucleus A} (c d : Fix j) : (c ⊓ d).1 = c.1 ⊓ d.1 := rfl

theorem Fix.sup_val {j : Nucleus A} (c d : Fix j) : (c ⊔ d).1 = j (c.1 ⊔ d.1) := rfl

instance (j : Nucleus A) : DistribLattice (Fix j) :=
  { (inferInstance : Lattice (Fix j)) with
    le_sup_inf := fun x y z => by
      show j (x.1 ⊔ y.1) ⊓ j (x.1 ⊔ z.1) ≤ j (x.1 ⊔ y.1 ⊓ z.1)
      rw [← Nucleus.map_inf]
      exact nmono le_sup_inf }

instance (j : Nucleus A) : BoundedOrder (Fix j) where
  top := ⟨⊤, le_antisymm le_top nle⟩
  le_top c := (le_top : c.1 ≤ ⊤)
  bot := ⟨j ⊥, nidem _⟩
  bot_le c := by
    show j ⊥ ≤ c.1
    calc j ⊥ ≤ j c.1 := nmono bot_le
      _ = c.1 := c.2

theorem Fix.top_val (j : Nucleus A) : (⊤ : Fix j).1 = ⊤ := rfl

theorem Fix.bot_val (j : Nucleus A) : (⊥ : Fix j).1 = j ⊥ := rfl

/-- `x ∈ N_j` iff `x` is closed under `j⁻¹`. -/
theorem mem_Nj {j : Nucleus A} {x : Spec A} :
    x ∈ Nj j ↔ ∀ c, j c ∈ x.carrier → c ∈ x.carrier := by
  constructor
  · intro h c hc
    have e : (⇑j ⁻¹' x.carrier) = x.carrier := h
    rw [← e]
    exact hc
  · intro h
    show ⇑j ⁻¹' x.carrier = x.carrier
    ext c
    exact ⟨fun hc => h c hc, fun hc => x.mem_of_le' nle hc⟩

/-- **The prime filter theorem relative to a nucleus**: if `a → j b ∉ x`
there is a prime `y ⊇ x` in `N_j` with `a ∈ y`, `b ∉ y`.  Proved by the
prime filter theorem in `A_j` (`exists_prime_set` at `Fix j`). -/
theorem exists_spec_nuclear (j : Nucleus A) (x : Spec A) {a b : A}
    (h : a ⇨ j b ∉ x.carrier) :
    ∃ y : Spec A, x ≤ y ∧ y ∈ Nj j ∧ a ∈ y.carrier ∧ b ∉ y.carrier := by
  obtain ⟨P, hGP, hPI, htop, hbot, hle, hinf, hor⟩ := exists_prime_set (α := Fix j)
    {c | ∃ e ∈ x.carrier, e ⊓ a ≤ c.1} {c | c.1 ≤ j b}
    ⟨⊤, ⊤, x.top_mem', le_top⟩
    (fun hcd ⟨e, he, hc⟩ => ⟨e, he, le_trans hc hcd⟩)
    (fun ⟨e₁, he₁, h₁⟩ ⟨e₂, he₂, h₂⟩ => ⟨e₁ ⊓ e₂, x.inf_mem' he₁ he₂,
      le_inf (le_trans (inf_le_inf_right a inf_le_left) h₁)
        (le_trans (inf_le_inf_right a inf_le_right) h₂)⟩)
    ⟨⊥, nmono bot_le⟩ (fun hcd hd => le_trans hcd hd)
    (fun {c d} hc hd => by
      show j (c.1 ⊔ d.1) ≤ j b
      calc j (c.1 ⊔ d.1) ≤ j (j b) := nmono (sup_le hc hd)
        _ = j b := nidem _)
    (fun c ⟨e, he, hc⟩ hcb => h (x.mem_of_le' (le_himp_iff.mpr (le_trans hc hcb)) he))
  let fx : A → Fix j := fun c => ⟨j c, nidem c⟩
  have hjj : ∀ c, fx (j c) = fx c := fun c => Subtype.ext (nidem c)
  let y : Spec A := Spec.ofSet {c | fx c ∈ P}
    (by
      have : fx ⊤ = ⊤ := Subtype.ext (le_antisymm le_top nle)
      show fx ⊤ ∈ P
      rw [this]; exact htop)
    (fun hb => hbot hb)
    (fun hcd hc => hle (nmono hcd) hc)
    (fun {c d} hc hd => by
      have : fx (c ⊓ d) = fx c ⊓ fx d := Subtype.ext Nucleus.map_inf
      show fx (c ⊓ d) ∈ P
      rw [this]; exact hinf hc hd)
    (fun {c d} hcd => by
      have : fx (c ⊔ d) = fx c ⊔ fx d := by
        apply Subtype.ext
        show j (c ⊔ d) = j (j c ⊔ j d)
        apply le_antisymm
        · exact nmono (sup_le_sup nle nle)
        · calc j (j c ⊔ j d) ≤ j (j (c ⊔ d)) :=
                nmono (sup_le (nmono le_sup_left)
                  (nmono le_sup_right))
            _ = j (c ⊔ d) := nidem _
      have h' : fx (c ⊔ d) ∈ P := hcd
      rw [this] at h'
      exact hor h')
  refine ⟨y, fun c hc => hGP ⟨c, hc, le_trans inf_le_left nle⟩, ?_, ?_, ?_⟩
  · refine mem_Nj.mpr fun c hc => ?_
    have h' : fx (j c) ∈ P := hc
    rw [hjj] at h'
    exact h'
  · exact hGP ⟨⊤, x.top_mem', le_trans inf_le_right nle⟩
  · intro hb
    exact hPI (fx b) hb (le_refl _)

/-! ## §2 `φ` -/

theorem mem_phi {a : A} {x : Spec A} : x ∈ phi a ↔ a ∈ x.carrier := Iff.rfl

theorem phi_inf (a b : A) : phi (a ⊓ b) = phi a ∩ phi b := by
  ext x
  exact ⟨fun h => ⟨x.mem_of_le' inf_le_left h, x.mem_of_le' inf_le_right h⟩,
    fun h => x.inf_mem' h.1 h.2⟩

theorem phi_sup (a b : A) : phi (a ⊔ b) = phi a ∪ phi b := by
  ext x
  exact ⟨fun h => x.isPrime.mem_or_mem h,
    fun h => h.elim (fun h => x.mem_of_le' le_sup_left h) (fun h => x.mem_of_le' le_sup_right h)⟩

theorem phi_top : phi (⊤ : A) = univ := eq_univ_of_forall fun x => x.top_mem'

theorem phi_bot : phi (⊥ : A) = ∅ := eq_empty_of_forall_notMem fun x h => x.isPrime.bot_not_mem h

theorem phi_upper (a : A) : IsUpperSet (phi a) := fun _ _ hxy ha => hxy ha

/-- `φ` is an order embedding (prime filter theorem). -/
theorem phi_subset_iff {a b : A} : phi a ⊆ phi b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    obtain ⟨y, hay, hby⟩ := exists_spec_not_le hab
    exact hby (h hay)
  · intro hab x hx
    exact x.mem_of_le' hab hx

theorem phi_injective : Function.Injective (phi (A := A)) := fun _ _ h =>
  le_antisymm (phi_subset_iff.mp h.le) (phi_subset_iff.mp h.ge)

theorem mem_lowerClosure_iff {s : Set (Spec A)} {x : Spec A} :
    x ∈ (lowerClosure s : Set (Spec A)) ↔ ∃ y ∈ s, x ≤ y := mem_lowerClosure

/-- `φ(a → b) = X ∖ ↓(φ a ∖ φ b)` (prime filter theorem). -/
theorem phi_himp (a b : A) :
    phi (a ⇨ b) = (lowerClosure (phi a \ phi b) : Set (Spec A))ᶜ := by
  ext x
  rw [mem_compl_iff, mem_lowerClosure_iff]
  constructor
  · rintro hx ⟨y, ⟨hay, hby⟩, hxy⟩
    exact hby (y.mem_of_le' inf_himp_le (y.inf_mem' hay (hxy hx)))
  · intro h
    by_contra hx
    obtain ⟨y, hxy, hay, hby⟩ := exists_spec_himp x hx
    exact h ⟨y, ⟨hay, hby⟩, hxy⟩

theorem finset_inf_mem (y : Spec A) {ι : Type*} (t : Finset ι) (f : ι → A)
    (h : ∀ i ∈ t, f i ∈ y.carrier) : t.inf f ∈ y.carrier := by
  induction t using Finset.cons_induction with
  | empty => rw [Finset.inf_empty]; exact y.top_mem'
  | cons i t hi ih =>
    rw [Finset.inf_cons]
    exact y.inf_mem' (h i (Finset.mem_cons.mpr (Or.inl rfl)))
      (ih fun k hk => h k (Finset.mem_cons.mpr (Or.inr hk)))

theorem finset_sup_mem (y : Spec A) {ι : Type*} (t : Finset ι) (f : ι → A)
    (h : t.sup f ∈ y.carrier) : ∃ i ∈ t, f i ∈ y.carrier := by
  induction t using Finset.cons_induction with
  | empty => rw [Finset.sup_empty] at h; exact absurd h y.isPrime.bot_not_mem
  | cons i t hi ih =>
    rw [Finset.sup_cons] at h
    rcases y.isPrime.mem_or_mem h with h | h
    · exact ⟨i, Finset.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨k, hk, hk'⟩ := ih h
      exact ⟨k, Finset.mem_cons.mpr (Or.inr hk), hk'⟩

/-! ## §3 The topology -/

/-- The subbasis `{φ a} ∪ {(φ a)ᶜ}` (D2). -/
def subbasis : Set (Set (Spec A)) := range (phi (A := A)) ∪ range fun a => (phi (A := A) a)ᶜ

theorem topology_eq : (inferInstance : TopologicalSpace (Spec A)) =
    TopologicalSpace.generateFrom (subbasis (A := A)) := rfl

theorem isOpen_phi (a : A) : IsOpen (phi a) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨a, rfl⟩)

theorem isOpen_phi_compl (a : A) : IsOpen (phi a)ᶜ :=
  TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr ⟨a, rfl⟩)

theorem isClopen_phi (a : A) : IsClopen (phi a) :=
  ⟨isOpen_compl_iff.mp (isOpen_phi_compl a), isOpen_phi a⟩

/-- The basic sets `φ(a) ∩ φ(b)ᶜ`. -/
def basic : Set (Set (Spec A)) := {s | ∃ a b : A, s = phi a ∩ (phi b)ᶜ}

theorem isBasis : TopologicalSpace.IsTopologicalBasis (basic (A := A)) := by
  refine TopologicalSpace.IsTopologicalBasis.mk ?_ ?_ ?_
  · rintro _ ⟨a₁, b₁, rfl⟩ _ ⟨a₂, b₂, rfl⟩ x hx
    refine ⟨phi (a₁ ⊓ a₂) ∩ (phi (b₁ ⊔ b₂))ᶜ, ⟨_, _, rfl⟩, ?_, ?_⟩
    · rw [phi_inf, phi_sup]
      exact ⟨⟨hx.1.1, hx.2.1⟩, fun h => h.elim hx.1.2 hx.2.2⟩
    · rw [phi_inf, phi_sup]
      rintro y ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, fun h => h3 (Or.inl h)⟩, h2, fun h => h3 (Or.inr h)⟩
  · exact eq_univ_of_forall fun x => ⟨phi ⊤ ∩ (phi ⊥)ᶜ, ⟨⊤, ⊥, rfl⟩, x.top_mem',
      fun h => x.isPrime.bot_not_mem h⟩
  · apply le_antisymm
    · rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
      rintro _ ⟨a, b, rfl⟩
      exact (isOpen_phi a).inter (isOpen_phi_compl b)
    · show TopologicalSpace.generateFrom basic ≤ TopologicalSpace.generateFrom subbasis
      rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
      rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
      · apply TopologicalSpace.isOpen_generateFrom_of_mem
        exact ⟨a, ⊥, Set.ext fun x => ⟨fun h => ⟨h, x.isPrime.bot_not_mem⟩, fun h => h.1⟩⟩
      · apply TopologicalSpace.isOpen_generateFrom_of_mem
        exact ⟨⊤, b, Set.ext fun x => ⟨fun h => ⟨x.top_mem', h⟩, fun h => h.2⟩⟩

/-- **Compactness** of the spectrum: Alexander's subbasis theorem
(`isCompact_generateFrom`) and the prime filter theorem. -/
instance compactSpace_spec : CompactSpace (Spec A) := by
  classical
  refine ⟨isCompact_generateFrom topology_eq fun P hP hcov => ?_⟩
  by_contra hno
  let As := {a : A | phi a ∈ P}
  let Bs := {b : A | (phi b)ᶜ ∈ P}
  have hdisj : ∀ c ∈ {c | ∃ s : Finset A, ↑s ⊆ Bs ∧ s.inf id ≤ c},
      c ∉ {c | ∃ s : Finset A, ↑s ⊆ As ∧ c ≤ s.sup id} := by
    rintro c ⟨s, hs, hsc⟩ ⟨s', hs', hcs'⟩
    refine hno ⟨(fun a => phi a) '' ↑s' ∪ (fun b => (phi b)ᶜ) '' ↑s, ?_, ?_, ?_⟩
    · rintro _ (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact hs' ha
      · exact hs hb
    · exact ((Finset.finite_toSet s').image _).union ((Finset.finite_toSet s).image _)
    · intro z _
      by_cases hz : ∀ b ∈ s, b ∈ z.carrier
      · have h1 := finset_inf_mem z s id hz
        have h2 := z.mem_of_le' (le_trans hsc hcs') h1
        obtain ⟨a, ha, haz⟩ := finset_sup_mem z s' id h2
        exact ⟨phi a, Or.inl ⟨a, ha, rfl⟩, haz⟩
      · push Not at hz
        obtain ⟨b, hb, hbz⟩ := hz
        exact ⟨(phi b)ᶜ, Or.inr ⟨b, hb, rfl⟩, hbz⟩
  obtain ⟨y, hG, hI⟩ := exists_spec
    {c | ∃ s : Finset A, ↑s ⊆ Bs ∧ s.inf id ≤ c} {c | ∃ s : Finset A, ↑s ⊆ As ∧ c ≤ s.sup id}
    ⟨⊤, ∅, by rw [Finset.coe_empty]; exact empty_subset _, le_top⟩
    (fun hcd ⟨s, hs, hc⟩ => ⟨s, hs, le_trans hc hcd⟩)
    (fun ⟨s, hs, hc⟩ ⟨s', hs', hc'⟩ => ⟨s ∪ s', by rw [Finset.coe_union]; exact union_subset hs hs',
      by rw [Finset.inf_union]; exact inf_le_inf hc hc'⟩)
    ⟨⊥, ∅, by rw [Finset.coe_empty]; exact empty_subset _, bot_le⟩
    (fun hcd ⟨s, hs, hd⟩ => ⟨s, hs, le_trans hcd hd⟩)
    (fun ⟨s, hs, hc⟩ ⟨s', hs', hc'⟩ => ⟨s ∪ s', by rw [Finset.coe_union]; exact union_subset hs hs',
      by rw [Finset.sup_union]; exact sup_le_sup hc hc'⟩)
    hdisj
  obtain ⟨t, htP, hyt⟩ := hcov (mem_univ y)
  rcases hP htP with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact hI a ⟨{a}, by rw [Finset.coe_singleton, singleton_subset_iff]; exact htP,
      by rw [Finset.sup_singleton]; exact le_refl _⟩ hyt
  · exact hyt (hG ⟨{b}, by rw [Finset.coe_singleton, singleton_subset_iff]; exact htP,
      by rw [Finset.inf_singleton]; exact le_refl _⟩)

/-- Every clopen set is a finite union of basic sets. -/
theorem clopen_eq_union {U : Set (Spec A)} (hU : IsClopen U) :
    ∃ s : Set (A × A), s.Finite ∧ U = ⋃ p ∈ s, phi p.1 ∩ (phi p.2)ᶜ := by
  classical
  obtain ⟨t, ht⟩ := hU.isClosed.isCompact.elim_finite_subcover
    (fun i : {p : A × A // phi p.1 ∩ (phi p.2)ᶜ ⊆ U} => phi i.1.1 ∩ (phi i.1.2)ᶜ)
    (fun i => (isOpen_phi _).inter (isOpen_phi_compl _))
    (fun x hx => by
      obtain ⟨v, ⟨a, b, rfl⟩, hxv, hvU⟩ := isBasis.exists_subset_of_mem_open hx hU.isOpen
      exact mem_iUnion.mpr ⟨⟨(a, b), hvU⟩, hxv⟩)
  refine ⟨↑(t.image Subtype.val), Finset.finite_toSet _, ?_⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion₂.mpr ⟨i.1, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩), hxi⟩
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    exact i.2 hxp

theorem lowerClosure_biUnion {ι : Type*} (s : Set ι) (f : ι → Set (Spec A)) :
    (lowerClosure (⋃ i ∈ s, f i) : Set (Spec A)) =
      ⋃ i ∈ s, (lowerClosure (f i) : Set (Spec A)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := mem_lowerClosure_iff.mp hx
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨i, hi, mem_lowerClosure_iff.mpr ⟨y, hyi, hxy⟩⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hy, hxy⟩ := mem_lowerClosure_iff.mp hxi
    exact mem_lowerClosure_iff.mpr ⟨y, mem_iUnion₂.mpr ⟨i, hi, hy⟩, hxy⟩

theorem lower_basic (a b : A) :
    (lowerClosure (phi a ∩ (phi b)ᶜ) : Set (Spec A)) = (phi (a ⇨ b))ᶜ := by
  rw [phi_himp, compl_compl]
  rfl

/-- **The Esakia condition**: the down-set of a clopen set is clopen. -/
theorem isClopen_lowerClosure {U : Set (Spec A)} (hU : IsClopen U) :
    IsClopen (lowerClosure U : Set (Spec A)) := by
  obtain ⟨s, hs, rfl⟩ := clopen_eq_union hU
  rw [lowerClosure_biUnion]
  refine hs.isClopen_biUnion fun p _ => ?_
  rw [lower_basic]
  exact (isClopen_phi _).compl

/-- Every clopen up-set is some `φ(a)`. -/
theorem exists_phi_of_clopen_upper {U : Set (Spec A)} (hU : IsClopen U) (hup : IsUpperSet U) :
    ∃ a : A, phi a = U := by
  classical
  have loc : ∀ x ∈ U, ∃ b : A, b ∈ x.carrier ∧ phi b ⊆ U := by
    intro x hx
    obtain ⟨t, ht⟩ := hU.isOpen.isClosed_compl.isCompact.elim_finite_subcover
      (fun c : x.carrier => (phi c.1)ᶜ) (fun c => isOpen_phi_compl _)
      (fun y hy => by
        have hxy : ¬ x.carrier ⊆ y.carrier := fun h => hy (hup (Spec.le_def.mpr h) hx)
        obtain ⟨c, hcx, hcy⟩ := not_subset.mp hxy
        exact mem_iUnion.mpr ⟨⟨c, hcx⟩, hcy⟩)
    refine ⟨t.inf fun c => c.1, finset_inf_mem x t _ fun c _ => c.2, fun z hz => ?_⟩
    by_contra hzU
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (ht hzU)
    exact hzc (z.mem_of_le' (Finset.inf_le hc) hz)
  obtain ⟨t, ht⟩ := hU.isClosed.isCompact.elim_finite_subcover
    (fun i : {b : A // phi b ⊆ U} => phi i.1) (fun i => isOpen_phi _)
    (fun x hx => by
      obtain ⟨b, hbx, hbU⟩ := loc x hx
      exact mem_iUnion.mpr ⟨⟨b, hbU⟩, hbx⟩)
  refine ⟨t.sup fun i => i.1, Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)⟩
  · obtain ⟨i, _, hiz⟩ := finset_sup_mem z t _ hz
    exact i.2 hiz
  · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (ht hz)
    exact z.mem_of_le' (Finset.le_sup (f := fun i : {b : A // phi b ⊆ U} => i.1) hi) hzi

instance priestleySpace_spec : PriestleySpace (Spec A) where
  priestley {x y} h := by
    obtain ⟨a, hax, hay⟩ := not_subset.mp (fun hs => h (Spec.le_def.mpr hs))
    exact ⟨phi a, isClopen_phi a, phi_upper a, hax, hay⟩

end EsakiaNuclear.Gen

/-! ## Axiom audit of the kit

Choice-free (no `Classical.choice`): the algebra of `φ`, the nucleus facts,
the lattice `A_j`, the basis. -/

#axioms_within EsakiaNuclear.Gen.Spec.ofSet []
#axioms_within EsakiaNuclear.Gen.nle []
#axioms_within EsakiaNuclear.Gen.nidem []
#axioms_within EsakiaNuclear.Gen.nmono [propext]
#axioms_within EsakiaNuclear.Gen.instLatticeFix [propext]
#axioms_within EsakiaNuclear.Gen.instDistribLatticeFix [propext]
#axioms_within EsakiaNuclear.Gen.instBoundedOrderFix [propext]
#axioms_within EsakiaNuclear.Gen.mem_Nj [propext, Quot.sound]
#axioms_within EsakiaNuclear.Gen.phi_inf [propext, Quot.sound]
#axioms_within EsakiaNuclear.Gen.phi_sup [propext, Quot.sound]
#axioms_within EsakiaNuclear.Gen.phi_top [propext, Quot.sound]
#axioms_within EsakiaNuclear.Gen.phi_bot [propext, Quot.sound]
#axioms_within EsakiaNuclear.Gen.phi_upper [propext, Quot.sound]
#axioms_within EsakiaNuclear.Gen.finset_inf_mem [propext, Quot.sound]
#axioms_within EsakiaNuclear.Gen.finset_sup_mem [propext, Quot.sound]
#axioms_within EsakiaNuclear.Gen.isOpen_phi []
#axioms_within EsakiaNuclear.Gen.isClopen_phi []
#axioms_within EsakiaNuclear.Gen.isBasis [propext, Quot.sound]
#axioms_within EsakiaNuclear.Gen.lowerClosure_biUnion [propext, Quot.sound]

/-! Classical: the prime filter theorem and everything resting on it or on
compactness. -/

#axioms_within EsakiaNuclear.Gen.exists_prime_set [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.exists_spec [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.exists_spec_not_le [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.exists_spec_himp [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.exists_spec_nuclear [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.phi_subset_iff [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.phi_injective [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.phi_himp [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.compactSpace_spec [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.clopen_eq_union [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.isClopen_lowerClosure [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.exists_phi_of_clopen_upper [propext, Classical.choice, Quot.sound]
#axioms_within EsakiaNuclear.Gen.priestleySpace_spec [propext, Classical.choice, Quot.sound]
