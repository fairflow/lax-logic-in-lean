/-
# The assembly: the flight corner SERVED — supply-free, guard-free completeness

The corner of the completeness recursion (the irregular `◯Z`-demand at
a world every proper extension of which forces `Z`) is closed HERE, in
the strict round-2 calculus, by construction:

* the world is cone-trivial (`coneTrivial_of_corner`), so the two
  coverage bricks apply;
* the premise family is THIN (`St = []` everywhere): `Ax^I` rows for
  every refuted `Sf^R`-prime, and `⊃∉` float rows for every `Sf^R`-imp
  with refuted antecedent (their regular premises live at `e > a` —
  height drops, so the recursion supplies them);
* two corner facts kill the remaining demands OUTRIGHT: a refuted
  implication has a REFUTED consequent (`a ⊩ B → a ⊩ A⊃B`), and a
  refuted `◯` has a REFUTED body (`a ⊩ Z → a ⊩ ◯Z`) — so no `◯`-cell
  is ever demanded, and with it the SEEN machinery dies;
* `corner_coverage` (+ `keptOf_saturated`) then covers everything: the
  row for `Z` is built by structural descent (`rowFor`) whose leaves
  are the three barren joins over the family — stable zones empty, so
  the strict (J2) is VACUOUS — and `◯∉` closes the irregular cell with
  `hTh` from the coverage.

`minModF` is `minModV` with the supply branch replaced by this
construction; `completenessV` at the end is the campaign statement:

    hloc → K.Infallible → ¬ K.valid G → ProvableV G

— no supply, no goal guard, no frame condition.
-/
import wip.minmodv
import wip.minmodv_flight
import FRJ.WitnessKit

namespace FRJ

open Form

/-! ## Small corner facts -/

theorem gHat_subset_sfL {G : Form} : gHat G ⊆ sfL G := by
  intro X hX
  simp only [gHat, List.mem_append] at hX
  rcases hX with (h | h) | h <;> exact (List.mem_filter.mp h).1

/-- A refuted implication has a refuted consequent. -/
theorem not_force_consequent {K : Kripke} {a : K.W} {A B : Form}
    (h : ¬ K.force a (.imp A B)) : ¬ K.force a B :=
  fun hB => h (fun u hu _ => K.force_mono hu hB)

/-- A refuted `◯` has a refuted body. -/
theorem not_force_body {K : Kripke} {a : K.W} {Z : Form}
    (h : ¬ K.force a (.circ Z)) : ¬ K.force a Z :=
  fun hZ => h (force_circ_of_force hZ)

/-! ## The thin premise family -/

/-- The family's Θ-zones hold every `a`-forced `Ĝ`-member. -/
def thGoodAt (K : Kripke) (G : Form) (a : K.W) (th : List Form) : Prop :=
  ∀ X ∈ gHat G, K.force a X → X ∈ th

/-- A family member: a thin irregular row with a good Θ-zone. -/
structure CornerRow (K : Kripke) (G : Form) (a : K.W) where
  row : IRow G
  hst : row.st = []
  hth : thGoodAt K G a row.th

/-- The `Ax^I` member for a refuted `Sf^R`-prime. -/
def axIRow (K : Kripke) (G : Form) (a : K.W) (q : Form)
    (hq : q.isPrime = true) (hsf : q ∈ sfR G) (hnq : ¬ K.force a q) :
    CornerRow K G a where
  row := ⟨[], rm (gAt G) q ++ gImp G ++ gCirc G, q,
    .axI q hq hsf (CtxEq.refl _)⟩
  hst := rfl
  hth := by
    intro X hX hfX
    simp only [gHat, List.mem_append] at hX
    rcases hX with (h | h) | h
    · refine List.mem_append_left _ (List.mem_append_left _ (mem_rm.mpr ⟨?_, h⟩))
      intro hc; exact hnq (hc ▸ hfX)
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h

/-- Refuted `Sf^R`-primes. -/
def refPrimes (K : Kripke) (G : Form) (a : K.W) : List Form :=
  (sfR G).filter (fun q => q.isPrime && !(decide (K.force a q)))

theorem mem_refPrimes {K : Kripke} {G : Form} {a : K.W} {q : Form} :
    q ∈ refPrimes K G a ↔
      (q ∈ sfR G ∧ q.isPrime = true ∧ ¬ K.force a q) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h2
    exact ⟨h1, h2.1, h2.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine List.mem_filter.mpr ⟨h1, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨h2, h3⟩

/-- Refuted `Sf^R`-implications with refuted antecedent. -/
def refAnteImps (K : Kripke) (G : Form) (a : K.W) : List Form :=
  (sfR G).filter (fun Y => match Y with
    | .imp A _ => !(decide (K.force a Y)) && !(decide (K.force a A))
    | _ => false)

theorem mem_refAnteImps {K : Kripke} {G : Form} {a : K.W} {A B : Form} :
    Form.imp A B ∈ refAnteImps K G a ↔
      (Form.imp A B ∈ sfR G ∧ ¬ K.force a (.imp A B) ∧ ¬ K.force a A) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h2
    exact ⟨h1, h2.1, h2.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine List.mem_filter.mpr ⟨h1, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨h2, h3⟩

theorem mem_refAnteImps_isImp {K : Kripke} {G : Form} {a : K.W} {Y : Form}
    (h : Y ∈ refAnteImps K G a) : Y.isImp = true := by
  have h2 := (List.mem_filter.mp h).2
  cases Y <;> first | rfl | (exfalso; simp at h2)

/-- The float-cell interface: what the outer recursion supplies for
each refuted-antecedent implication. -/
def IFloat (K : Kripke) (G : Form) (a : K.W) : Type :=
  ∀ A B : Form, Form.imp A B ∈ sfR G → ¬ K.force a (.imp A B) →
    ¬ K.force a A →
    { cr : CornerRow K G a // cr.row.rhs = Form.imp A B }

/-- The family: `Ax^I` rows for refuted primes, float rows for
refuted-antecedent implications. -/
def familyRows (K : Kripke) (G : Form) (a : K.W) (ifl : IFloat K G a) :
    List (CornerRow K G a) :=
  ((refPrimes K G a).attach.map (fun ⟨q, hq⟩ =>
    axIRow K G a q (mem_refPrimes.mp hq).2.1 (mem_refPrimes.mp hq).1
      (mem_refPrimes.mp hq).2.2)) ++
  ((refAnteImps K G a).attach.map (fun ⟨Y, hY⟩ =>
    match Y, mem_refAnteImps_isImp hY, hY with
    | .imp A B, _, hY =>
        (ifl A B (mem_refAnteImps.mp hY).1 (mem_refAnteImps.mp hY).2.1
          (mem_refAnteImps.mp hY).2.2).1))

theorem familyRows_prop {K : Kripke} {G : Form} {a : K.W}
    {ifl : IFloat K G a} :
    ∀ cr ∈ familyRows K G a ifl,
      cr.row.st = [] ∧ thGoodAt K G a cr.row.th :=
  fun cr _ => ⟨cr.hst, cr.hth⟩

/-- Rhs-realisation: every refuted prime is some member's rhs. -/
theorem refPrime_rhs {K : Kripke} {G : Form} {a : K.W}
    {ifl : IFloat K G a} {q : Form} (hq : q ∈ refPrimes K G a) :
    ∃ cr ∈ familyRows K G a ifl, cr.row.rhs = q := by
  refine ⟨axIRow K G a q (mem_refPrimes.mp hq).2.1 (mem_refPrimes.mp hq).1
    (mem_refPrimes.mp hq).2.2, ?_, rfl⟩
  exact List.mem_append_left _ (List.mem_map.mpr
    ⟨⟨q, hq⟩, List.mem_attach _ _, rfl⟩)

/-- Rhs-realisation: every refuted-antecedent implication is some
member's rhs. -/
theorem refAnteImp_rhs {K : Kripke} {G : Form} {a : K.W}
    {ifl : IFloat K G a} {A B : Form}
    (hY : Form.imp A B ∈ refAnteImps K G a) :
    ∃ cr ∈ familyRows K G a ifl, cr.row.rhs = Form.imp A B := by
  refine ⟨(ifl A B (mem_refAnteImps.mp hY).1 (mem_refAnteImps.mp hY).2.1
    (mem_refAnteImps.mp hY).2.2).1, ?_,
    (ifl A B _ _ _).2⟩
  exact List.mem_append_right _ (List.mem_map.mpr
    ⟨⟨Form.imp A B, hY⟩, List.mem_attach _ _, rfl⟩)

/-- **The family is nonempty** whenever anything in `Sf^R` is refuted:
descend the refuted skeleton to a prime or a refuted-antecedent
implication. -/
theorem familyRows_ne {K : Kripke} {G : Form} {a : K.W}
    (ifl : IFloat K G a) :
    ∀ n (Z : Form), Z.size ≤ n → Z ∈ sfR G → ¬ K.force a Z →
      familyRows K G a ifl ≠ [] := by
  intro n
  induction n with
  | zero => intro Z hZ; exfalso; cases Z <;> (simp only [Form.size] at hZ; omega)
  | succ k ih =>
      intro Z hZ hsf hnf
      have hne_of_mem : ∀ {cr : CornerRow K G a},
          cr ∈ familyRows K G a ifl → familyRows K G a ifl ≠ [] :=
        fun h hc => absurd (hc ▸ h) List.not_mem_nil
      cases Z with
      | atom p =>
          obtain ⟨cr, hcr, -⟩ := refPrime_rhs (ifl := ifl)
            (mem_refPrimes.mpr ⟨hsf, rfl, hnf⟩)
          exact hne_of_mem hcr
      | bot =>
          obtain ⟨cr, hcr, -⟩ := refPrime_rhs (ifl := ifl)
            (mem_refPrimes.mpr ⟨hsf, rfl, hnf⟩)
          exact hne_of_mem hcr
      | and Z₁ Z₂ =>
          have hsz : Z₁.size ≤ k ∧ Z₂.size ≤ k := by
            constructor <;> (simp only [Form.size] at hZ; omega)
          obtain h1 | h1 := Decidable.em (K.force a Z₁)
          · exact ih Z₂ hsz.2 (sfR_and hsf).2 (fun h => hnf ⟨h1, h⟩)
          · exact ih Z₁ hsz.1 (sfR_and hsf).1 h1
      | or Z₁ Z₂ =>
          have hsz : Z₁.size ≤ k := by simp only [Form.size] at hZ; omega
          exact ih Z₁ hsz (sfR_or hsf).1 (fun h => hnf (Or.inl h))
      | imp A B =>
          have hsz : B.size ≤ k := by simp only [Form.size] at hZ; omega
          obtain hA | hA := Decidable.em (K.force a A)
          · exact ih B hsz (sfR_imp hsf).2 (not_force_consequent hnf)
          · obtain ⟨cr, hcr, -⟩ := refAnteImp_rhs (ifl := ifl)
              (mem_refAnteImps.mpr ⟨hsf, hnf, hA⟩)
            exact hne_of_mem hcr
      | circ Z' =>
          have hsz : Z'.size ≤ k := by simp only [Form.size] at hZ; omega
          exact ih Z' hsz (sfR_circ hsf) (not_force_body hnf)

/-! ## The tagged row with coverage -/

/-- A regular row for `Z` serving world `a`, with the tag obligation
and full `(F)`-coverage of its context. -/
structure CRow (K : Kripke) (G : Form) (a : K.W) (Z : Form) where
  ctx : List Form
  t : Tag
  der : FRJVr G t ctx Z
  tOK : t = .barren ∨ ∃ W, t = .chain W ∧ Covers ctx W Z
  covF : ∀ X ∈ sfL G, K.force a X → Clo ctx X

/-- The regular-float interface: a `CRow` for a refuted-antecedent
implication, supplied by the outer recursion (built at the `minEta`
witness, strictly above). -/
def RFloat (K : Kripke) (G : Form) (a : K.W) : Type :=
  ∀ A B : Form, Form.imp A B ∈ sfR G → ¬ K.force a (.imp A B) →
    ¬ K.force a A → CRow K G a (.imp A B)

/-! ## The corner construction -/

section Corner

variable {K : Kripke} {G : Form} {a : K.W}

/-- Everything the corner needs, bundled once the family is split into
head and tail. -/
structure CornerCtx (K : Kripke) (G : Form) (a : K.W) where
  jr : IRow G
  jrs : List (IRow G)
  hmem : ∀ ir ∈ jr :: jrs, ir.st = [] ∧ thGoodAt K G a ir.th
  hrhs : ∀ q ∈ refPrimes K G a, ∃ j : Fin (jrs.length + 1),
    irhsF jr jrs j = q
  hrhsImp : ∀ Y ∈ refAnteImps K G a, ∃ j : Fin (jrs.length + 1),
    irhsF jr jrs j = Y

/-- Split the family. -/
def mkCornerCtx (ifl : IFloat K G a)
    {Z : Form} (hsf : Z ∈ sfR G) (hnf : ¬ K.force a Z) :
    CornerCtx K G a := by
  have hne := familyRows_ne ifl Z.size Z (Nat.le_refl _) hsf hnf
  match hrows : (familyRows K G a ifl).map (·.row) with
  | [] =>
      exact absurd (List.map_eq_nil_iff.mp hrows) hne
  | jr :: jrs =>
      refine ⟨jr, jrs, ?_, ?_, ?_⟩
      · intro ir hir
        have : ir ∈ (familyRows K G a ifl).map (·.row) := by
          rw [hrows]; exact hir
        obtain ⟨cr, hcr, hcrr⟩ := List.mem_map.mp this
        exact hcrr ▸ ⟨cr.hst, cr.hth⟩
      · intro q hq
        obtain ⟨cr, hcr, hcrr⟩ := refPrime_rhs (ifl := ifl) hq
        have : cr.row ∈ jr :: jrs := by
          rw [← hrows]; exact List.mem_map.mpr ⟨cr, hcr, rfl⟩
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp this
        exact ⟨j, by simp only [irhsF, hj, hcrr]⟩
      · intro Y hY
        match Y, mem_refAnteImps_isImp hY, hY with
        | .imp A B, _, hY =>
            obtain ⟨cr, hcr, hcrr⟩ := refAnteImp_rhs (ifl := ifl) hY
            have : cr.row ∈ jr :: jrs := by
              rw [← hrows]; exact List.mem_map.mpr ⟨cr, hcr, rfl⟩
            obtain ⟨j, hj⟩ := List.mem_iff_get.mp this
            exact ⟨j, by simp only [irhsF, hj, hcrr]⟩

variable (cc : CornerCtx K G a)

/-- Stable zones are empty. -/
theorem cc_stE : ∀ j, istF cc.jr cc.jrs j = [] :=
  fun j => (cc.hmem _ (List.get_mem (cc.jr :: cc.jrs) j)).1

theorem cc_thGood : ∀ j, thGoodAt K G a (ithF cc.jr cc.jrs j) :=
  fun j => (cc.hmem _ (List.get_mem (cc.jr :: cc.jrs) j)).2

theorem cc_unionAt :
    unionAll (fun j => atPart (istF cc.jr cc.jrs j)) = [] :=
  eq_nil_of_forall_not_mem (fun X hX => by
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    rw [cc_stE cc j] at hj
    exact absurd hj List.not_mem_nil)

theorem cc_unionImp :
    unionAll (fun j => impPart (istF cc.jr cc.jrs j)) = [] :=
  eq_nil_of_forall_not_mem (fun X hX => by
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    rw [cc_stE cc j] at hj
    exact absurd hj List.not_mem_nil)

theorem cc_unionCirc :
    unionAll (fun j => circPart (istF cc.jr cc.jrs j)) = [] :=
  eq_nil_of_forall_not_mem (fun X hX => by
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    rw [cc_stE cc j] at hj
    exact absurd hj List.not_mem_nil)

theorem cc_hJ1 : ∀ i j, i ≠ j →
    istF cc.jr cc.jrs i ⊆ istF cc.jr cc.jrs j ++ ithF cc.jr cc.jrs j :=
  fun i _ _ => by rw [cc_stE cc i]; exact List.nil_subset _

theorem cc_hJ2 : ∀ A B : Form,
    Form.imp A B ∈ unionAll (fun j => impPart (istF cc.jr cc.jrs j)) →
    A ∈ upsilon (irhsF cc.jr cc.jrs) :=
  fun A B h => absurd (cc_unionImp cc ▸ h) List.not_mem_nil

/-- Forced `Ĝ`-members inhabit every Θ-zone, hence the intersections. -/
theorem cc_interTh {X : Form} (hX : X ∈ gHat G) (hf : K.force a X) :
    X ∈ interAll (fun j => ithF cc.jr cc.jrs j) :=
  mem_interAll.mpr (fun j => cc_thGood cc j X hX hf)

/-- Forced `Ĝ`-atoms inhabit the joint atom zone. -/
theorem cc_interAt {p : String}
    (hp : Form.atom p ∈ gAt G) (hf : K.force a (.atom p)) :
    Form.atom p ∈ interAll (fun j => atPart (ithF cc.jr cc.jrs j)) :=
  mem_interAll.mpr (fun j => List.mem_filter.mpr
    ⟨cc_thGood cc j _ (List.mem_append_left _ (List.mem_append_left _ hp)) hf,
      rfl⟩)

/-- ForceStar implications inhabit the pool. -/
theorem cc_pool {A B : Form} (hAB : Form.imp A B ∈ sfL G)
    (hf : K.force a (.imp A B)) :
    Form.imp A B ∈ thPool (fun j => ithF cc.jr cc.jrs j) := by
  refine List.mem_filter.mpr ⟨?_, rfl⟩
  refine cc_interTh cc ?_ hf
  simp only [gHat, List.mem_append]
  exact Or.inl (Or.inr (List.mem_filter.mpr ⟨hAB, rfl⟩))

/-- Υ contains every refuted `Sf^R`-prime… -/
theorem cc_upsPrime {q : Form} (hq : q ∈ refPrimes K G a) :
    q ∈ upsilon (irhsF cc.jr cc.jrs) := by
  obtain ⟨j, hj⟩ := cc.hrhs q hq
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, hj⟩

/-- …and every refuted-antecedent `Sf^R`-implication. -/
theorem cc_upsImp {Y : Form} (hY : Y ∈ refAnteImps K G a) :
    Y ∈ upsilon (irhsF cc.jr cc.jrs) := by
  obtain ⟨j, hj⟩ := cc.hrhsImp Y hY
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, hj⟩

/-- The `CornerSupply` instance over an arbitrary base whose atom zone
absorbs the forced atoms. -/
def cc_supply (hcone : K.ConeTrivial a)
    (base : List Form)
    (hbase : ∀ p : String, Form.atom p ∈ sfL G → K.force a (.atom p) →
      Form.atom p ∈ base) :
    CornerSupply K G a (upsilon (irhsF cc.jr cc.jrs)) base
      (thPool (fun j => ithF cc.jr cc.jrs j)) where
  hat := hbase
  hpool := fun A B hAB hf _ => cc_pool cc hAB hf
  hUat := fun p hp hnp => cc_upsPrime cc
    (mem_refPrimes.mpr ⟨hp, rfl, hnp⟩)
  hUimp := fun A B hAB hnf h => by
    rcases h with hnA | hfB
    · exact cc_upsImp cc (mem_refAnteImps.mpr ⟨hAB, hnf, hnA⟩)
    · exact absurd (fun u hu _ => K.force_mono hu hfB) hnf
  hUcirc := fun Z _ hnf hfZ => absurd (force_circ_of_force hfZ) hnf

/-! ### The three barren leaves -/

/-- The `⋈^At` leaf for a refuted prime. -/
def atLeaf (hcone : K.ConeTrivial a) (hinfa : ¬ K.Fal a)
    (F : Form) (hFp : F.isPrime = true) (hsf : F ∈ sfR G)
    (hnf : ¬ K.force a F) : CRow K G a F := by
  refine
    { ctx := joinCtxAtVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs) F ++
        keptOf (upsilon (irhsF cc.jr cc.jrs))
          (joinCtxAtVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs) F)
          (thPool (fun j => ithF cc.jr cc.jrs j))
      t := .barren
      der := .joinAt (ipremF cc.jr cc.jrs) (cc_hJ1 cc) (cc_hJ2 cc)
        (cc_unionCirc cc) (keptOf_ok _ _ _) hFp
        (by rw [cc_unionAt cc]; exact List.not_mem_nil) hsf (CtxEq.refl _)
      tOK := Or.inl rfl
      covF := corner_coverage_forced hcone hinfa
        (cc_supply cc hcone _ ?_) }
  intro p hp hfp
  refine List.mem_append_left _ (List.mem_append_right _ (mem_rm.mpr
    ⟨?_, cc_interAt cc (List.mem_filter.mpr ⟨hp, rfl⟩) hfp⟩))
  intro hc
  exact hnf (hc ▸ hfp)

/-- The `⋈^∨` leaf. -/
def orLeaf (hcone : K.ConeTrivial a) (hinfa : ¬ K.Fal a)
    (Z₁ Z₂ : Form) (hsf : Form.or Z₁ Z₂ ∈ sfR G)
    (hnf : ¬ K.force a (.or Z₁ Z₂)) : CRow K G a (.or Z₁ Z₂) := by
  have hbase : ∀ p : String, Form.atom p ∈ sfL G → K.force a (.atom p) →
      Form.atom p ∈ joinCtxOrVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs) := by
    intro p hp hfp
    exact List.mem_append_left _ (List.mem_append_right _
      (cc_interAt cc (List.mem_filter.mpr ⟨hp, rfl⟩) hfp))
  refine
    { ctx := joinCtxOrVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs) ++
        keptOf (upsilon (irhsF cc.jr cc.jrs))
          (joinCtxOrVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs))
          (thPool (fun j => ithF cc.jr cc.jrs j))
      t := .barren
      der := .joinOr (ipremF cc.jr cc.jrs) (cc_hJ1 cc) (cc_hJ2 cc)
        (cc_unionCirc cc) (keptOf_ok _ _ _)
        ⟨corner_coverage_refuted hcone hinfa (cc_supply cc hcone _ hbase)
            Z₁ (sfR_or hsf).1 (fun h => hnf (Or.inl h)),
          corner_coverage_refuted hcone hinfa (cc_supply cc hcone _ hbase)
            Z₂ (sfR_or hsf).2 (fun h => hnf (Or.inr h))⟩
        hsf (CtxEq.refl _)
      tOK := Or.inl rfl
      covF := corner_coverage_forced hcone hinfa (cc_supply cc hcone _ hbase) }

/-- The `⋈^◯` leaf. -/
def circLeaf (hcone : K.ConeTrivial a) (hinfa : ¬ K.Fal a)
    (Z' : Form) (hsf : Form.circ Z' ∈ sfR G)
    (hnf : ¬ K.force a (.circ Z')) : CRow K G a (.circ Z') := by
  have hbase : ∀ p : String, Form.atom p ∈ sfL G → K.force a (.atom p) →
      Form.atom p ∈ joinCtxOrVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs) := by
    intro p hp hfp
    exact List.mem_append_left _ (List.mem_append_right _
      (cc_interAt cc (List.mem_filter.mpr ⟨hp, rfl⟩) hfp))
  refine
    { ctx := joinCtxOrVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs) ++
        keptOf (upsilon (irhsF cc.jr cc.jrs))
          (joinCtxOrVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs))
          (thPool (fun j => ithF cc.jr cc.jrs j))
      t := .barren
      der := .joinCirc (ipremF cc.jr cc.jrs) (cc_hJ1 cc) (cc_hJ2 cc)
        (cc_unionCirc cc) (keptOf_ok _ _ _)
        (corner_coverage_refuted hcone hinfa (cc_supply cc hcone _ hbase)
          Z' (sfR_circ hsf) (not_force_body hnf))
        hsf (CtxEq.refl _)
      tOK := Or.inl rfl
      covF := corner_coverage_forced hcone hinfa (cc_supply cc hcone _ hbase) }

/-- **The row builder**: structural descent to the three barren
leaves. -/
def rowFor (hcone : K.ConeTrivial a) (hinfa : ¬ K.Fal a)
    (rfl' : RFloat K G a) :
    ∀ (Z : Form), Z ∈ sfR G → ¬ K.force a Z → CRow K G a Z
  | .atom p, hsf, hnf => atLeaf cc hcone hinfa (.atom p) rfl hsf hnf
  | .bot, hsf, hnf => atLeaf cc hcone hinfa .bot rfl hsf hnf
  | .or Z₁ Z₂, hsf, hnf => orLeaf cc hcone hinfa Z₁ Z₂ hsf hnf
  | .circ Z', hsf, hnf => circLeaf cc hcone hinfa Z' hsf hnf
  | .and Z₁ Z₂, hsf, hnf =>
      if h1 : K.force a Z₁ then
        let w := rowFor hcone hinfa rfl' Z₂ (sfR_and hsf).2
          (fun h => hnf ⟨h1, h⟩)
        { ctx := w.ctx, t := w.t, der := .andR2 w.der hsf
          tOK := tOK_lift w.tOK (fun hc => .andR hc), covF := w.covF }
      else
        let w := rowFor hcone hinfa rfl' Z₁ (sfR_and hsf).1 h1
        { ctx := w.ctx, t := w.t, der := .andR1 w.der hsf
          tOK := tOK_lift w.tOK (fun hc => .andL hc), covF := w.covF }
  | .imp A B, hsf, hnf =>
      if hfA : K.force a A then
        let w := rowFor hcone hinfa rfl' B (sfR_imp hsf).2
          (not_force_consequent hnf)
        have hA : Clo w.ctx A := w.covF A (sfR_imp hsf).1 hfA
        { ctx := w.ctx, t := w.t, der := .impIn w.der hA hsf
          tOK := tOK_lift w.tOK (fun hc => .imp hc hA), covF := w.covF }
      else rfl' A B hsf hnf hfA

/-- **The corner's irregular `◯Z`-cell**, by `◯∉` over the built row;
`hTh` is the coverage. -/
def cornerIrrWit (hcone : K.ConeTrivial a) (hinfa : ¬ K.Fal a)
    (rfl' : RFloat K G a)
    {Z : Form} (hOZ : Form.circ Z ∈ sfR G)
    (hnfOZ : ¬ K.force a (.circ Z)) : IrrWitV K G a (.circ Z) :=
  let w := rowFor cc hcone hinfa rfl' Z (sfR_circ hOZ) (not_force_body hnfOZ)
  { stab := []
    th := lamStar K a G
    der := .circNotIn w.der w.tOK
      (fun X hX => ⟨w.covF X (mem_lamStar.mp hX).1
          (K.forceStar_force (mem_lamStar.mp hX).2),
        lamStar_subset_gHat hX⟩) hOZ
    sub := fun _ h => absurd h List.not_mem_nil
    cov := fun _ hx => hx }

end Corner

/-! ## The recursion, corner served in place -/

def minModF (K : Kripke) (G : Form)
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = [])
    (hinf : K.Infallible)
    (a : K.W) (t : Nat) (C : Form)
    (hC : C ∈ sfR G) (hnf : ¬ K.force a C) : MinModStmtV K G a t C := by
  match t, C with
  | 0, .circ Z =>
      have hnfZ : ¬ K.force a Z := not_force_body hnf
      match hcand : K.elems.filter
          (fun u => decide (K.le a u ∧ u ≠ a ∧ ¬ K.force u Z)) with
      | u :: _ =>
          have hu : u ∈ K.elems.filter
              (fun u => decide (K.le a u ∧ u ≠ a ∧ ¬ K.force u Z)) := by
            rw [hcand]; exact List.mem_cons_self
          have hspec : K.le a u ∧ u ≠ a ∧ ¬ K.force u Z := by
            have := (List.mem_filter.mp hu).2
            simpa using this
          let w := minModF K G hloc hinf u 1 Z (sfR_circ hC) hspec.2.2
          exact { stab := [], th := lamStar K a G
                  der := .circNotIn w.der w.tOK
                    (fun X hX => ⟨clo_mono w.cov (lamStar_mono (hinf _)
                        (K.le_trans hspec.1 w.wle) X hX),
                      lamStar_subset_gHat hX⟩) hC
                  sub := fun _ h => absurd h List.not_mem_nil
                  cov := fun _ hx => hx }
      | [] =>
          -- THE CORNER, SERVED: every proper extension forces `Z`
          have hsole : ∀ u, K.le a u → u ≠ a → K.force u Z := by
            intro u hau hune
            by_contra hufZ
            have hmem : u ∈ K.elems.filter
                (fun u => decide (K.le a u ∧ u ≠ a ∧ ¬ K.force u Z)) :=
              List.mem_filter.mpr ⟨K.complete u, by simp [hau, hune, hufZ]⟩
            rw [hcand] at hmem
            exact absurd hmem List.not_mem_nil
          have hcone : K.ConeTrivial a := coneTrivial_of_corner hnf hsole
          -- the float-cell suppliers, both recursing strictly above
          exact cornerIrrWit
            (mkCornerCtx
              (fun A B hsf hnfY hnA =>
                let m := minEta hnfY
                have hea : ¬(m.e = a) := fun h => hnA (h ▸ m.fA)
                let w := minModF K G hloc hinf m.e 1 B (sfR_imp hsf).2 m.nfB
                have hthg : thGoodAt K G a
                    ((gHat G).filter (fun X =>
                      cloB w.ctx X && decide (K.force a X))) := by
                  intro X hX hfX
                  refine List.mem_filter.mpr ⟨hX, ?_⟩
                  have hclo : Clo w.ctx X := clo_mono w.cov
                    (mem_clo_lamStar (hinf _) (gHat_subset_sfL hX)
                      (K.force_mono (K.le_trans m.le w.wle) hfX))
                  simp [cloB_iff.mpr hclo, hfX]
                ⟨⟨⟨[], (gHat G).filter (fun X =>
                      cloB w.ctx X && decide (K.force a X)), .imp A B,
                    .impNotIn w.der
                      (fun X hX => ⟨cloB_iff.mp
                          (Bool.and_elim_left ((List.mem_filter.mp hX).2)),
                        (List.mem_filter.mp hX).1⟩)
                      (clo_mono w.cov (mem_clo_lamStar (hinf _)
                        (sfR_imp hsf).1 (K.force_mono w.wle m.fA)))
                      (fun hc => hnA (clo_forces
                        (fun X hX => of_decide_eq_true
                          (Bool.and_elim_right ((List.mem_filter.mp hX).2)))
                        hc))
                      hsf⟩,
                  rfl, hthg⟩, rfl⟩)
              hC hnf)
            hcone (hinf a)
            (fun A B hsf hnfY hnA =>
              let m := minEta hnfY
              have hea : ¬(m.e = a) := fun h => hnA (h ▸ m.fA)
              let w := minModF K G hloc hinf m.e 1 B (sfR_imp hsf).2 m.nfB
              have hAclo : Clo w.ctx A := clo_mono w.cov
                (mem_clo_lamStar (hinf _) (sfR_imp hsf).1
                  (K.force_mono w.wle m.fA))
              { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hsf
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                covF := fun X hXs hfX => clo_mono w.cov
                  (mem_clo_lamStar (hinf _) hXs
                    (K.force_mono (K.le_trans m.le w.wle) hfX)) })
            hC hnf
  | (n+1), .circ Z =>
      have hnfZ : ¬ K.force a Z := not_force_body hnf
      let w := minModF K G hloc hinf a (n+1) Z (sfR_circ hC) hnfZ
      exact { ctx := w.ctx, t := w.t
              der := .circIn w.der w.tOK hC
              tOK := tOK_lift w.tOK (fun hc => .circ hc)
              wld := w.wld, wle := w.wle, cov := w.cov }
  | 0, .atom p =>
      exact { stab := [], th := (rm (gAt G) (.atom p)) ++ gImp G ++ gCirc G
              der := .axI (.atom p) rfl hC (CtxEq.refl _)
              sub := fun _ h => absurd h List.not_mem_nil
              cov := fun _ hx => lamStar_subset_axI hnf hx }
  | 0, .bot =>
      exact { stab := [], th := (rm (gAt G) .bot) ++ gImp G ++ gCirc G
              der := .axI .bot rfl hC (CtxEq.refl _)
              sub := fun _ h => absurd h List.not_mem_nil
              cov := fun _ hx => lamStar_subset_axI hnf hx }
  | 0, .and C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_and hC
      by_cases h1 : K.force a C₁
      · have h2 : ¬ K.force a C₂ := fun hc => hnf ⟨h1, hc⟩
        let w := minModF K G hloc hinf a 0 C₂ hC2 h2
        exact { stab := w.stab, th := w.th, der := .andI2 w.der hC
                sub := w.sub, cov := w.cov }
      · let w := minModF K G hloc hinf a 0 C₁ hC1 h1
        exact { stab := w.stab, th := w.th, der := .andI1 w.der hC
                sub := w.sub, cov := w.cov }
  | 0, .or C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_or hC
      have h1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
      have h2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
      let w₁ := minModF K G hloc hinf a 0 C₁ hC1 h1
      let w₂ := minModF K G hloc hinf a 0 C₂ hC2 h2
      refine { stab := w₁.stab ++ w₂.stab, th := cap w₁.th w₂.th
               der := .orI w₁.der w₂.der (fun X hX => w₂.cov (w₁.sub hX))
                        (fun X hX => w₁.cov (w₂.sub hX)) hC (CtxEq.refl _)
                        (CtxEq.refl _)
               sub := ?_, cov := ?_ }
      · intro X hX
        rcases List.mem_append.mp hX with hX' | hX'
        · exact w₁.sub hX'
        · exact w₂.sub hX'
      · intro X hX
        by_cases hx1 : X ∈ w₁.stab
        · exact List.mem_append_left _ (List.mem_append_left _ hx1)
        · by_cases hx2 : X ∈ w₂.stab
          · exact List.mem_append_left _ (List.mem_append_right _ hx2)
          · exact List.mem_append_right _ (mem_cap.mpr
              ⟨(List.mem_append.mp (w₁.cov hX)).resolve_left hx1,
               (List.mem_append.mp (w₂.cov hX)).resolve_left hx2⟩)
  | 0, .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      let m := minEta hnf
      by_cases hea : m.e = a
      · have heA : K.force a A := hea ▸ m.fA
        have heB : ¬ K.force a B := hea ▸ m.nfB
        let w := minModF K G hloc hinf a 0 B hB heB
        have hLamTh : sdiff (lamStar K a G) w.stab ⊆ w.th := by
          intro x hx
          obtain ⟨hx1, hx2⟩ := mem_sdiff.mp hx
          exact (List.mem_append.mp (w.cov hx1)).resolve_left hx2
        have hStLam : lamStar K a G ⊆ w.stab ++ sdiff (lamStar K a G) w.stab := by
          intro x hx
          by_cases hs : x ∈ w.stab
          · exact List.mem_append_left _ hs
          · exact List.mem_append_right _ (mem_sdiff.mpr ⟨hx, hs⟩)
        have hzone : w.th ≐ sdiff w.th (sdiff (lamStar K a G) w.stab) ++
            sdiff (lamStar K a G) w.stab := by
          intro x
          constructor
          · intro hx
            by_cases hL : x ∈ sdiff (lamStar K a G) w.stab
            · exact List.mem_append_right _ hL
            · exact List.mem_append_left _ (mem_sdiff.mpr ⟨hx, hL⟩)
          · intro hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact (mem_sdiff.mp hx').1
            · exact hLamTh hx'
        have hAclo : Clo (w.stab ++ sdiff (lamStar K a G) w.stab) A :=
          clo_mono hStLam (mem_clo_lamStar (hinf _) hA heA)
        refine { stab := w.stab ++ sdiff (lamStar K a G) w.stab
                 th := sdiff w.th (sdiff (lamStar K a G) w.stab)
                 der := .impInI w.der hzone cap_sdiff_eq_nil hAclo hC
                          (CtxEq.refl _) (CtxEq.refl _)
                 sub := ?_, cov := ?_ }
        · intro X hX
          rcases List.mem_append.mp hX with hX' | hX'
          · exact w.sub hX'
          · exact (mem_sdiff.mp hX').1
        · intro X hX
          exact List.mem_append_left _ (hStLam hX)
      · have hnaA : ¬ K.force a A :=
          m.min a (K.le_refl a) m.le (fun hc => hea hc.symm)
        let w := minModF K G hloc hinf m.e 1 B hB m.nfB
        exact { stab := [], th := lamStar K a G
                der := .impNotIn w.der
                  (fun X hX => ⟨clo_mono w.cov (lamStar_mono (hinf _)
                      (K.le_trans m.le w.wle) X hX),
                    lamStar_subset_gHat hX⟩)
                  (clo_mono w.cov (mem_clo_lamStar (hinf _) hA
                    (K.force_mono w.wle m.fA)))
                  (fun hc => hnaA (forces_clo_lamStar hc)) hC
                sub := fun _ h => absurd h List.not_mem_nil
                cov := fun _ hx => hx }
  | (n+1), .atom p =>
      by_cases hempty : impPart (lamStar K a G) = []
      · exact regPrimeV_ax K G a (.atom p) (hloc a) rfl hC hnf hempty
      · refine regPrimeV_join K G a (.atom p) (hloc a) rfl hC hnf ?_
          (fun A hA hnA => minModF K G hloc hinf a 0 A hA hnA)
        intro hc
        refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
        obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
        match X, hXi with
        | .imp A B, _ =>
            exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
  | (n+1), .bot =>
      by_cases hempty : impPart (lamStar K a G) = []
      · exact regPrimeV_ax K G a .bot (hloc a) rfl hC hnf hempty
      · refine regPrimeV_join K G a .bot (hloc a) rfl hC hnf ?_
          (fun A hA hnA => minModF K G hloc hinf a 0 A hA hnA)
        intro hc
        refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
        obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
        match X, hXi with
        | .imp A B, _ =>
            exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
  | (n+1), .and C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_and hC
      by_cases h1 : K.force a C₁
      · have h2 : ¬ K.force a C₂ := fun hc => hnf ⟨h1, hc⟩
        let w := minModF K G hloc hinf a (n+1) C₂ hC2 h2
        exact { ctx := w.ctx, t := w.t, der := .andR2 w.der hC
                tOK := tOK_lift w.tOK (fun hc => .andR hc)
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModF K G hloc hinf a (n+1) C₁ hC1 h1
        exact { ctx := w.ctx, t := w.t, der := .andR1 w.der hC
                tOK := tOK_lift w.tOK (fun hc => .andL hc)
                wld := w.wld, wle := w.wle, cov := w.cov }
  | (n+1), .or C₁ C₂ =>
      exact regOrV_join K G a C₁ C₂ (hloc a) hC hnf
        (fun A hA hnA => minModF K G hloc hinf a 0 A hA hnA)
  | (n+1), .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      let m := minEta hnf
      by_cases hea : m.e = a
      · have heA : K.force a A := hea ▸ m.fA
        have heB : ¬ K.force a B := hea ▸ m.nfB
        let w := minModF K G hloc hinf a (n+1) B hB heB
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle heA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModF K G hloc hinf m.e 1 B hB m.nfB
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle m.fA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                wld := w.wld, wle := K.le_trans m.le w.wle, cov := w.cov }
termination_by (ht K a, t, C.size)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left
         exact ht_lt m.le hea)
      | (apply Prod.Lex.left
         exact ht_lt hspec.1 hspec.2.1)
      | (apply Prod.Lex.right
         apply Prod.Lex.left
         omega)
      | (apply Prod.Lex.right
         apply Prod.Lex.right
         first
           | omega
           | (simp only [Form.size]; omega))

/-! ## The campaign statement -/

/-- **FRJV completeness — supply-free, guard-free, frame-free**: every
infallible countermodel with world-wise `◯`-free `Λ*` yields an FRJV
derivation, `◯` unrestricted on both sides of the goal. -/
theorem completenessV {G : Form} (K : Kripke)
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = [])
    (hinf : K.Infallible)
    (hK : ¬ K.valid G) : ProvableV G :=
  let w := minModF K G hloc hinf K.root 1 G (sfR_self G) hK
  ⟨w.t, w.ctx, ⟨w.der⟩⟩

/-- info: 'FRJ.minModF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms minModF

/-- info: 'FRJ.completenessV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completenessV

end FRJ
