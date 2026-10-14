import LaxLogic.PLL.SemUI.SubframeLayered

/-!
# Step 3 of the semantic route in the subframe semantics: amalgamation

From a layered bisimulation linking `k₀ ∈ K` and `m₀ ∈ M` at a sufficient
level, over the atoms of a subformula-closed `X` other than `p`, build a
`p`-variant `N` of `M` (an unbounded bisimulation off `p`) whose copy of `m₀`
forces exactly the formulas of `X` that `k₀` forces.  With `ν` the number of
atoms, implications and `◯`-formulas in `X` (`SemUI.nu`), the levels are

    2ν + 1   for the ◯-free instance (`amalgamationI`, rule 8 first),
    3ν + 2   for PLL (`amalgamation`).

The ◯-free instance is Visser's lemma in the form of Litak–Visser: a world of
the amalgam is a *reservoir* pair `k′ Z m′` at level `2d + 1` and a *current*
pair `k Z m` at level `2d`, with `k′ ≤ k`, `m′ ≤ m` and `k′`, `k` forcing the
same formulas of `X`; `d` is the depth of `k′`, the number of budget formulas
of `X` it does not force (`dep`).  The order is componentwise on the
`M`-coordinate and on the `X`-theory of the current `K`-world.  Moves of `M`
are answered from the reservoir, so they cost nothing; a move that enlarges
the `X`-theory drops the depth and lands on a fresh reservoir.

For PLL the subframe clause `x ⊩ ◯φ ⟺ ∀ y ≥ x, y ∈ S → y ⊩ φ` adds one kind of
world, an *`S`-world*: the current pair at level `3d` with both ends
`S`-points.  `S` of the amalgam is the set of worlds whose current pair has
both ends in `S`.

* An `S`-world refutes in place every `◯ξ` its current `K`-world refutes: if
  `s ≥ k` is an `S`-point refuting `ξ`, so does `k`, and the world is its own
  `S`-successor.
* A world not in `S` refuting `◯ξ` through an `S`-point `s` with the same
  `X`-theory moves to the `S`-world over `s`, one level down from the
  current pair; with a larger theory the depth drops.
* Moves of `M`, to `S`-points or not, are answered from the reservoir.

So the current pair lives at `3d + 1` (normal) or `3d` (`S`-world), the
reservoir at `3d + 2`, and a theory-enlarging move from level `3d` still lands
at `3(d − 1) + 2`.  The constraint-model proof
(`SemUI.LayeredAmalg.amalgamationE`, level `4ν + 2`) needed `X`-rigid worlds to
block `◯` along `Rₘ`; here `S`-points block in place, and that saves a level.

`PBisim.force_iff` is the invariance of `p`-free formulas under a `p`-variant,
which the assembly of the route needs.
-/

open PLLFormula

namespace PLLND
namespace SubframeModel

open SemUI (boxFree isBudget nu)

/-! ## `p`-variants of subframe models -/

/-- An unbounded bisimulation off `p` without the `S`-clauses (the ◯-free
notion). -/
structure PBisimI (p : String) (M N : SubframeModel) where
  Z : M.W → N.W → Prop
  atoms : ∀ {m n}, Z m n → ∀ a, a ≠ p → (m ∈ M.V a ↔ n ∈ N.V a)
  forth : ∀ {m n}, Z m n → ∀ {m₂}, M.le m m₂ → ∃ n₂, N.le n n₂ ∧ Z m₂ n₂
  back : ∀ {m n}, Z m n → ∀ {n₂}, N.le n n₂ → ∃ m₂, M.le m m₂ ∧ Z m₂ n₂

/-- An unbounded bisimulation off `p`: `N` is a `p`-variant of `M`. -/
structure PBisim (p : String) (M N : SubframeModel) extends PBisimI p M N where
  sforth : ∀ {m n}, Z m n → ∀ {m₂}, M.le m m₂ → m₂ ∈ M.S →
    ∃ n₂, N.le n n₂ ∧ n₂ ∈ N.S ∧ Z m₂ n₂
  sback : ∀ {m n}, Z m n → ∀ {n₂}, N.le n n₂ → n₂ ∈ N.S →
    ∃ m₂, M.le m m₂ ∧ m₂ ∈ M.S ∧ Z m₂ n₂

variable {M N : SubframeModel}

theorem ne_of_not_mem_atoms_prop {p a : String}
    (hp : p ∉ (PLLFormula.prop a).atoms) : a ≠ p := by
  rintro rfl
  exact hp (by simp)

/-- **Invariance, ◯-free**: a `p`-variant preserves the ◯-free `p`-free
formulas. -/
theorem PBisimI.force_iff {p : String} (C : PBisimI p M N) :
    ∀ (φ : PLLFormula), boxFree φ = true → p ∉ φ.atoms →
      ∀ {m : M.W} {n : N.W}, C.Z m n → (M.force m φ ↔ N.force n φ)
  | .prop a, _, hp, _, _, hZ => C.atoms hZ a (ne_of_not_mem_atoms_prop hp)
  | .falsePLL, _, _, _, _, _ => Iff.rfl
  | .and φ ψ, hb, hp, _, _, hZ => by
      simp only [boxFree, Bool.and_eq_true] at hb
      exact and_congr
        (PBisimI.force_iff C φ hb.1 (fun h => hp (mem_atoms_and.mpr (Or.inl h))) hZ)
        (PBisimI.force_iff C ψ hb.2 (fun h => hp (mem_atoms_and.mpr (Or.inr h))) hZ)
  | .or φ ψ, hb, hp, _, _, hZ => by
      simp only [boxFree, Bool.and_eq_true] at hb
      exact or_congr
        (PBisimI.force_iff C φ hb.1 (fun h => hp (mem_atoms_or.mpr (Or.inl h))) hZ)
        (PBisimI.force_iff C ψ hb.2 (fun h => hp (mem_atoms_or.mpr (Or.inr h))) hZ)
  | .ifThen φ ψ, hb, hp, _, _, hZ => by
      simp only [boxFree, Bool.and_eq_true] at hb
      have hpφ : p ∉ φ.atoms := fun h => hp (mem_atoms_ifThen.mpr (Or.inl h))
      have hpψ : p ∉ ψ.atoms := fun h => hp (mem_atoms_ifThen.mpr (Or.inr h))
      constructor
      · intro hM n₂ hn hφ
        obtain ⟨m₂, hm, hZ'⟩ := C.back hZ hn
        exact (PBisimI.force_iff C ψ hb.2 hpψ hZ').mp
          (hM m₂ hm ((PBisimI.force_iff C φ hb.1 hpφ hZ').mpr hφ))
      · intro hN m₂ hm hφ
        obtain ⟨n₂, hn, hZ'⟩ := C.forth hZ hm
        exact (PBisimI.force_iff C ψ hb.2 hpψ hZ').mpr
          (hN n₂ hn ((PBisimI.force_iff C φ hb.1 hpφ hZ').mp hφ))
  | .somehow _, hb, _, _, _, _ => by simp [boxFree] at hb

/-- **Invariance**: a `p`-variant preserves the `p`-free formulas. -/
theorem PBisim.force_iff {p : String} (C : PBisim p M N) :
    ∀ (φ : PLLFormula), p ∉ φ.atoms →
      ∀ {m : M.W} {n : N.W}, C.Z m n → (M.force m φ ↔ N.force n φ)
  | .prop a, hp, _, _, hZ => C.atoms hZ a (ne_of_not_mem_atoms_prop hp)
  | .falsePLL, _, _, _, _ => Iff.rfl
  | .and φ ψ, hp, _, _, hZ =>
      and_congr
        (PBisim.force_iff C φ (fun h => hp (mem_atoms_and.mpr (Or.inl h))) hZ)
        (PBisim.force_iff C ψ (fun h => hp (mem_atoms_and.mpr (Or.inr h))) hZ)
  | .or φ ψ, hp, _, _, hZ =>
      or_congr
        (PBisim.force_iff C φ (fun h => hp (mem_atoms_or.mpr (Or.inl h))) hZ)
        (PBisim.force_iff C ψ (fun h => hp (mem_atoms_or.mpr (Or.inr h))) hZ)
  | .ifThen φ ψ, hp, _, _, hZ => by
      have hpφ : p ∉ φ.atoms := fun h => hp (mem_atoms_ifThen.mpr (Or.inl h))
      have hpψ : p ∉ ψ.atoms := fun h => hp (mem_atoms_ifThen.mpr (Or.inr h))
      constructor
      · intro hM n₂ hn hφ
        obtain ⟨m₂, hm, hZ'⟩ := C.back hZ hn
        exact (PBisim.force_iff C ψ hpψ hZ').mp
          (hM m₂ hm ((PBisim.force_iff C φ hpφ hZ').mpr hφ))
      · intro hN m₂ hm hφ
        obtain ⟨n₂, hn, hZ'⟩ := C.forth hZ hm
        exact (PBisim.force_iff C ψ hpψ hZ').mpr
          (hN n₂ hn ((PBisim.force_iff C φ hpφ hZ').mp hφ))
  | .somehow φ, hp, _, _, hZ => by
      constructor
      · intro hM n₂ hn hS
        obtain ⟨m₂, hm, hmS, hZ'⟩ := C.sback hZ hn hS
        exact (PBisim.force_iff C φ hp hZ').mp (hM m₂ hm hmS)
      · intro hN m₂ hm hS
        obtain ⟨n₂, hn, hnS, hZ'⟩ := C.sforth hZ hm hS
        exact (PBisim.force_iff C φ hp hZ').mpr (hN n₂ hn hnS)

/-- Levels drop along `≤`. -/
theorem LayeredBisimI.mono_le {A : String → Prop} (B : LayeredBisimI A M N) :
    ∀ {m n : Nat}, m ≤ n → ∀ {w w'}, B.Z n w w' → B.Z m w w' := by
  intro m n h
  induction h with
  | refl => exact fun h => h
  | step _ ih => exact fun h => ih (B.mono h)

namespace Amalg

attribute [local instance] Classical.propDecidable

variable {K M : SubframeModel}

/-! ## Depth -/

/-- Depth of a world relative to `X`: how many budget formulas of `X` (atoms,
implications, `◯`-formulas) it does not force. -/
noncomputable def dep (X : Finset PLLFormula) (K : SubframeModel) (k : K.W) : Nat :=
  (X.filter (fun φ => isBudget φ = true ∧ ¬ K.force k φ)).card

theorem dep_le_nu (X : Finset PLLFormula) (K : SubframeModel) (k : K.W) :
    dep X K k ≤ nu X := by
  unfold dep nu
  apply Finset.card_le_card
  intro φ hφ
  simp only [Finset.mem_filter] at hφ ⊢
  exact ⟨hφ.1, hφ.2.1⟩

/-- The budget formulas of `X` decide all of `X`. -/
theorem force_of_budget {X : Finset PLLFormula} (hX : SubClosed X) {k k' : K.W}
    (h : ∀ φ ∈ X, isBudget φ = true → K.force k' φ → K.force k φ) :
    ∀ φ, φ ∈ X → K.force k' φ → K.force k φ := by
  intro φ
  induction φ with
  | prop a => exact fun hφ hf => h _ hφ rfl hf
  | falsePLL => exact fun _ hf => False.elim hf
  | and φ ψ ihφ ihψ =>
      intro hφ hf
      simp only [force] at hf ⊢
      exact ⟨ihφ (hX.and_left hφ) hf.1, ihψ (hX.and_right hφ) hf.2⟩
  | or φ ψ ihφ ihψ =>
      intro hφ hf
      simp only [force] at hf ⊢
      exact hf.elim (fun x => .inl (ihφ (hX.or_left hφ) x))
        (fun x => .inr (ihψ (hX.or_right hφ) x))
  | ifThen φ ψ _ _ => exact fun hφ hf => h _ hφ rfl hf
  | somehow φ _ => exact fun hφ hf => h _ hφ rfl hf

/-- **A strict move drops the depth.** -/
theorem dep_lt {X : Finset PLLFormula} (hX : SubClosed X) {k k' : K.W}
    (hkk : K.le k k') (hne : ¬ ∀ φ ∈ X, K.force k' φ → K.force k φ) :
    dep X K k' < dep X K k := by
  have hex : ∃ φ ∈ X, isBudget φ = true ∧ K.force k' φ ∧ ¬ K.force k φ := by
    by_contra hc
    refine hne (force_of_budget hX fun φ hφ hb hf => ?_)
    by_contra hn
    exact hc ⟨φ, hφ, hb, hf, hn⟩
  obtain ⟨φ, hφ, hb, hf, hn⟩ := hex
  unfold dep
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro ψ hψ
    simp only [Finset.mem_filter] at hψ ⊢
    exact ⟨hψ.1, hψ.2.1, fun hh => hψ.2.2 (K.force_mono ψ hkk hh)⟩
  · intro hEq
    have hm : φ ∈ X.filter (fun φ => isBudget φ = true ∧ ¬ K.force k φ) :=
      Finset.mem_filter.mpr ⟨hφ, hb, hn⟩
    rw [← hEq] at hm
    exact (Finset.mem_filter.mp hm).2.2 hf

/-- A world refuting `φ ↠ ψ` has a successor forcing `φ` and refuting `ψ`. -/
theorem exists_of_not_force_imp {K : SubframeModel} {k : K.W} {φ ψ : PLLFormula}
    (hn : ¬ K.force k (φ ↠ ψ)) :
    ∃ k₂, K.le k k₂ ∧ K.force k₂ φ ∧ ¬ K.force k₂ ψ := by
  by_contra hc
  refine hn fun v hv hf => ?_
  by_contra hψ
  exact hc ⟨v, hv, hf, hψ⟩

/-- A world refuting `◯ξ` has an `S`-point above it refuting `ξ`. -/
theorem exists_of_not_force_box {K : SubframeModel} {k : K.W} {ξ : PLLFormula}
    (hn : ¬ K.force k (◯ξ)) :
    ∃ s, K.le k s ∧ s ∈ K.S ∧ ¬ K.force s ξ := by
  by_contra hc
  refine hn fun v hv hS => ?_
  by_contra hξ
  exact hc ⟨v, hv, hS, hξ⟩

/-! ## The ◯-free instance (IPC), level `2ν + 1` -/

section IPC

variable {A : String → Prop} (X : Finset PLLFormula) (B : LayeredBisimI A K M)

/-- Certificate of an amalgam world over `m`: a reservoir pair `(k′, m′)` at
level `2d + 1` below a current pair `(k, m)` at level `2d`, with `k′` and `k`
forcing the same formulas of `X`, `d` the depth of `k′`. -/
structure CertI (k' k : K.W) (m' m : M.W) : Prop where
  hk : K.le k' k
  hm : M.le m' m
  hth : ∀ φ ∈ X, K.force k φ → K.force k' φ
  hres : B.Z (2 * dep X K k' + 1) k' m'
  hcur : B.Z (2 * dep X K k') k m

/-- The worlds of the ◯-free amalgam. -/
structure WI where
  k' : K.W
  k : K.W
  m' : M.W
  m : M.W
  c : CertI X B k' k m' m

variable {X B}

/-- Inclusion of the `X`-theories of the current `K`-worlds. -/
def thLeI (w w' : WI X B) : Prop := ∀ φ ∈ X, K.force w.k φ → K.force w'.k φ

variable (X B)

/-- **The ◯-free amalgam.**  The order is componentwise on the `M`-coordinate
and the `X`-theory; atoms other than `p` are read from `M`, `p` from the
current `K`-world. -/
def amalI (p : String) : SubframeModel where
  W := WI X B
  le := fun a b => M.le a.m b.m ∧ thLeI a b
  S := ∅
  V := fun x => {a | if x = p then PLLFormula.prop p ∈ X ∧ K.force a.k (.prop p)
    else a.m ∈ M.V x}
  refl := fun a => ⟨M.refl _, fun _ _ h => h⟩
  trans := fun h₁ h₂ => ⟨M.trans h₁.1 h₂.1, fun φ hφ h => h₂.2 φ hφ (h₁.2 φ hφ h)⟩
  hered := by
    intro x a b h hv
    have hv' : (if x = p then PLLFormula.prop p ∈ X ∧ K.force a.k (.prop p)
        else a.m ∈ M.V x) := hv
    show (if x = p then PLLFormula.prop p ∈ X ∧ K.force b.k (.prop p)
        else b.m ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx] at hv' ⊢
      exact ⟨hv'.1, h.2 _ hv'.1 hv'.2⟩
    · rw [if_neg hx] at hv' ⊢
      exact M.hered h.1 hv'

variable {X B}

/-- **Landing after a strict move**, ◯-free. -/
theorem land_strictI (hX : SubClosed X) {k' k₂ : K.W} {m₂ : M.W} {n : Nat}
    (hk : K.le k' k₂) (hZ : B.Z n k₂ m₂)
    (hstrict : ¬ ∀ φ ∈ X, K.force k₂ φ → K.force k' φ)
    (hlev : 2 * dep X K k' ≤ n + 1) :
    ∃ w : WI X B, w.m = m₂ ∧ w.k = k₂ := by
  have hlt := dep_lt hX hk hstrict
  exact ⟨⟨k₂, k₂, m₂, m₂, ⟨K.refl _, M.refl _, fun _ _ h => h,
    B.mono_le (by omega) hZ, B.mono_le (by omega) hZ⟩⟩, rfl, rfl⟩

/-- **Answering a move of `M` from the reservoir**, ◯-free. -/
theorem land_reservoirI (hX : SubClosed X) {k' k₂ : K.W} {m' m₂ : M.W}
    (hres : B.Z (2 * dep X K k' + 1) k' m') (hk : K.le k' k₂) (hm : M.le m' m₂)
    (hZ : B.Z (2 * dep X K k') k₂ m₂) :
    ∃ w : WI X B, w.m = m₂ ∧ w.k = k₂ := by
  by_cases hsame : ∀ φ ∈ X, K.force k₂ φ → K.force k' φ
  · exact ⟨⟨k', k₂, m', m₂, ⟨hk, hm, hsame, hres, hZ⟩⟩, rfl, rfl⟩
  · exact land_strictI hX hk hZ hsame (by omega)

/-- **Truth lemma, ◯-free.** -/
theorem amalI_force (p : String)
    (hA : ∀ a, a ≠ p → PLLFormula.prop a ∈ X → A a) (hX : SubClosed X)
    (hX0 : ∀ φ ∈ X, boxFree φ = true) :
    ∀ (φ : PLLFormula), φ ∈ X → ∀ w : WI X B,
      ((amalI X B p).force w φ ↔ K.force w.k φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ w
      show (if a = p then PLLFormula.prop p ∈ X ∧ K.force w.k (.prop p)
        else w.m ∈ M.V a) ↔ _
      by_cases ha : a = p
      · subst ha
        rw [if_pos rfl]
        exact ⟨fun h => h.2, fun h => ⟨hφ, h⟩⟩
      · rw [if_neg ha]
        exact (B.atoms w.c.hcur a (hA a ha hφ)).symm
  | falsePLL => exact fun _ _ => Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro hφ w
      exact and_congr (ihφ (hX.and_left hφ) w) (ihψ (hX.and_right hφ) w)
  | or φ ψ ihφ ihψ =>
      intro hφ w
      exact or_congr (ihφ (hX.or_left hφ) w) (ihψ (hX.or_right hφ) w)
  | ifThen φ ψ ihφ ihψ =>
      intro hmem w
      have hφX := hX.imp_left hmem
      have hψX := hX.imp_right hmem
      constructor
      · -- forcing ⇒ `K`: refute in place, or by a strict move
        intro hN
        by_contra hn
        obtain ⟨k₂, hk₂, hf, hnψ⟩ := exists_of_not_force_imp hn
        by_cases hkφ : K.force w.k φ
        · have h1 := hN w ((amalI X B p).refl w) ((ihφ hφX w).mpr hkφ)
          exact hnψ (K.force_mono ψ hk₂ ((ihψ hψX w).mp h1))
        · have hstrict : ¬ ∀ χ ∈ X, K.force k₂ χ → K.force w.k' χ :=
            fun h => hkφ (K.force_mono φ w.c.hk (h φ hφX hf))
          have hlt := dep_lt hX (K.trans w.c.hk hk₂) hstrict
          have hcur : B.Z ((2 * dep X K w.k' - 1) + 1) w.k w.m :=
            B.mono_le (by omega) w.c.hcur
          obtain ⟨m₂, hm₂, hZ⟩ := B.forth hcur hk₂
          obtain ⟨w₂, hpt, hk2⟩ :=
            land_strictI hX (K.trans w.c.hk hk₂) hZ hstrict (by omega)
          have hR : (amalI X B p).le w w₂ :=
            ⟨by rw [hpt]; exact hm₂, fun χ _ h => by
              rw [hk2]; exact K.force_mono χ hk₂ h⟩
          have h1 := hN w₂ hR ((ihφ hφX w₂).mpr (by rw [hk2]; exact hf))
          exact hnψ (by have := (ihψ hψX w₂).mp h1; rwa [hk2] at this)
      · -- `K` ⇒ forcing: the implication travels along the theory order
        intro hw w' hww' hfφ
        have hw' : K.force w'.k (φ.ifThen ψ) := hww'.2 _ hmem hw
        exact (ihψ hψX w').mpr (hw' w'.k (K.refl _) ((ihφ hφX w').mp hfφ))
  | somehow ξ _ =>
      intro hmem
      exact absurd (hX0 _ hmem) (by simp [boxFree])

/-- **The projection to `M` is a `p`-variant**, ◯-free. -/
def amalI_pbisim (p : String) (hX : SubClosed X) : PBisimI p M (amalI X B p) where
  Z := fun m w => w.m = m
  atoms := by
    rintro m w rfl a ha
    show w.m ∈ M.V a ↔ (if a = p then PLLFormula.prop p ∈ X ∧ K.force w.k (.prop p)
      else w.m ∈ M.V a)
    rw [if_neg ha]
  forth := by
    rintro m w rfl m₂ hm₂
    obtain ⟨k₂, hk₂, hZ⟩ := B.back w.c.hres (M.trans w.c.hm hm₂)
    obtain ⟨w₂, hpt, hk2⟩ :=
      land_reservoirI hX w.c.hres hk₂ (M.trans w.c.hm hm₂) hZ
    exact ⟨w₂, ⟨by rw [hpt]; exact hm₂, fun φ hφ h => by
      rw [hk2]; exact K.force_mono φ hk₂ (w.c.hth φ hφ h)⟩, hpt⟩
  back := by
    rintro m w rfl w₂ hw
    exact ⟨w₂.m, hw.1, rfl⟩

end IPC

/-! ## PLL, level `3ν + 2` -/

section PLL

variable {A : String → Prop} (X : Finset PLLFormula) (B : LayeredBisim A K M)

/-- Certificate of an amalgam world over `m`: a reservoir pair `(k′, m′)` at
level `3d + 2` below a current pair `(k, m)`, either *normal* at level
`3d + 1` or an *`S`-world* at level `3d` with both ends `S`-points; `k′` and
`k` force the same formulas of `X`, `d` the depth of `k′`. -/
structure Cert (k' k : K.W) (m' m : M.W) : Prop where
  hk : K.le k' k
  hm : M.le m' m
  hth : ∀ φ ∈ X, K.force k φ → K.force k' φ
  hres : B.Z (3 * dep X K k' + 2) k' m'
  hcur : B.Z (3 * dep X K k' + 1) k m ∨
    (B.Z (3 * dep X K k') k m ∧ k ∈ K.S ∧ m ∈ M.S)

variable {X B}

theorem Cert.cur {k' k : K.W} {m' m : M.W} (c : Cert X B k' k m' m) :
    B.Z (3 * dep X K k') k m :=
  c.hcur.elim (fun h => B.mono h) (fun h => h.1)

variable (X B)

/-- The worlds of the amalgam. -/
structure AW where
  k' : K.W
  k : K.W
  m' : M.W
  m : M.W
  c : Cert X B k' k m' m

variable {X B}

/-- Inclusion of the `X`-theories of the current `K`-worlds. -/
def thLe (w w' : AW X B) : Prop := ∀ φ ∈ X, K.force w.k φ → K.force w'.k φ

variable (X B)

/-- **The amalgam.**  The order is componentwise on the `M`-coordinate and the
`X`-theory; `S` is the set of worlds whose current pair has both ends in `S`;
atoms other than `p` are read from `M`, `p` from the current `K`-world. -/
def amal (p : String) : SubframeModel where
  W := AW X B
  le := fun a b => M.le a.m b.m ∧ thLe a b
  S := {a | a.m ∈ M.S ∧ a.k ∈ K.S}
  V := fun x => {a | if x = p then PLLFormula.prop p ∈ X ∧ K.force a.k (.prop p)
    else a.m ∈ M.V x}
  refl := fun a => ⟨M.refl _, fun _ _ h => h⟩
  trans := fun h₁ h₂ => ⟨M.trans h₁.1 h₂.1, fun φ hφ h => h₂.2 φ hφ (h₁.2 φ hφ h)⟩
  hered := by
    intro x a b h hv
    have hv' : (if x = p then PLLFormula.prop p ∈ X ∧ K.force a.k (.prop p)
        else a.m ∈ M.V x) := hv
    show (if x = p then PLLFormula.prop p ∈ X ∧ K.force b.k (.prop p)
        else b.m ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx] at hv' ⊢
      exact ⟨hv'.1, h.2 _ hv'.1 hv'.2⟩
    · rw [if_neg hx] at hv' ⊢
      exact M.hered h.1 hv'

variable {X B}

/-- **Landing after a strict move.**  A `K`-world `k₂` above the reservoir
world `k′`, forcing an `X`-formula `k′` lacks, linked to `m₂` at a level
`n ≥ 3·dep k′ − 1`, is the current world of a normal amalgam world over
`m₂`. -/
theorem land_strict (hX : SubClosed X) {k' k₂ : K.W} {m₂ : M.W} {n : Nat}
    (hk : K.le k' k₂) (hZ : B.Z n k₂ m₂)
    (hstrict : ¬ ∀ φ ∈ X, K.force k₂ φ → K.force k' φ)
    (hlev : 3 * dep X K k' ≤ n + 1) :
    ∃ w : AW X B, w.m = m₂ ∧ w.k = k₂ := by
  have hlt := dep_lt hX hk hstrict
  exact ⟨⟨k₂, k₂, m₂, m₂, ⟨K.refl _, M.refl _, fun _ _ h => h,
    B.mono_le (by omega) hZ, Or.inl (B.mono_le (by omega) hZ)⟩⟩, rfl, rfl⟩

/-- **Answering a move of `M` from the reservoir.** -/
theorem land_reservoir (hX : SubClosed X) {k' k₂ : K.W} {m' m₂ : M.W}
    (hres : B.Z (3 * dep X K k' + 2) k' m') (hk : K.le k' k₂) (hm : M.le m' m₂)
    (hZ : B.Z (3 * dep X K k' + 1) k₂ m₂) :
    ∃ w : AW X B, w.m = m₂ ∧ w.k = k₂ := by
  by_cases hsame : ∀ φ ∈ X, K.force k₂ φ → K.force k' φ
  · exact ⟨⟨k', k₂, m', m₂, ⟨hk, hm, hsame, hres, Or.inl hZ⟩⟩, rfl, rfl⟩
  · exact land_strict hX hk hZ hsame (by omega)

/-- **Truth lemma**: an amalgam world forces a formula of `X` exactly when its
current `K`-world does. -/
theorem amal_force (p : String)
    (hA : ∀ a, a ≠ p → PLLFormula.prop a ∈ X → A a) (hX : SubClosed X) :
    ∀ (φ : PLLFormula), φ ∈ X → ∀ w : AW X B,
      ((amal X B p).force w φ ↔ K.force w.k φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ w
      show (if a = p then PLLFormula.prop p ∈ X ∧ K.force w.k (.prop p)
        else w.m ∈ M.V a) ↔ _
      by_cases ha : a = p
      · subst ha
        rw [if_pos rfl]
        exact ⟨fun h => h.2, fun h => ⟨hφ, h⟩⟩
      · rw [if_neg ha]
        exact (B.atoms w.c.cur a (hA a ha hφ)).symm
  | falsePLL => exact fun _ _ => Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro hφ w
      exact and_congr (ihφ (hX.and_left hφ) w) (ihψ (hX.and_right hφ) w)
  | or φ ψ ihφ ihψ =>
      intro hφ w
      exact or_congr (ihφ (hX.or_left hφ) w) (ihψ (hX.or_right hφ) w)
  | ifThen φ ψ ihφ ihψ =>
      intro hmem w
      have hφX := hX.imp_left hmem
      have hψX := hX.imp_right hmem
      constructor
      · -- forcing ⇒ `K`: refute in place, or by a strict move
        intro hN
        by_contra hn
        obtain ⟨k₂, hk₂, hf, hnψ⟩ := exists_of_not_force_imp hn
        by_cases hkφ : K.force w.k φ
        · have h1 := hN w ((amal X B p).refl w) ((ihφ hφX w).mpr hkφ)
          exact hnψ (K.force_mono ψ hk₂ ((ihψ hψX w).mp h1))
        · have hstrict : ¬ ∀ χ ∈ X, K.force k₂ χ → K.force w.k' χ :=
            fun h => hkφ (K.force_mono φ w.c.hk (h φ hφX hf))
          have hlt := dep_lt hX (K.trans w.c.hk hk₂) hstrict
          have hcur : B.Z ((3 * dep X K w.k' - 1) + 1) w.k w.m :=
            B.mono_le (by omega) w.c.cur
          obtain ⟨m₂, hm₂, hZ⟩ := B.forth hcur hk₂
          obtain ⟨w₂, hpt, hk2⟩ :=
            land_strict hX (K.trans w.c.hk hk₂) hZ hstrict (by omega)
          have hR : (amal X B p).le w w₂ :=
            ⟨by rw [hpt]; exact hm₂, fun χ _ h => by
              rw [hk2]; exact K.force_mono χ hk₂ h⟩
          have h1 := hN w₂ hR ((ihφ hφX w₂).mpr (by rw [hk2]; exact hf))
          exact hnψ (by have := (ihψ hψX w₂).mp h1; rwa [hk2] at this)
      · -- `K` ⇒ forcing: the implication travels along the theory order
        intro hw w' hww' hfφ
        have hw' : K.force w'.k (φ.ifThen ψ) := hww'.2 _ hmem hw
        exact (ihψ hψX w').mpr (hw' w'.k (K.refl _) ((ihφ hφX w').mp hfφ))
  | somehow ξ ih =>
      intro hmem w
      have hξX := hX.lax hmem
      constructor
      · -- forcing ⇒ `K`: an `S`-world refutes in place; otherwise move to the
        -- `S`-world over the refuting `S`-point, or land after a strict move
        intro hN
        by_contra hn
        obtain ⟨s, hks, hsS, hnξ⟩ := exists_of_not_force_box hn
        by_cases hS : w.m ∈ M.S ∧ w.k ∈ K.S
        · have h1 := hN w ((amal X B p).refl w) hS
          exact hnξ (K.force_mono ξ hks ((ih hξX w).mp h1))
        · have hcur1 : B.Z (3 * dep X K w.k' + 1) w.k w.m :=
            w.c.hcur.resolve_right fun h => hS ⟨h.2.2, h.2.1⟩
          obtain ⟨m₂, hm₂, hm₂S, hZ⟩ := B.sforth hcur1 hks hsS
          have hw₂ : ∃ w₂ : AW X B, w₂.m = m₂ ∧ w₂.k = s := by
            by_cases hsame : ∀ χ ∈ X, K.force s χ → K.force w.k' χ
            · exact ⟨⟨w.k', s, w.m', m₂, ⟨K.trans w.c.hk hks, M.trans w.c.hm hm₂,
                hsame, w.c.hres, Or.inr ⟨hZ, hsS, hm₂S⟩⟩⟩, rfl, rfl⟩
            · exact land_strict hX (K.trans w.c.hk hks) hZ hsame (by omega)
          obtain ⟨w₂, hpt, hk2⟩ := hw₂
          have hR : (amal X B p).le w w₂ :=
            ⟨by rw [hpt]; exact hm₂, fun χ _ h => by
              rw [hk2]; exact K.force_mono χ hks h⟩
          have hS₂ : w₂ ∈ (amal X B p).S :=
            ⟨by rw [hpt]; exact hm₂S, by rw [hk2]; exact hsS⟩
          have h1 := hN w₂ hR hS₂
          exact hnξ (by have := (ih hξX w₂).mp h1; rwa [hk2] at this)
      · -- `K` ⇒ forcing: the `◯`-formula travels along the theory order and
        -- is discharged at the `S`-point in the current pair
        intro hw w' hww' hw'S
        have hw' : K.force w'.k ξ.somehow := hww'.2 _ hmem hw
        exact (ih hξX w').mpr (hw' w'.k (K.refl _) hw'S.2)

/-- **The projection to `M` is a `p`-variant.**  The zigs are componentwise;
the zags, to `S`-points or not, are answered from the reservoirs. -/
def amal_pbisim (p : String) (hX : SubClosed X) : PBisim p M (amal X B p) where
  Z := fun m w => w.m = m
  atoms := by
    rintro m w rfl a ha
    show w.m ∈ M.V a ↔ (if a = p then PLLFormula.prop p ∈ X ∧ K.force w.k (.prop p)
      else w.m ∈ M.V a)
    rw [if_neg ha]
  forth := by
    rintro m w rfl m₂ hm₂
    obtain ⟨k₂, hk₂, hZ⟩ := B.back w.c.hres (M.trans w.c.hm hm₂)
    obtain ⟨w₂, hpt, hk2⟩ :=
      land_reservoir hX w.c.hres hk₂ (M.trans w.c.hm hm₂) hZ
    exact ⟨w₂, ⟨by rw [hpt]; exact hm₂, fun φ hφ h => by
      rw [hk2]; exact K.force_mono φ hk₂ (w.c.hth φ hφ h)⟩, hpt⟩
  back := by
    rintro m w rfl w₂ hw
    exact ⟨w₂.m, hw.1, rfl⟩
  sforth := by
    rintro m w rfl m₂ hm₂ hm₂S
    obtain ⟨k₂, hk₂, hk₂S, hZ⟩ := B.sback w.c.hres (M.trans w.c.hm hm₂) hm₂S
    obtain ⟨w₂, hpt, hk2⟩ :=
      land_reservoir hX w.c.hres hk₂ (M.trans w.c.hm hm₂) hZ
    exact ⟨w₂, ⟨by rw [hpt]; exact hm₂, fun φ hφ h => by
      rw [hk2]; exact K.force_mono φ hk₂ (w.c.hth φ hφ h)⟩,
      ⟨by rw [hpt]; exact hm₂S, by rw [hk2]; exact hk₂S⟩, hpt⟩
  sback := by
    rintro m w rfl w₂ hw hS
    exact ⟨w₂.m, hw.1, hS.1, rfl⟩

end PLL

end Amalg

open Amalg

/-! ## The amalgamation lemmas -/

/-- **Amalgamation, ◯-free instance, at level `2ν + 1`.**  For a
subformula-closed ◯-free `X`, a link at level `2·(nu X) + 1` between `k₀` and
`m₀`, protecting the atoms of `X` other than `p`, gives a `p`-variant of `M`
(without `S`-clauses) whose distinguished world forces exactly the formulas
of `X` that `k₀` forces. -/
theorem amalgamationI (X : Finset PLLFormula) (hX : SubClosed X)
    (hX0 : ∀ φ ∈ X, boxFree φ = true)
    (p : String) (K M : SubframeModel) (k₀ : K.W) (m₀ : M.W)
    (A : String → Prop) (hA : ∀ a, a ≠ p → PLLFormula.prop a ∈ X → A a)
    (B : LayeredBisimI A K M) (hB : B.Z (2 * nu X + 1) k₀ m₀) :
    ∃ (N : SubframeModel) (C : PBisimI p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ X, (N.force n₀ φ ↔ K.force k₀ φ) := by
  have hd := dep_le_nu X K k₀
  exact ⟨amalI X B p, amalI_pbisim p hX,
    ⟨k₀, k₀, m₀, m₀, ⟨K.refl _, M.refl _, fun _ _ h => h,
      B.mono_le (by omega) hB, B.mono_le (by omega) hB⟩⟩, rfl,
    fun φ hφ => amalI_force p hA hX hX0 φ hφ _⟩

/-- **Amalgamation for PLL in the subframe semantics, at level `3ν + 2`.**
For a subformula-closed `X`, a link at level `3·(nu X) + 2` between `k₀` and
`m₀`, protecting the atoms of `X` other than `p`, gives a `p`-variant of `M`
whose distinguished world forces exactly the formulas of `X` that `k₀`
forces.  The amalgam reads every atom other than `p` from `M`, so it is a
`p`-variant for the full alphabet whatever `K` does off `X`. -/
theorem amalgamation (X : Finset PLLFormula) (hX : SubClosed X)
    (p : String) (K M : SubframeModel) (k₀ : K.W) (m₀ : M.W)
    (A : String → Prop) (hA : ∀ a, a ≠ p → PLLFormula.prop a ∈ X → A a)
    (B : LayeredBisim A K M) (hB : B.Z (3 * nu X + 2) k₀ m₀) :
    ∃ (N : SubframeModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ X, (N.force n₀ φ ↔ K.force k₀ φ) := by
  have hd := dep_le_nu X K k₀
  exact ⟨amal X B p, amal_pbisim p hX,
    ⟨k₀, k₀, m₀, m₀, ⟨K.refl _, M.refl _, fun _ _ h => h,
      B.mono_le (by omega) hB, Or.inl (B.mono_le (by omega) hB)⟩⟩, rfl,
    fun φ hφ => amal_force p hA hX φ hφ _⟩

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SubframeModel.amalgamationI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms amalgamationI

/--
info: 'PLLND.SubframeModel.amalgamation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms amalgamation

/--
info: 'PLLND.SubframeModel.PBisim.force_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PBisim.force_iff

end SubframeModel
end PLLND
