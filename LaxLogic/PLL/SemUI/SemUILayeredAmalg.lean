import LaxLogic.PLL.SemUI.SemUILayered

/-!
# The layered amalgamation lemma for PLL — PROVED at level `4·ν + 2`

`SemUILayered.lean` states the amalgamation lemma of the Litak–Visser route
(their Lemma 5.4; Visser's Lemma 5.1) at level `2·ν + 1` and leaves it open.
This file proves it at level `4·ν + 2`, and from the WEAKER escape form
`LayeredBisimE` of the link:

    amalgamationE :
      SubClosed X → B.Z (4 * nu X + 2) k₀ m₀ →
      ∃ N (C : PBisim p M N) n₀, C.Z m₀ n₀ ∧ ∀ φ ∈ X, (N.force n₀ φ ↔ K.force k₀ φ)

for `B : LayeredBisimE A K M` with `A` protecting the atoms of `X` other than
`p`; the strong form `LayeredBisim (· ≠ p)` follows by `LayeredBisim.toE`.  The statement at `2·ν + 1` is NOT proved here and stays
OPEN.

## Where the earlier attempt stopped, and what is different

The witnessing-triple construction ported from Litak–Visser pairs a canonical
theory with a world of `M` and keeps two links, at levels `2d+1` and `2d`
(`d` the depth of the theory).  It stopped at the forward `◯`-case: a world
`k` refuting `◯ξ` has a successor `v` none of whose `Rₘ`-successors forces
`ξ`, and when `v` forces the same closure formulas as `k` the depth does not
drop, so nothing pays for the move.  In iSL that case never arises (the
refuting world is chosen `⊏`-maximal, which needs the Löb structure).

Two observations remove the obstruction.

1. **Only `X`-rigid refuters are needed.**  Call `z` *`X`-rigid* when every
   `Rₘ`-successor of `z` forces exactly the formulas of `X` that `z` forces.
   Every world has an `X`-rigid `Rₘ`-successor (`exists_rigid`: the set of
   `X`-formulas forced only grows along `Rₘ`, and `X` is finite).  Being
   blocked for `ξ` is inherited along `Rₘ`, so the refuter `v` may always be
   replaced by an `X`-rigid one.  At an `X`-rigid world `◯ξ` and `ξ` have the
   same truth value, so a rigid world refutes every `◯ξ` it does not force
   *in place*: the alternation of promises along an `Rᵢ`-chain, which no
   finite budget can pay for, never has to be reproduced.

2. **A rigid pair is its own reservoir for `Rₘ`.**  The amalgam's worlds are
   of two kinds over a world `m` of `M`:

   * *normal* — a reservoir pair `k′ Z m′` below, at level `4d+2`, and a
     current pair `k Z m` at level `4d+1`, with `k′`, `k` forcing the same
     `X`-formulas.  Moves of `M` (both `Rᵢ` and `Rₘ`) are answered from the
     reservoir, exactly as in Litak–Visser, so they cost nothing.
   * *rigid* — the same reservoir, an `X`-rigid `z₀` linked to `m₀` at level
     `4d`, and a current pair `z Z m` at level `4d−1` with `z₀ Rₘ z`,
     `m₀ Rₘ m`.  An `Rₘ`-move of `M` from `m` is an `Rₘ`-move from `m₀`
     (transitivity), so it is answered from `(z₀, m₀)` and lands on a rigid
     pair with the SAME certificate: no decay.

   The amalgam's `Rₘ` out of a rigid world reaches only rigid worlds with the
   same theory, which is what makes the rigid world block.

The price is two extra levels per unit of depth (the hop to the rigid pair and
the derivation of its current link), hence `4d + 2` in place of `2d + 1`.

The design was fixed by an exact finite computation before any proof was
written (`docs/semui-amalgamation-2026-10-14.md`): on three designed families
of models the realisable closure-types are unchanged when the construction is
restricted to these two kinds of world.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace LayeredAmalg

attribute [local instance] Classical.propDecidable

variable {K M : ConstraintModel}

/-! ## Depth -/

/-- Depth of a world relative to `X`: how many budget formulas of `X`
(variables, implications, `◯`-formulas) it does not force. -/
noncomputable def dep (X : Finset PLLFormula) (K : ConstraintModel) (k : K.W) : Nat :=
  (X.filter (fun φ => isBudget φ = true ∧ ¬ K.force k φ)).card

theorem dep_le_nu (X : Finset PLLFormula) (K : ConstraintModel) (k : K.W) :
    dep X K k ≤ nu X := by
  unfold dep nu
  apply Finset.card_le_card
  intro φ hφ
  simp only [Finset.mem_filter] at hφ ⊢
  exact ⟨hφ.1, hφ.2.1⟩

/-- The budget formulas of `X` decide all of `X` at a non-fallible world. -/
theorem force_of_budget {X : Finset PLLFormula} (hX : SubClosed X) {k k' : K.W}
    (hk' : k' ∉ K.F)
    (h : ∀ φ ∈ X, isBudget φ = true → K.force k' φ → K.force k φ) :
    ∀ φ, φ ∈ X → K.force k' φ → K.force k φ := by
  intro φ
  induction φ with
  | prop a => exact fun hφ hf => h _ hφ rfl hf
  | falsePLL => exact fun _ hf => absurd hf hk'
  | and φ ψ ihφ ihψ =>
      exact fun hφ hf => ⟨ihφ (hX.and_left hφ) hf.1, ihψ (hX.and_right hφ) hf.2⟩
  | or φ ψ ihφ ihψ =>
      exact fun hφ hf => hf.elim (fun x => .inl (ihφ (hX.or_left hφ) x))
        (fun x => .inr (ihψ (hX.or_right hφ) x))
  | ifThen φ ψ _ _ => exact fun hφ hf => h _ hφ rfl hf
  | somehow φ _ => exact fun hφ hf => h _ hφ rfl hf

/-- **A strict move drops the depth**: a non-fallible successor forcing an
`X`-formula the source lacks forces a budget formula the source lacks. -/
theorem dep_lt {X : Finset PLLFormula} (hX : SubClosed X) {k k' : K.W}
    (hkk : K.Ri k k') (hk' : k' ∉ K.F)
    (hne : ¬ ∀ φ ∈ X, K.force k' φ → K.force k φ) :
    dep X K k' < dep X K k := by
  have hex : ∃ φ ∈ X, isBudget φ = true ∧ K.force k' φ ∧ ¬ K.force k φ := by
    by_contra hc
    refine hne (force_of_budget hX hk' fun φ hφ hb hf => ?_)
    by_contra hn
    exact hc ⟨φ, hφ, hb, hf, hn⟩
  obtain ⟨φ, hφ, hb, hf, hn⟩ := hex
  unfold dep
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro ψ hψ
    simp only [Finset.mem_filter] at hψ ⊢
    exact ⟨hψ.1, hψ.2.1, fun hh => hψ.2.2 (K.force_hered hkk hh)⟩
  · intro hEq
    have hm : φ ∈ X.filter (fun φ => isBudget φ = true ∧ ¬ K.force k φ) :=
      Finset.mem_filter.mpr ⟨hφ, hb, hn⟩
    rw [← hEq] at hm
    exact (Finset.mem_filter.mp hm).2.2 hf

/-- A world that does not force some budget formula of `X` has positive depth. -/
theorem dep_pos {X : Finset PLLFormula} {k : K.W} {φ : PLLFormula}
    (hφ : φ ∈ X) (hb : isBudget φ = true) (hn : ¬ K.force k φ) :
    1 ≤ dep X K k :=
  Finset.card_pos.mpr ⟨φ, Finset.mem_filter.mpr ⟨hφ, hb, hn⟩⟩

/-! ## `X`-rigid worlds -/

/-- **Every world has an `X`-rigid `Rₘ`-successor**: along `Rₘ` the set of
forced `X`-formulas only grows, and `X` is finite. -/
theorem exists_rigid (X : Finset PLLFormula) (K : ConstraintModel) :
    ∀ (n : Nat) (v : K.W), (X.filter (fun φ => ¬ K.force v φ)).card = n →
      ∃ z, K.Rm v z ∧ ∀ u, K.Rm z u → ∀ φ ∈ X, K.force u φ → K.force z φ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    by_cases hr : ∀ u, K.Rm v u → ∀ φ ∈ X, K.force u φ → K.force v φ
    · exact ⟨v, K.refl_m v, hr⟩
    · have hex : ∃ u, K.Rm v u ∧ ∃ φ ∈ X, K.force u φ ∧ ¬ K.force v φ := by
        by_contra hc
        refine hr fun u hu φ hφ hf => ?_
        by_contra hn
        exact hc ⟨u, hu, φ, hφ, hf, hn⟩
      obtain ⟨u, hvu, φ, hφ, hfu, hnv⟩ := hex
      have hlt : (X.filter (fun φ => ¬ K.force u φ)).card < n := by
        rw [← hv]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro ψ hψ
          simp only [Finset.mem_filter] at hψ ⊢
          exact ⟨hψ.1, fun hh => hψ.2 (K.force_hered (K.sub_mi hvu) hh)⟩
        · intro hEq
          have hm : φ ∈ X.filter (fun φ => ¬ K.force v φ) :=
            Finset.mem_filter.mpr ⟨hφ, hnv⟩
          rw [← hEq] at hm
          exact (Finset.mem_filter.mp hm).2 hfu
      obtain ⟨z, huz, hz⟩ := ih _ hlt u rfl
      exact ⟨z, K.trans_m hvu huz, hz⟩

/-! ## Certificates and the amalgam's worlds -/

section Amalgam

variable {A : String → Prop} (X : Finset PLLFormula) (B : LayeredBisimE A K M)

/-- Certificate of a *normal* world over `m`: a reservoir pair `(k′, m′)` below
it and a current pair `(k, m)`, with `k′` and `k` forcing the same
`X`-formulas. -/
structure NorCert (k' k : K.W) (m' m : M.W) : Prop where
  hk : K.Ri k' k
  hm : M.Ri m' m
  hth : ∀ φ ∈ X, K.force k φ → K.force k' φ
  hres : B.Z (4 * dep X K k' + 2) k' m'
  hcur : B.Z (4 * dep X K k' + 1) k m

/-- Certificate of a *rigid* world over `m`: the reservoir pair `(k′, m′)`, an
`X`-rigid `z₀` linked to `m₀`, and a current pair `(z, m)` reached from
`(z₀, m₀)` along `Rₘ`. -/
structure RigCert (k' z₀ z : K.W) (m' m₀ m : M.W) : Prop where
  hk : K.Ri k' z₀
  hm' : M.Ri m' m₀
  hth : ∀ φ ∈ X, K.force z₀ φ → K.force k' φ
  hres : B.Z (4 * dep X K k' + 2) k' m'
  hrig : ∀ u, K.Rm z₀ u → ∀ φ ∈ X, K.force u φ → K.force z₀ φ
  hz : K.Rm z₀ z
  hm : M.Rm m₀ m
  hnF : z₀ ∉ K.F
  hpos : 1 ≤ dep X K k'
  hmres : B.Z (4 * dep X K k') z₀ m₀
  hcur : B.Z (4 * dep X K k' - 1) z m

/-- The worlds of the amalgam. -/
inductive NW : Type
  | fal (m : M.W) (h : m ∈ M.F)
  | nor (k' k : K.W) (m' m : M.W) (c : NorCert X B k' k m' m)
  | rig (k' z₀ z : K.W) (m' m₀ m : M.W) (c : RigCert X B k' z₀ z m' m₀ m)

variable {X B}

/-- The `M`-coordinate. -/
def NW.pt : NW X B → M.W
  | .fal m _ => m
  | .nor _ _ _ m _ => m
  | .rig _ _ _ _ _ m _ => m

/-- What the world is meant to force: everything at a fallible world, the
theory of the current `K`-world otherwise. -/
def NW.holds : NW X B → PLLFormula → Prop
  | .fal _ _, _ => True
  | .nor _ k _ _ _, φ => K.force k φ
  | .rig _ _ z _ _ _ _, φ => K.force z φ

def NW.isRig : NW X B → Prop
  | .rig .. => True
  | _ => False

/-- Inclusion of intended theories on `X`. -/
def thLe (w w' : NW X B) : Prop := ∀ φ ∈ X, w.holds φ → w'.holds φ

theorem thLe_refl (w : NW X B) : thLe w w := fun _ _ h => h

theorem thLe_trans {a b c : NW X B} (h₁ : thLe a b) (h₂ : thLe b c) : thLe a c :=
  fun φ hφ h => h₂ φ hφ (h₁ φ hφ h)

/-- A world over a fallible point of `M` is meant to force everything. -/
theorem NW.holds_of_fallible (w : NW X B) (h : w.pt ∈ M.F) (φ : PLLFormula) :
    w.holds φ := by
  cases w with
  | fal m hm => trivial
  | nor k' k m' m c => exact K.force_of_fallible ((B.fall c.hcur).mpr h)
  | rig k' z₀ z m' m₀ m c => exact K.force_of_fallible ((B.fall c.hcur).mpr h)

variable (X B)

/-- **The amalgam.**  Relations componentwise on the `M`-coordinate and the
intended theory; `Rₘ` out of a rigid world reaches only rigid worlds with the
same theory.  Atoms other than `p` and fallibility are read from `M`; `p` is
read from the intended theory. -/
def amal (p : String) : ConstraintModel where
  W := NW X B
  Ri := fun a b => M.Ri a.pt b.pt ∧ thLe a b
  Rm := fun a b => M.Rm a.pt b.pt ∧ thLe a b ∧ (a.isRig → b.isRig ∧ thLe b a)
  F := fun a => a.pt ∈ M.F
  V := fun x a =>
    if x = p then (PLLFormula.prop p ∈ X ∧ a.holds (.prop p)) ∨ a.pt ∈ M.F
    else a.pt ∈ M.V x
  refl_i := fun a => ⟨M.refl_i _, thLe_refl a⟩
  trans_i := fun h₁ h₂ => ⟨M.trans_i h₁.1 h₂.1, thLe_trans h₁.2 h₂.2⟩
  refl_m := fun a => ⟨M.refl_m _, thLe_refl a, fun h => ⟨h, thLe_refl a⟩⟩
  trans_m := fun h₁ h₂ =>
    ⟨M.trans_m h₁.1 h₂.1, thLe_trans h₁.2.1 h₂.2.1, fun h =>
      ⟨(h₂.2.2 (h₁.2.2 h).1).1,
        thLe_trans (h₂.2.2 (h₁.2.2 h).1).2 (h₁.2.2 h).2⟩⟩
  sub_mi := fun h => ⟨M.sub_mi h.1, h.2.1⟩
  hered_F := fun h hF => M.hered_F h.1 hF
  hered_V := by
    intro x a b h hv
    have hv' : (if x = p then (PLLFormula.prop p ∈ X ∧ a.holds (.prop p)) ∨ a.pt ∈ M.F
        else a.pt ∈ M.V x) := hv
    show (if x = p then (PLLFormula.prop p ∈ X ∧ b.holds (.prop p)) ∨ b.pt ∈ M.F
        else b.pt ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx] at hv' ⊢
      rcases hv' with ⟨hpX, ha⟩ | hF
      · exact Or.inl ⟨hpX, h.2 _ hpX ha⟩
      · exact Or.inr (M.hered_F h.1 hF)
    · rw [if_neg hx] at hv' ⊢
      exact M.hered_V h.1 hv'
  full_F := by
    intro x a hF
    show (if x = p then (PLLFormula.prop p ∈ X ∧ a.holds (.prop p)) ∨ a.pt ∈ M.F
        else a.pt ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx]
      exact Or.inr hF
    · rw [if_neg hx]
      exact M.full_F hF

variable {X B}

/-! ## The two landing lemmas -/

/-- **Landing after a strict move.**  A `K`-world `k₂` above the reservoir
world `k′`, forcing an `X`-formula `k′` lacks, and linked to `m₂` with two
levels of slack below `4·dep k′`, is the current world of a non-rigid amalgam
world over `m₂`. -/
theorem land_strict (hX : SubClosed X) {k' k₂ : K.W} {m₂ : M.W} {n : Nat}
    (hk : K.Ri k' k₂) (hZ : B.Z n k₂ m₂)
    (hstrict : ¬ ∀ φ ∈ X, K.force k₂ φ → K.force k' φ)
    (hlev : 4 * dep X K k' ≤ n + 2) :
    ∃ w : NW X B, w.pt = m₂ ∧ ¬ w.isRig ∧ ∀ φ, (w.holds φ ↔ K.force k₂ φ) := by
  by_cases hF : m₂ ∈ M.F
  · refine ⟨.fal m₂ hF, rfl, fun h => h, fun φ => ?_⟩
    exact ⟨fun _ => K.force_of_fallible ((B.fall hZ).mpr hF), fun _ => trivial⟩
  · have hk₂ : k₂ ∉ K.F := fun h => hF ((B.fall hZ).mp h)
    have hlt := dep_lt hX hk hk₂ hstrict
    refine ⟨.nor k₂ k₂ m₂ m₂ ⟨K.refl_i _, M.refl_i _, fun _ _ h => h,
      B.mono_le (by omega) hZ, B.mono_le (by omega) hZ⟩, rfl, fun h => h,
      fun φ => Iff.rfl⟩

/-- **Answering a move of `M` from the reservoir.**  For any `m₂` above the
reservoir point there is a non-rigid amalgam world over `m₂` whose intended
theory contains the reservoir's. -/
theorem land_reservoir (hX : SubClosed X) {k' : K.W} {m' m₂ : M.W}
    (hres : B.Z (4 * dep X K k' + 2) k' m') (hm : M.Ri m' m₂) :
    ∃ w : NW X B, w.pt = m₂ ∧ ¬ w.isRig ∧ ∀ φ ∈ X, K.force k' φ → w.holds φ := by
  by_cases hF : m₂ ∈ M.F
  · exact ⟨.fal m₂ hF, rfl, fun h => h, fun _ _ _ => trivial⟩
  · rcases B.iback hres hm with ⟨k₂, hk, hZ⟩ | hF'
    · by_cases hsame : ∀ φ ∈ X, K.force k₂ φ → K.force k' φ
      · exact ⟨.nor k' k₂ m' m₂ ⟨hk, hm, hsame, hres, hZ⟩, rfl, fun h => h,
          fun φ _ h => K.force_hered hk h⟩
      · obtain ⟨w, hpt, hnr, hw⟩ := land_strict (B := B) hX hk hZ hsame (by omega)
        exact ⟨w, hpt, hnr, fun φ _ h => (hw φ).mpr (K.force_hered hk h)⟩
    · exact absurd hF' hF

/-! ## The truth lemma -/

/-- **Truth lemma**: an amalgam world forces a formula of `X` exactly when its
intended theory contains it. -/
theorem amal_force (p : String)
    (hA : ∀ a, a ≠ p → PLLFormula.prop a ∈ X → A a) (hX : SubClosed X) :
    ∀ (φ : PLLFormula), φ ∈ X → ∀ w : NW X B,
      ((amal X B p).force w φ ↔ w.holds φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ w
      show (if a = p then (PLLFormula.prop p ∈ X ∧ w.holds (.prop p)) ∨ w.pt ∈ M.F
        else w.pt ∈ M.V a) ↔ _
      by_cases ha : a = p
      · subst ha
        rw [if_pos rfl]
        constructor
        · rintro (⟨-, h⟩ | hF)
          · exact h
          · exact w.holds_of_fallible hF _
        · exact fun h => Or.inl ⟨hφ, h⟩
      · rw [if_neg ha]
        cases w with
        | fal m hm => exact ⟨fun _ => trivial, fun _ => M.full_F hm⟩
        | nor k' k m' m c => exact (B.atoms c.hcur a (hA a ha hφ)).symm
        | rig k' z₀ z m' m₀ m c => exact (B.atoms c.hcur a (hA a ha hφ)).symm
  | falsePLL =>
      intro _ w
      show w.pt ∈ M.F ↔ _
      cases w with
      | fal m hm => exact ⟨fun _ => trivial, fun _ => hm⟩
      | nor k' k m' m c => exact (B.fall c.hcur).symm
      | rig k' z₀ z m' m₀ m c => exact (B.fall c.hcur).symm
  | and φ ψ ihφ ihψ =>
      intro hφ w
      have h1 := ihφ (hX.and_left hφ) w
      have h2 := ihψ (hX.and_right hφ) w
      show (amal X B p).force w φ ∧ (amal X B p).force w ψ ↔ _
      cases w with
      | fal m hm => exact ⟨fun _ => trivial, fun _ => ⟨h1.mpr trivial, h2.mpr trivial⟩⟩
      | nor k' k m' m c => exact and_congr h1 h2
      | rig k' z₀ z m' m₀ m c => exact and_congr h1 h2
  | or φ ψ ihφ ihψ =>
      intro hφ w
      have h1 := ihφ (hX.or_left hφ) w
      have h2 := ihψ (hX.or_right hφ) w
      show (amal X B p).force w φ ∨ (amal X B p).force w ψ ↔ _
      cases w with
      | fal m hm => exact ⟨fun _ => trivial, fun _ => .inl (h1.mpr trivial)⟩
      | nor k' k m' m c => exact or_congr h1 h2
      | rig k' z₀ z m' m₀ m c => exact or_congr h1 h2
  | ifThen φ ψ ihφ ihψ =>
      intro hmem w
      have hφX := hX.imp_left hmem
      have hψX := hX.imp_right hmem
      constructor
      · -- forcing ⇒ intended: refute in place, or by a strict move
        intro hN
        cases w with
        | fal m hm => trivial
        | nor k' k m' m c =>
            show K.force k (φ.ifThen ψ)
            by_contra hn
            have hex : ∃ k₂, K.Ri k k₂ ∧ K.force k₂ φ ∧ ¬ K.force k₂ ψ := by
              by_contra hc
              refine hn fun v hv hf => ?_
              by_contra hψ
              exact hc ⟨v, hv, hf, hψ⟩
            obtain ⟨k₂, hk₂, hf, hnψ⟩ := hex
            by_cases hkφ : K.force k φ
            · have h1 := hN (.nor k' k m' m c) ((amal X B p).refl_i _)
                ((ihφ hφX _).mpr hkφ)
              exact hnψ (K.force_hered hk₂ ((ihψ hψX _).mp h1))
            · rcases B.iforth c.hcur hk₂ with ⟨m₂, hm₂, hZ⟩ | hF
              · have hstrict : ¬ ∀ χ ∈ X, K.force k₂ χ → K.force k' χ :=
                  fun h => hkφ (K.force_hered c.hk (h φ hφX hf))
                obtain ⟨w₂, hpt, -, hw₂⟩ := land_strict (B := B) hX
                  (K.trans_i c.hk hk₂) hZ hstrict (by omega)
                have hR : (amal X B p).Ri (.nor k' k m' m c) w₂ :=
                  ⟨by rw [hpt]; exact hm₂,
                    fun χ _ h => (hw₂ χ).mpr (K.force_hered hk₂ h)⟩
                have h1 := hN w₂ hR ((ihφ hφX _).mpr ((hw₂ φ).mpr hf))
                exact hnψ ((hw₂ ψ).mp ((ihψ hψX _).mp h1))
              · exact hnψ (K.force_of_fallible hF)
        | rig k' z₀ z m' m₀ m c =>
            show K.force z (φ.ifThen ψ)
            by_contra hn
            have hex : ∃ k₂, K.Ri z k₂ ∧ K.force k₂ φ ∧ ¬ K.force k₂ ψ := by
              by_contra hc
              refine hn fun v hv hf => ?_
              by_contra hψ
              exact hc ⟨v, hv, hf, hψ⟩
            obtain ⟨k₂, hk₂, hf, hnψ⟩ := hex
            by_cases hkφ : K.force z φ
            · have h1 := hN (.rig k' z₀ z m' m₀ m c) ((amal X B p).refl_i _)
                ((ihφ hφX _).mpr hkφ)
              exact hnψ (K.force_hered hk₂ ((ihψ hψX _).mp h1))
            · have hpos := c.hpos
              have hcur : B.Z ((4 * dep X K k' - 2) + 1) z m :=
                B.mono_le (by omega) c.hcur
              have hk'z : K.Ri k' z := K.trans_i c.hk (K.sub_mi c.hz)
              rcases B.iforth hcur hk₂ with ⟨m₂, hm₂, hZ⟩ | hF
              · have hstrict : ¬ ∀ χ ∈ X, K.force k₂ χ → K.force k' χ :=
                  fun h => hkφ (K.force_hered hk'z (h φ hφX hf))
                obtain ⟨w₂, hpt, -, hw₂⟩ := land_strict (B := B) hX
                  (K.trans_i hk'z hk₂) hZ hstrict (by omega)
                have hR : (amal X B p).Ri (.rig k' z₀ z m' m₀ m c) w₂ :=
                  ⟨by rw [hpt]; exact hm₂,
                    fun χ _ h => (hw₂ χ).mpr (K.force_hered hk₂ h)⟩
                have h1 := hN w₂ hR ((ihφ hφX _).mpr ((hw₂ φ).mpr hf))
                exact hnψ ((hw₂ ψ).mp ((ihψ hψX _).mp h1))
              · exact hnψ (K.force_of_fallible hF)
      · -- intended ⇒ forcing: the implication travels along `thLe`
        intro hw w' hww' hfφ
        have hw' : w'.holds (φ.ifThen ψ) := hww'.2 _ hmem hw
        have hφ' : w'.holds φ := (ihφ hφX w').mp hfφ
        refine (ihψ hψX w').mpr ?_
        cases w' with
        | fal m hm => trivial
        | nor k' k m' m c => exact hw' k (K.refl_i k) hφ'
        | rig k' z₀ z m' m₀ m c => exact hw' z (K.refl_i z) hφ'
  | somehow ξ ih =>
      intro hmem w
      have hξX := hX.lax hmem
      constructor
      · -- forcing ⇒ intended: a rigid world blocks in place; a normal one
        -- hops to an `X`-rigid refuter
        intro hN
        cases w with
        | fal m hm => trivial
        | rig k' z₀ z m' m₀ m c =>
            show K.force z ξ.somehow
            by_contra hn
            have hnξ : ¬ K.force z ξ := fun h =>
              hn fun v hv => ⟨v, K.refl_m v, K.force_hered hv h⟩
            obtain ⟨w'', hR, hf⟩ := hN (.rig k' z₀ z m' m₀ m c) ((amal X B p).refl_i _)
            exact hnξ ((hR.2.2 trivial).2 _ hξX ((ih hξX w'').mp hf))
        | nor k' k m' m c =>
            show K.force k ξ.somehow
            by_contra hn
            have hex : ∃ v, K.Ri k v ∧ ∀ u, K.Rm v u → ¬ K.force u ξ := by
              by_contra hc
              refine hn fun v hv => ?_
              by_contra hno
              exact hc ⟨v, hv, fun u hu hf => hno ⟨u, hu, hf⟩⟩
            obtain ⟨v, hkv, hblock⟩ := hex
            obtain ⟨z, hvz, hrig⟩ := exists_rigid X K _ v rfl
            have hnξ : ¬ K.force z ξ := hblock z hvz
            have hzF : z ∉ K.F := fun h => hnξ (K.force_of_fallible h)
            have hnbox : ¬ K.force z ξ.somehow := by
              intro h
              obtain ⟨u, hu, hf⟩ := h z (K.refl_i z)
              exact hnξ (hrig u hu ξ hξX hf)
            have hkz : K.Ri k z := K.trans_i hkv (K.sub_mi hvz)
            have hk'z : K.Ri k' z := K.trans_i c.hk hkz
            rcases B.iforth c.hcur hkz with ⟨m₂, hm₂, hZ⟩ | hF
            · -- the rigid world over `m₂`, with the old or a fresh reservoir
              have hw' : ∃ w' : NW X B, w'.pt = m₂ ∧ w'.isRig ∧
                  ∀ φ, (w'.holds φ ↔ K.force z φ) := by
                by_cases hsame : ∀ φ ∈ X, K.force z φ → K.force k' φ
                · have hpos : 1 ≤ dep X K k' :=
                    dep_pos hmem rfl fun h => hnbox (K.force_hered hk'z h)
                  exact ⟨.rig k' z z m' m₂ m₂
                    ⟨hk'z, M.trans_i c.hm hm₂, hsame, c.hres, hrig, K.refl_m z,
                      M.refl_m m₂, hzF, hpos, hZ, B.mono_le (by omega) hZ⟩,
                    rfl, trivial, fun φ => Iff.rfl⟩
                · have hlt := dep_lt hX hk'z hzF hsame
                  have hpos : 1 ≤ dep X K z := dep_pos hmem rfl hnbox
                  exact ⟨.rig z z z m₂ m₂ m₂
                    ⟨K.refl_i z, M.refl_i m₂, fun _ _ h => h,
                      B.mono_le (by omega) hZ, hrig, K.refl_m z, M.refl_m m₂, hzF,
                      hpos, B.mono_le (by omega) hZ, B.mono_le (by omega) hZ⟩,
                    rfl, trivial, fun φ => Iff.rfl⟩
              obtain ⟨w', hpt, hrg, hw'⟩ := hw'
              have hR : (amal X B p).Ri (.nor k' k m' m c) w' :=
                ⟨by rw [hpt]; exact hm₂,
                  fun χ _ h => (hw' χ).mpr (K.force_hered hkz h)⟩
              obtain ⟨w'', hR', hf⟩ := hN w' hR
              exact hnξ ((hw' ξ).mp ((hR'.2.2 hrg).2 _ hξX ((ih hξX w'').mp hf)))
            · exact hzF hF
      · -- intended ⇒ forcing: a witness in place, or by one strict `Rₘ`-move
        intro hw w' hww'
        have hw' : w'.holds ξ.somehow := hww'.2 _ hmem hw
        cases w' with
        | fal m hm =>
            exact ⟨.fal m hm, (amal X B p).refl_m _, (ih hξX _).mpr trivial⟩
        | rig k' z₀ z m' m₀ m c =>
            obtain ⟨u, hu, hf⟩ := hw' z (K.refl_i z)
            have hz₀ : K.force z₀ ξ := c.hrig u (K.trans_m c.hz hu) ξ hξX hf
            exact ⟨.rig k' z₀ z m' m₀ m c, (amal X B p).refl_m _,
              (ih hξX _).mpr (K.force_hered (K.sub_mi c.hz) hz₀)⟩
        | nor k' k m' m c =>
            obtain ⟨u, hu, hf⟩ := hw' k (K.refl_i k)
            by_cases hkξ : K.force k ξ
            · exact ⟨.nor k' k m' m c, (amal X B p).refl_m _, (ih hξX _).mpr hkξ⟩
            · obtain ⟨m₂, hm₂, hZ | ⟨-, hF⟩⟩ := B.mforth c.hcur hu
              · have hku : K.Ri k u := K.sub_mi hu
                have hstrict : ¬ ∀ χ ∈ X, K.force u χ → K.force k' χ :=
                  fun h => hkξ (K.force_hered c.hk (h ξ hξX hf))
                obtain ⟨w₂, hpt, -, hw₂⟩ := land_strict (B := B) hX
                  (K.trans_i c.hk hku) hZ hstrict (by omega)
                refine ⟨w₂, ⟨by rw [hpt]; exact hm₂,
                  fun χ _ h => (hw₂ χ).mpr (K.force_hered hku h),
                  fun h => h.elim⟩, (ih hξX _).mpr ((hw₂ ξ).mpr hf)⟩
              · exact ⟨.fal m₂ hF, ⟨hm₂, fun _ _ _ => trivial, fun h => h.elim⟩,
                  (ih hξX _).mpr trivial⟩

/-! ## The amalgam is a `p`-variant of `M` -/

/-- **The projection to `M` is an unbounded bisimulation off `p`.**  The zigs
are componentwise; the zags are answered from the reservoirs. -/
def amal_pbisim (p : String) (hX : SubClosed X) : PBisim p M (amal X B p) where
  Z := fun m w => w.pt = m
  atoms := by
    rintro m w rfl a ha
    show w.pt ∈ M.V a ↔
      (if a = p then (PLLFormula.prop p ∈ X ∧ w.holds (.prop p)) ∨ w.pt ∈ M.F
        else w.pt ∈ M.V a)
    rw [if_neg ha]
  fall := by
    rintro m w rfl
    exact Iff.rfl
  iforth := by
    rintro m w rfl m₂ hm₂
    cases w with
    | fal m hm =>
        exact ⟨.fal m₂ (M.hered_F hm₂ hm), ⟨hm₂, fun _ _ _ => trivial⟩, rfl⟩
    | nor k' k m' m c =>
        obtain ⟨w₂, hpt, -, hw₂⟩ :=
          land_reservoir (B := B) hX c.hres (M.trans_i c.hm hm₂)
        exact ⟨w₂, ⟨by rw [hpt]; exact hm₂, fun φ hφ h => hw₂ φ hφ (c.hth φ hφ h)⟩, hpt⟩
    | rig k' z₀ z m' m₀ m c =>
        obtain ⟨w₂, hpt, -, hw₂⟩ := land_reservoir (B := B) hX c.hres
          (M.trans_i c.hm' (M.trans_i (M.sub_mi c.hm) hm₂))
        refine ⟨w₂, ⟨by rw [hpt]; exact hm₂, fun φ hφ h => hw₂ φ hφ ?_⟩, hpt⟩
        exact c.hth φ hφ (c.hrig z c.hz φ hφ h)
  iback := by
    rintro m w rfl w₂ hw
    exact ⟨w₂.pt, hw.1, rfl⟩
  mforth := by
    rintro m w rfl m₂ hm₂
    cases w with
    | fal m hm =>
        exact ⟨.fal m₂ (M.hered_F (M.sub_mi hm₂) hm),
          ⟨hm₂, fun _ _ _ => trivial, fun h => h.elim⟩, rfl⟩
    | nor k' k m' m c =>
        obtain ⟨w₂, hpt, -, hw₂⟩ :=
          land_reservoir (B := B) hX c.hres (M.trans_i c.hm (M.sub_mi hm₂))
        exact ⟨w₂, ⟨by rw [hpt]; exact hm₂, fun φ hφ h => hw₂ φ hφ (c.hth φ hφ h),
          fun h => h.elim⟩, hpt⟩
    | rig k' z₀ z m' m₀ m c =>
        have hpos := c.hpos
        have hmres : B.Z ((4 * dep X K k' - 1) + 1) z₀ m₀ :=
          B.mono_le (by omega) c.hmres
        have hm₀ : M.Rm m₀ m₂ := M.trans_m c.hm hm₂
        obtain ⟨z₂, hz₂, hZ | ⟨hF, -⟩⟩ := B.mback hmres hm₀
        · refine ⟨.rig k' z₀ z₂ m' m₀ m₂
            ⟨c.hk, c.hm', c.hth, c.hres, c.hrig, hz₂, hm₀, c.hnF, c.hpos, c.hmres, hZ⟩,
            ⟨hm₂, fun φ hφ h => ?_, fun _ => ⟨trivial, fun φ hφ h => ?_⟩⟩, rfl⟩
          · exact K.force_hered (K.sub_mi hz₂) (c.hrig z c.hz φ hφ h)
          · exact K.force_hered (K.sub_mi c.hz) (c.hrig z₂ hz₂ φ hφ h)
        · exact absurd (c.hrig z₂ hz₂ _ hX.bot (K.force_of_fallible hF)) c.hnF
  mback := by
    rintro m w rfl w₂ hw
    exact ⟨w₂.pt, hw.1, rfl⟩

end Amalgam

/-! ## The amalgamation lemma -/

/-- **THE PLL AMALGAMATION LEMMA, escape form, at level `4·ν + 2`.**

For a subformula-closed `X`, if `k₀ ∈ K` and `m₀ ∈ M` are linked at level
`4·(nu X) + 2` by a layered bisimulation with fallibility escapes, then `M` has
a `p`-variant (an UNBOUNDED bisimulation off `p`) whose distinguished world
forces exactly the formulas of `X` that `k₀` forces.

The link has to protect only the atoms of `X` other than `p` (hypothesis `hA`):
the amalgam reads every other atom from `M`, so the output is a `p`-variant of
`M` for the FULL alphabet whatever `K` does off `X`.  This is the form the
route needs, where `K` comes from completeness and knows nothing of `M`'s
other atoms. -/
theorem amalgamationE (X : Finset PLLFormula) (hX : SubClosed X)
    (p : String) (K M : ConstraintModel) (k₀ : K.W) (m₀ : M.W)
    (A : String → Prop) (hA : ∀ a, a ≠ p → PLLFormula.prop a ∈ X → A a)
    (B : LayeredBisimE A K M)
    (hB : B.Z (4 * nu X + 2) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ X, (N.force n₀ φ ↔ K.force k₀ φ) := by
  have hd := dep_le_nu X K k₀
  refine ⟨amal X B p, amal_pbisim p hX,
    .nor k₀ k₀ m₀ m₀ ⟨K.refl_i _, M.refl_i _, fun _ _ h => h,
      B.mono_le (by omega) hB, B.mono_le (by omega) hB⟩, rfl, fun φ hφ => ?_⟩
  exact amal_force p hA hX φ hφ _

/-- **The amalgamation lemma for the strong layered bisimulation**, the
hypothesis form of `SemUILayered.amalgamation`, at level `4·ν + 2`. -/
theorem amalgamation_strong (X : Finset PLLFormula) (hX : SubClosed X)
    (p : String) (K M : ConstraintModel) (k₀ : K.W) (m₀ : M.W)
    (B : LayeredBisim (fun a => a ≠ p) K M)
    (hB : B.Z (4 * nu X + 2) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ X, (N.force n₀ φ ↔ K.force k₀ φ) :=
  amalgamationE X hX p K M k₀ m₀ (fun a => a ≠ p) (fun _ ha _ => ha) B.toE hB

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.LayeredAmalg.exists_rigid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_rigid

/--
info: 'PLLND.SemUI.LayeredAmalg.amal_force' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms amal_force

/--
info: 'PLLND.SemUI.LayeredAmalg.amalgamationE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms amalgamationE

/--
info: 'PLLND.SemUI.LayeredAmalg.amalgamation_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms amalgamation_strong

end LayeredAmalg
end SemUI
end PLLND
